#!/usr/bin/env python3
"""powerk - local control for the LG U+ / Jinheung MTTL-W01 4-outlet smart strip.

Stdlib only, one file, three commands:

  python powerk.py serve       TCP 10086 device server + web UI on 8080  (default)
  python powerk.py provision   point the strip at this PC (while in SoftAP setup mode)
  python powerk.py selftest    offline protocol check

The strip speaks plain text lines ("up:...") over TCP 10086. It connects to this
PC directly because provisioning stores the PC's IP in the strip. No cloud, no
router DNS or DNAT change, no MQTT, no Home Assistant.
"""
from __future__ import annotations

import argparse
import asyncio
import base64
import csv
import io
import ipaddress
import json
import re
import secrets
import socket
import sqlite3
import sys
import threading
import time
from datetime import datetime, timedelta
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

DEVICE_PORT = 10086
SETUP_HOST = "192.168.1.1"      # strip SoftAP setup service
SETUP_PORT = 30300
WEB_PORT = 8080
POLL_SECONDS = 1.0              # 1 s polling for responsive live stats
DIAG_EVERY = 5                  # voltage/RSSI every 5th poll (~5 s)
STATS_RETENTION_DAYS = 7        # persist 1-minute rollups and events for 7 days
RAW_RETENTION_SECONDS = 86400   # keep raw per-poll samples for 24 h
DEFAULT_DB_PATH = Path(__file__).resolve().with_name("powerk_stats.db")

BOOTINFO_RE = re.compile(
    r"^up:bootinfo:([^;\r\n]+);([0-9A-Fa-f]{12});([0-9A-Fa-f]{12});([^;\r\n]+);connect$"
)
GETINFO_RE = re.compile(
    r"(?P<ch>[1-5]):(?P<runtime>-?\d+);(?P<relay>on|off);(?P<state>-?\d+);"
    r"(?P<overload>[^;:]+);(?P<overheat>[^;:]+);(?P<power>-?\d+);"
    r"(?P<energy>[0-9A-Fa-f]{8});(?P<previous>[0-9A-Fa-f]{8});"
    r"(?P<config>[0-9A-Fa-f]{8});(?P<status>[^;:]+);"
    r"(?P<event>[0-9A-Fa-f]{2});(?P<temperature>-?\d+)",
    re.I,
)
ONOFF_ACK_RE = re.compile(r"^up:onoff:([1-4]):(on|off)$", re.I)
EVENT_RE = re.compile(r"^up:event:onoff:([0-4]):(on|off)$", re.I)
POWER_REPORT_RE = re.compile(r"^up:power_report:([1-5]):(-?\d+)$", re.I)
QUERY_RE = re.compile(r"^up:query:(-?\d+)$")

_RANGE_SECONDS = {"1h": 3600, "24h": 86400, "7d": 7 * 86400}


def _flag_active(raw: str) -> bool:
    return raw.strip().lower() not in ("0", "false", "no", "ok", "normal", "")


def _parse_getinfo_record(g: dict[str, str]) -> dict:
    ch = int(g["ch"])
    return {
        "n": ch,
        "on": g["relay"].lower() == "on",
        "power_w": round(int(g["power"]) / 1000.0, 2),
        "energy_kwh": round(int(g["energy"], 16) / 1000.0, 3),
        "prev_energy_kwh": round(int(g["previous"], 16) / 1000.0, 3),
        "temp_c": int(g["temperature"]),
        "runtime_s": int(g["runtime"]),
        "overload": _flag_active(g["overload"]),
        "overheat": _flag_active(g["overheat"]),
        "state_code": int(g["state"]),
        "status": g["status"].strip(),
        "event_hex": g["event"].upper(),
        "config_hex": g["config"].upper(),
    }


def parse_getinfo_all(line: str) -> tuple[list[dict], dict | None]:
    """Parse 'up:getinfo:...' into (outlets 1..4, optional channel-5 aggregate)."""
    text = line.strip("\r\n\x00 ")
    if text.startswith("up:getinfo:"):
        text = text[len("up:getinfo:"):]
    outlets: list[dict] = []
    aggregate: dict | None = None
    for m in GETINFO_RE.finditer(text):
        rec = _parse_getinfo_record(m.groupdict())
        if rec["n"] == 5:
            aggregate = rec
        elif 1 <= rec["n"] <= 4:
            outlets.append(rec)
    return outlets, aggregate


def parse_getinfo(line: str) -> list[dict]:
    """Parse 'up:getinfo:...' into per-outlet records (channel 5 is the aggregate)."""
    outlets, _ = parse_getinfo_all(line)
    return outlets


class Device:
    def __init__(self, mac: str, model: str, fw: str, ip: str):
        self.mac = mac.upper()
        self.model = model
        self.fw = fw
        self.ip = ip
        self.online = False
        self.voltage_v: float | None = None
        self.rssi: int | None = None
        self.last_seen: float | None = None
        self.connected_since: float | None = None
        self.reconnects = 0
        self.poll_ok = 0
        self.poll_timeouts = 0
        self.aggregate: dict | None = None
        self.reported_current_a: dict[int, float] = {}
        self.outlets = {
            n: {
                "n": n,
                "on": False,
                "power_w": 0.0,
                "energy_kwh": 0.0,
                "prev_energy_kwh": 0.0,
                "temp_c": 0,
                "runtime_s": 0,
                "overload": False,
                "overheat": False,
                "state_code": 0,
                "status": "0",
                "event_hex": "00",
                "config_hex": "00000000",
            }
            for n in range(1, 5)
        }

    @property
    def name(self) -> str:
        return f"MTTL {self.mac[-7:]}"

    @property
    def current_a(self) -> float:
        if not self.voltage_v:
            return 0.0
        return round(sum(o["power_w"] for o in self.outlets.values()) / self.voltage_v, 2)

    def snapshot(self) -> dict:
        v = self.voltage_v
        outlets = []
        for o in self.outlets.values():
            rec = dict(o)
            rep_a = self.reported_current_a.get(o["n"])
            rec["reported_current_a"] = rep_a
            rec["current_a"] = rep_a if rep_a is not None else (round(o["power_w"] / v, 2) if v else 0.0)
            outlets.append(rec)
        temps = [o["temp_c"] for o in outlets]
        uptime_s = int(max(0.0, time.time() - self.connected_since)) if (self.online and self.connected_since) else 0
        return {
            "mac": self.mac,
            "name": self.name,
            "model": self.model,
            "fw": self.fw,
            "ip": self.ip,
            "online": self.online,
            "on": any(o["on"] for o in outlets),
            "power_w": round(sum(o["power_w"] for o in outlets), 2),
            "energy_kwh": round(sum(o["energy_kwh"] for o in outlets), 3),
            "voltage": v,
            "current_a": self.current_a,
            "rssi": self.rssi,
            "avg_temp_c": round(sum(temps) / len(temps), 1) if temps else 0.0,
            "max_temp_c": max(temps) if temps else 0,
            "overload": any(bool(o.get("overload")) for o in outlets) or bool((self.aggregate or {}).get("overload")),
            "overheat": any(bool(o.get("overheat")) for o in outlets) or bool((self.aggregate or {}).get("overheat")),
            "aggregate": self.aggregate,
            "last_seen": self.last_seen,
            "connected_since": self.connected_since,
            "uptime_s": uptime_s,
            "reconnects": self.reconnects,
            "poll_ok": self.poll_ok,
            "poll_timeouts": self.poll_timeouts,
            "outlets": outlets,
        }


class StatsStore:
    """Thread-safe persistent SQLite store for 7-day strip & outlet statistics."""

    def __init__(
        self,
        db_path: str | Path = ":memory:",
        retention_days: int = STATS_RETENTION_DAYS,
        poll_seconds: float = POLL_SECONDS,
        flush_interval: float = 5.0,
    ) -> None:
        self.db_path = str(db_path)
        self.retention_days = max(1, int(retention_days))
        self.retention_seconds = self.retention_days * 86400
        self.poll_seconds = max(0.25, float(poll_seconds))
        self.flush_interval = max(0.5, float(flush_interval))
        self._lock = threading.Lock()
        self._conn = sqlite3.connect(self.db_path, check_same_thread=False)
        self._conn.row_factory = sqlite3.Row
        self._init_schema()

        self._last_state: dict[str, dict] = {}
        self._dev_buf: dict[tuple[str, int], dict] = {}
        self._out_buf: dict[tuple[str, int, int], dict] = {}
        self._sample_buf: list[tuple] = []
        self._event_buf: list[tuple] = []
        self._device_buf: dict[str, tuple] = {}
        self._last_flush = time.monotonic()
        self._last_prune = 0.0
        self.prune(time.time())

    def _init_schema(self) -> None:
        with self._lock:
            self._conn.executescript("""
                PRAGMA journal_mode=WAL;
                PRAGMA synchronous=NORMAL;
                CREATE TABLE IF NOT EXISTS devices (
                    mac TEXT PRIMARY KEY,
                    model TEXT NOT NULL,
                    fw TEXT NOT NULL,
                    ip TEXT NOT NULL,
                    last_seen REAL,
                    outlets_json TEXT NOT NULL,
                    voltage_v REAL,
                    rssi INTEGER
                );
                CREATE TABLE IF NOT EXISTS samples (
                    mac TEXT NOT NULL,
                    ts REAL NOT NULL,
                    online INTEGER NOT NULL,
                    power_w REAL NOT NULL,
                    voltage_v REAL,
                    current_a REAL NOT NULL,
                    rssi INTEGER,
                    avg_temp_c REAL NOT NULL,
                    max_temp_c INTEGER NOT NULL,
                    outlets_json TEXT NOT NULL,
                    PRIMARY KEY (mac, ts)
                );
                CREATE TABLE IF NOT EXISTS device_stats_1m (
                    mac TEXT NOT NULL,
                    bucket_ts INTEGER NOT NULL,
                    samples INTEGER NOT NULL,
                    online_samples INTEGER NOT NULL,
                    observed_seconds REAL NOT NULL,
                    online_seconds REAL NOT NULL,
                    on_seconds REAL NOT NULL,
                    energy_wh REAL NOT NULL,
                    power_sum REAL NOT NULL,
                    power_min REAL,
                    power_max REAL,
                    peak_at REAL,
                    voltage_sum REAL NOT NULL,
                    voltage_min REAL,
                    voltage_max REAL,
                    voltage_count INTEGER NOT NULL,
                    current_sum REAL NOT NULL,
                    current_max REAL NOT NULL,
                    temp_sum REAL NOT NULL,
                    temp_min INTEGER,
                    temp_max INTEGER,
                    rssi_sum REAL NOT NULL,
                    rssi_min INTEGER,
                    rssi_max INTEGER,
                    rssi_count INTEGER NOT NULL,
                    PRIMARY KEY (mac, bucket_ts)
                );
                CREATE TABLE IF NOT EXISTS outlet_stats_1m (
                    mac TEXT NOT NULL,
                    bucket_ts INTEGER NOT NULL,
                    outlet INTEGER NOT NULL,
                    samples INTEGER NOT NULL,
                    online_samples INTEGER NOT NULL,
                    on_seconds REAL NOT NULL,
                    energy_wh REAL NOT NULL,
                    power_sum REAL NOT NULL,
                    power_min REAL,
                    power_max REAL,
                    peak_at REAL,
                    temp_sum REAL NOT NULL,
                    temp_min INTEGER,
                    temp_max INTEGER,
                    kwh_last REAL NOT NULL,
                    PRIMARY KEY (mac, bucket_ts, outlet)
                );
                CREATE TABLE IF NOT EXISTS events (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    mac TEXT NOT NULL,
                    ts REAL NOT NULL,
                    outlet INTEGER NOT NULL,
                    event_type TEXT NOT NULL,
                    detail TEXT NOT NULL DEFAULT ''
                );
                CREATE TABLE IF NOT EXISTS rules (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    mac TEXT NOT NULL,
                    outlet INTEGER NOT NULL,
                    kind TEXT NOT NULL,
                    target_on INTEGER NOT NULL,
                    enabled INTEGER NOT NULL DEFAULT 1,
                    fire_at REAL,
                    time_hhmm TEXT,
                    days_json TEXT NOT NULL DEFAULT '[]',
                    threshold_w REAL,
                    idle_s INTEGER,
                    last_fired TEXT,
                    created_at REAL NOT NULL
                );
                CREATE INDEX IF NOT EXISTS idx_events_mac_ts ON events(mac, ts);
                CREATE INDEX IF NOT EXISTS idx_samples_ts ON samples(ts);
                CREATE INDEX IF NOT EXISTS idx_rules_mac ON rules(mac);
            """)

    def load_devices(self) -> dict[str, Device]:
        """Restore previously known devices from disk (initially offline until reconnect)."""
        with self._lock:
            rows = self._conn.execute(
                "SELECT mac, model, fw, ip, last_seen, outlets_json, voltage_v, rssi FROM devices"
            ).fetchall()
        restored: dict[str, Device] = {}
        for r in rows:
            d = Device(r["mac"], r["model"], r["fw"], r["ip"])
            d.online = False
            d.last_seen = r["last_seen"]
            d.voltage_v = r["voltage_v"]
            d.rssi = r["rssi"]
            try:
                saved_outlets = json.loads(r["outlets_json"])
                for item in saved_outlets:
                    n = int(item["n"])
                    if n in d.outlets:
                        d.outlets[n].update(item)
            except Exception:
                pass
            restored[d.mac] = d
        return restored

    def sync_outlet_state(self, mac: str, outlet: int, on: bool) -> None:
        with self._lock:
            st = self._last_state.get(mac.upper())
            if st is not None:
                st["outlet_on"][outlet] = on

    def record_event(self, mac: str, outlet: int, event_type: str, detail: str = "", ts: float | None = None) -> None:
        now = time.time() if ts is None else ts
        with self._lock:
            self._event_buf.append((mac.upper(), now, int(outlet), event_type, detail))
            self._maybe_flush_locked(force=True)

    def record_sample(self, device: Device, now: float | None = None) -> None:
        ts = time.time() if now is None else float(now)
        bucket_ts = int(ts // 60) * 60
        mac = device.mac.upper()
        online = bool(device.online)
        outlets = [device.outlets[n] for n in range(1, 5)]
        total_w = round(sum(float(o["power_w"]) for o in outlets), 2) if online else 0.0
        voltage = device.voltage_v if online else None
        current_a = device.current_a if online else 0.0
        rssi = device.rssi if online else None
        temps = [int(o["temp_c"]) for o in outlets]
        avg_temp = sum(temps) / len(temps) if temps else 0.0
        min_temp = min(temps) if temps else 0
        max_temp = max(temps) if temps else 0

        with self._lock:
            prev = self._last_state.get(mac)
            max_gap = max(15.0, self.poll_seconds * 4.0)
            if prev is None:
                dt = min(self.poll_seconds, 5.0)
                prev_online = False
                prev_power_w = total_w
                prev_out_w = {o["n"]: float(o["power_w"]) for o in outlets}
            else:
                dt = max(0.0, min(ts - prev["ts"], max_gap))
                prev_online = prev["online"]
                prev_power_w = prev["power_w"]
                prev_out_w = prev["outlet_w"]

            # Detect outlet toggles & safety transitions on live updates
            if online and prev is not None:
                for o in outlets:
                    n = o["n"]
                    cur_on = bool(o["on"])
                    if prev["outlet_on"].get(n) is not None and prev["outlet_on"][n] != cur_on:
                        self._event_buf.append((mac, ts, n, "on" if cur_on else "off", "state change"))
                    for flag in ("overload", "overheat"):
                        cur_flag = bool(o.get(flag, False))
                        if cur_flag and not prev[flag].get(n, False):
                            self._event_buf.append((mac, ts, n, flag, f"outlet {n} {flag}"))

            self._last_state[mac] = {
                "ts": ts,
                "online": online,
                "power_w": total_w,
                "outlet_w": {o["n"]: float(o["power_w"]) for o in outlets},
                "outlet_on": {o["n"]: bool(o["on"]) for o in outlets},
                "overload": {o["n"]: bool(o.get("overload", False)) for o in outlets},
                "overheat": {o["n"]: bool(o.get("overheat", False)) for o in outlets},
            }

            energy_wh = ((prev_power_w + total_w) / 2.0 if prev_online else total_w) * (dt / 3600.0) if online else 0.0
            any_on = online and any(bool(o["on"]) for o in outlets)

            d_key = (mac, bucket_ts)
            db = self._dev_buf.get(d_key)
            if db is None:
                db = {
                    "samples": 0, "online_samples": 0,
                    "observed_seconds": 0.0, "online_seconds": 0.0, "on_seconds": 0.0,
                    "energy_wh": 0.0,
                    "power_sum": 0.0, "power_min": None, "power_max": None, "peak_at": None,
                    "voltage_sum": 0.0, "voltage_min": None, "voltage_max": None, "voltage_count": 0,
                    "current_sum": 0.0, "current_max": 0.0,
                    "temp_sum": 0.0, "temp_min": None, "temp_max": None,
                    "rssi_sum": 0.0, "rssi_min": None, "rssi_max": None, "rssi_count": 0,
                }
                self._dev_buf[d_key] = db

            db["samples"] += 1
            db["observed_seconds"] += dt
            if online:
                db["online_samples"] += 1
                db["online_seconds"] += dt
                if any_on:
                    db["on_seconds"] += dt
                db["energy_wh"] += energy_wh
                db["power_sum"] += total_w
                if db["power_min"] is None or total_w < db["power_min"]:
                    db["power_min"] = total_w
                if db["power_max"] is None or total_w > db["power_max"]:
                    db["power_max"] = total_w
                    db["peak_at"] = ts
                if voltage is not None:
                    db["voltage_sum"] += voltage
                    db["voltage_count"] += 1
                    if db["voltage_min"] is None or voltage < db["voltage_min"]:
                        db["voltage_min"] = voltage
                    if db["voltage_max"] is None or voltage > db["voltage_max"]:
                        db["voltage_max"] = voltage
                db["current_sum"] += current_a
                if current_a > db["current_max"]:
                    db["current_max"] = current_a
                db["temp_sum"] += avg_temp
                if db["temp_min"] is None or min_temp < db["temp_min"]:
                    db["temp_min"] = min_temp
                if db["temp_max"] is None or max_temp > db["temp_max"]:
                    db["temp_max"] = max_temp
                if rssi is not None:
                    db["rssi_sum"] += rssi
                    db["rssi_count"] += 1
                    if db["rssi_min"] is None or rssi < db["rssi_min"]:
                        db["rssi_min"] = rssi
                    if db["rssi_max"] is None or rssi > db["rssi_max"]:
                        db["rssi_max"] = rssi

            for o in outlets:
                n = o["n"]
                ow = float(o["power_w"]) if online else 0.0
                ot = int(o["temp_c"])
                o_key = (mac, bucket_ts, n)
                ob = self._out_buf.get(o_key)
                if ob is None:
                    ob = {
                        "samples": 0, "online_samples": 0, "on_seconds": 0.0,
                        "energy_wh": 0.0, "power_sum": 0.0,
                        "power_min": None, "power_max": None, "peak_at": None,
                        "temp_sum": 0.0, "temp_min": None, "temp_max": None,
                        "kwh_last": float(o["energy_kwh"]),
                    }
                    self._out_buf[o_key] = ob
                ob["samples"] += 1
                if online:
                    ob["online_samples"] += 1
                    if o["on"]:
                        ob["on_seconds"] += dt
                    o_ewh = ((prev_out_w.get(n, ow) + ow) / 2.0 if prev_online else ow) * (dt / 3600.0)
                    ob["energy_wh"] += o_ewh
                    ob["power_sum"] += ow
                    if ob["power_min"] is None or ow < ob["power_min"]:
                        ob["power_min"] = ow
                    if ob["power_max"] is None or ow > ob["power_max"]:
                        ob["power_max"] = ow
                        ob["peak_at"] = ts
                    ob["temp_sum"] += ot
                    if ob["temp_min"] is None or ot < ob["temp_min"]:
                        ob["temp_min"] = ot
                    if ob["temp_max"] is None or ot > ob["temp_max"]:
                        ob["temp_max"] = ot
                    ob["kwh_last"] = float(o["energy_kwh"])

            if online:
                compact_outlets = [
                    {"n": o["n"], "on": bool(o["on"]), "power_w": float(o["power_w"]), "temp_c": int(o["temp_c"])}
                    for o in outlets
                ]
                self._sample_buf.append((
                    mac, ts, 1, total_w, voltage, current_a, rssi,
                    round(avg_temp, 1), max_temp, json.dumps(compact_outlets),
                ))
                self._device_buf[mac] = (
                    mac, device.model, device.fw, device.ip, device.last_seen,
                    json.dumps(outlets), device.voltage_v, device.rssi,
                )

            self._maybe_flush_locked(force=False, now=ts)

    def _maybe_flush_locked(self, force: bool = False, now: float | None = None) -> None:
        mono = time.monotonic()
        if not force and (mono - self._last_flush) < self.flush_interval:
            return
        self._flush_locked()
        wall = time.time() if now is None else now
        if (mono - self._last_prune) >= 600.0:
            self._prune_locked(wall)

    def flush(self) -> None:
        with self._lock:
            self._flush_locked()

    def _flush_locked(self) -> None:
        if not (self._dev_buf or self._out_buf or self._sample_buf or self._event_buf or self._device_buf):
            self._last_flush = time.monotonic()
            return
        with self._conn:
            if self._device_buf:
                self._conn.executemany(
                    """
                    INSERT INTO devices (mac, model, fw, ip, last_seen, outlets_json, voltage_v, rssi)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                    ON CONFLICT(mac) DO UPDATE SET
                        model=excluded.model, fw=excluded.fw, ip=excluded.ip,
                        last_seen=excluded.last_seen, outlets_json=excluded.outlets_json,
                        voltage_v=excluded.voltage_v, rssi=excluded.rssi
                    """,
                    list(self._device_buf.values()),
                )
                self._device_buf.clear()

            if self._dev_buf:
                self._conn.executemany(
                    """
                    INSERT INTO device_stats_1m (
                        mac, bucket_ts, samples, online_samples, observed_seconds, online_seconds, on_seconds,
                        energy_wh, power_sum, power_min, power_max, peak_at,
                        voltage_sum, voltage_min, voltage_max, voltage_count,
                        current_sum, current_max,
                        temp_sum, temp_min, temp_max,
                        rssi_sum, rssi_min, rssi_max, rssi_count
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    ON CONFLICT(mac, bucket_ts) DO UPDATE SET
                        samples = device_stats_1m.samples + excluded.samples,
                        online_samples = device_stats_1m.online_samples + excluded.online_samples,
                        observed_seconds = device_stats_1m.observed_seconds + excluded.observed_seconds,
                        online_seconds = device_stats_1m.online_seconds + excluded.online_seconds,
                        on_seconds = device_stats_1m.on_seconds + excluded.on_seconds,
                        energy_wh = device_stats_1m.energy_wh + excluded.energy_wh,
                        power_sum = device_stats_1m.power_sum + excluded.power_sum,
                        power_min = CASE
                            WHEN device_stats_1m.power_min IS NULL THEN excluded.power_min
                            WHEN excluded.power_min IS NULL THEN device_stats_1m.power_min
                            ELSE MIN(device_stats_1m.power_min, excluded.power_min)
                        END,
                        power_max = CASE
                            WHEN device_stats_1m.power_max IS NULL THEN excluded.power_max
                            WHEN excluded.power_max IS NULL THEN device_stats_1m.power_max
                            ELSE MAX(device_stats_1m.power_max, excluded.power_max)
                        END,
                        peak_at = CASE
                            WHEN excluded.power_max IS NOT NULL AND (
                                device_stats_1m.power_max IS NULL OR excluded.power_max >= device_stats_1m.power_max
                            ) THEN excluded.peak_at
                            ELSE device_stats_1m.peak_at
                        END,
                        voltage_sum = device_stats_1m.voltage_sum + excluded.voltage_sum,
                        voltage_min = CASE
                            WHEN device_stats_1m.voltage_min IS NULL THEN excluded.voltage_min
                            WHEN excluded.voltage_min IS NULL THEN device_stats_1m.voltage_min
                            ELSE MIN(device_stats_1m.voltage_min, excluded.voltage_min)
                        END,
                        voltage_max = CASE
                            WHEN device_stats_1m.voltage_max IS NULL THEN excluded.voltage_max
                            WHEN excluded.voltage_max IS NULL THEN device_stats_1m.voltage_max
                            ELSE MAX(device_stats_1m.voltage_max, excluded.voltage_max)
                        END,
                        voltage_count = device_stats_1m.voltage_count + excluded.voltage_count,
                        current_sum = device_stats_1m.current_sum + excluded.current_sum,
                        current_max = MAX(device_stats_1m.current_max, excluded.current_max),
                        temp_sum = device_stats_1m.temp_sum + excluded.temp_sum,
                        temp_min = CASE
                            WHEN device_stats_1m.temp_min IS NULL THEN excluded.temp_min
                            WHEN excluded.temp_min IS NULL THEN device_stats_1m.temp_min
                            ELSE MIN(device_stats_1m.temp_min, excluded.temp_min)
                        END,
                        temp_max = CASE
                            WHEN device_stats_1m.temp_max IS NULL THEN excluded.temp_max
                            WHEN excluded.temp_max IS NULL THEN device_stats_1m.temp_max
                            ELSE MAX(device_stats_1m.temp_max, excluded.temp_max)
                        END,
                        rssi_sum = device_stats_1m.rssi_sum + excluded.rssi_sum,
                        rssi_min = CASE
                            WHEN device_stats_1m.rssi_min IS NULL THEN excluded.rssi_min
                            WHEN excluded.rssi_min IS NULL THEN device_stats_1m.rssi_min
                            ELSE MIN(device_stats_1m.rssi_min, excluded.rssi_min)
                        END,
                        rssi_max = CASE
                            WHEN device_stats_1m.rssi_max IS NULL THEN excluded.rssi_max
                            WHEN excluded.rssi_max IS NULL THEN device_stats_1m.rssi_max
                            ELSE MAX(device_stats_1m.rssi_max, excluded.rssi_max)
                        END,
                        rssi_count = device_stats_1m.rssi_count + excluded.rssi_count
                    """,
                    [
                        (
                            mac, bts,
                            d["samples"], d["online_samples"], d["observed_seconds"], d["online_seconds"], d["on_seconds"],
                            d["energy_wh"], d["power_sum"], d["power_min"], d["power_max"], d["peak_at"],
                            d["voltage_sum"], d["voltage_min"], d["voltage_max"], d["voltage_count"],
                            d["current_sum"], d["current_max"],
                            d["temp_sum"], d["temp_min"], d["temp_max"],
                            d["rssi_sum"], d["rssi_min"], d["rssi_max"], d["rssi_count"],
                        )
                        for (mac, bts), d in self._dev_buf.items()
                    ],
                )
                self._dev_buf.clear()

            if self._out_buf:
                self._conn.executemany(
                    """
                    INSERT INTO outlet_stats_1m (
                        mac, bucket_ts, outlet, samples, online_samples, on_seconds, energy_wh,
                        power_sum, power_min, power_max, peak_at, temp_sum, temp_min, temp_max, kwh_last
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    ON CONFLICT(mac, bucket_ts, outlet) DO UPDATE SET
                        samples = outlet_stats_1m.samples + excluded.samples,
                        online_samples = outlet_stats_1m.online_samples + excluded.online_samples,
                        on_seconds = outlet_stats_1m.on_seconds + excluded.on_seconds,
                        energy_wh = outlet_stats_1m.energy_wh + excluded.energy_wh,
                        power_sum = outlet_stats_1m.power_sum + excluded.power_sum,
                        power_min = CASE
                            WHEN outlet_stats_1m.power_min IS NULL THEN excluded.power_min
                            WHEN excluded.power_min IS NULL THEN outlet_stats_1m.power_min
                            ELSE MIN(outlet_stats_1m.power_min, excluded.power_min)
                        END,
                        power_max = CASE
                            WHEN outlet_stats_1m.power_max IS NULL THEN excluded.power_max
                            WHEN excluded.power_max IS NULL THEN outlet_stats_1m.power_max
                            ELSE MAX(outlet_stats_1m.power_max, excluded.power_max)
                        END,
                        peak_at = CASE
                            WHEN excluded.power_max IS NOT NULL AND (
                                outlet_stats_1m.power_max IS NULL OR excluded.power_max >= outlet_stats_1m.power_max
                            ) THEN excluded.peak_at
                            ELSE outlet_stats_1m.peak_at
                        END,
                        temp_sum = outlet_stats_1m.temp_sum + excluded.temp_sum,
                        temp_min = CASE
                            WHEN outlet_stats_1m.temp_min IS NULL THEN excluded.temp_min
                            WHEN excluded.temp_min IS NULL THEN outlet_stats_1m.temp_min
                            ELSE MIN(outlet_stats_1m.temp_min, excluded.temp_min)
                        END,
                        temp_max = CASE
                            WHEN outlet_stats_1m.temp_max IS NULL THEN excluded.temp_max
                            WHEN excluded.temp_max IS NULL THEN outlet_stats_1m.temp_max
                            ELSE MAX(outlet_stats_1m.temp_max, excluded.temp_max)
                        END,
                        kwh_last = excluded.kwh_last
                    """,
                    [
                        (
                            mac, bts, outlet,
                            d["samples"], d["online_samples"], d["on_seconds"], d["energy_wh"],
                            d["power_sum"], d["power_min"], d["power_max"], d["peak_at"],
                            d["temp_sum"], d["temp_min"], d["temp_max"], d["kwh_last"],
                        )
                        for (mac, bts, outlet), d in self._out_buf.items()
                    ],
                )
                self._out_buf.clear()

            if self._sample_buf:
                self._conn.executemany(
                    """
                    INSERT OR REPLACE INTO samples (
                        mac, ts, online, power_w, voltage_v, current_a, rssi, avg_temp_c, max_temp_c, outlets_json
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """,
                    self._sample_buf,
                )
                self._sample_buf.clear()

            if self._event_buf:
                self._conn.executemany(
                    "INSERT INTO events (mac, ts, outlet, event_type, detail) VALUES (?, ?, ?, ?, ?)",
                    self._event_buf,
                )
                self._event_buf.clear()

        self._last_flush = time.monotonic()

    def prune(self, now: float | None = None) -> None:
        with self._lock:
            self._prune_locked(time.time() if now is None else now)

    def _prune_locked(self, now: float) -> None:
        cutoff_7d = int(now - self.retention_seconds)
        cutoff_raw = now - RAW_RETENTION_SECONDS
        with self._conn:
            self._conn.execute("DELETE FROM device_stats_1m WHERE bucket_ts < ?", (cutoff_7d,))
            self._conn.execute("DELETE FROM outlet_stats_1m WHERE bucket_ts < ?", (cutoff_7d,))
            self._conn.execute("DELETE FROM events WHERE ts < ?", (now - self.retention_seconds,))
            self._conn.execute("DELETE FROM samples WHERE ts < ?", (cutoff_raw,))
        self._last_prune = time.monotonic()

    def today_summary(self, mac: str, now: float | None = None) -> dict:
        """Fast summary for today (local midnight to now) used to enrich /api/state."""
        ts = time.time() if now is None else now
        today_start = datetime.fromtimestamp(ts).replace(hour=0, minute=0, second=0, microsecond=0).timestamp()
        bucket_start = int(today_start // 60) * 60
        mac = mac.upper()
        with self._lock:
            self._flush_locked()
            row = self._conn.execute(
                """
                SELECT COALESCE(SUM(energy_wh), 0.0) AS energy_wh,
                       COALESCE(MAX(power_max), 0.0) AS peak_power_w,
                       COALESCE(SUM(on_seconds), 0.0) AS on_seconds
                FROM device_stats_1m
                WHERE mac = ? AND bucket_ts >= ?
                """,
                (mac, bucket_start),
            ).fetchone()
            out_rows = self._conn.execute(
                """
                SELECT outlet,
                       COALESCE(SUM(energy_wh), 0.0) AS energy_wh,
                       COALESCE(SUM(on_seconds), 0.0) AS on_seconds
                FROM outlet_stats_1m
                WHERE mac = ? AND bucket_ts >= ?
                GROUP BY outlet
                """,
                (mac, bucket_start),
            ).fetchall()
        out_map = {
            int(r["outlet"]): {
                "today_kwh": round(r["energy_wh"] / 1000.0, 4),
                "today_on_s": int(round(r["on_seconds"])),
            }
            for r in out_rows
        }
        return {
            "today_kwh": round((row["energy_wh"] or 0.0) / 1000.0, 4),
            "peak_power_w_today": round(row["peak_power_w"] or 0.0, 2),
            "today_on_s": int(round(row["on_seconds"] or 0.0)),
            "outlets": out_map,
        }

    def query_stats(
        self,
        devices: dict[str, Device],
        range_name: str = "24h",
        mac_filter: str | None = None,
        now: float | None = None,
    ) -> dict:
        ts = time.time() if now is None else float(now)
        if range_name not in _RANGE_SECONDS:
            range_name = "24h"
        span = _RANGE_SECONDS[range_name]
        since_ts = ts - span
        since_bucket = int(since_ts // 60) * 60
        today_dt = datetime.fromtimestamp(ts).replace(hour=0, minute=0, second=0, microsecond=0)
        seven_day_start = (today_dt - timedelta(days=self.retention_days - 1)).timestamp()
        seven_day_bucket = int(seven_day_start // 60) * 60

        with self._lock:
            self._flush_locked()
            macs = [mac_filter.upper()] if mac_filter else sorted(devices.keys())
            result_devices = []
            for mac in macs:
                dev = devices.get(mac)
                if dev is None:
                    continue
                result_devices.append(
                    self._build_device_stats_locked(dev, range_name, since_ts, since_bucket, seven_day_bucket, ts)
                )

        return {
            "retention_days": self.retention_days,
            "poll_seconds": self.poll_seconds,
            "range": range_name,
            "generated_at": ts,
            "devices": result_devices,
        }

    def _build_device_stats_locked(
        self,
        dev: Device,
        range_name: str,
        since_ts: float,
        since_bucket: int,
        seven_day_bucket: int,
        now: float,
    ) -> dict:
        mac = dev.mac
        dev_rows = self._conn.execute(
            "SELECT * FROM device_stats_1m WHERE mac = ? AND bucket_ts >= ? ORDER BY bucket_ts ASC",
            (mac, min(since_bucket, seven_day_bucket)),
        ).fetchall()
        out_rows = self._conn.execute(
            "SELECT * FROM outlet_stats_1m WHERE mac = ? AND bucket_ts >= ? ORDER BY bucket_ts ASC, outlet ASC",
            (mac, min(since_bucket, seven_day_bucket)),
        ).fetchall()
        event_rows = self._conn.execute(
            "SELECT ts, outlet, event_type, detail FROM events WHERE mac = ? AND ts >= ? ORDER BY ts DESC LIMIT 100",
            (mac, since_ts),
        ).fetchall()

        win_dev = [r for r in dev_rows if r["bucket_ts"] >= since_bucket]
        win_out = [r for r in out_rows if r["bucket_ts"] >= since_bucket]

        summary = self._summarize_device_rows(win_dev, event_rows)
        outlets = self._summarize_outlet_rows(win_out, event_rows, summary["energy_kwh"], summary["observed_seconds"])

        if range_name == "1h":
            sample_rows = self._conn.execute(
                "SELECT * FROM samples WHERE mac = ? AND ts >= ? ORDER BY ts ASC",
                (mac, since_ts),
            ).fetchall()
            series = self._series_from_samples(sample_rows, step_s=15) if sample_rows else self._series_from_1m(win_dev, win_out, step_s=60)
        elif range_name == "24h":
            series = self._series_from_1m(win_dev, win_out, step_s=900)
        else:
            series = self._series_from_1m(win_dev, win_out, step_s=3600)

        daily_7d = self._build_daily_7d(
            [r for r in dev_rows if r["bucket_ts"] >= seven_day_bucket],
            [r for r in out_rows if r["bucket_ts"] >= seven_day_bucket],
            now,
        )

        return {
            "mac": mac,
            "name": dev.name,
            "online": dev.online,
            "summary": summary,
            "outlets": outlets,
            "series": series,
            "daily_7d": daily_7d,
            "events": [
                {"ts": r["ts"], "outlet": r["outlet"], "type": r["event_type"], "detail": r["detail"]}
                for r in event_rows[:40]
            ],
        }

    def _summarize_device_rows(self, rows: list[sqlite3.Row], event_rows: list[sqlite3.Row]) -> dict:
        samples = sum(r["samples"] for r in rows)
        online_samples = sum(r["online_samples"] for r in rows)
        observed_s = sum(r["observed_seconds"] for r in rows)
        online_s = sum(r["online_seconds"] for r in rows)
        on_s = sum(r["on_seconds"] for r in rows)
        energy_wh = sum(r["energy_wh"] for r in rows)

        p_mins = [r["power_min"] for r in rows if r["power_min"] is not None]
        p_max_row = max((r for r in rows if r["power_max"] is not None), key=lambda r: r["power_max"], default=None)
        v_sum = sum(r["voltage_sum"] for r in rows)
        v_cnt = sum(r["voltage_count"] for r in rows)
        v_mins = [r["voltage_min"] for r in rows if r["voltage_min"] is not None]
        v_maxs = [r["voltage_max"] for r in rows if r["voltage_max"] is not None]
        c_sum = sum(r["current_sum"] for r in rows)
        c_max = max((r["current_max"] for r in rows), default=0.0)
        t_sum = sum(r["temp_sum"] for r in rows)
        t_mins = [r["temp_min"] for r in rows if r["temp_min"] is not None]
        t_maxs = [r["temp_max"] for r in rows if r["temp_max"] is not None]
        r_sum = sum(r["rssi_sum"] for r in rows)
        r_cnt = sum(r["rssi_count"] for r in rows)
        r_mins = [r["rssi_min"] for r in rows if r["rssi_min"] is not None]
        r_maxs = [r["rssi_max"] for r in rows if r["rssi_max"] is not None]

        return {
            "energy_kwh": round(energy_wh / 1000.0, 4),
            "avg_power_w": round(sum(r["power_sum"] for r in rows) / online_samples, 2) if online_samples else 0.0,
            "min_power_w": round(min(p_mins), 2) if p_mins else 0.0,
            "max_power_w": round(p_max_row["power_max"], 2) if p_max_row else 0.0,
            "peak_power_at": p_max_row["peak_at"] if p_max_row else None,
            "avg_voltage_v": round(v_sum / v_cnt, 1) if v_cnt else None,
            "min_voltage_v": round(min(v_mins), 1) if v_mins else None,
            "max_voltage_v": round(max(v_maxs), 1) if v_maxs else None,
            "avg_current_a": round(c_sum / online_samples, 2) if online_samples else 0.0,
            "max_current_a": round(c_max, 2),
            "avg_temp_c": round(t_sum / online_samples, 1) if online_samples else 0.0,
            "min_temp_c": min(t_mins) if t_mins else 0,
            "max_temp_c": max(t_maxs) if t_maxs else 0,
            "avg_rssi": round(r_sum / r_cnt, 1) if r_cnt else None,
            "min_rssi": min(r_mins) if r_mins else None,
            "max_rssi": max(r_maxs) if r_maxs else None,
            "on_seconds": int(round(on_s)),
            "online_seconds": int(round(online_s)),
            "observed_seconds": int(round(observed_s)),
            "duty_cycle_pct": min(100.0, round(on_s / observed_s * 100.0, 1)) if observed_s else 0.0,
            "online_pct": min(100.0, round(online_s / observed_s * 100.0, 1)) if observed_s else 0.0,
            "samples": samples,
            "overload_events": sum(1 for e in event_rows if e["event_type"] == "overload"),
            "overheat_events": sum(1 for e in event_rows if e["event_type"] == "overheat"),
        }

    def _summarize_outlet_rows(
        self,
        rows: list[sqlite3.Row],
        event_rows: list[sqlite3.Row],
        total_energy_kwh: float,
        observed_s: float,
    ) -> list[dict]:
        by_n: dict[int, list[sqlite3.Row]] = {n: [] for n in range(1, 5)}
        for r in rows:
            n = int(r["outlet"])
            if n in by_n:
                by_n[n].append(r)

        out = []
        for n in range(1, 5):
            rs = by_n[n]
            on_samples = sum(r["online_samples"] for r in rs)
            on_s = sum(r["on_seconds"] for r in rs)
            ewh = sum(r["energy_wh"] for r in rs)
            ekwh = round(ewh / 1000.0, 4)
            p_mins = [r["power_min"] for r in rs if r["power_min"] is not None]
            p_maxs = [r["power_max"] for r in rs if r["power_max"] is not None]
            t_mins = [r["temp_min"] for r in rs if r["temp_min"] is not None]
            t_maxs = [r["temp_max"] for r in rs if r["temp_max"] is not None]
            toggles = sum(1 for e in event_rows if e["outlet"] == n and e["event_type"] in ("on", "off"))
            out.append({
                "n": n,
                "energy_kwh": ekwh,
                "share_pct": round(ekwh / total_energy_kwh * 100.0, 1) if total_energy_kwh > 0 else 0.0,
                "avg_power_w": round(sum(r["power_sum"] for r in rs) / on_samples, 2) if on_samples else 0.0,
                "min_power_w": round(min(p_mins), 2) if p_mins else 0.0,
                "max_power_w": round(max(p_maxs), 2) if p_maxs else 0.0,
                "avg_temp_c": round(sum(r["temp_sum"] for r in rs) / on_samples, 1) if on_samples else 0.0,
                "min_temp_c": min(t_mins) if t_mins else 0,
                "max_temp_c": max(t_maxs) if t_maxs else 0,
                "on_seconds": int(round(on_s)),
                "duty_cycle_pct": min(100.0, round(on_s / observed_s * 100.0, 1)) if observed_s else 0.0,
                "toggle_count": toggles,
            })
        return out

    def _series_from_samples(self, sample_rows: list[sqlite3.Row], step_s: int = 15) -> list[dict]:
        buckets: dict[int, list[sqlite3.Row]] = {}
        for r in sample_rows:
            b = int(r["ts"] // step_s) * step_s
            buckets.setdefault(b, []).append(r)
        out = []
        for b in sorted(buckets):
            rs = buckets[b]
            cnt = len(rs)
            volts = [r["voltage_v"] for r in rs if r["voltage_v"] is not None]
            rssis = [r["rssi"] for r in rs if r["rssi"] is not None]
            op_sum = [0.0, 0.0, 0.0, 0.0]
            for r in rs:
                try:
                    for item in json.loads(r["outlets_json"]):
                        idx = int(item["n"]) - 1
                        if 0 <= idx < 4:
                            op_sum[idx] += float(item["power_w"])
                except Exception:
                    pass
            avg_p = sum(r["power_w"] for r in rs) / cnt
            covered_s = min(step_s, cnt * self.poll_seconds)
            out.append({
                "ts": b,
                "avg_power_w": round(avg_p, 2),
                "min_power_w": round(min(r["power_w"] for r in rs), 2),
                "max_power_w": round(max(r["power_w"] for r in rs), 2),
                "energy_wh": round(avg_p * (covered_s / 3600.0), 3),
                "avg_voltage_v": round(sum(volts) / len(volts), 1) if volts else None,
                "avg_temp_c": round(sum(r["avg_temp_c"] for r in rs) / cnt, 1),
                "avg_rssi": round(sum(rssis) / len(rssis), 1) if rssis else None,
                "online_pct": 100.0,
                "outlet_power_w": [round(x / cnt, 2) for x in op_sum],
            })
        return out

    def _series_from_1m(self, dev_rows: list[sqlite3.Row], out_rows: list[sqlite3.Row], step_s: int) -> list[dict]:
        dbuckets: dict[int, list[sqlite3.Row]] = {}
        for r in dev_rows:
            b = (int(r["bucket_ts"]) // step_s) * step_s
            dbuckets.setdefault(b, []).append(r)
        obuckets: dict[tuple[int, int], list[sqlite3.Row]] = {}
        for r in out_rows:
            b = (int(r["bucket_ts"]) // step_s) * step_s
            obuckets.setdefault((b, int(r["outlet"])), []).append(r)

        out = []
        for b in sorted(dbuckets):
            rs = dbuckets[b]
            on_samples = sum(r["online_samples"] for r in rs)
            obs_s = sum(r["observed_seconds"] for r in rs)
            onl_s = sum(r["online_seconds"] for r in rs)
            v_sum = sum(r["voltage_sum"] for r in rs)
            v_cnt = sum(r["voltage_count"] for r in rs)
            r_sum = sum(r["rssi_sum"] for r in rs)
            r_cnt = sum(r["rssi_count"] for r in rs)
            p_mins = [r["power_min"] for r in rs if r["power_min"] is not None]
            p_maxs = [r["power_max"] for r in rs if r["power_max"] is not None]
            op_w = []
            for n in range(1, 5):
                ors = obuckets.get((b, n), [])
                osamp = sum(x["online_samples"] for x in ors)
                op_w.append(round(sum(x["power_sum"] for x in ors) / osamp, 2) if osamp else 0.0)
            out.append({
                "ts": b,
                "avg_power_w": round(sum(r["power_sum"] for r in rs) / on_samples, 2) if on_samples else 0.0,
                "min_power_w": round(min(p_mins), 2) if p_mins else 0.0,
                "max_power_w": round(max(p_maxs), 2) if p_maxs else 0.0,
                "energy_wh": round(sum(r["energy_wh"] for r in rs), 3),
                "avg_voltage_v": round(v_sum / v_cnt, 1) if v_cnt else None,
                "avg_temp_c": round(sum(r["temp_sum"] for r in rs) / on_samples, 1) if on_samples else 0.0,
                "avg_rssi": round(r_sum / r_cnt, 1) if r_cnt else None,
                "online_pct": min(100.0, round(onl_s / obs_s * 100.0, 1)) if obs_s else 0.0,
                "outlet_power_w": op_w,
            })
        return out

    def _build_daily_7d(
        self,
        dev_rows: list[sqlite3.Row],
        out_rows: list[sqlite3.Row],
        now: float,
    ) -> list[dict]:
        today = datetime.fromtimestamp(now).date()
        days = [(today - timedelta(days=i)).isoformat() for i in range(self.retention_days - 1, -1, -1)]
        d_by_day: dict[str, list[sqlite3.Row]] = {d: [] for d in days}
        o_by_day: dict[tuple[str, int], list[sqlite3.Row]] = {}
        for r in dev_rows:
            day = datetime.fromtimestamp(r["bucket_ts"]).date().isoformat()
            if day in d_by_day:
                d_by_day[day].append(r)
        for r in out_rows:
            day = datetime.fromtimestamp(r["bucket_ts"]).date().isoformat()
            if day in d_by_day:
                o_by_day.setdefault((day, int(r["outlet"])), []).append(r)

        out = []
        for day in days:
            rs = d_by_day[day]
            on_samples = sum(r["online_samples"] for r in rs)
            obs_s = sum(r["observed_seconds"] for r in rs)
            onl_s = sum(r["online_seconds"] for r in rs)
            on_s = sum(r["on_seconds"] for r in rs)
            v_sum = sum(r["voltage_sum"] for r in rs)
            v_cnt = sum(r["voltage_count"] for r in rs)
            v_mins = [r["voltage_min"] for r in rs if r["voltage_min"] is not None]
            v_maxs = [r["voltage_max"] for r in rs if r["voltage_max"] is not None]
            p_maxs = [r["power_max"] for r in rs if r["power_max"] is not None]
            t_maxs = [r["temp_max"] for r in rs if r["temp_max"] is not None]
            outlet_kwh = [
                round(sum(x["energy_wh"] for x in o_by_day.get((day, n), [])) / 1000.0, 4)
                for n in range(1, 5)
            ]
            out.append({
                "date": day,
                "energy_kwh": round(sum(r["energy_wh"] for r in rs) / 1000.0, 4),
                "avg_power_w": round(sum(r["power_sum"] for r in rs) / on_samples, 2) if on_samples else 0.0,
                "max_power_w": round(max(p_maxs), 2) if p_maxs else 0.0,
                "avg_voltage_v": round(v_sum / v_cnt, 1) if v_cnt else None,
                "min_voltage_v": round(min(v_mins), 1) if v_mins else None,
                "max_voltage_v": round(max(v_maxs), 1) if v_maxs else None,
                "avg_temp_c": round(sum(r["temp_sum"] for r in rs) / on_samples, 1) if on_samples else 0.0,
                "max_temp_c": max(t_maxs) if t_maxs else 0,
                "on_seconds": int(round(on_s)),
                "online_pct": min(100.0, round(onl_s / obs_s * 100.0, 1)) if obs_s else 0.0,
                "samples": sum(r["samples"] for r in rs),
                "outlet_kwh": outlet_kwh,
            })
        return out

    def export_csv(self, devices: dict[str, Device], range_name: str = "7d", mac_filter: str | None = None) -> str:
        stats = self.query_stats(devices, range_name="7d" if range_name == "daily" else range_name, mac_filter=mac_filter)
        buf = io.StringIO()
        w = csv.writer(buf)
        if range_name == "daily":
            w.writerow([
                "mac", "name", "date", "energy_kwh", "avg_power_w", "max_power_w",
                "avg_voltage_v", "min_voltage_v", "max_voltage_v", "avg_temp_c", "max_temp_c",
                "on_seconds", "online_pct", "outlet1_kwh", "outlet2_kwh", "outlet3_kwh", "outlet4_kwh",
            ])
            for d in stats["devices"]:
                for row in d["daily_7d"]:
                    w.writerow([
                        d["mac"], d["name"], row["date"], row["energy_kwh"], row["avg_power_w"], row["max_power_w"],
                        row["avg_voltage_v"], row["min_voltage_v"], row["max_voltage_v"],
                        row["avg_temp_c"], row["max_temp_c"], row["on_seconds"], row["online_pct"],
                        *row["outlet_kwh"],
                    ])
        else:
            w.writerow([
                "mac", "name", "timestamp", "iso_time", "energy_wh", "avg_power_w", "min_power_w", "max_power_w",
                "avg_voltage_v", "avg_temp_c", "avg_rssi", "online_pct",
                "outlet1_w", "outlet2_w", "outlet3_w", "outlet4_w",
            ])
            for d in stats["devices"]:
                for row in d["series"]:
                    iso = datetime.fromtimestamp(row["ts"]).isoformat(timespec="seconds")
                    w.writerow([
                        d["mac"], d["name"], row["ts"], iso, row["energy_wh"],
                        row["avg_power_w"], row["min_power_w"], row["max_power_w"],
                        row["avg_voltage_v"], row["avg_temp_c"], row["avg_rssi"], row["online_pct"],
                        *row["outlet_power_w"],
                    ])
        return buf.getvalue()

    def list_rules(self, mac_filter: str | None = None) -> list[dict]:
        now = time.time()
        with self._lock:
            if mac_filter:
                rows = self._conn.execute(
                    "SELECT * FROM rules WHERE mac = ? ORDER BY id DESC", (mac_filter.upper(),)
                ).fetchall()
            else:
                rows = self._conn.execute("SELECT * FROM rules ORDER BY id DESC").fetchall()
        out = []
        for r in rows:
            days = json.loads(r["days_json"] or "[]")
            rem = max(0, int(round(r["fire_at"] - now))) if r["kind"] == "timer" and r["fire_at"] else None
            out.append({
                "id": int(r["id"]),
                "mac": r["mac"],
                "outlet": int(r["outlet"]),
                "kind": r["kind"],
                "target_on": bool(r["target_on"]),
                "enabled": bool(r["enabled"]),
                "fire_at": r["fire_at"],
                "remaining_s": rem,
                "time_hhmm": r["time_hhmm"],
                "days": days,
                "threshold_w": r["threshold_w"],
                "idle_s": r["idle_s"],
                "last_fired": r["last_fired"],
            })
        return out

    def add_rule(self, req: dict) -> dict:
        mac = str(req["mac"]).upper()
        outlet = int(req.get("outlet", 0))
        kind = str(req["kind"]).lower()
        target_on = bool(req.get("target_on", False))
        now = time.time()
        if outlet not in (0, 1, 2, 3, 4):
            raise ValueError("bad outlet")
        if kind == "timer":
            delay_s = max(1, int(req["delay_s"]))
            fire_at = now + delay_s
            vals = (mac, outlet, "timer", int(target_on), 1, fire_at, None, "[]", None, None, None, now)
        elif kind == "schedule":
            hhmm = str(req["time_hhmm"]).strip()
            if not re.fullmatch(r"(?:[01]\d|2[0-3]):[0-5]\d", hhmm):
                raise ValueError("time_hhmm must be HH:MM")
            days = [int(d) for d in req.get("days", []) if 0 <= int(d) <= 6]
            vals = (mac, outlet, "schedule", int(target_on), 1, None, hhmm, json.dumps(sorted(set(days))), None, None, None, now)
        elif kind == "standby":
            if outlet == 0:
                raise ValueError("standby auto-off applies to outlets 1-4")
            threshold_w = max(0.0, float(req.get("threshold_w", 2.0)))
            idle_s = max(10, int(req.get("idle_s", 300)))
            vals = (mac, outlet, "standby", 0, 1, None, None, "[]", threshold_w, idle_s, None, now)
        else:
            raise ValueError("bad rule kind")

        with self._lock, self._conn:
            cur = self._conn.execute(
                """
                INSERT INTO rules (
                    mac, outlet, kind, target_on, enabled, fire_at, time_hhmm,
                    days_json, threshold_w, idle_s, last_fired, created_at
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """,
                vals,
            )
            rule_id = cur.lastrowid
        return next(r for r in self.list_rules(mac) if r["id"] == rule_id)

    def toggle_rule(self, rule_id: int, enabled: bool) -> bool:
        with self._lock, self._conn:
            cur = self._conn.execute("UPDATE rules SET enabled = ? WHERE id = ?", (int(bool(enabled)), int(rule_id)))
            return cur.rowcount > 0

    def delete_rule(self, rule_id: int) -> bool:
        with self._lock, self._conn:
            cur = self._conn.execute("DELETE FROM rules WHERE id = ?", (int(rule_id),))
            return cur.rowcount > 0

    def mark_rule_fired(self, rule_id: int, last_fired: str, disable: bool = False) -> None:
        with self._lock, self._conn:
            if disable:
                self._conn.execute(
                    "UPDATE rules SET enabled = 0, last_fired = ? WHERE id = ?", (last_fired, int(rule_id))
                )
            else:
                self._conn.execute(
                    "UPDATE rules SET last_fired = ? WHERE id = ?", (last_fired, int(rule_id))
                )

    def close(self) -> None:
        with self._lock:
            self._flush_locked()
            self._conn.close()


class Session:
    """One connected strip. Only one command transaction runs at a time."""

    def __init__(self, ip: str, reader: asyncio.StreamReader, writer: asyncio.StreamWriter):
        self.ip = ip
        self.reader = reader
        self.writer = writer
        self.lock = asyncio.Lock()
        self.device: Device | None = None
        self.got_getinfo = asyncio.Event()
        self.last_cmd = ""
        self.last_rx = ""

    async def send(self, cmd: str) -> None:
        self.last_cmd = cmd
        self.writer.write((cmd + "\r\n").encode("ascii"))
        await self.writer.drain()

    async def _refresh(self, timeout: float = 2.5) -> bool:
        self.got_getinfo.clear()
        await self.send("up:getinfo:all")
        try:
            await asyncio.wait_for(self.got_getinfo.wait(), timeout)
            return True
        except asyncio.TimeoutError:
            return False

    async def refresh(self, timeout: float = 2.5) -> bool:
        async with self.lock:
            return await self._refresh(timeout)

    async def set_outlets(self, channels: list[int], on: bool, stats: StatsStore | None = None, source: str = "api") -> bool:
        async with self.lock:
            for ch in channels:
                await self.send(f"up:onoff:{ch}:{'on' if on else 'off'}")
                if stats and self.device:
                    prev_on = bool(self.device.outlets[ch]["on"])
                    if prev_on != on:
                        stats.record_event(self.device.mac, ch, "on" if on else "off", source)
                    stats.sync_outlet_state(self.device.mac, ch, on)
            await asyncio.sleep(0.3)          # let the relay settle before the snapshot
            return await self._refresh(timeout=4.0)

    async def diagnostics(self) -> None:
        async with self.lock:
            await self.send("up:power_report:1:vol")
            await self.send("up:query:wifirssi")


class Hub:
    def __init__(
        self,
        db_path: str | Path = ":memory:",
        poll_seconds: float = POLL_SECONDS,
        retention_days: int = STATS_RETENTION_DAYS,
    ) -> None:
        self.poll_seconds = max(0.25, float(poll_seconds))
        self.stats = StatsStore(db_path=db_path, retention_days=retention_days, poll_seconds=self.poll_seconds)
        self.devices: dict[str, Device] = self.stats.load_devices()
        self.sessions: dict[str, Session] = {}
        self._standby_since: dict[tuple[str, int], float] = {}

    def session(self, mac: str) -> Session | None:
        s = self.sessions.get(mac.upper())
        if s and s.device and s.device.online and not s.writer.is_closing():
            return s
        return None

    def snapshot(self) -> dict:
        out = []
        for d in self.devices.values():
            snap = d.snapshot()
            today = self.stats.today_summary(d.mac)
            snap["today_kwh"] = today["today_kwh"]
            snap["peak_power_w_today"] = today["peak_power_w_today"]
            snap["today_on_s"] = today["today_on_s"]
            for o in snap["outlets"]:
                o_today = today["outlets"].get(o["n"], {})
                o["today_kwh"] = o_today.get("today_kwh", 0.0)
                o["today_on_s"] = o_today.get("today_on_s", 0)
            out.append(snap)
        return {"devices": out}

    async def _initial_sync(self, s: Session) -> None:
        try:
            await s.refresh(timeout=4.0)
            await s.diagnostics()
        except Exception:
            pass

    async def handle_client(self, reader: asyncio.StreamReader, writer: asyncio.StreamWriter) -> None:
        peer = writer.get_extra_info("peername")
        ip = peer[0] if peer else "?"
        s = Session(ip, reader, writer)
        print(f"[device] connection from {ip}")
        try:
            while True:
                raw = await reader.readline()
                if not raw:
                    break
                if len(raw) > 8192:
                    raise ValueError("line too long")
                line = raw.replace(b"\x00", b"").decode("utf-8", "replace").strip("\r\n ")
                s.last_rx = line

                m = BOOTINFO_RE.match(line)
                if m:
                    mac = m.group(2).upper()
                    now = time.time()
                    d = self.devices.get(mac) or Device(mac, m.group(1), m.group(4), ip)
                    d.model, d.fw, d.ip, d.online = m.group(1), m.group(4), ip, True
                    d.last_seen = now
                    d.connected_since = now
                    d.reconnects += 1
                    s.device = d
                    self.devices[mac] = d
                    old = self.sessions.get(mac)
                    if old and old is not s:
                        old.writer.close()
                    self.sessions[mac] = s
                    self.stats.record_event(mac, 0, "online", f"ip={ip} fw={d.fw}", ts=now)
                    print(f"[device] {d.name} model={d.model} fw={d.fw}")
                    asyncio.create_task(self._initial_sync(s))
                    continue

                if not s.device:
                    continue

                if line.startswith("up:getinfo:"):
                    records, aggregate = parse_getinfo_all(line)
                    if len(records) == 4:
                        now = time.time()
                        s.device.outlets = {r["n"]: r for r in records}
                        s.device.aggregate = aggregate
                        s.device.last_seen = now
                        s.device.poll_ok += 1
                        self.stats.record_sample(s.device, now=now)
                        s.got_getinfo.set()
                    continue

                if line.lower().startswith("up:power_report:"):
                    m = POWER_REPORT_RE.fullmatch(line)
                    if m:
                        ch, val = int(m.group(1)), int(m.group(2))
                        if val >= 50000:                     # mV -> V
                            s.device.voltage_v = round(val / 1000.0, 1)
                        elif 1 <= ch <= 5 and val >= 0:      # sub-50000 -> mA
                            s.device.reported_current_a[ch] = round(val / 1000.0, 3)
                    continue

                m = QUERY_RE.fullmatch(line)
                if m:
                    s.device.rssi = int(m.group(1))
                    continue

                m = EVENT_RE.fullmatch(line)
                if m:
                    ch, on = int(m.group(1)), m.group(2).lower() == "on"
                    if ch == 0:
                        for idx in range(1, 5):
                            s.device.outlets[idx]["on"] = on
                            self.stats.sync_outlet_state(s.device.mac, idx, on)
                        self.stats.record_event(s.device.mac, 0, "on" if on else "off", "master button")
                        asyncio.create_task(s.refresh())
                    elif 1 <= ch <= 4:
                        prev_on = bool(s.device.outlets[ch]["on"])
                        s.device.outlets[ch]["on"] = on
                        if prev_on != on:
                            self.stats.record_event(s.device.mac, ch, "on" if on else "off", "device button")
                        self.stats.sync_outlet_state(s.device.mac, ch, on)
                    continue

                if ONOFF_ACK_RE.fullmatch(line):
                    continue
        except (ConnectionResetError, BrokenPipeError, asyncio.IncompleteReadError):
            pass
        except Exception as err:
            print(f"[device] session error {ip}: {err!r} (last sent {s.last_cmd!r}, last received {s.last_rx!r})")
        finally:
            if s.device:
                if self.sessions.get(s.device.mac) is s:
                    self.sessions.pop(s.device.mac, None)
                    s.device.online = False
                    s.device.connected_since = None
                    now = time.time()
                    self.stats.record_event(s.device.mac, 0, "offline", "disconnected", ts=now)
                    self.stats.record_sample(s.device, now=now)
                    print(f"[device] {s.device.name} offline")
            writer.close()
            try:
                await writer.wait_closed()
            except Exception:
                pass

    async def _poll_session(self, s: Session, run_diag: bool) -> None:
        if not s.device:
            return
        try:
            if not await s.refresh():
                s.device.poll_timeouts += 1
                print(f"[device] {s.device.name} poll timeout")
            elif run_diag:
                await s.diagnostics()
        except Exception as err:
            print(f"[device] poll error: {err!r}")

    async def _evaluate_rules(self, now: float) -> None:
        dt_now = datetime.fromtimestamp(now)
        hhmm = dt_now.strftime("%H:%M")
        minute_key = dt_now.strftime("%Y-%m-%d %H:%M")
        weekday = dt_now.weekday()
        for rule in self.stats.list_rules():
            if not rule["enabled"]:
                continue
            mac = rule["mac"]
            s = self.session(mac)
            if not s or not s.device:
                continue
            channels = [1, 2, 3, 4] if rule["outlet"] == 0 else [rule["outlet"]]
            kind = rule["kind"]
            if kind == "timer" and rule["fire_at"] and now >= rule["fire_at"]:
                self.stats.mark_rule_fired(rule["id"], minute_key, disable=True)
                await s.set_outlets(channels, rule["target_on"], stats=self.stats, source="timer")
            elif kind == "schedule":
                days = rule["days"]
                if rule["time_hhmm"] == hhmm and (not days or weekday in days) and rule["last_fired"] != minute_key:
                    self.stats.mark_rule_fired(rule["id"], minute_key, disable=False)
                    await s.set_outlets(channels, rule["target_on"], stats=self.stats, source="schedule")
            elif kind == "standby":
                ch = rule["outlet"]
                o = s.device.outlets.get(ch)
                if o and o["on"] and o["power_w"] <= float(rule["threshold_w"] or 0.0):
                    since = self._standby_since.setdefault((mac, ch), now)
                    if (now - since) >= float(rule["idle_s"] or 300):
                        self._standby_since.pop((mac, ch), None)
                        self.stats.mark_rule_fired(rule["id"], dt_now.isoformat(timespec="seconds"), disable=False)
                        await s.set_outlets([ch], False, stats=self.stats, source="standby")
                else:
                    self._standby_since.pop((mac, ch), None)

    async def poll_loop(self) -> None:
        n = 0
        while True:
            t0 = time.monotonic()
            n += 1
            run_diag = (n % DIAG_EVERY == 0)
            active = list(self.sessions.values())
            if active:
                await asyncio.gather(*(self._poll_session(s, run_diag) for s in active), return_exceptions=True)
            now = time.time()
            for d in list(self.devices.values()):
                if not d.online:
                    self.stats.record_sample(d, now=now)
            await self._evaluate_rules(now)
            elapsed = time.monotonic() - t0
            await asyncio.sleep(max(0.05, self.poll_seconds - elapsed))


PAGE = """<!doctype html>
<meta charset=utf-8>
<meta name=viewport content="width=device-width,initial-scale=1">
<title>powerk</title>
<style>
:root{--bg:#0f1115;--card:#191d24;--card2:#212731;--on:#2ecc71;--off:#39424f;--warn:#e67e22;--err:#e74c3c;--fg:#e8ecf1;--dim:#8b96a5;--line:#2b323f;--acc:#4ea8de}
*{box-sizing:border-box}
body{margin:auto;padding:16px;max-width:960px;background:var(--bg);color:var(--fg);font:15px/1.45 system-ui,sans-serif}
h1{font-size:21px;margin:0}
h2{font-size:16px;margin:0 0 10px}
.top{display:flex;justify-content:space-between;align-items:baseline;gap:12px;flex-wrap:wrap}
.hint{color:var(--dim);font-size:13px;margin:6px 0 16px}
.card{background:var(--card);border-radius:14px;padding:16px;margin-bottom:16px;border:1px solid var(--line)}
.card.off{opacity:.72}
.head{display:flex;justify-content:space-between;align-items:center;gap:10px;flex-wrap:wrap}
.mac{font-weight:600;font-size:16px}
.dot{width:9px;height:9px;border-radius:50%;display:inline-block;background:var(--err);margin-left:4px}
.dot.on{background:var(--on)}
.badge{display:inline-block;font-size:11px;font-weight:600;padding:2px 8px;border-radius:999px;background:var(--card2);color:var(--dim);margin-left:6px}
.badge.warn{background:#4d2c10;color:#ffb86c}
.badge.err{background:#4d1616;color:#ff8a80}
.stats{color:var(--dim);font-size:13px;margin:8px 0 12px;display:flex;flex-wrap:wrap;gap:6px 14px}
.grid{display:grid;grid-template-columns:1fr 1fr;gap:10px}
@media(min-width:720px){.grid{grid-template-columns:repeat(4,1fr)}}
button{border:0;border-radius:12px;padding:12px;font:inherit;color:var(--fg);background:var(--off);text-align:left;width:100%;cursor:pointer;transition:transform .08s ease}
button:active{transform:scale(.99)}
button.on{background:var(--on);color:#06130a}
button small{display:block;opacity:.88;font-size:12px;margin-top:3px}
.toolbar{display:flex;justify-content:space-between;align-items:center;gap:10px;flex-wrap:wrap;margin-bottom:14px}
.tabs{display:inline-flex;gap:6px;background:var(--bg);padding:4px;border-radius:10px;border:1px solid var(--line)}
.tab{width:auto;padding:6px 12px;border-radius:8px;background:transparent;color:var(--dim);font-size:13px;font-weight:600}
.tab.active{background:var(--acc);color:#06131c}
.links{display:flex;gap:10px;font-size:13px}
.links a{color:var(--acc);text-decoration:none}
.links a:hover{text-decoration:underline}
.kpis{display:grid;grid-template-columns:repeat(2,1fr);gap:10px;margin-bottom:14px}
@media(min-width:680px){.kpis{grid-template-columns:repeat(4,1fr)}}
.kpi{background:var(--card2);border-radius:10px;padding:10px 12px}
.kpi .lbl{font-size:11px;color:var(--dim);text-transform:uppercase;letter-spacing:.04em}
.kpi .val{font-size:18px;font-weight:700;margin-top:2px}
.kpi .sub{font-size:12px;color:var(--dim);margin-top:2px}
.chart-wrap{background:var(--bg);border:1px solid var(--line);border-radius:10px;padding:10px;margin-bottom:14px}
.chart-head{display:flex;justify-content:space-between;align-items:center;font-size:12px;color:var(--dim);margin-bottom:6px;min-height:18px}
svg.chart{width:100%;height:170px;display:block}
table{width:100%;border-collapse:collapse;font-size:13px;margin-bottom:14px}
th,td{padding:7px 8px;border-bottom:1px solid var(--line);text-align:right;white-space:nowrap}
th:first-child,td:first-child{text-align:left}
th{color:var(--dim);font-weight:600;font-size:12px}
.table-scroll{overflow-x:auto}
.bar-bg{background:var(--bg);height:6px;border-radius:999px;overflow:hidden;margin-top:4px;min-width:56px}
.bar-fill{background:var(--on);height:100%}
.events{max-height:220px;overflow-y:auto;font-size:12px;background:var(--bg);border:1px solid var(--line);border-radius:10px;padding:8px 10px}
.ev{display:flex;justify-content:space-between;gap:10px;padding:4px 0;border-bottom:1px solid #1d222b}
.ev:last-child{border-bottom:0}
.muted{color:var(--dim)}
.form-row{display:flex;flex-wrap:wrap;gap:8px;align-items:center;margin-bottom:10px}
.ctrl{background:var(--bg);color:var(--fg);border:1px solid var(--line);border-radius:8px;padding:7px 9px;font:inherit;font-size:13px}
.btn-sm{width:auto;padding:7px 12px;border-radius:8px;font-size:13px;font-weight:600;background:var(--acc);color:#06131c}
.btn-ghost{width:auto;padding:5px 9px;border-radius:8px;font-size:12px;background:var(--card2);color:var(--fg)}
.rule{display:flex;justify-content:space-between;align-items:center;gap:10px;padding:8px 10px;background:var(--card2);border-radius:10px;margin-top:6px;font-size:13px;flex-wrap:wrap}
</style>
<div class=top>
  <h1>powerk</h1>
  <div class=hint id=hint style="margin:0"></div>
</div>
<div style="height:12px"></div>
<div id=app></div>
<div id=rules-app></div>
<div id=stats-app></div>
<script>
const tok = new URLSearchParams(location.search).get('t') || '';
const withTok = p => tok ? p + (p.includes('?') ? '&' : '?') + 't=' + encodeURIComponent(tok) : p;
const api = async (p, b) => (await fetch(withTok(p), b ? {method:'POST', headers:{'Content-Type':'application/json'}, body:JSON.stringify(b)} : undefined)).json();
const cmd = (mac, outlet, on) => { api('api/onoff', {mac, outlet, on}).catch(()=>{}).then(() => { refreshState(); refreshStats(); }); };
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const fmtDur = s => {
  s = Math.max(0, Math.round(s || 0));
  const d = Math.floor(s / 86400), h = Math.floor((s % 86400) / 3600), m = Math.floor((s % 3600) / 60), sec = s % 60;
  if (d > 0) return `${d}d ${h}h`;
  if (h > 0) return `${h}h ${m}m`;
  if (m > 0) return `${m}m ${sec}s`;
  return `${sec}s`;
};
const fmtTime = ts => ts ? new Date(ts * 1000).toLocaleTimeString([], {hour:'2-digit', minute:'2-digit', second:'2-digit'}) : '-';
const fmtShortTime = ts => ts ? new Date(ts * 1000).toLocaleString([], {month:'short', day:'numeric', hour:'2-digit', minute:'2-digit'}) : '-';
let curRange = '24h';
let lastState = null;

function setRange(r) { curRange = r; refreshStats(); }

function renderState(s) {
  lastState = s;
  document.getElementById('hint').textContent =
    `server ${s.local_ip} | TCP ${s.port} | poll ${s.poll_seconds}s | ${s.retention_days}d persistent stats`;
  document.getElementById('app').innerHTML = s.devices.map(d => `
  <div class="card${d.online ? '' : ' off'}">
    <div class=head>
      <div>
        <span class=mac>${esc(d.name)} <span class="dot${d.online ? ' on' : ''}"></span></span>
        <span class=badge>${d.online ? 'ONLINE · up ' + fmtDur(d.uptime_s) : 'OFFLINE · last ' + fmtShortTime(d.last_seen)}</span>
        ${d.overload ? '<span class="badge err">OVERLOAD</span>' : ''}
        ${d.overheat ? '<span class="badge warn">OVERHEAT</span>' : ''}
      </div>
      <button class="on-off${d.on ? ' on' : ''}" onclick="cmd('${esc(d.mac)}',0,${!d.on})" style="width:auto;padding:9px 16px" ${d.online ? '' : 'disabled'}>${d.on ? 'ALL OFF' : 'ALL ON'}</button>
    </div>
    <div class=stats>
      <span><b>${d.power_w} W</b> live</span>
      <span>Today: <b>${d.today_kwh ?? 0} kWh</b> (peak ${d.peak_power_w_today ?? 0} W)</span>
      <span>Strip meter: ${d.energy_kwh} kWh</span>
      ${d.voltage ? `<span>${d.voltage} V · ${d.current_a} A</span>` : ''}
      <span>Temp: ${d.avg_temp_c ?? 0}°C (max ${d.max_temp_c ?? 0}°C)</span>
      ${d.rssi !== null && d.rssi !== undefined ? `<span>Wi-Fi: ${d.rssi} dBm</span>` : ''}
      ${d.aggregate ? `<span>Ch5 agg: ${d.aggregate.power_w} W · ${d.aggregate.energy_kwh} kWh · ${d.aggregate.temp_c}°C</span>` : ''}
      <span>fw ${esc(d.fw)}</span>
    </div>
    <div class=grid>${d.outlets.map(o => `
      <button class="${o.on ? 'on' : ''}" onclick="cmd('${esc(d.mac)}',${o.n},${!o.on})" ${d.online ? '' : 'disabled'}>
        Outlet ${o.n} · ${o.on ? 'ON' : 'OFF'}
        <small>${o.power_w} W · ${o.current_a ?? 0} A · ${o.temp_c}°C</small>
        <small>Today: ${o.today_kwh ?? 0} kWh (${fmtDur(o.today_on_s ?? 0)})</small>
        ${o.config_hex && o.config_hex !== '00000000' ? `<small>cfg ${esc(o.config_hex)}</small>` : ''}
        ${o.overload || o.overheat ? `<small style="color:#ffdfba">${o.overload ? 'OVERLOAD ' : ''}${o.overheat ? 'OVERHEAT' : ''}</small>` : ''}
      </button>`).join('')}
    </div>
  </div>`).join('') || `<div class=card>No strip connected yet. Provision with: <code>python powerk.py provision --ip ${esc(s.local_ip)} --ssid WIFI --password PW</code></div>`;
}

function buildChart(series, mac) {
  if (!series || series.length === 0) return '<div class="muted" style="padding:20px;text-align:center">Waiting for samples…</div>';
  const W = 760, H = 160, padL = 42, padR = 12, padT = 12, padB = 24;
  const maxP = Math.max(10, ...series.map(p => Math.max(p.max_power_w || 0, p.avg_power_w || 0)));
  const xOf = i => padL + (series.length === 1 ? (W - padL - padR) / 2 : i * (W - padL - padR) / (series.length - 1));
  const yOf = v => padT + (H - padT - padB) * (1 - Math.min(1, Math.max(0, v / maxP)));
  const avgPts = series.map((p, i) => `${xOf(i).toFixed(1)},${yOf(p.avg_power_w).toFixed(1)}`).join(' ');
  const maxPts = series.map((p, i) => `${xOf(i).toFixed(1)},${yOf(p.max_power_w).toFixed(1)}`).join(' ');
  const areaPts = `${xOf(0).toFixed(1)},${(H - padB).toFixed(1)} ${avgPts} ${xOf(series.length - 1).toFixed(1)},${(H - padB).toFixed(1)}`;
  const midP = (maxP / 2).toFixed(0);
  const firstT = fmtShortTime(series[0].ts), lastT = fmtShortTime(series[series.length - 1].ts);
  window['_series_' + mac] = series;
  return `
  <div class=chart-head>
    <span>Power (W) — solid: avg, dashed: peak</span>
    <span id="tip-${esc(mac)}">${series.length} points · hover for details</span>
  </div>
  <svg class=chart viewBox="0 0 ${W} ${H}" onmousemove="hoverChart(event,'${esc(mac)}',${W},${padL},${padR})">
    <line x1=${padL} y1=${padT} x2=${W-padR} y2=${padT} stroke="#2b323f" stroke-dasharray="3,3"/>
    <line x1=${padL} y1=${yOf(maxP/2).toFixed(1)} x2=${W-padR} y2=${yOf(maxP/2).toFixed(1)} stroke="#2b323f" stroke-dasharray="3,3"/>
    <line x1=${padL} y1=${H-padB} x2=${W-padR} y2=${H-padB} stroke="#2b323f"/>
    <text x=4 y=${padT+8} fill="#8b96a5" font-size="11">${maxP.toFixed(0)}W</text>
    <text x=4 y=${yOf(maxP/2).toFixed(1)} fill="#8b96a5" font-size="11">${midP}W</text>
    <text x=4 y=${H-padB} fill="#8b96a5" font-size="11">0W</text>
    <text x=${padL} y=${H-5} fill="#8b96a5" font-size="11">${esc(firstT)}</text>
    <text x=${W-padR} y=${H-5} fill="#8b96a5" font-size="11" text-anchor="end">${esc(lastT)}</text>
    <polygon points="${areaPts}" fill="rgba(46,204,113,0.16)"/>
    <polyline fill="none" stroke="#4ea8de" stroke-width="1.5" stroke-dasharray="4,3" points="${maxPts}"/>
    <polyline fill="none" stroke="#2ecc71" stroke-width="2" points="${avgPts}"/>
  </svg>`;
}

function hoverChart(ev, mac, W, padL, padR) {
  const series = window['_series_' + mac];
  if (!series || !series.length) return;
  const rect = ev.currentTarget.getBoundingClientRect();
  const x = (ev.clientX - rect.left) * (W / rect.width);
  const ratio = Math.min(1, Math.max(0, (x - padL) / Math.max(1, W - padL - padR)));
  const idx = Math.min(series.length - 1, Math.round(ratio * (series.length - 1)));
  const p = series[idx];
  const tip = document.getElementById('tip-' + mac);
  if (tip) {
    tip.textContent = `${fmtShortTime(p.ts)} · avg ${p.avg_power_w}W · peak ${p.max_power_w}W · ${p.energy_wh}Wh · ${p.avg_temp_c}°C` +
      (p.avg_voltage_v ? ` · ${p.avg_voltage_v}V` : '');
  }
}

function renderStats(data) {
  const devs = data.devices || [];
  if (!devs.length) { document.getElementById('stats-app').innerHTML = ''; return; }
  document.getElementById('stats-app').innerHTML = devs.map(d => {
    const s = d.summary;
    const rangeBtn = r => `<button class="tab${curRange === r ? ' active' : ''}" onclick="setRange('${r}')">${r.toUpperCase()}</button>`;
    return `
    <div class=card>
      <div class=toolbar>
        <div>
          <h2 style="margin:0">${esc(d.name)} · Detailed Statistics</h2>
          <div class=muted style="font-size:12px">Persisted ${data.retention_days} days · ${s.samples} samples · ${data.poll_seconds}s polling</div>
        </div>
        <div style="display:flex;align-items:center;gap:12px;flex-wrap:wrap">
          <div class=tabs>${rangeBtn('1h')}${rangeBtn('24h')}${rangeBtn('7d')}</div>
          <div class=links>
            <a href="${withTok(`api/stats.csv?mac=${encodeURIComponent(d.mac)}&range=${curRange}`)}">Series CSV</a>
            <a href="${withTok(`api/stats.csv?mac=${encodeURIComponent(d.mac)}&range=daily`)}">7d Daily CSV</a>
          </div>
        </div>
      </div>

      <div class=kpis>
        <div class=kpi><div class=lbl>Energy (${curRange})</div><div class=val>${s.energy_kwh} kWh</div><div class=sub>${(s.energy_kwh * 1000).toFixed(1)} Wh integrated</div></div>
        <div class=kpi><div class=lbl>Power</div><div class=val>${s.avg_power_w} W</div><div class=sub>min ${s.min_power_w} · peak ${s.max_power_w} W</div></div>
        <div class=kpi><div class=lbl>Voltage</div><div class=val>${s.avg_voltage_v ?? '-'} V</div><div class=sub>${s.min_voltage_v ?? '-'}–${s.max_voltage_v ?? '-'} V</div></div>
        <div class=kpi><div class=lbl>Current</div><div class=val>${s.avg_current_a} A</div><div class=sub>peak ${s.max_current_a} A</div></div>
        <div class=kpi><div class=lbl>Temperature</div><div class=val>${s.avg_temp_c}°C</div><div class=sub>${s.min_temp_c}–${s.max_temp_c}°C</div></div>
        <div class=kpi><div class=lbl>Wi-Fi RSSI</div><div class=val>${s.avg_rssi ?? '-'} dBm</div><div class=sub>${s.min_rssi ?? '-'} to ${s.max_rssi ?? '-'} dBm</div></div>
        <div class=kpi><div class=lbl>Active Time</div><div class=val>${fmtDur(s.on_seconds)}</div><div class=sub>${s.duty_cycle_pct}% duty cycle</div></div>
        <div class=kpi><div class=lbl>Online Uptime</div><div class=val>${s.online_pct}%</div><div class=sub>${fmtDur(s.online_seconds)} · peak ${fmtTime(s.peak_power_at)}</div></div>
      </div>

      <div class=chart-wrap>${buildChart(d.series, d.mac)}</div>

      <h2>Per-Outlet Breakdown (${curRange})</h2>
      <div class=table-scroll>
        <table>
          <thead><tr><th>Outlet</th><th>Energy</th><th>Share</th><th>Avg Power</th><th>Peak Power</th><th>Temp (Avg/Max)</th><th>On Time</th><th>Toggles</th></tr></thead>
          <tbody>${d.outlets.map(o => `
            <tr>
              <td>Outlet ${o.n}</td>
              <td>${o.energy_kwh} kWh</td>
              <td>${o.share_pct}%<div class=bar-bg><div class=bar-fill style="width:${Math.min(100, o.share_pct)}%"></div></div></td>
              <td>${o.avg_power_w} W</td>
              <td>${o.max_power_w} W</td>
              <td>${o.avg_temp_c}° / ${o.max_temp_c}°C</td>
              <td>${fmtDur(o.on_seconds)} (${o.duty_cycle_pct}%)</td>
              <td>${o.toggle_count}</td>
            </tr>`).join('')}
          </tbody>
        </table>
      </div>

      <h2>7-Day Daily History</h2>
      <div class=table-scroll>
        <table>
          <thead><tr><th>Date</th><th>Total kWh</th><th>Avg W</th><th>Peak W</th><th>Voltage</th><th>Max °C</th><th>On Time</th><th>Online</th><th>Outlets 1–4 (kWh)</th></tr></thead>
          <tbody>${d.daily_7d.slice().reverse().map(day => `
            <tr>
              <td>${esc(day.date)}</td>
              <td><b>${day.energy_kwh}</b></td>
              <td>${day.avg_power_w}</td>
              <td>${day.max_power_w}</td>
              <td>${day.avg_voltage_v ?? '-'} V</td>
              <td>${day.max_temp_c}°C</td>
              <td>${fmtDur(day.on_seconds)}</td>
              <td>${day.online_pct}%</td>
              <td class=muted>${day.outlet_kwh.join(' / ')}</td>
            </tr>`).join('')}
          </tbody>
        </table>
      </div>

      <h2>Recent Events (${curRange})</h2>
      <div class=events>${(d.events && d.events.length) ? d.events.map(e => `
        <div class=ev>
          <span><b>${e.outlet ? 'Outlet ' + e.outlet : 'Strip'}</b> · ${esc(e.type.toUpperCase())} <span class=muted>${esc(e.detail)}</span></span>
          <span class=muted>${fmtShortTime(e.ts)}</span>
        </div>`).join('') : '<div class=muted>No events recorded in this window.</div>'}
      </div>
    </div>`;
  }).join('');
}

let lastRules = {rules: []};
async function addRule(mac) {
  const kind = document.getElementById('r-kind-' + mac).value;
  const outlet = Number(document.getElementById('r-out-' + mac).value);
  const target_on = document.getElementById('r-act-' + mac).value === '1';
  const body = {action:'add', mac, outlet, kind, target_on};
  if (kind === 'timer') body.delay_s = Math.max(1, Math.round(Number(document.getElementById('r-min-' + mac).value || 15) * 60));
  if (kind === 'schedule') body.time_hhmm = document.getElementById('r-hhmm-' + mac).value || '22:00';
  if (kind === 'standby') {
    body.threshold_w = Number(document.getElementById('r-watt-' + mac).value || 2);
    body.idle_s = Math.max(10, Math.round(Number(document.getElementById('r-idle-' + mac).value || 5) * 60));
  }
  await api('api/rules', body);
  refreshRules(true);
}
async function toggleRule(id, enabled) { await api('api/rules', {action:'toggle', id, enabled}); refreshRules(true); }
async function delRule(id) { await api('api/rules', {action:'delete', id}); refreshRules(true); }
function onRuleKindChange(mac) {
  const k = document.getElementById('r-kind-' + mac).value;
  document.getElementById('r-timer-box-' + mac).style.display = k === 'timer' ? 'inline-flex' : 'none';
  document.getElementById('r-sched-box-' + mac).style.display = k === 'schedule' ? 'inline-flex' : 'none';
  document.getElementById('r-standby-box-' + mac).style.display = k === 'standby' ? 'inline-flex' : 'none';
  document.getElementById('r-act-' + mac).style.display = k === 'standby' ? 'none' : 'inline-block';
}
function renderRules() {
  const devs = (lastState && lastState.devices) || [];
  if (!devs.length) { document.getElementById('rules-app').innerHTML = ''; return; }
  const rules = lastRules.rules || [];
  document.getElementById('rules-app').innerHTML = devs.map(d => {
    const dr = rules.filter(r => r.mac === d.mac);
    const ruleDesc = r => {
      const target = r.outlet ? 'Outlet ' + r.outlet : 'All Outlets';
      if (r.kind === 'timer') return `${target} → ${r.target_on ? 'ON' : 'OFF'} in ${r.enabled ? fmtDur(r.remaining_s ?? 0) : 'done'}`;
      if (r.kind === 'schedule') return `${target} → ${r.target_on ? 'ON' : 'OFF'} daily at ${esc(r.time_hhmm)}`;
      return `${target} → auto OFF below ${r.threshold_w} W for ${fmtDur(r.idle_s)}`;
    };
    return `
    <div class=card>
      <h2>${esc(d.name)} · Timers, Schedules & Standby Auto-Off</h2>
      <div class=form-row>
        <select class=ctrl id="r-kind-${esc(d.mac)}" onchange="onRuleKindChange('${esc(d.mac)}')">
          <option value=timer>Countdown Timer</option>
          <option value=schedule>Daily Schedule</option>
          <option value=standby>Standby Auto-Off</option>
        </select>
        <select class=ctrl id="r-out-${esc(d.mac)}">
          <option value=1>Outlet 1</option><option value=2>Outlet 2</option>
          <option value=3>Outlet 3</option><option value=4>Outlet 4</option>
          <option value=0>All Outlets</option>
        </select>
        <select class=ctrl id="r-act-${esc(d.mac)}"><option value=0>Turn OFF</option><option value=1>Turn ON</option></select>
        <span id="r-timer-box-${esc(d.mac)}" style="display:inline-flex;gap:6px;align-items:center">
          after <input class=ctrl id="r-min-${esc(d.mac)}" type=number min=1 step=1 value=15 style="width:74px"> min
        </span>
        <span id="r-sched-box-${esc(d.mac)}" style="display:none;gap:6px;align-items:center">
          at <input class=ctrl id="r-hhmm-${esc(d.mac)}" type=time value="23:00">
        </span>
        <span id="r-standby-box-${esc(d.mac)}" style="display:none;gap:6px;align-items:center">
          ≤ <input class=ctrl id="r-watt-${esc(d.mac)}" type=number min=0 step=0.5 value=2 style="width:68px"> W for
          <input class=ctrl id="r-idle-${esc(d.mac)}" type=number min=1 step=1 value=5 style="width:68px"> min
        </span>
        <button class=btn-sm onclick="addRule('${esc(d.mac)}')">Add Rule</button>
      </div>
      ${dr.length ? dr.map(r => `
        <div class=rule style="${r.enabled ? '' : 'opacity:.55'}">
          <span><b>${esc(r.kind.toUpperCase())}</b> · ${ruleDesc(r)}${r.last_fired ? ` <span class=muted>(last ${esc(r.last_fired)})</span>` : ''}</span>
          <span style="display:flex;gap:6px">
            <button class=btn-ghost onclick="toggleRule(${r.id},${!r.enabled})">${r.enabled ? 'Pause' : 'Enable'}</button>
            <button class=btn-ghost onclick="delRule(${r.id})">Delete</button>
          </span>
        </div>`).join('') : '<div class=muted style="font-size:13px">No timers, schedules, or standby rules configured.</div>'}
    </div>`;
  }).join('');
}

async function refreshState() { try { renderState(await api('api/state')); } catch(e) {} }
async function refreshStats() { try { renderStats(await api(`api/stats?range=${curRange}`)); } catch(e) {} }
async function refreshRules(force) {
  try {
    lastRules = await api('api/rules');
    const el = document.getElementById('rules-app');
    if (force || !el.contains(document.activeElement)) renderRules();
  } catch(e) {}
}
refreshState();
refreshStats();
refreshRules(true);
setInterval(refreshState, 1000);
setInterval(refreshStats, 5000);
setInterval(() => refreshRules(false), 5000);
</script>
"""


class Web(BaseHTTPRequestHandler):
    hub: Hub
    loop: asyncio.AbstractEventLoop
    local_ip: str
    port: int
    token: str = ""

    def log_message(self, fmt, *args):
        pass

    def _authorized(self) -> bool:
        """No token set -> open. Otherwise: X-Token header, HTTP Basic (browser) or ?t= (simple clients)."""
        if not self.token:
            return True
        if secrets.compare_digest(self.headers.get("X-Token", ""), self.token):
            return True
        auth = self.headers.get("Authorization", "")
        if auth.startswith("Basic "):
            try:
                user, _, password = base64.b64decode(auth[6:]).decode("utf-8").partition(":")
            except Exception:
                return False
            if secrets.compare_digest(password, self.token) or secrets.compare_digest(user, self.token):
                return True
        return secrets.compare_digest(parse_qs(urlparse(self.path).query).get("t", [""])[0], self.token)

    def _deny(self):
        body = b"powerk: token required\n"
        self.send_response(401)
        self.send_header("WWW-Authenticate", 'Basic realm="powerk"')
        self.send_header("Content-Type", "text/plain")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _json(self, obj, code=200):
        body = json.dumps(obj).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        parsed = urlparse(self.path)
        path = parsed.path
        qs = parse_qs(parsed.query)
        if path not in ("/powerk.py", "/powerk.apk") and not self._authorized():
            self._deny()
            return
        if path.startswith("/api/state"):
            snap = self.hub.snapshot()
            snap["local_ip"] = self.local_ip
            snap["port"] = self.port
            snap["poll_seconds"] = self.hub.poll_seconds
            snap["retention_days"] = self.hub.stats.retention_days
            self._json(snap)
        elif path == "/api/stats":
            range_name = qs.get("range", ["24h"])[0]
            mac = qs.get("mac", [None])[0]
            self._json(self.hub.stats.query_stats(self.hub.devices, range_name=range_name, mac_filter=mac))
        elif path == "/api/rules":
            mac = qs.get("mac", [None])[0]
            self._json({"rules": self.hub.stats.list_rules(mac_filter=mac)})
        elif path == "/api/stats.csv":
            range_name = qs.get("range", ["7d"])[0]
            mac = qs.get("mac", [None])[0]
            body = self.hub.stats.export_csv(self.hub.devices, range_name=range_name, mac_filter=mac).encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "text/csv; charset=utf-8")
            self.send_header("Content-Disposition", f'attachment; filename="powerk_stats_{range_name}.csv"')
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        elif path in ("/", "/index.html"):
            body = PAGE.encode()
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        elif path == "/powerk.py":               # public: lets a phone/borrowed laptop fetch this file to run `provision`
            body = Path(__file__).resolve().read_bytes()
            self.send_response(200)
            self.send_header("Content-Type", "text/x-python")
            self.send_header("Content-Disposition", 'attachment; filename="powerk.py"')
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        elif path == "/powerk.apk":              # public: the Android app, once built (android/ -> gradlew assembleDebug)
            apk = Path(__file__).resolve().parent / "android/app/build/outputs/apk/debug/app-debug.apk"
            if not apk.is_file():
                self._json({"error": "no APK built yet: cd android && gradlew assembleDebug"}, 404)
                return
            body = apk.read_bytes()
            self.send_response(200)
            self.send_header("Content-Type", "application/vnd.android.package-archive")
            self.send_header("Content-Disposition", 'attachment; filename="powerk.apk"')
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        else:
            self._json({"error": "not found"}, 404)

    def do_POST(self):
        path = urlparse(self.path).path
        if not self._authorized():
            self._deny()
            return
        try:
            req = json.loads(self.rfile.read(int(self.headers.get("Content-Length", 0))) or b"{}")
        except Exception:
            self._json({"error": "bad request"}, 400)
            return

        if path == "/api/rules":
            action = str(req.get("action", "add")).lower()
            try:
                if action == "add":
                    rule = self.hub.stats.add_rule(req)
                    self._json({"ok": True, "rule": rule})
                elif action == "toggle":
                    ok = self.hub.stats.toggle_rule(int(req["id"]), bool(req["enabled"]))
                    self._json({"ok": ok})
                elif action == "delete":
                    ok = self.hub.stats.delete_rule(int(req["id"]))
                    self._json({"ok": ok})
                else:
                    self._json({"error": "bad action"}, 400)
            except Exception as err:
                self._json({"error": str(err)}, 400)
            return

        if not path.startswith("/api/onoff"):
            self._json({"error": "not found"}, 404)
            return
        try:
            mac = str(req["mac"]).upper()
            outlet = int(req["outlet"])
            on = bool(req["on"])
        except Exception:
            self._json({"error": "bad request"}, 400)
            return

        s = self.hub.session(mac)
        if not s:
            self._json({"error": "device offline"}, 503)
            return
        channels = [1, 2, 3, 4] if outlet == 0 else [outlet]
        if not set(channels) <= {1, 2, 3, 4}:
            self._json({"error": "bad outlet"}, 400)
            return
        try:
            fut = asyncio.run_coroutine_threadsafe(
                s.set_outlets(channels, on, stats=self.hub.stats, source="web/api"), self.loop
            )
            ok = fut.result(timeout=10)
        except Exception as err:
            self._json({"error": f"command failed: {err}"}, 502)
            return
        self._json({"ok": bool(ok), "confirmed": ok})


def local_ipv4s() -> list[str]:
    try:
        ips = socket.gethostbyname_ex(socket.gethostname())[2]
    except OSError:
        ips = []
    return [i for i in ips if not i.startswith(("127.", "169.254."))]


def setup_command(cmd: str, expect: str, host: str, timeout: float = 6.0) -> str:
    with socket.create_connection((host, SETUP_PORT), timeout=timeout) as s:
        s.settimeout(timeout)
        s.sendall((cmd + "\r\n").encode())
        buf = b""
        deadline = time.monotonic() + timeout
        while b"\n" not in buf and time.monotonic() < deadline:
            try:
                chunk = s.recv(1024)
            except socket.timeout:
                break
            if not chunk:
                break
            buf += chunk
    text = buf.decode("utf-8", "replace").strip()
    if expect and expect not in text:
        raise SystemExit(f"strip answered {text!r}, expected {expect!r} (command {cmd!r})")
    return text


def cmd_provision(args) -> int:
    for value in (args.ssid, args.password):
        if any(c in value for c in ":\r\n"):
            raise SystemExit("the strip's command protocol cannot use ':' or newlines in the SSID/password")

    if not args.ip:
        print("Need the IP this PC will have on your home Wi-Fi (the strip connects to it).")
        cands = local_ipv4s()
        print("Candidates found right now:", ", ".join(cands) or "none")
        print("Run `python powerk.py` on the home Wi-Fi first; it prints the exact IP. Then:")
        print('  python powerk.py provision --ip 192.168.0.50 --ssid "YOURWIFI" --password "..."')
        return 2

    try:
        args.ip = str(ipaddress.IPv4Address(args.ip))     # never pass an unchecked string into the strip's command protocol
    except ValueError:
        raise SystemExit(f"--ip must be an IPv4 address (got {args.ip!r})")

    print(f"Looking for the strip's setup service at {args.host}:{SETUP_PORT} ...")
    deadline = time.monotonic() + args.wait
    while True:
        try:
            with socket.create_connection((args.host, SETUP_PORT), timeout=2):
                break
        except OSError:
            if time.monotonic() > deadline:
                print("Not reachable. Do this first:")
                print("  1. hold the strip's main button ~10s until the LED blinks fast")
                print("  2. join the Wi-Fi network 'TONLY_TAP_XXXXXXX' from this PC")
                print("     (password: LGU_XXXXXXX - the same 7 characters as in the name)")
                print("  3. re-run this command")
                return 1
            time.sleep(2)

    print(f"  {setup_command(f'up:ip:{args.ip}', 'up:ip:ip_ok', args.host)}")
    print(f"  {setup_command(f'up:connect:{args.ssid}:{args.password}', 'up:connect:connect_ok', args.host)}")
    print(f"\nDone. Reconnect this PC to your home Wi-Fi and start `python powerk.py`.")
    print(f"The strip will connect to {args.ip}:{DEVICE_PORT} shortly.")
    return 0


async def cmd_serve(args) -> int:
    hub = Hub(
        db_path=args.db,
        poll_seconds=args.poll_interval,
        retention_days=args.retention_days,
    )
    server = await asyncio.start_server(hub.handle_client, "0.0.0.0", args.port)
    candidates = local_ipv4s()
    ip = args.ip or (candidates or ["127.0.0.1"])[0]

    Web.hub, Web.loop, Web.local_ip, Web.port = hub, asyncio.get_running_loop(), ip, args.port
    Web.token = args.token
    httpd = ThreadingHTTPServer(("0.0.0.0", args.web_port), Web)
    httpd.daemon_threads = True
    threading.Thread(target=httpd.serve_forever, daemon=True).start()

    print(f"powerk")
    print(f"  web UI (phone/PC)  http://{ip}:{args.web_port}")
    print(f"  strip server       TCP {args.port}")
    print(f"  polling / stats    every {hub.poll_seconds:.2f}s · {hub.stats.retention_days}d persistent DB ({args.db})")
    print(f"  auth               {'token required' if args.token else 'NONE - only safe on a trusted LAN'}")
    if args.token:
        print(f"                     browser: user 'powerk' + the token as password; app: Settings -> Token")
    print(f"  if not provisioned yet:  python powerk.py provision --ip {ip} --ssid WIFI --password PW")
    if (Path(__file__).resolve().parent / "android/app/build/outputs/apk/debug/app-debug.apk").is_file():
        print(f"  android app        http://{ip}:{args.web_port}/powerk.apk")
    if len(candidates) > 1 and not args.ip:
        print(f"  other local IPs: {', '.join(c for c in candidates if c != ip)}  (pick one with --ip if wrong)")
    print("  Ctrl+C to stop")
    try:
        async with server:
            await hub.poll_loop()
    finally:
        hub.stats.close()
    return 0


def _fake_tags(state_on: set[int]) -> str:
    """A 'up:getinfo:' payload shaped like the real strip's, for offline checks."""
    return ":".join(
        f"{n}:{n * 111};{'on' if n in state_on else 'off'};{int(n in state_on)};0;0;"
        f"{5300 if n == 2 and n in state_on else 0};0000000A;00000000;00000000;0;00;{30 + n}"
        for n in (1, 2, 3, 4)
    )


async def _selftest() -> None:
    hub = Hub(db_path=":memory:", poll_seconds=1.0, retention_days=7)
    server = await asyncio.start_server(hub.handle_client, "127.0.0.1", 0)
    port = server.sockets[0].getsockname()[1]
    reader, writer = await asyncio.open_connection("127.0.0.1", port)

    # A stand-in for the strip: answers getinfo, records onoff commands, keeps relay state.
    state_on = {2}

    async def fake_strip():
        while True:
            raw = await reader.readline()
            if not raw:
                return
            line = raw.decode().strip()
            if line == "up:getinfo:all":
                writer.write(f"up:getinfo:{_fake_tags(state_on)}\r\n".encode())
                await writer.drain()
            elif line.startswith("up:onoff:"):
                _, _, ch, val = line.split(":")
                (state_on.add if val == "on" else state_on.discard)(int(ch))

    strip_task = asyncio.create_task(fake_strip())

    writer.write(b"up:bootinfo:LGU+-TAP-HW002;aabbccddeeff;001122334455;1.0.66;connect\r\n")
    writer.write(b"up:power_report:1:224500\r\n")
    writer.write(b"up:query:-52\r\n")
    await writer.drain()
    await asyncio.sleep(0.3)

    dev = hub.devices["AABBCCDDEEFF"]
    assert dev.outlets[1]["on"] is False and dev.outlets[2]["on"] is True
    assert dev.outlets[2]["power_w"] == 5.3 and dev.outlets[2]["energy_kwh"] == 0.01
    assert dev.outlets[1]["temp_c"] == 31 and dev.outlets[4]["temp_c"] == 34
    assert dev.outlets[2]["runtime_s"] == 222
    assert dev.voltage_v == 224.5 and dev.rssi == -52
    assert dev.current_a == 0.02
    assert dev.outlets[1]["config_hex"] == "00000000"

    assert await hub.session("aabbccddeeff").set_outlets([2], False, stats=hub.stats, source="selftest") is True
    assert dev.outlets[2]["on"] is False and state_on == set()
    snapshot = hub.snapshot()["devices"][0]
    assert snapshot["on"] is False and snapshot["energy_kwh"] == 0.04

    rule = hub.stats.add_rule({"mac": "aabbccddeeff", "outlet": 1, "kind": "timer", "target_on": True, "delay_s": 60})
    assert len(hub.stats.list_rules("aabbccddeeff")) == 1
    assert hub.stats.delete_rule(rule["id"]) is True

    stats = hub.stats.query_stats(hub.devices, range_name="24h")
    assert stats["retention_days"] == 7
    assert stats["devices"][0]["summary"]["samples"] >= 1
    assert len(stats["devices"][0]["daily_7d"]) == 7

    strip_task.cancel()
    writer.close()
    server.close()
    hub.stats.close()
    print("selftest: parser + command + stats round-trip OK")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd")
    s = sub.add_parser("serve", help="run device server + web UI (default)")
    s.add_argument("--port", type=int, default=DEVICE_PORT, help=f"device TCP port (default {DEVICE_PORT}, the strip's fixed port)")
    s.add_argument("--web-port", type=int, default=WEB_PORT)
    s.add_argument("--ip", help="IP to print in the UI/provision hint (default: auto-detect)")
    s.add_argument("--token", default="", help="require this token (password) for the web UI/API; use it whenever the port is reachable from the internet")
    s.add_argument("--poll-interval", type=float, default=POLL_SECONDS, help=f"seconds between strip polls (default {POLL_SECONDS}, min 0.25)")
    s.add_argument("--db", default=str(DEFAULT_DB_PATH), help=f"SQLite file for persistent 7-day stats (default {DEFAULT_DB_PATH.name})")
    s.add_argument("--retention-days", type=int, default=STATS_RETENTION_DAYS, help=f"days of persistent statistics to keep (default {STATS_RETENTION_DAYS})")
    p = sub.add_parser("provision", help="send home Wi-Fi + this PC's IP to a strip in setup mode")
    p.add_argument("--ip", help="IPv4 this PC will have on the home Wi-Fi (what the strip connects to)")
    p.add_argument("--ssid", required=True)
    p.add_argument("--password", required=True)
    p.add_argument("--host", default=SETUP_HOST, help=f"strip setup address (default {SETUP_HOST})")
    p.add_argument("--wait", type=float, default=20.0, help="seconds to wait for the strip setup service")
    sub.add_parser("selftest", help="offline protocol check")
    args = ap.parse_args()

    if args.cmd == "provision":
        return cmd_provision(args)
    if args.cmd == "selftest":
        asyncio.run(_selftest())
        return 0
    if args.cmd in (None, "serve"):
        args.port = getattr(args, "port", DEVICE_PORT)
        args.web_port = getattr(args, "web_port", WEB_PORT)
        args.ip = getattr(args, "ip", None)
        args.token = getattr(args, "token", "")
        args.poll_interval = getattr(args, "poll_interval", POLL_SECONDS)
        args.db = getattr(args, "db", str(DEFAULT_DB_PATH))
        args.retention_days = getattr(args, "retention_days", STATS_RETENTION_DAYS)
        try:
            return asyncio.run(cmd_serve(args))
        except KeyboardInterrupt:
            return 0
    ap.error("unknown command")


if __name__ == "__main__":
    sys.exit(main())
