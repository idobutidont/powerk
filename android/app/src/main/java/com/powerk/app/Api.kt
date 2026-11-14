package com.powerk.app

import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.withContext
import org.json.JSONObject
import java.net.HttpURLConnection
import java.net.URL

data class Outlet(
    val n: Int,
    val on: Boolean,
    val powerW: Double,
    val energyKwh: Double,
    val tempC: Int,
    val currentA: Double = 0.0,
    val todayKwh: Double = 0.0,
    val todayOnS: Int = 0,
    val runtimeS: Int = 0,
    val overload: Boolean = false,
    val overheat: Boolean = false,
)

data class Strip(
    val mac: String,
    val name: String,
    val model: String,
    val fw: String,
    val online: Boolean,
    val on: Boolean,
    val powerW: Double,
    val energyKwh: Double,
    val voltage: Double?,
    val currentA: Double?,
    val rssi: Int?,
    val outlets: List<Outlet>,
    val avgTempC: Double = 0.0,
    val maxTempC: Int = 0,
    val overload: Boolean = false,
    val overheat: Boolean = false,
    val uptimeS: Int = 0,
    val todayKwh: Double = 0.0,
    val peakPowerWToday: Double = 0.0,
)

data class Snapshot(
    val serverIp: String,
    val strips: List<Strip>,
    val pollSeconds: Double = 1.0,
    val retentionDays: Int = 7,
)

data class StatsSummary(
    val energyKwh: Double,
    val avgPowerW: Double,
    val minPowerW: Double,
    val maxPowerW: Double,
    val avgVoltageV: Double?,
    val minVoltageV: Double?,
    val maxVoltageV: Double?,
    val avgCurrentA: Double,
    val maxCurrentA: Double,
    val avgTempC: Double,
    val minTempC: Int,
    val maxTempC: Int,
    val avgRssi: Double?,
    val minRssi: Int?,
    val maxRssi: Int?,
    val onSeconds: Int,
    val onlineSeconds: Int,
    val dutyCyclePct: Double,
    val onlinePct: Double,
    val samples: Int,
)

data class OutletStats(
    val n: Int,
    val energyKwh: Double,
    val sharePct: Double,
    val avgPowerW: Double,
    val maxPowerW: Double,
    val avgTempC: Double,
    val maxTempC: Int,
    val onSeconds: Int,
    val dutyCyclePct: Double,
    val toggleCount: Int,
)

data class SeriesPoint(
    val ts: Long,
    val avgPowerW: Double,
    val maxPowerW: Double,
)

data class DailyStats(
    val date: String,
    val energyKwh: Double,
    val avgPowerW: Double,
    val maxPowerW: Double,
    val avgVoltageV: Double?,
    val maxTempC: Int,
    val onSeconds: Int,
    val onlinePct: Double,
    val outletKwh: List<Double>,
)

data class DeviceStats(
    val mac: String,
    val name: String,
    val online: Boolean,
    val summary: StatsSummary,
    val outlets: List<OutletStats>,
    val series: List<SeriesPoint>,
    val daily7d: List<DailyStats>,
)

data class StatsResponse(
    val retentionDays: Int,
    val pollSeconds: Double,
    val range: String,
    val devices: List<DeviceStats>,
)

/** Outlet by its number (1..4) - never by list position. */
fun Strip.outletOn(n: Int): Boolean = outlets.firstOrNull { it.n == n }?.on ?: false

fun Strip.outlet(n: Int): Outlet? = outlets.firstOrNull { it.n == n }

class ServerException(message: String) : Exception(message)

/** Talks to the powerk.py JSON API: GET /api/state, GET /api/stats, POST /api/onoff. */
object Api {

    suspend fun snapshot(base: String, token: String): Snapshot = withContext(Dispatchers.IO) {
        val root = JSONObject(request("$base/api/state", null, token))
        val array = root.optJSONArray("devices")
        val strips = (0 until (array?.length() ?: 0)).map { parseStrip(array!!.getJSONObject(it)) }
        Snapshot(
            serverIp = root.optString("local_ip"),
            strips = strips,
            pollSeconds = root.optDouble("poll_seconds", 1.0),
            retentionDays = root.optInt("retention_days", 7),
        )
    }

    suspend fun stats(base: String, token: String, range: String = "24h"): StatsResponse = withContext(Dispatchers.IO) {
        val root = JSONObject(request("$base/api/stats?range=$range", null, token))
        val devsArray = root.optJSONArray("devices")
        val devices = (0 until (devsArray?.length() ?: 0)).map { parseDeviceStats(devsArray!!.getJSONObject(it)) }
        StatsResponse(
            retentionDays = root.optInt("retention_days", 7),
            pollSeconds = root.optDouble("poll_seconds", 1.0),
            range = root.optString("range", range),
            devices = devices,
        )
    }

    suspend fun setOutlet(base: String, token: String, mac: String, outlet: Int, on: Boolean) = withContext(Dispatchers.IO) {
        val body = JSONObject()
            .put("mac", mac)
            .put("outlet", outlet)
            .put("on", on)
            .toString()
        val response = JSONObject(request("$base/api/onoff", body, token))
        if (!response.optBoolean("ok")) {
            throw ServerException(response.optString("error").ifBlank { "command failed" })
        }
    }

    internal fun request(url: String, body: String?, token: String): String {
        val connection = (URL(url).openConnection() as HttpURLConnection)
        try {
            connection.connectTimeout = 4000
            connection.readTimeout = 6000
            connection.requestMethod = if (body == null) "GET" else "POST"
            if (token.isNotBlank()) connection.setRequestProperty("X-Token", token)
            if (body != null) {
                connection.doOutput = true
                connection.setRequestProperty("Content-Type", "application/json")
                connection.outputStream.use { it.write(body.toByteArray(Charsets.UTF_8)) }
            }
            val code = connection.responseCode
            val stream = if (code in 200..299) connection.inputStream else connection.errorStream
            val text = stream?.bufferedReader()?.use { it.readText() }.orEmpty()
            if (code !in 200..299) throw ServerException(errorOf(text, code))
            return text
        } catch (e: ServerException) {
            throw e
        } catch (e: Exception) {
            throw ServerException(e.message ?: "connection failed")
        } finally {
            connection.disconnect()
        }
    }

    private fun errorOf(body: String, code: Int): String =
        try {
            JSONObject(body).optString("error").ifBlank { "HTTP $code" }
        } catch (e: Exception) {
            "HTTP $code"
        }

    private fun parseStrip(o: JSONObject): Strip {
        val array = o.optJSONArray("outlets")
        val outlets = (0 until (array?.length() ?: 0)).map { i ->
            val x = array!!.getJSONObject(i)
            Outlet(
                n = x.optInt("n"),
                on = x.optBoolean("on"),
                powerW = x.optDouble("power_w", 0.0),
                energyKwh = x.optDouble("energy_kwh", 0.0),
                tempC = x.optInt("temp_c"),
                currentA = x.optDouble("current_a", 0.0),
                todayKwh = x.optDouble("today_kwh", 0.0),
                todayOnS = x.optInt("today_on_s", 0),
                runtimeS = x.optInt("runtime_s", 0),
                overload = x.optBoolean("overload", false),
                overheat = x.optBoolean("overheat", false),
            )
        }
        return Strip(
            mac = o.optString("mac"),
            name = o.optString("name"),
            model = o.optString("model"),
            fw = o.optString("fw"),
            online = o.optBoolean("online"),
            on = o.optBoolean("on"),
            powerW = o.optDouble("power_w", 0.0),
            energyKwh = o.optDouble("energy_kwh", 0.0),
            voltage = o.optDoubleOrNull("voltage"),
            currentA = o.optDoubleOrNull("current_a"),
            rssi = if (o.isNull("rssi")) null else o.optInt("rssi"),
            outlets = outlets,
            avgTempC = o.optDouble("avg_temp_c", 0.0),
            maxTempC = o.optInt("max_temp_c", 0),
            overload = o.optBoolean("overload", false),
            overheat = o.optBoolean("overheat", false),
            uptimeS = o.optInt("uptime_s", 0),
            todayKwh = o.optDouble("today_kwh", 0.0),
            peakPowerWToday = o.optDouble("peak_power_w_today", 0.0),
        )
    }

    private fun parseDeviceStats(o: JSONObject): DeviceStats {
        val sum = o.optJSONObject("summary") ?: JSONObject()
        val summary = StatsSummary(
            energyKwh = sum.optDouble("energy_kwh", 0.0),
            avgPowerW = sum.optDouble("avg_power_w", 0.0),
            minPowerW = sum.optDouble("min_power_w", 0.0),
            maxPowerW = sum.optDouble("max_power_w", 0.0),
            avgVoltageV = sum.optDoubleOrNull("avg_voltage_v"),
            minVoltageV = sum.optDoubleOrNull("min_voltage_v"),
            maxVoltageV = sum.optDoubleOrNull("max_voltage_v"),
            avgCurrentA = sum.optDouble("avg_current_a", 0.0),
            maxCurrentA = sum.optDouble("max_current_a", 0.0),
            avgTempC = sum.optDouble("avg_temp_c", 0.0),
            minTempC = sum.optInt("min_temp_c", 0),
            maxTempC = sum.optInt("max_temp_c", 0),
            avgRssi = sum.optDoubleOrNull("avg_rssi"),
            minRssi = if (sum.isNull("min_rssi")) null else sum.optInt("min_rssi"),
            maxRssi = if (sum.isNull("max_rssi")) null else sum.optInt("max_rssi"),
            onSeconds = sum.optInt("on_seconds", 0),
            onlineSeconds = sum.optInt("online_seconds", 0),
            dutyCyclePct = sum.optDouble("duty_cycle_pct", 0.0),
            onlinePct = sum.optDouble("online_pct", 0.0),
            samples = sum.optInt("samples", 0),
        )
        val outArr = o.optJSONArray("outlets")
        val outlets = (0 until (outArr?.length() ?: 0)).map { i ->
            val x = outArr!!.getJSONObject(i)
            OutletStats(
                n = x.optInt("n"),
                energyKwh = x.optDouble("energy_kwh", 0.0),
                sharePct = x.optDouble("share_pct", 0.0),
                avgPowerW = x.optDouble("avg_power_w", 0.0),
                maxPowerW = x.optDouble("max_power_w", 0.0),
                avgTempC = x.optDouble("avg_temp_c", 0.0),
                maxTempC = x.optInt("max_temp_c", 0),
                onSeconds = x.optInt("on_seconds", 0),
                dutyCyclePct = x.optDouble("duty_cycle_pct", 0.0),
                toggleCount = x.optInt("toggle_count", 0),
            )
        }
        val serArr = o.optJSONArray("series")
        val series = (0 until (serArr?.length() ?: 0)).map { i ->
            val x = serArr!!.getJSONObject(i)
            SeriesPoint(
                ts = x.optLong("ts"),
                avgPowerW = x.optDouble("avg_power_w", 0.0),
                maxPowerW = x.optDouble("max_power_w", 0.0),
            )
        }
        val dayArr = o.optJSONArray("daily_7d")
        val daily7d = (0 until (dayArr?.length() ?: 0)).map { i ->
            val x = dayArr!!.getJSONObject(i)
            val okwhArr = x.optJSONArray("outlet_kwh")
            val outletKwh = (0 until (okwhArr?.length() ?: 0)).map { j -> okwhArr!!.optDouble(j, 0.0) }
            DailyStats(
                date = x.optString("date"),
                energyKwh = x.optDouble("energy_kwh", 0.0),
                avgPowerW = x.optDouble("avg_power_w", 0.0),
                maxPowerW = x.optDouble("max_power_w", 0.0),
                avgVoltageV = x.optDoubleOrNull("avg_voltage_v"),
                maxTempC = x.optInt("max_temp_c", 0),
                onSeconds = x.optInt("on_seconds", 0),
                onlinePct = x.optDouble("online_pct", 0.0),
                outletKwh = outletKwh,
            )
        }
        return DeviceStats(
            mac = o.optString("mac"),
            name = o.optString("name"),
            online = o.optBoolean("online"),
            summary = summary,
            outlets = outlets,
            series = series,
            daily7d = daily7d,
        )
    }

    private fun JSONObject.optDoubleOrNull(key: String): Double? =
        if (isNull(key)) null else optDouble(key)
}
