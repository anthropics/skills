#!/usr/bin/env python3
"""Weather and environmental data. All free, no API keys required."""

import sys
import json
import urllib.request
import urllib.parse
import argparse
import threading
from datetime import datetime, date

NOMINATIM = "https://nominatim.openstreetmap.org/search"
OPEN_METEO = "https://api.open-meteo.com/v1/forecast"
OPENAQ = "https://api.openaq.org/v2/latest"

HEADERS = {"User-Agent": "weather-context/1.0 (money-brain)"}

WMO_CODES = {
    0: "Clear sky", 1: "Mainly clear", 2: "Partly cloudy", 3: "Overcast",
    45: "Foggy", 48: "Icy fog",
    51: "Light drizzle", 53: "Moderate drizzle", 55: "Dense drizzle",
    61: "Slight rain", 63: "Moderate rain", 65: "Heavy rain",
    71: "Slight snow", 73: "Moderate snow", 75: "Heavy snow",
    77: "Snow grains", 80: "Rain showers", 81: "Moderate showers", 82: "Violent showers",
    85: "Snow showers", 86: "Heavy snow showers",
    95: "Thunderstorm", 96: "Thunderstorm + hail", 99: "Heavy thunderstorm + hail"
}

UV_LABELS = [(0, 2, "Low"), (3, 5, "Moderate"), (6, 7, "High"), (8, 10, "Very High"), (11, 99, "Extreme")]

WIND_DIRS = ["N", "NNE", "NE", "ENE", "E", "ESE", "SE", "SSE", "S", "SSW", "SW", "WSW", "W", "WNW", "NW", "NNW"]


def fetch_json(url, headers=None, timeout=15):
    try:
        req = urllib.request.Request(url, headers=headers or HEADERS)
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return json.loads(resp.read().decode('utf-8'))
    except Exception as e:
        return {"_error": str(e)}


def geocode(location):
    encoded = urllib.parse.quote(location)
    url = f"{NOMINATIM}?q={encoded}&format=json&limit=1"
    data = fetch_json(url)
    if isinstance(data, list) and data:
        r = data[0]
        return {
            "lat": float(r["lat"]),
            "lon": float(r["lon"]),
            "display_name": r.get("display_name", location)
        }
    return {"_error": f"Location not found: {location}"}


def fetch_weather(lat, lon, days=7, use_fahrenheit=False):
    units = "&temperature_unit=fahrenheit&wind_speed_unit=mph" if use_fahrenheit else ""
    url = (
        f"{OPEN_METEO}?latitude={lat}&longitude={lon}"
        f"&current=temperature_2m,relative_humidity_2m,apparent_temperature,precipitation,weather_code,"
        f"wind_speed_10m,wind_direction_10m,uv_index"
        f"&daily=weather_code,temperature_2m_max,temperature_2m_min,precipitation_sum,"
        f"precipitation_probability_max,uv_index_max,wind_speed_10m_max"
        f"&timezone=auto&forecast_days={days}{units}"
    )
    return fetch_json(url)


def fetch_air_quality(lat, lon):
    url = f"{OPENAQ}?coordinates={lat},{lon}&radius=25000&limit=5&order_by=lastUpdated&sort=desc"
    return fetch_json(url, headers={**HEADERS, "Accept": "application/json"})


def wind_direction(degrees):
    if degrees is None:
        return "N/A"
    idx = round(degrees / 22.5) % 16
    return WIND_DIRS[idx]


def uv_label(val):
    if val is None:
        return "N/A"
    for lo, hi, label in UV_LABELS:
        if lo <= val <= hi:
            return label
    return "Extreme"


def wmo(code):
    return WMO_CODES.get(code, f"Code {code}")


def temp_str(val, fahrenheit=False):
    if val is None:
        return "N/A"
    unit = "°F" if fahrenheit else "°C"
    return f"{val:.1f}{unit}"


def aqi_from_pm25(pm25):
    if pm25 is None:
        return "N/A"
    if pm25 <= 12:
        return "Good"
    if pm25 <= 35.4:
        return "Moderate"
    if pm25 <= 55.4:
        return "Unhealthy for Sensitive Groups"
    if pm25 <= 150.4:
        return "Unhealthy"
    if pm25 <= 250.4:
        return "Very Unhealthy"
    return "Hazardous"


def print_markdown(location_name, weather, air, use_fahrenheit=False):
    today = datetime.utcnow().strftime("%Y-%m-%d %H:%M UTC")
    temp_unit = "°F" if use_fahrenheit else "°C"
    speed_unit = "mph" if use_fahrenheit else "km/h"

    print(f"# Weather: {location_name}")
    print(f"*{today} | Timezone: {weather.get('timezone', 'UTC')}*\n")

    curr = weather.get("current", {})
    if curr:
        wcode = curr.get("weather_code")
        temp = curr.get("temperature_2m")
        feels = curr.get("apparent_temperature")
        humidity = curr.get("relative_humidity_2m")
        precip = curr.get("precipitation")
        wind = curr.get("wind_speed_10m")
        wind_dir = wind_direction(curr.get("wind_direction_10m"))
        uv = curr.get("uv_index")

        print("## Current Conditions")
        print(f"**{wmo(wcode)}**")
        print(f"- 🌡️ Temperature: {temp_str(temp, use_fahrenheit)} (feels like {temp_str(feels, use_fahrenheit)})")
        print(f"- 💧 Humidity: {humidity}%")
        print(f"- 🌧️ Precipitation: {precip}mm")
        print(f"- 💨 Wind: {wind} {speed_unit} {wind_dir}")
        if uv is not None:
            print(f"- ☀️ UV Index: {uv} ({uv_label(uv)})")
        print()

    # Daily forecast
    daily = weather.get("daily", {})
    if daily:
        dates = daily.get("time", [])
        wcodes = daily.get("weather_code", [])
        maxtemps = daily.get("temperature_2m_max", [])
        mintemps = daily.get("temperature_2m_min", [])
        precip_sums = daily.get("precipitation_sum", [])
        precip_probs = daily.get("precipitation_probability_max", [])
        uv_maxs = daily.get("uv_index_max", [])

        print("## 7-Day Forecast")
        print(f"| Day | Conditions | High | Low | Rain% | Precip |")
        print(f"|-----|-----------|------|-----|-------|--------|")

        for i in range(min(7, len(dates))):
            day = dates[i]
            try:
                day_name = datetime.strptime(day, "%Y-%m-%d").strftime("%a %d")
            except ValueError:
                day_name = day
            cond = wmo(wcodes[i] if i < len(wcodes) else None)[:15]
            hi = temp_str(maxtemps[i] if i < len(maxtemps) else None, use_fahrenheit)
            lo = temp_str(mintemps[i] if i < len(mintemps) else None, use_fahrenheit)
            prob = f"{precip_probs[i]}%" if i < len(precip_probs) and precip_probs[i] is not None else "N/A"
            psum = f"{precip_sums[i]:.1f}mm" if i < len(precip_sums) and precip_sums[i] is not None else "0mm"
            print(f"| {day_name} | {cond} | {hi} | {lo} | {prob} | {psum} |")
        print()

    # Air quality
    if air and "_error" not in air:
        results = air.get("results", [])
        if results:
            print("## Air Quality (nearest station)")
            pm25_val = None
            for result in results[:3]:
                station = result.get("location", "Unknown station")
                measurements = result.get("measurements", [])
                print(f"**Station:** {station}")
                for m in measurements:
                    param = m.get("parameter", "")
                    val = m.get("value")
                    unit = m.get("unit", "")
                    if val is not None:
                        print(f"- {param.upper()}: {val:.1f} {unit}")
                        if param == "pm25":
                            pm25_val = val
                print()
            if pm25_val is not None:
                print(f"**Air Quality Status:** {aqi_from_pm25(pm25_val)}\n")
    else:
        print("*Air quality: no nearby stations found*\n")


def main():
    parser = argparse.ArgumentParser(description="Weather and air quality data")
    parser.add_argument("--location", required=True, help="Location name")
    parser.add_argument("--days", type=int, default=7, help="Forecast days (1-16)")
    parser.add_argument("--fahrenheit", action="store_true")
    parser.add_argument("--geocode-only", action="store_true")
    parser.add_argument("--no-air", action="store_true")
    parser.add_argument("--format", default="markdown", choices=["markdown", "json"])
    args = parser.parse_args()

    geo = geocode(args.location)
    if "_error" in geo:
        print(f"Error: {geo['_error']}", file=sys.stderr)
        sys.exit(1)

    if args.geocode_only:
        print(json.dumps(geo, indent=2))
        return

    lat, lon = geo["lat"], geo["lon"]
    location_name = geo["display_name"].split(",")[0:3]
    location_name = ", ".join(location_name)

    weather, air = {}, {}
    threads = [
        threading.Thread(target=lambda: weather.update(fetch_weather(lat, lon, args.days, args.fahrenheit)))
    ]
    if not args.no_air:
        threads.append(threading.Thread(target=lambda: air.update(fetch_air_quality(lat, lon))))

    for t in threads:
        t.start()
    for t in threads:
        t.join(timeout=15)

    if args.format == "json":
        print(json.dumps({"location": geo, "weather": weather, "air_quality": air}, indent=2))
    else:
        print_markdown(location_name, weather, air, args.fahrenheit)


if __name__ == "__main__":
    main()
