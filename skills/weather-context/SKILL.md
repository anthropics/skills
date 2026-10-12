---
name: weather-context
description: Weather and environmental data for any location. Fetches current conditions, forecasts, air quality, UV index, and historical climate context. No API key required. Use when user asks about weather, forecast, temperature, rain, climate, air quality, or environmental conditions for any location. Triggers on phrases like "weather in", "what's the weather", "will it rain", "forecast for", "temperature in", "climate in", "air quality", "how hot is it in", "should I bring an umbrella".
license: Complete terms in LICENSE.txt
allowed-tools: Bash(python:*) WebFetch
metadata:
  author: Maksim Soltan
  version: 1.0.0
  apis: Open-Meteo, OpenAQ, Nominatim
  auth: none-required
---

# Weather Context

Full weather intelligence with zero API keys. Open-Meteo has a completely free tier with no limits for reasonable use.

## APIs Used (all free, no auth)

- **Open-Meteo**: `https://api.open-meteo.com/v1/forecast` — weather + forecast
- **Nominatim**: `https://nominatim.openstreetmap.org/search` — geocoding
- **OpenAQ**: `https://api.openaq.org/v2/latest` — air quality

## Workflow

### Step 1: Geocode Location

```python
scripts/weather_fetch.py --location "San Francisco" --geocode-only
```

```
GET https://nominatim.openstreetmap.org/search?q={LOCATION}&format=json&limit=1
Headers: User-Agent: weather-context/1.0
```

Extract: `lat`, `lon`, `display_name`

### Step 2: Fetch Weather

```python
scripts/weather_fetch.py --location "San Francisco" --days 7
```

```
GET https://api.open-meteo.com/v1/forecast?
  latitude={LAT}&longitude={LON}
  &current=temperature_2m,relative_humidity_2m,apparent_temperature,precipitation,weather_code,wind_speed_10m,wind_direction_10m,uv_index
  &hourly=temperature_2m,precipitation_probability,weather_code
  &daily=weather_code,temperature_2m_max,temperature_2m_min,precipitation_sum,precipitation_probability_max,uv_index_max,wind_speed_10m_max
  &timezone=auto
  &forecast_days=7
```

### Step 3: Fetch Air Quality (optional)

```
GET https://api.openaq.org/v2/latest?coordinates={LAT},{LON}&radius=25000&limit=5
```

Returns: PM2.5, PM10, NO2, O3, CO readings from nearest stations.

### WMO Weather Code Mapping

```
0: Clear sky
1, 2, 3: Mainly clear, partly cloudy, overcast
45, 48: Fog
51, 53, 55: Drizzle (light/moderate/dense)
61, 63, 65: Rain (slight/moderate/heavy)
71, 73, 75: Snow (slight/moderate/heavy)
80, 81, 82: Rain showers
85, 86: Snow showers
95: Thunderstorm
96, 99: Thunderstorm with hail
```

### Step 4: Generate Report

```
## Weather: [LOCATION]
[DATE] | Timezone: [TZ]

### Current Conditions
🌡️ Temperature: X°C (feels like X°C)
💧 Humidity: X%
🌧️ Precipitation: Xmm
💨 Wind: Xkm/h [DIRECTION]
☀️ UV Index: X ([LOW/MODERATE/HIGH/VERY HIGH])
Conditions: [WMO code description]

### 7-Day Forecast
| Day | Conditions | High | Low | Rain% | Precip |
|-----|-----------|------|-----|-------|--------|

### Air Quality
[AQI data if available, nearest station name]
PM2.5: X μg/m³ | PM10: X μg/m³
Status: [GOOD/MODERATE/UNHEALTHY]

### Climate Context
[Historical averages for this month if available]
```

## Unit Handling

Open-Meteo default: Celsius, km/h, mm.
Add `&temperature_unit=fahrenheit&wind_speed_unit=mph` for US units if user context suggests it.

## Error Handling

- Geocoding fails: ask user to be more specific or provide lat/lon
- Open-Meteo unavailable: rare, note in output
- OpenAQ no nearby stations: skip air quality, note gap

## Examples

User: "What's the weather in Tokyo?"
→ Geocode "Tokyo" → fetch forecast + air quality

User: "Will it rain in London this week?"
→ Geocode "London" → daily forecast, focus precipitation_probability

User: "Air quality in Beijing"
→ Geocode "Beijing" → OpenAQ priority
