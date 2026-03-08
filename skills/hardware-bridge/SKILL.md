---
name: hardware-bridge
description: "Connect Claude to physical hardware devices (Raspberry Pi, Arduino, ESP32, IoT sensors, OBD2 readers) via a lightweight open protocol. Read sensor data, send commands, and analyze device output. TRIGGER when: user asks to read sensors, check hardware, talk to a Pi/Arduino/ESP32, read OBD2 data, check IoT devices, or analyze physical environment data. DO NOT TRIGGER when: user asks about hardware specs, buying hardware, or hardware unrelated to live data."
---

# Hardware Bridge — Open Standard for AI ↔ Hardware Communication

Connect Claude to any physical hardware device using a lightweight REST protocol. Any device that implements 5 HTTP endpoints becomes Claude-compatible — Raspberry Pi, Arduino, ESP32, phones, cars, industrial sensors, anything with a network connection.

## The Open Hardware Agent Protocol (OHAP)

### Design Principles
- **5 endpoints** — that's the entire spec. Any device can implement it in <50 lines
- **HTTP/JSON** — no special libraries, SDKs, or drivers needed
- **Device-agnostic** — works with any hardware that has a network stack
- **AI-native** — responses designed for LLM consumption, not just machine parsing
- **Secure by default** — bearer token auth, local network only unless explicitly exposed

### Protocol Specification (v1.0)

#### 1. Device Info
```
GET /agent/info
```
Returns device identity and capabilities.

```json
{
  "name": "Garage Pi",
  "type": "environmental",
  "version": "1.0",
  "capabilities": ["temperature", "humidity", "co_level", "motion", "camera"],
  "description": "Raspberry Pi 4 monitoring garage environment",
  "location": "Garage",
  "uptime_seconds": 86400
}
```

**Supported types:** `environmental`, `automotive`, `industrial`, `security`, `energy`, `agricultural`, `medical`, `general`

#### 2. List Sensors
```
GET /agent/sensors
```
Returns all available sensor channels with metadata.

```json
{
  "sensors": [
    {
      "id": "temp_1",
      "name": "Temperature",
      "type": "temperature",
      "unit": "celsius",
      "range": [-40, 85],
      "precision": 0.1,
      "interval_ms": 1000
    },
    {
      "id": "humidity_1",
      "name": "Humidity",
      "type": "humidity",
      "unit": "percent",
      "range": [0, 100],
      "precision": 1
    },
    {
      "id": "co_1",
      "name": "Carbon Monoxide",
      "type": "gas",
      "unit": "ppm",
      "range": [0, 1000],
      "alert_threshold": 50
    }
  ]
}
```

**Standard sensor types:** `temperature`, `humidity`, `pressure`, `gas`, `motion`, `light`, `sound`, `voltage`, `current`, `power`, `speed`, `rpm`, `gps`, `acceleration`, `gyroscope`, `camera`, `obd2`, `gpio`

#### 3. Read Sensor
```
GET /agent/read/{sensor_id}
GET /agent/read/all
```
Returns current reading(s).

```json
{
  "sensor_id": "temp_1",
  "value": 18.5,
  "unit": "celsius",
  "timestamp": "2026-03-08T22:15:00Z",
  "quality": "good"
}
```

For `/agent/read/all`:
```json
{
  "readings": [
    {"sensor_id": "temp_1", "value": 18.5, "unit": "celsius", "quality": "good"},
    {"sensor_id": "humidity_1", "value": 65, "unit": "percent", "quality": "good"},
    {"sensor_id": "co_1", "value": 0, "unit": "ppm", "quality": "good"}
  ],
  "timestamp": "2026-03-08T22:15:00Z"
}
```

**Quality values:** `good`, `degraded`, `stale`, `error`

#### 4. Send Command
```
POST /agent/command
```
Execute an action on the device.

```json
{
  "command": "set_gpio",
  "params": {
    "pin": 18,
    "state": "high"
  }
}
```

Response:
```json
{
  "status": "ok",
  "result": "GPIO 18 set to HIGH",
  "timestamp": "2026-03-08T22:15:01Z"
}
```

**Standard commands:** `set_gpio`, `capture_image`, `read_obd`, `clear_dtc`, `reboot`, `calibrate`, `start_recording`, `stop_recording`

#### 5. Health Check
```
GET /agent/health
```

```json
{
  "status": "healthy",
  "uptime_seconds": 86400,
  "cpu_percent": 12.5,
  "memory_percent": 34.2,
  "disk_percent": 18.0,
  "temperature_c": 45.2,
  "wifi_signal_dbm": -42,
  "battery_percent": null,
  "errors": []
}
```

### Authentication

All endpoints require a bearer token:
```
Authorization: Bearer <device_token>
```

The token is set on the device during initial setup. For local network devices, a simple shared secret is sufficient.

### Device Discovery

Devices announce themselves via mDNS:
```
_ohap._tcp.local
```

Or configure manually by IP/hostname in the skill configuration.

## How Claude Uses This

### Step 1: Connect
When a user asks to check a device, the skill runs the connection script:

```bash
python scripts/ohap_client.py --host 192.168.1.100 --action info
```

### Step 2: Discover Capabilities
Read what sensors are available and what the device can do.

### Step 3: Read Data
Pull all sensor readings or specific ones the user asked about.

### Step 4: Analyze
Claude interprets the readings in context:
- Is the temperature normal for this location/time?
- Are any readings in dangerous ranges?
- Do the readings suggest a problem?
- What action should the user take?

### Step 5: Act (if requested)
Send commands to the device (with user confirmation for anything that changes state).

## Response Format

When presenting hardware data to the user:

```
**Device:** [name] ([location])
**Status:** [healthy/degraded/offline]

**Readings:**
| Sensor | Value | Status |
|--------|-------|--------|
| [name] | [value] [unit] | [normal/warning/critical] |

**Analysis:** [Plain English interpretation]

**Recommendations:** [What to do, if anything]
```

## Example Use Cases

### Home Environment Monitoring
```
User: "Check my garage sensors"
Claude: Connects to Garage Pi → reads temp, humidity, CO
→ "Garage is 4°C (normal for March), humidity 78% (slightly high —
   consider a dehumidifier to prevent rust), CO at 0 ppm (safe).
   All sensors healthy."
```

### Car Diagnostics via Pi + OBD2
```
User: "Read my car's engine data"
Claude: Connects to Car Pi → reads OBD2 sensors
→ "Engine RPM: 780 (normal idle), Coolant: 89°C (optimal),
   Battery: 12.6V (good), No active fault codes.
   Everything looks healthy."
```

### Garden/Agricultural
```
User: "How are my greenhouse conditions?"
Claude: Connects to Greenhouse ESP32 → reads sensors
→ "Temperature 24°C (ideal), Soil moisture 45% (getting low —
   water within 24hrs), Light level 850 lux (sufficient),
   Humidity 70% (good for tomatoes)."
```

### Industrial/Workshop
```
User: "Check the workshop air quality"
Claude: Connects to Workshop Pi → reads gas sensors
→ "VOC level 120 ppb (normal), PM2.5 at 35 µg/m³ (moderate —
   turn on extraction if using solvents), CO2 at 800 ppm
   (fine but open a window if it rises above 1000)."
```

### Energy Monitoring
```
User: "What's my solar panel output?"
Claude: Connects to Energy Monitor ESP32 → reads power sensors
→ "Current output: 2.8 kW (good for overcast day), Daily total:
   14.2 kWh, Grid export: 8.1 kWh, House consumption: 6.1 kWh.
   Battery at 78%."
```

## Reference Implementations

### Raspberry Pi (Python, <50 lines)

The included `scripts/ohap_server_pi.py` provides a complete OHAP server for Raspberry Pi with:
- DHT22 temperature/humidity sensor support
- GPIO input/output
- System health monitoring
- mDNS announcement

### ESP32 (MicroPython)

The included `scripts/ohap_server_esp32.py` provides a minimal OHAP server for ESP32/ESP8266.

### Client Script

The included `scripts/ohap_client.py` is what Claude executes to talk to devices:

```bash
# Get device info
python scripts/ohap_client.py --host 192.168.1.100 --action info

# Read all sensors
python scripts/ohap_client.py --host 192.168.1.100 --action read-all

# Read specific sensor
python scripts/ohap_client.py --host 192.168.1.100 --action read --sensor temp_1

# Send command
python scripts/ohap_client.py --host 192.168.1.100 --action command --cmd set_gpio --params '{"pin": 18, "state": "high"}'

# Health check
python scripts/ohap_client.py --host 192.168.1.100 --action health
```

## Safety Guidelines

- **NEVER** send commands to devices without explicit user confirmation
- **ALWAYS** check health before reading sensors (stale data is dangerous)
- **Flag** any readings in critical ranges immediately (CO > 50 ppm, temperature extremes, etc.)
- **Warn** if a sensor quality is `degraded` or `stale` — readings may be unreliable
- **Local network only** by default — never expose OHAP endpoints to the public internet without TLS + strong auth
- For automotive (OBD2): **read-only by default**. Never send write commands (clear DTCs, reset ECU) without explicit user consent

## The Vision

OHAP (Open Hardware Agent Protocol) makes any physical device an AI-accessible sensor. The same way MCP standardised how AI tools connect to software services, OHAP standardises how AI agents connect to the physical world.

5 endpoints. Any device. Any AI.

**Spec:** [github.com/razashariff/ohap](https://github.com/razashariff/ohap)

## Author

Created by Raza Al-Rehman Sharif (raza.sharif@outlook.com)
CyberSecAI Ltd
