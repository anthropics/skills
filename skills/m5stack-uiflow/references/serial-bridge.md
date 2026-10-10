# Serial Bridge & Integration Reference

## Table of Contents
- Serial Bridge Usage
- Serial Bridge Protocol
- Serial Bridge Gotchas
- BLE Setup (Future/Optional)
- iOS App Integration Gotchas
- Architecture Overview
- Data Flow
- WiFi Polling vs BLE

## Serial Bridge Usage

For development with real TTS but without WiFi setup, use the serial bridge:

```bash
# Run on host computer
python tools/serial_bridge.py --port /dev/cu.usbserial-5410 --server http://localhost:3001
```

Set `TRANSPORT_MODE = "serial"` in config.py to use this mode.

**Auto-detect port:**
```python
# Bridge auto-detects M5Stack by looking for:
# - "usbserial" or "usbmodem" in device name
# - "CP210" or "CH340" in description
# - "M5" in description
```

## Serial Bridge Protocol

```
M5Stack sends:    TILE_CMD:GET_ROUTINE
Bridge responds:  TILE_RESP:OK:{"routine":{...}}

M5Stack sends:    TILE_CMD:VOICE:{"text":"Hello","voice":"alloy"}
Bridge responds:  TILE_RESP:OK:<base64 audio data>
```

## Serial Bridge Gotchas

**1. Command parity — bridge must handle every command the Tile sends.**

The Tile firmware sends commands like `POLL_STATUS`, `AUDIO_CLIP`, `VOICE`, `GET_ROUTINE`, `COMPLETE`. Each one needs a handler in `serial_bridge.py`'s `handle_command()` function. If you add a new transport method to `SerialTransport`, you MUST add a matching handler in the bridge — otherwise you'll see `ERR: Unknown command` in the bridge logs.

**2. `sys.stdout.flush()` crashes on M5Stack MicroPython.**

MicroPython's `TextIOWrapper` (stdout) may not have a `flush()` method on some firmware builds. Always wrap in try/except:

```python
print(f"TILE_CMD:{message}")
try:
    sys.stdout.flush()
except AttributeError:
    pass  # MicroPython TextIOWrapper may lack flush()
```

**3. AudioEngine requires WiFi transport — skip in serial mode.**

`audio_engine.py` uses raw sockets and `transport.api_base_url` for music download. `SerialTransport` doesn't have `api_base_url` (it routes through the bridge). Guard music download with transport mode check:

```python
# In main.py — only download music in WiFi mode
if AUDIO_ENGINE_AVAILABLE and audio_engine and TRANSPORT_MODE == "wifi":
    audio_engine.set_transport(transport)
    audio_engine.download_music(...)
```

Using `TRANSPORT_MODE == "wifi"` (not `!= "demo"`) prevents the `AttributeError: 'SerialTransport' object has no attribute 'api_base_url'` crash.

**4. Disconnect Thonny before running the bridge.**

Thonny and the serial bridge can't share the USB port. Close Thonny's REPL connection first, then start the bridge.

**5. pyserial DTR assertion resets the ESP32 — disable DTR before opening.**

By default, `serial.Serial(port, baud)` asserts DTR on open, which triggers a reset on ESP32 boards. This creates a boot loop where the bridge connects -> resets device -> device disconnects -> bridge reconnects -> resets again. Fix by setting DTR/RTS before opening:

```python
ser = serial.Serial()
ser.port = port
ser.baudrate = baud_rate
ser.timeout = 0.1
ser.dtr = False   # Don't reset ESP32 when opening port
ser.rts = False
ser.open()
```

**6. M5Stack CoreS3 SE can auto-run main.py on boot.**

In UIFlow 2.0 settings, you can configure the device to auto-start `main.py` instead of requiring a manual "App Run" tap. This is the recommended setup for serial mode development — the Tile boots, auto-starts the firmware, and begins sending TILE_CMD messages immediately.

## BLE Setup (Future/Optional)

BLE peripheral for iOS app pairing (ready but not enabled by default):

```python
# Custom UUIDs for Cue Tile
SERVICE_UUID = "4C554500-0000-1000-8000-00805F9B34FB"
CHAR_WIFI_CONFIG = "4C554501-..."   # Write SSID/password
CHAR_SYNC_TRIGGER = "4C554502-..."  # Trigger routine sync
CHAR_STATUS = "4C554503-..."        # Read status (notify)
CHAR_COMPLETION = "4C554504-..."    # Completion notification
```

Use `main_with_ble.py` instead of `main.py` to enable BLE.

## iOS App Integration Gotchas

### React Native `fetch()` has no timeout

When the app calls `POST /api/tile/sync` or `/api/tile/start`, if the server is unreachable, `fetch()` hangs indefinitely (60+ seconds on iOS). Always use `AbortController`:

```typescript
function fetchWithTimeout(url: string, options: RequestInit, timeoutMs = 8000) {
  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), timeoutMs);
  return fetch(url, { ...options, signal: controller.signal })
    .finally(() => clearTimeout(timer));
}
```

### Use `localhost` for iOS simulator, not LAN IP

The iOS simulator runs on the Mac — `localhost:3001` reaches the server directly. Hardcoded LAN IPs (e.g. `192.168.0.189`) go stale when the network changes and cause the app to hang.

### SiriTTS / CoreBluetooth warnings are noise

These iOS simulator logs are harmless and NOT the cause of hangs:
- `[SiriTTSService] Failed to get sandbox extensions`
- `[CoreBluetooth] API MISUSE: <CBCentralManager>`

## Architecture Overview

```
┌─────────────────┐         ┌─────────────────┐         ┌─────────────────┐
│    iOS App      │ ──────► │  Bridge Server  │ ◄────── │    Cue Tile     │
│   (Phone)       │         │   (Computer)    │         │   (M5Stack)     │
└─────────────────┘         └─────────────────┘         └─────────────────┘
      │                            │                           │
      │  User creates              │  Stores routines          │  Fetches routine
      │  routines                  │  Generates voice          │  Displays timer
      │                            │  Records completions      │  Plays audio
      ▼                            ▼                           ▼
   React Native              Express.js (Node)           MicroPython
   (Expo)                    TypeScript                  (UIFlow 2.0)
```

## Data Flow

1. **User creates routine** -> iOS App
2. **App syncs** -> `POST /api/tile/sync` -> Server caches it
3. **Tile boots** -> `GET /api/tile/routine` -> Loads into RAM
4. **User starts** -> `POST /api/tile/start` -> Sets flag
5. **Tile polls** -> `GET /api/tile/status` -> Sees `startRequested: true`
6. **Tile runs** -> Timer, audio, touch controls
7. **Tile completes** -> `POST /api/tile/complete` -> Server records

## WiFi Polling vs BLE

| Approach | Latency | Complexity | Status |
|----------|---------|------------|--------|
| WiFi Polling | 1-2 sec | Simple | Current |
| BLE Direct | Instant | Needs native build | Ready, deferred |
