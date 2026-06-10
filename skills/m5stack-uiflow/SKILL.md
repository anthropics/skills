---
name: m5stack-uiflow
description: >
  Deploy and debug MicroPython firmware on M5Stack CoreS3 SE, Core2, and Core2 for AWS
  using UIFlow 2.0. Use when flashing firmware, playing audio (voice TTS or background music),
  handling touch input, configuring WiFi/serial/demo transport, onboarding new devices,
  or troubleshooting ghost touch, timer flicker, serial bridge, and audio streaming issues.
  Triggers: m5stack, tile, cue tile, cores3, core2, core2 for aws, esp32, micropython, uiflow,
  speaker, lcd display, touch screen, thonny, m5burner, serial bridge, ghost touch, timer flicker,
  audio gap, psram, background music, onboarding, new device, flash firmware.
  File patterns: firmware/**, **/tile_*.py, **/audio_engine.py, **/transport.py.
---

# M5Stack UIFlow Development Skill

Development guide for M5Stack devices (CoreS3 SE, Core2, Core2 for AWS) with UIFlow 2.0 MicroPython firmware.

## References

- [Audio Playback](references/audio.md) — formats, playRaw params, PSRAM streaming, chunked playback, prefetching, concatenation, LCD quirks
- [Audio Streaming Learnings](references/audio-streaming.md) — detailed debugging logs from audio implementation sessions
- [Hardware & Onboarding](references/hardware.md) — device comparison, Core2/CoreS3 specifics, onboarding steps, firmware portability, unified API
- [Serial Bridge & Integration](references/serial-bridge.md) — serial bridge protocol/gotchas, BLE setup, iOS app integration, architecture

## File Deployment (CRITICAL)

### What DOESN'T Work (CoreS3 SE)

```bash
# These tools DO NOT WORK on CoreS3 SE (native USB incompatibility):
mpremote connect /dev/tty.* fs cp main.py :main.py  # FAILS
ampy --port /dev/tty.* put main.py                   # FAILS
rshell cp main.py /pyboard/                          # FAILS
# Note: mpremote, ampy, and rshell DO work on Core2 (CH9102F uses standard UART)
```

### What DOES Work: Thonny (Both Devices)

1. Install [Thonny IDE](https://thonny.org/)
2. Connect M5Stack via USB
3. In Thonny: **Run -> Configure interpreter -> MicroPython (ESP32)**
4. Select the correct port (`/dev/tty.usbserial-*` for Core2, `/dev/tty.usbmodem-*` for CoreS3 SE)
5. Open your `.py` file
6. **File -> Save as -> MicroPython device**
7. Save as `main.py` (or other filename)

## Display & Colors

```python
SCREEN_WIDTH = 320
SCREEN_HEIGHT = 240

# Dark Theme Colors
BG_COLOR = 0x121212       # Background default
BG_SECONDARY = 0x1E1E1E   # Cards
BG_TERTIARY = 0x2A2A2A    # Buttons
TEXT_COLOR = 0xFFFFFF     # Primary text (white)
TEXT_SECONDARY = 0xA0A0A0 # Secondary text (gray)
PRIMARY_COLOR = 0xD35400  # Brand orange
SUCCESS_COLOR = 0x3DA861  # Green (skip/play)
ERROR_COLOR = 0xFF3B30    # Red (stop)
BORDER_COLOR = 0x333333   # Borders
```

```python
BTN_RADIUS = 12
Lcd.fillRoundRect(x, y, width, height, BTN_RADIUS, BG_TERTIARY)

# Text sizing
Lcd.setTextSize(1)    # Small
Lcd.setTextSize(1.4)  # Step title
Lcd.setTextSize(2.5)  # App title, PAUSED
Lcd.setTextSize(3)    # Timer (large)
```

### Layout Zones (Avoiding Ghost Touch)

```
┌──────────────────────────────────┐
│ Status line (y=10)               │
│ Routine title (y=35)             │
│ Step info (y=60-78)              │
│ Timer (y=95-135)                 │
│ [PAUSE] [SKIP] [STOP] (y=140)   │  ← Button row ABOVE ghost zone
│          ⚠ GHOST ZONE (y=202)   │
└──────────────────────────────────┘
```

## Module Naming Conflicts

**NEVER** name your file `audio.py` — it conflicts with the built-in module. Use `tile_audio.py` or `audio_engine.py`.

## Audio Playback (Quick Reference)

For deep dives see [references/audio.md](references/audio.md).

```python
from M5 import Speaker

# Voice (OpenAI TTS): PCM 24kHz, 16-bit, Mono
VOICE_SAMPLE_RATE = 24000
# Music (background): PCM 16kHz, 16-bit, Mono
MUSIC_SAMPLE_RATE = 16000

Speaker.begin()
Speaker.setVolume(190)  # 0-255

Speaker.playRaw(
    data,           # Raw PCM bytes (or memoryview)
    sample_rate,    # 24000 for voice, 16000 for music
    stereo,         # False for mono
    repeat,         # 1 = play once
    channel,        # 0 = default channel
    stop_current    # True = interrupt current, False = queue
)
```

Key gotchas:
- `playRaw()` silently truncates large buffers — feed in **1MB chunks**
- Download music to PSRAM at boot, not via streaming (streaming has gaps)
- Use `readinto(memoryview(...))` for fast downloads, not `recv()`
- Pre-fetch ALL audio before starting timers — don't fetch on-demand

## Touch Handling

### Ghost Touch Filter (CoreS3 SE ONLY)

```python
GHOST_X, GHOST_Y, GHOST_RADIUS = 58, 202, 30

def is_ghost_touch(x, y):
    return abs(x - GHOST_X) < GHOST_RADIUS and abs(y - GHOST_Y) < GHOST_RADIUS
```

### Touch Polling with Debounce

```python
import M5
from M5 import Touch

TOUCH_DEBOUNCE_MS = 300
_last_touch_time = 0
_touch_was_active = False

def check_touch():
    global _touch_was_active, _last_touch_time
    M5.update()

    if Touch.getCount() > 0:
        if not _touch_was_active:
            _touch_was_active = True
            current_time = time.ticks_ms()
            if current_time - _last_touch_time < TOUCH_DEBOUNCE_MS:
                return None
            _last_touch_time = current_time
            x, y = Touch.getX(), Touch.getY()
            if is_ghost_touch(x, y):
                return None
            return (x, y)
    else:
        _touch_was_active = False
    return None
```

## Timer Display (Avoiding Flicker)

```python
last_remaining = -1

while True:
    remaining = calculate_remaining_seconds()
    if not is_paused and remaining != last_remaining:
        last_remaining = remaining
        Lcd.fillRect(0, 95, SCREEN_WIDTH, 40, BG_COLOR)  # Clear ONLY timer area
        draw_timer(remaining)
    time.sleep(0.1)
```

After resume, reset `last_remaining = -1` to force redraw.

### Time Warnings Guard

Only announce warnings if the step is long enough:

```python
if remaining == 60 and not warned_60 and duration_seconds > 90:
    warned_60 = True
    play_time_warning(60)
elif remaining == 30 and not warned_30 and duration_seconds > 45:
    warned_30 = True
    play_time_warning(30)
```

## WiFi / Network

```python
# CORRECT — UIFlow provides full requests module
import requests
r = requests.get(url, headers=headers)
data = r.text
r.close()  # Always close!

# WRONG — urequests may not work with UIFlow
# import urequests as requests
```

### WiFi Connection Priority

```python
import network
wlan = network.WLAN(network.STA_IF)
wlan.active(True)

# 1. Check if already connected (UIFlow often auto-connects)
if wlan.isconnected():
    return True
# 2. Try UIFlow stored credentials (from M5Burner)
try:
    import wlan as uiflow_wlan
    uiflow_wlan.connect_to_wifi()
except:
    pass
# 3. Fall back to hardcoded credentials
wlan.connect(SSID, PASSWORD)
```

## Transport Abstraction

| Mode | Use Case | Network |
|------|----------|---------|
| `demo` | Test UI/timer without network | None |
| `serial` | Development with host bridge | USB |
| `wifi` | Production | HTTP over WiFi |

```python
# config.py
TRANSPORT_MODE = "wifi"  # or "demo" or "serial"

# transport.py usage
from transport import get_transport
transport = get_transport()
routine = transport.fetch_routine()
```

## Serial Bridge (Quick Reference)

For full details see [references/serial-bridge.md](references/serial-bridge.md).

```bash
python tools/serial_bridge.py --port /dev/cu.usbserial-5410 --server http://localhost:3001
```

Key gotchas:
- Every Tile command needs a handler in `serial_bridge.py` (command parity)
- Disconnect Thonny before running the bridge (can't share USB port)
- Set `TRANSPORT_MODE = "wifi"` guard around AudioEngine (serial has no `api_base_url`)
- Disable DTR before opening serial port (prevents ESP32 reset loop)

## Common Errors & Fixes

| Error | Fix |
|-------|-----|
| `ModuleNotFoundError: audio` | Rename file from `audio.py` to `tile_audio.py` |
| `Network request failed` | Check `API_BASE_URL` uses computer's IP, not `localhost`. Ensure same WiFi (2.4GHz). |
| Touch not responding | Call `M5.update()` in main loop. Check ghost zone (x=58, y=202). |
| `OSError: [Errno 23] ENFILE` | Always `r.close()` after HTTP requests |
| Music cuts out or has gaps | Download to PSRAM at boot, feed in 1MB chunks, use `readinto(memoryview)` |
| Timer flickering | Only update when `remaining != last_remaining`. Clear timer area only. |
| Time warning plays immediately | Guard: only play "30s remaining" if `duration_seconds > 45` |
| Audio delays during timer | Pre-fetch ALL audio before routine starts. Concatenate clips. |

## Project Structure

```
firmware/m5stack/
├── main.py           # Entry point, UI, routine execution
├── config.py         # Transport mode, API URL
├── secrets.py        # WiFi credentials, API keys (gitignored)
├── transport.py      # Network abstraction (demo/serial/wifi)
├── tile_audio.py     # Speaker utilities
├── audio_engine.py   # Music streaming with voice interruption
├── touch_diagnostic.py  # Debug tool for ghost touch
└── ble.py            # BLE support (future)
```

## Testing Workflow

### Quick Test (Demo Mode)

Set `TRANSPORT_MODE = "demo"` in config.py, upload via Thonny, tap "App Run". Runs hardcoded routine without network. **Verify:** Timer counts down, touch buttons respond, audio tone plays.

### Full Test (WiFi Mode)

1. Start server: `OPENAI_API_KEY=sk-your-key npm run server:dev`
2. Set `TRANSPORT_MODE = "wifi"` in config.py, upload via Thonny
3. Power on M5Stack -> tap "App Run"
4. **Verify:** Server shows `GET /api/tile/status` polling every ~2s
5. From iOS app: tap "Start on Tile"
6. **Verify:** Tile displays routine, timer counts down, TTS voice plays

## Tips

- **Never name a file `audio.py`** — it shadows MicroPython's built-in module and causes cryptic import errors. Use `tile_audio.py` or `audio_engine.py`.
- **`Speaker.playRaw()` silently truncates large buffers.** Feed audio in 1MB chunks, not the full file. A 6.6MB buffer will just stop partway through with no error.
- **Use `readinto(memoryview(...))` for large downloads, not `recv()`.** `recv()` allocates new bytes on every call and is dramatically slower.
- **Always pass both foreground AND background to `Lcd.setTextColor()`.** Passing only foreground leaves black highlight boxes behind text.
- **`boot_option=0` breaks serial mode.** Auto-run uses raw REPL which redirects stdout away from USB serial. Set `boot_option=1` via NVS. Renaming `main.py` does NOT prevent auto-run.
- **macOS will silently block the CH9102 driver** (Core2 only). After installing, go to System Settings -> Privacy & Security, allow "Qinheng Microelectronics", then restart Mac.
- **Pre-fetch ALL audio before starting the timer.** Fetching TTS on-demand during a step adds noticeable delays. Cache at routine start, concatenate clips for dynamic phrases.
- **Core2 sub-screen touch buttons have a grounding issue.** They only work with USB plugged in or device held. Use on-screen buttons (y < 240).
- **CoreS3 SE has a ghost touch at x=58, y=202.** Filter with a 30px dead zone radius. Core2 does not have this defect.
- **Always close HTTP responses** with `r.close()`. Leaking handles causes `OSError: [Errno 23] ENFILE` after ~10 requests.

## Glossary

| Term | Definition |
|------|------------|
| **Bridge Server** | Middleman server connecting iOS app and Tile |
| **Tile** | M5Stack hardware device (CoreS3 SE, Core2, or Core2 for AWS) |
| **TTS** | Text-to-Speech (OpenAI API) |
| **PCM** | Raw audio format: voice=24kHz, music=16kHz, both 16-bit mono |
| **Transport** | Abstraction layer (demo/serial/wifi modes) |
| **Ghost touch** | Phantom touch at x=58, y=202 on CoreS3 SE |
| **PSRAM** | 8MB pseudo-static RAM for large buffers (music, audio cache) |
