# Hardware & Onboarding Reference

## Table of Contents
- Device Comparison
- CoreS3 SE Specifics
- Core2 / Core2 for AWS Specifics
- Onboarding a New Device
- Firmware Portability
- UIFlow 2.0 Unified API
- Memory Model
- Phone App Connectivity

## Device Comparison

Both devices run UIFlow 2.0 MicroPython and share the same high-level API (`M5.Lcd`, `M5.Speaker`, `M5.Touch`), so firmware is largely portable between them.

| Spec | Core2 / Core2 for AWS | CoreS3 SE |
|---|---|---|
| **SoC** | ESP32-D0WDQ6-V3 (LX6, 240MHz) | ESP32-S3 (LX7, 240MHz) |
| **Display** | 320x240 IPS, ILI9342C | 320x240 IPS, ILI9342C |
| **Touch** | FT6336U (screen + 3 sub-screen zones) | FT6336U (screen only) |
| **Speaker Amp** | NS4168 (I2S) | AW88298 Smart PA (I2S) |
| **PSRAM** | 8MB | 8MB |
| **Flash** | 16MB | 16MB |
| **Battery** | 390mAh built-in (500mAh on V1.1) | None (external only) |
| **PMU** | AXP192 (original) / AXP2101 (V1.1) | AXP2101 |
| **USB Chip** | CH9102F (external UART) | Native USB OTG (ESP32-S3) |
| **Bluetooth** | BT 4.2 + Classic BT | BT 5.0 (BLE only) |
| **UIFlow** | 1.0 and **2.0** | **2.0** only |
| **WiFi** | 2.4GHz only (no 5GHz!) | 2.4GHz only (no 5GHz!) |

## CoreS3 SE Specifics

- **Ghost touch:** Spurious touch at x=58, y=202 (hardware defect). Workaround: 30px dead zone filter. Core2 does NOT have this issue.
- **Boot recovery:** "Hold BtnA + reset" does NOT work (no physical BtnA). Only fix: change NVS `boot_option` to 1 via Thonny REPL (see Onboarding section below).
- **File upload:** Only **Thonny** and UIFlow Web IDE work. `mpremote`, `ampy`, `rshell` do NOT work (native USB incompatibility).
- **USB serial:** Native USB OTG — shows up as ESP32-S3 device (`/dev/tty.usbmodem-*`). No external driver needed.

## Core2 / Core2 for AWS Specifics

### Variants

- **Core2 (original):** AXP192 PMU, 390mAh battery
- **Core2 V1.1:** AXP2101 PMU, 500mAh battery, INA3221 current meter
- **Core2 for AWS:** Same as original Core2 + ATECC608 secure element in battery base

### Sub-Screen Touch Buttons (Core2 ONLY)

Three printed circles below screen mapped to touch zones at **y=240-279**. These are capacitive zones on the same FT6336U controller, NOT physical buttons.

**Grounding issue:** Sub-screen buttons only work reliably when:
- USB cable is plugged in, OR
- Device is held in hand, OR
- Device sits on a conductive surface

They do NOT work on wood/plastic/non-conductive surfaces. **Recommendation:** Use on-screen touch buttons (y < 240) instead.

### Boot Recovery (Core2)

- **Hold left touch zone (BtnA) + reset** works on Core2 to force startup menu (easier than CoreS3 SE NVS hack)
- NVS method also works as a permanent fix (same command as CoreS3 SE)

### File Upload (Core2)

- **Thonny** works (recommended)
- **mpremote** works (CH9102F uses standard UART protocol)
- **ampy** works but is slow (~115200 baud, 3+ min for large files)
- **rshell** works
- UIFlow 2.0 Web IDE works

### USB Serial & Driver Setup (Core2)

Uses **CH9102F** external USB-UART chip:
- **macOS:** Requires CH9102 driver from [M5Stack](https://docs.m5stack.com/en/download) or [WCH](https://www.wch.cn/downloads/CH34XSER_MAC_ZIP.html)
- **macOS will block the driver** on first install — go to **System Settings -> Privacy & Security**, find the blocked message for "Qinheng Microelectronics", click **Allow**, then **restart Mac**
- Verify: `ls /dev/tty.usbserial*` — should show `/dev/tty.usbserial-5410`
- Serial port: `/dev/tty.usbserial-*` (NOT `/dev/tty.usbmodem-*` like CoreS3 SE)

### Battery / Power

- Built-in LiPo battery (390mAh original, 500mAh V1.1)
- Charges via USB-C
- Power button: short press = wake, long press = off

### WiFi

- 2.4GHz only (same as CoreS3 SE)
- WiFi credentials set via M5Burner during firmware flash
- Can also use M5Burner "Configure" button to update WiFi without reflashing

## Onboarding a New Device

### Prerequisites

1. M5Burner installed ([download](https://docs.m5stack.com/en/download))
2. USB-C cable
3. Thonny IDE installed (for file upload and REPL)
4. CH9102 driver (macOS, for Core2 only — see Core2 USB section above)

### Steps

1. **Flash UIFlow 2.0 firmware:**
   - Open M5Burner
   - Select device type (Core2 -> "CORE2 & TOUGH", CoreS3 -> "CORES3")
   - Choose **UIFlow2.0** firmware (NOT UIFlow 1.0, NOT UIFlow_Tough)
   - **Core2 for AWS (ships with AWS factory firmware) — burn sequence:**
     1. Click **Burn**, set baud rate to **115200** (default 1500000 may hang with CH9102F chip; 921600 also works), click **Start**
     2. When prompted "bind your account?" -> click **Yes** (required on first burn)
     3. After burn completes, a **Configure** dialog appears — set:
        - **Boot Option:** "Show startup menu and network setup" (`boot_option=1` — required for serial mode)
        - **WiFi SSID/password:** Optional — leave blank if using serial mode only
        - **COM:** Verify it's `tty.usbserial-*` (NOT `tty.Bluetooth-Incoming-Port`)
     4. Click **Next** to write the configuration
   - **Verify burn succeeded:** Log should show multiple MB written (not just 24KB — that means only config was written)
   - After restart, screen should show **UIFlow 2.0 startup menu**

2. **Set boot_option (if not already set via M5Burner Configure):**
   - Open Thonny
   - **Set interpreter:** Run -> Configure Interpreter -> **MicroPython (ESP32)** -> select correct port (`/dev/tty.usbserial-*` for Core2, `/dev/tty.usbmodem-*` for CoreS3 SE)
   - Run in REPL:
     ```python
     import esp32; nvs = esp32.NVS("uiflow"); nvs.set_u8("boot_option", 1); nvs.commit()
     ```
   - Reset device — should now show startup menu

3. **Upload firmware files** (via Thonny: File -> Save as -> MicroPython device):
   - `main.py`, `config.py`, `transport.py`, `tile_audio.py`, `secrets.py`
   - Optionally: `audio_engine.py` (for background music)

4. **Configure secrets:**
   - Copy `secrets.py.example` -> `secrets.py`
   - Fill in `API_KEY`, `WIFI_SSID`, `WIFI_PASSWORD`

5. **Test:**
   - Reset device, tap "App Run" on startup menu
   - **Verify display:** Should show "Microsteps" / "Waiting for routine..."
   - Start server on host, trigger routine from iOS app
   - **Verify server logs:** Should see `GET /api/tile/status` requests every ~2 seconds (confirms Tile is polling)
   - **Verify routine runs:** Tile should display timer and play audio after tapping "Start on Tile" in the app

### WiFi Credentials

WiFi creds are flashed via M5Burner. To change them later:
- Use M5Burner "Configure" button (no reflash needed), or
- Use `secrets.py` fallback, or
- Implement BLE config (future)

### Known: Serial Mode Audio is Slow

Each audio clip is base64-encoded over USB serial. A routine with multiple steps triggers 20-30 serial round-trips at startup. Use `TRANSPORT_MODE = "demo"` for quick display/touch/timer testing without waiting for audio downloads.

## Firmware Portability

### Confirmed: Zero-Change Portability (Feb 2026)

All firmware files (`main.py`, `transport.py`, `tile_audio.py`, `config.py`) ran on Core2 for AWS with **zero code changes** from the CoreS3 SE codebase. Display, touch, speaker, serial bridge, and polling all work identically under UIFlow 2.0.

### What Works As-Is (No Changes Needed)

- `transport.py` — WiFi/Serial/Demo transport layer
- `tile_audio.py` — Speaker API is unified in UIFlow 2.0
- `config.py` — Configuration format identical
- `audio_engine.py` — PSRAM streaming works on both (8MB each)
- `ble.py` — BLE APIs differ but deferred for MVP

### What May Need Minor Adjustment in `main.py`

- **Ghost touch filter:** CoreS3 SE-specific. Harmless on Core2 but can be removed/conditioned
- **Touch button positions:** Current on-screen buttons work on both. Optionally use Core2's sub-screen zones (not recommended due to grounding issue)

## UIFlow 2.0 Unified API (Both Devices)

The following APIs work identically on both Core2 and CoreS3 SE under UIFlow 2.0:

```python
# Initialization
import M5
from M5 import Lcd, Speaker, Touch
M5.begin()
M5.update()

# Display (ILI9342C, 320x240, 16-bit color)
Lcd.fillScreen(color)
Lcd.drawString(text, x, y)
Lcd.fillRoundRect(x, y, w, h, radius, color)
Lcd.fillRect(x, y, w, h, color)
Lcd.fillCircle(x, y, r, color)
Lcd.setTextSize(size)
Lcd.setTextColor(fg, bg)

# Speaker (I2S — NS4168 on Core2, AW88298 on CoreS3 SE)
Speaker.begin()
Speaker.setVolume(0-255)
Speaker.tone(frequency_hz, duration_ms)
Speaker.playRaw(pcm_data, sample_rate, stereo, repeat, channel, stop_current)
Speaker.isPlaying()
Speaker.stop()

# Touch (FT6336U on both)
Touch.getCount()
Touch.getX()
Touch.getY()

# Network
import network
wlan = network.WLAN(network.STA_IF)

# HTTP (use `requests`, NOT `urequests`)
import requests
```

### Audio Format (Both Devices)

- PCM **24kHz, 16-bit, mono** for voice (matches OpenAI TTS output)
- PCM **16kHz, 16-bit, mono** for background music
- NS4168 and AW88298 both support 8kHz-96kHz sample rates

## Memory Model (What Survives Reboot)

```
+---------------------------+----------------------------------+
|  RAM (~512 KB)            |  Flash Storage (~8 MB)           |
|  "Working Memory"         |  "Hard Drive"                    |
+---------------------------+----------------------------------+
|  - Current routine        |  - main.py (firmware)            |
|  - Current step index     |  - config.py (WiFi, transport)   |
|  - Timer state            |  - tile_audio.py (audio module)  |
|  - Audio buffers          |  - transport.py (API layer)      |
|                           |                                  |
|  LOST on power off        |  SURVIVES power off              |
+---------------------------+----------------------------------+
```

The Tile fetches a fresh routine every boot. Edit on phone -> next boot gets the update.

## Phone App -> Tile Connectivity

- **Physical phone (Expo Go):** Must use Mac's LAN IP (e.g., `http://192.168.x.x:3001`), not `localhost`. Set via `EXPO_PUBLIC_API_URL` env var when starting Expo.
- **iOS Simulator:** `localhost` works fine.
- **UIFlow version:** Always flash **UIFlow 2.0** firmware (not 1.0) — the APIs are completely different. UIFlow 1.0 uses `from m5stack import *` (lowercase) — incompatible.
