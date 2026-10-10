# M5Stack Audio & SD Card — Complete Reference

Comprehensive reference covering SD card setup, audio streaming, I2S DMA buffering, FreeRTOS task architecture, codec performance, and troubleshooting for M5Stack devices. Built from hands-on experience with the Cue Tile project (CoreS3 SE, MicroPython/UIFlow 2.0) and deep research across community sources, Espressif docs, and GitHub issues.

---

## Table of Contents

1. [Hardware Specs](#1-hardware-specs)
2. [SD Card Setup](#2-sd-card-setup)
3. [Audio Hardware Reference](#3-audio-hardware-reference)
4. [Speaker.playRaw() Deep Behavior](#4-speakerplayraw-deep-behavior)
5. [WiFi Audio Streaming — The Fundamental Problem](#5-wifi-audio-streaming--the-fundamental-problem)
6. [Strategy A: Download-Then-Play (MicroPython)](#6-strategy-a-download-then-play-micropython)
7. [Strategy B: True Streaming (C/Arduino Only)](#7-strategy-b-true-streaming-carduino-only)
8. [I2S DMA Buffering Deep Dive](#8-i2s-dma-buffering-deep-dive)
9. [FreeRTOS Task Architecture for Audio](#9-freertos-task-architecture-for-audio)
10. [WiFi Optimization for Streaming](#10-wifi-optimization-for-streaming)
11. [Audio Codec Performance](#11-audio-codec-performance)
12. [MicroPython Audio Limitations](#12-micropython-audio-limitations)
13. [C/Arduino Audio Libraries (Ranked)](#13-carduino-audio-libraries-ranked)
14. [WiFi vs Alternatives for Audio](#14-wifi-vs-alternatives-for-audio)
15. [Music File Conversion](#15-music-file-conversion)
16. [Cue Project: Current Implementation](#16-cue-project-current-implementation)
17. [Cue Project: Known Bugs & Next Steps](#17-cue-project-known-bugs--next-steps)
18. [Complete Working Examples](#18-complete-working-examples)
19. [Troubleshooting Quick Reference](#19-troubleshooting-quick-reference)
20. [Key Principles Learned](#20-key-principles-learned)

---

## 1. Hardware Specs

### CoreS3 SE (Our Device)

| Component | Spec | Audio Relevance |
|-----------|------|-----------------|
| **MCU** | ESP32-S3, dual-core 240MHz | Core pinning matters for streaming |
| **RAM** | 512KB SRAM | NOT the limit — PSRAM is |
| **PSRAM** | 8MB | Can hold ~170s of 24kHz/16-bit/mono audio |
| **Flash** | 16MB | Firmware storage, not audio |
| **Speaker** | AW88298 Smart PA, 1W, I2S | Best audio quality in M5Stack lineup |
| **Audio Codec** | ES7210 (input only) | Not used for playback |
| **WiFi** | 2.4GHz only (no 5GHz!) | Streaming source for audio |
| **Display** | 320x240 IPS LCD | Shares SPI bus with SD card (conflict!) |
| **Touch** | FT6336U capacitive | Ghost touch at x=58, y=202 |

**Memory math:** 24000 samples/sec x 2 bytes = 48,000 bytes/sec = ~48KB/s. 8MB PSRAM = ~170 seconds (~2.8 min) of 24kHz/16-bit/mono audio.

### All M5Stack Models

| Model | MCU | Flash | PSRAM | SD Card | Audio Output | Audio Quality |
|-------|-----|-------|-------|---------|-------------|---------------|
| Core Basic | ESP32-D0WDQ6 | 16MB | None | Yes (SPI) | 8-bit internal DAC | Poor |
| Core Gray | ESP32-D0WDQ6 | 16MB | 520KB | Yes (SPI) | 8-bit internal DAC | Poor |
| Core Fire | ESP32-D0WDQ6 | 16MB | 8MB | Yes (SPI) | 8-bit internal DAC | Poor |
| **Core2** | ESP32-D0WDQ6 | 16MB | **8MB** | Yes (SPI) | **NS4168 I2S amp** | Good |
| **CoreS3 / CoreS3 SE** | **ESP32-S3** | 16MB | **8MB** | Yes (SPI) | **AW88298 I2S amp** | **Best** |
| ATOM Echo | ESP32-PICO | 4MB | — | No | NS4168 I2S amp | Acceptable |
| Tab5 | ESP32-P4 | — | — | — | ES8388 + NS4150B | Hi-Fi capable |

**Key takeaway:** Core2 or CoreS3 are the minimum for serious audio. Basic/Gray/Fire use the ESP32's internal 8-bit DAC, which sounds terrible.

---

## 2. SD Card Setup

### 2.1 Pin Mappings by Model

**Using the wrong pins is the #1 reason SD cards fail to initialize.**

| Model | SCK (CLK) | MOSI | MISO | CS | Notes |
|-------|-----------|------|------|-----|-------|
| Core Basic / Gray / Fire | GPIO 18 | GPIO 23 | GPIO 19 | GPIO 4 | Shared SPI bus with LCD |
| Core2 / Core2 v1.1 / Tough | GPIO 18 | GPIO 23 | GPIO 38 | GPIO 4 | MISO differs from Basic |
| **CoreS3 (ESP32-S3)** | **GPIO 36** | **GPIO 37** | **GPIO 35** | **GPIO 4** | **Completely different pins** |
| Cardputer (StampS3) | GPIO 40 | GPIO 14 | GPIO 39 | GPIO 12 | Unique layout |
| M5Paper | GPIO 14 | GPIO 12 | GPIO 13 | GPIO 4 | Yet another set |

> **Critical observation**: The MISO pin changes most often. Basic=19, Core2=38, CoreS3=35.

### 2.2 CoreS3 SE SD Card — FAILED (Don't Try Again in MicroPython)

**What we tried:** Stream background music from SD card for local gapless playback.

**Result:** `OSError 16 (EBUSY)` — SD card mount fails every time.

**Root cause:** Hardware SPI bus conflict. The CoreS3 SE shares the SPI bus between the LCD display and SD card. In MicroPython/UIFlow 2.0, once the LCD is initialized (which happens automatically), the SPI bus is locked by the display driver.

**Workarounds that exist (but NOT in MicroPython):**
- Arduino `SD.begin()` with custom SPI pins works in C++
- Some users report success with specific pin configurations in C++
- **No known MicroPython solution exists**

**Verdict:** SD card is dead for audio on CoreS3 SE with UIFlow firmware. Don't revisit unless switching to Arduino/C++.

### 2.3 Formatting Requirements (For Models Where SD Works)

- **Partition scheme MUST be MBR** (not GPT — macOS Disk Utility may default to GPT)
- **Format: FAT32** (not exFAT, not NTFS)
- **Maximum supported size: 32GB**
- **Single partition** or superfloppy format

**Correct formatting on macOS:**
```bash
sudo diskutil eraseDisk FAT32 SDCARD MBRFormat /dev/diskN
```

### 2.4 Mounting Code Examples

#### Method A: `machine.SDCard` (Recommended)
```python
import machine, os
sd = machine.SDCard(
    slot=2,
    sck=machine.Pin(18),
    mosi=machine.Pin(23),
    miso=machine.Pin(19),   # 19=Basic, 38=Core2, 35=CoreS3
    cs=machine.Pin(4),
    freq=1000000             # Start at 1MHz for reliability
)
os.mount(sd, '/sd')
```

#### Method B: Pure-Python sdcard.py with SoftSPI
Requires uploading `sdcard.py` from micropython-lib:
```python
from machine import SoftSPI, Pin
import sdcard, os
spi = SoftSPI(baudrate=100000, polarity=1, phase=0,
              sck=Pin(18), mosi=Pin(23), miso=Pin(38))
sd = sdcard.SDCard(spi, Pin(4))
os.mount(sd, '/sd')
```

#### Method C: UIFlow 2.x Hardware Module
```python
from hardware import sdcard
sdcard.SDCard(20000000)  # freq in Hz
import os
print(os.listdir('/sd'))
```

### 2.5 UIFlow vs Standard MicroPython

| Feature | UIFlow 1.x | UIFlow 2.x | Standard MicroPython |
|---------|------------|------------|---------------------|
| SD init API | `uos.sdconfig()` + `uos.mountsd()` | `hardware.sdcard.SDCard()` | `machine.SDCard()` |
| Auto-mount | Yes (some devices) | No | No |
| SPI conflict | Rare | **Common** | No (you control init order) |
| Thonny REPL | Works | Works | Native |

**Critical UIFlow 2.x issue:** `OSError: (-259, 'ESP_ERR_INVALID_STATE')` means display grabbed SPI bus first. Fixed in v2.1.6 — earlier versions have broken SD card support.

### 2.6 Core2-Specific: Power Management

Core2 uses AXP192 PMU that controls power to SD card slot. On vanilla MicroPython (not UIFlow), you may need:
```python
import axp202c
axp = axp202c.PMU(address=0x34)
axp.enablePower(axp202c.AXP192_LDO2)
```

### 2.7 The `slot` Parameter

| Chip | Slot 2 |
|------|--------|
| ESP32 | SPI (id=0) |
| ESP32-S3 | SPI (id=1) |

**For all M5Stack devices, use `slot=2`.**

### 2.8 SD Card Error Reference

| Error | Cause | Fix |
|-------|-------|-----|
| `OSError: (-259, 'ESP_ERR_INVALID_STATE')` | SPI bus already initialized | Hard reset, init SD before display |
| `OSError: [Errno 19] ENODEV` | Card not detected | Check physical insertion + correct pins |
| `OSError: [Errno 5] EIO` | SPI communication failure | Lower freq to 1MHz, reformat MBR FAT32 |
| `OSError: 16` (EBUSY) | Already mounted or SPI conflict | `os.umount('/sd')` first, or reset |
| `timeout waiting for v2 card` | Card not responding | Wrong pins, try different card brand |
| `spi bus 2 not available` | Bus occupied by display | Reset device, use explicit pins |

### 2.9 Diagnostic Script

Full SD card diagnostic script — paste into Thonny REPL with Ctrl+E:

```python
# === M5Stack SD Card Diagnostic Script ===
import sys, os
print("=" * 50)
print("M5Stack SD Card Diagnostic Report")
print("=" * 50)

# System info
print("\n[1] System Information")
print("  Implementation:", sys.implementation)
print("  Version:", sys.version)

# Check available modules
print("\n[2] Available SD Card Modules")
has_machine_sd = False
try:
    import machine
    has_machine_sd = hasattr(machine, 'SDCard')
    print("  machine.SDCard:", "AVAILABLE" if has_machine_sd else "NOT AVAILABLE")
except Exception as e:
    print("  machine module error:", e)

# Check filesystem
print("\n[3] Current Filesystem")
root = os.listdir('/')
print("  Root:", root)
print("  SD mounted:", 'sd' in root)

# Attempt mount — CHANGE PINS FOR YOUR MODEL
SCK, MOSI, MISO, CS = 36, 37, 35, 4  # CoreS3 pins
print(f"\n[4] Trying pins: SCK={SCK}, MOSI={MOSI}, MISO={MISO}, CS={CS}")

if has_machine_sd:
    try:
        sd = machine.SDCard(slot=2, sck=machine.Pin(SCK), mosi=machine.Pin(MOSI),
                            miso=machine.Pin(MISO), cs=machine.Pin(CS), freq=1000000)
        vfs = os.VfsFat(sd)
        os.mount(vfs, '/sd')
        print("  SUCCESS: SD card mounted at /sd")
        print("  Contents:", os.listdir('/sd'))
        # Read/write test
        with open('/sd/_test.txt', 'w') as f:
            f.write('test')
        with open('/sd/_test.txt', 'r') as f:
            assert f.read() == 'test'
        os.remove('/sd/_test.txt')
        print("  Read/Write test: PASSED")
    except Exception as e:
        print("  FAILED:", type(e).__name__, e)

print("=" * 50)
```

---

## 3. Audio Hardware Reference

### 3.1 Audio Chips by Model

| Device | Audio Chip | Speaker | I2S Interface | Audio Quality |
|--------|-----------|---------|---------------|---------------|
| Core Basic/Gray/Fire | ESP32 internal DAC (GPIO 25/26) | 1W | 8-bit DAC, not true I2S | Poor |
| **Core2** | **NS4168** I2S amplifier | 1W | True I2S digital | Good |
| **CoreS3 / CoreS3 SE** | **AW88298** 16-bit I2S amp + ES7210 codec | 1W | True I2S, dual mic | **Best** |
| ATOM Echo | NS4168 + SPM1423 PDM mic | Small | True I2S | Acceptable |
| Tab5 (ESP32-P4) | ES8388 + ES7210 AEC + NS4150B | 1W 8ohm | Full I2S with MCLK | Hi-Fi |

NS4168 and AW88298 are true I2S amplifiers with automatic sample rate detection (8kHz-96kHz).

### 3.2 I2S Pin Mappings

| Model | BCK (BCLK) | WS (LRC) | DATA (DOUT) |
|-------|-----------|---------|-------------|
| Core Basic/Gray/Core2 | 12 | 0 | 2 |
| **CoreS3** | **34** | **33** | **13** |
| ATOM Echo | 19 | 33 | 22 |

### 3.3 Models Without Audio

No built-in audio output: M5StickC series (buzzer only), ATOM Lite/Matrix/S3, M5Stamp series. These require an external DAC HAT or speaker module.

---

## 4. Speaker.playRaw() Deep Behavior

### API Signature
```python
Speaker.playRaw(data, sample_rate, stereo, repeat, channel, stop_current)
```

| Parameter | Type | Value | Notes |
|-----------|------|-------|-------|
| `data` | bytes | PCM buffer | **Stores POINTER, not copy!** |
| `sample_rate` | int | 24000 | Must match source |
| `stereo` | bool | False | Mono |
| `repeat` | int | 1 | Play once |
| `channel` | int | 0 | Default channel (0-7, 8 virtual channels) |
| `stop_current` | bool | True/False | True = interrupt, False = queue |

### Critical: Pointer Storage (M5Unified GitHub Issue #29)

**`playRaw()` stores a pointer to your buffer, it does NOT copy the data.**

- You **cannot** reuse a buffer immediately after calling `playRaw()`
- If you overwrite buffer data while it's still being played → **corrupted/garbled audio**
- Double buffering (2 buffers) is NOT enough — speaker may still read from "old" buffer
- **Triple buffering (3 buffers) is the minimum** for gapless cycling
- Calling thread must have FreeRTOS priority >= 1

### stop_current Parameter

| Value | Behavior | Use Case |
|-------|----------|----------|
| `True` | Stop current audio, start new | First chunk, voice interrupts |
| `False` | Add to internal speaker queue | Queuing subsequent chunks |

**Reality check:** Even with `stop_current=False`, transitions between queued chunks still have small audible gaps at the MicroPython level. The M5Unified Speaker class was designed for one-shot playback, not streaming.

### UIFlow Speaker Class Limitations

UIFlow2's Speaker class is designed for one-shot playback, NOT streaming:
- `Speaker.playRaw(data, rate)` — requires entire audio in memory
- `Speaker.playWav(data)` — plays complete WAV from memory
- `Speaker.playWavFile(path)` — plays from filesystem
- Calling `playRaw()` repeatedly produces **clicking artifacts** between calls

---

## 5. WiFi Audio Streaming — The Fundamental Problem

### MicroPython Cannot Do Simultaneous WiFi + Audio

Every community attempt has failed above ~16kHz mono. The reasons are fundamental:

| Limitation | Impact |
|------------|--------|
| **GC pauses** (1-10ms) | Audible clicks — GC scans entire PSRAM (up to 4MB) |
| **Single-threaded** (`_thread` still uses GIL) | No true dual-core task pinning |
| **No task priority control** | Cannot prioritize audio over network |
| **~100-255x slower than C** | Buffer management too slow |
| **WiFi + I2S DMA interrupt contention** | ESP32 bug #12955 |
| **Measured throughput ceiling** | ~16-32 kbps (need ~384 kbps for 24kHz) |

**Nobody has built a working MicroPython WiFi audio streamer on ESP32.** All successful projects use C/C++.

Community evidence:
- Bug #12955: I2S streaming clicks at >= 22050 Hz, even with large buffers
- Discussion #13561: ESP32-to-ESP32 audio = "metallic and choppy"
- Discussion #12945: HTTP audio streamer works at 8kHz, choppy at 44.1kHz

---

## 6. Strategy A: Download-Then-Play (MicroPython)

**Recommended for TTS and short audio.** Completely eliminates the WiFi-vs-I2S conflict. This is what successful M5Stack audio projects actually do (including xiaozhi-esp32 AI assistant).

```
Phase 1: Download entire audio to PSRAM (WiFi has full resources)
Phase 2: Play from PSRAM via Speaker (no network activity)
```

### PSRAM Capacity for Audio

| Format | Data Rate | Duration in 4MB | Duration in 8MB |
|--------|-----------|-----------------|-----------------|
| 8kHz, 8-bit, mono | 8 KB/s | ~8.7 min | ~17.4 min |
| 16kHz, 16-bit, mono | 32 KB/s | ~2.2 min | ~4.3 min |
| **24kHz, 16-bit, mono (current)** | **48 KB/s** | **~1.4 min** | **~2.8 min** |
| 44.1kHz, 16-bit, stereo | 176.4 KB/s | ~23 sec | ~46 sec |

### Advantages
- Works in MicroPython
- Glitch-free playback guaranteed
- Simple implementation — no buffering complexity
- WiFi dropout during playback is irrelevant

### Tradeoffs
- 5-10 second startup delay while downloading
- Limited by PSRAM capacity (~170s at 24kHz/16-bit/mono)
- Can't stream indefinitely

### Implementation (MicroPython)
```python
import requests, gc
from M5 import Speaker

# Phase 1: Download entire file
gc.collect()
r = requests.get(f"{api_url}/api/tile/music/chunk?offset=0&length={file_size}")
audio_data = r.content
r.close()
gc.collect()

# Phase 2: Play from memory
Speaker.playRaw(audio_data, 24000, False, 1, 0, True)
```

### With machine.I2S (Standard MicroPython)
```python
from machine import I2S, Pin
audio_out = I2S(0, sck=Pin(34), ws=Pin(33), sd=Pin(13),
                mode=I2S.TX, bits=16, format=I2S.MONO,
                rate=24000, ibuf=40000)
audio_out.write(audio_data)
audio_out.deinit()
```

---

## 7. Strategy B: True Streaming (C/Arduino Only)

Required for longer audio, internet radio, or low-latency needs. **Must use C/Arduino** — MicroPython cannot do this reliably.

### Required Architecture

```
Core 0 (WiFi)                        Core 1 (Audio)
=================                    =================
WiFi driver (system)                 I2S output task (pri 17-20)
TCP/IP stack (lwIP, pri 18)          Audio decode task (pri 15-17)
WiFi receive task (pri 10-15)
        |                                    |
        v                                    v
   [PSRAM Ring Buffer: 128-512KB]    [I2S DMA: 8-32KB internal SRAM]
        ^                                    |
        |                                    v
   HTTP/TCP receive              Read from ring buffer → I2S DAC → Speaker
```

### Critical Configuration Checklist

| Setting | Value | Why |
|---------|-------|-----|
| `esp_wifi_set_ps(WIFI_PS_NONE)` | **Mandatory** | WiFi modem sleep causes 100-300ms gaps |
| `tx_desc_auto_clear = true` | **Mandatory** | Outputs silence on DMA underrun (not buzzing) |
| `use_apll = true` | Recommended | Precise sample rate clock via Audio PLL |
| Audio task → Core 1 | **Mandatory** | WiFi interrupts are on Core 0 |
| Audio task priority: 17 | Recommended | Below lwIP (18), above everything else |
| Network task priority: 15 | Recommended | Below lwIP, below audio |
| DMA: 8 buffers x 512 samples | Good default | ~70-186ms of DMA-level buffer |
| Ring buffer: 128-512KB in PSRAM | **Mandatory** | 2-4 seconds of jitter absorption |
| Pre-buffer 1-2 seconds | **Mandatory** | Don't start I2S until buffer is 50%+ full |
| HTTP reads: 4096 bytes | Important | Tiny reads are as slow as big reads on ESP32 |
| HTTP keep-alive | Important | Avoids TCP/TLS handshake between chunks |

---

## 8. I2S DMA Buffering Deep Dive

### 8.1 How DMA Buffering Works

ESP32 I2S uses DMA (Direct Memory Access) to transfer audio samples between memory and I2S hardware without CPU intervention. Operates as a linked list of buffers cycling in round-robin.

**Two key parameters:**
- `dma_buf_len`: Number of samples per DMA buffer (max 1024)
- `dma_buf_count`: Number of DMA buffers (minimum 2)

**Buffer size calculation:**
```
real_dma_buf_size = dma_buf_len × num_channels × (bits_per_sample / 8)
```

Example: stereo 16-bit, `dma_buf_len=1024`: 1024 × 2 × 2 = 4096 bytes per DMA buffer.

**Maximum real DMA buffer size: 4092 bytes.** DMA buffers **must reside in internal SRAM** — cannot be in PSRAM.

**How `i2s_write()` works:** Fills one DMA buffer at a time. If all buffers are full, the call **blocks** until DMA hardware finishes transmitting one. This blocking provides natural flow control.

**Underrun behavior:**
- Without `tx_desc_auto_clear`: DMA replays last buffer → buzzing/clicking
- With `tx_desc_auto_clear = true`: DMA zeros the buffer → clean silence

### 8.2 Optimal DMA Settings

| Parameter | Recommended | Rationale |
|-----------|-------------|-----------|
| `dma_buf_len` | 512-1024 samples | Larger = fewer interrupts = less CPU overhead |
| `dma_buf_count` | 6-8 buffers | ~70-186ms of DMA-level buffering at 44.1kHz |
| `tx_desc_auto_clear` | `true` | Silence on underrun instead of noise |
| `use_apll` | `true` | Precise sample rate clocking |

**Configuration examples:**
```c
// For 16kHz mono voice streaming (low latency)
.dma_buf_count = 8,
.dma_buf_len = 256,     // 8 × 256 × 2 = 4 KB, ~128ms buffer
.sample_rate = 16000,

// For 44.1kHz stereo music streaming
.dma_buf_count = 8,
.dma_buf_len = 1024,    // 8 × 1024 × 4 = 32 KB, ~186ms buffer
.sample_rate = 44100,
```

**Constraints:**
- DMA buffers allocated from internal SRAM only (~328KB total)
- Each DMA buffer ≤ 4092 bytes
- More buffers = more headroom for variable processing times
- Larger individual buffers = fewer interrupts

### 8.3 Ring Buffer Implementation

DMA buffers cannot absorb WiFi jitter (50-500ms spikes). You need an application-level ring buffer between network reception and I2S output.

**Use ESP-IDF's `xRingbuffer` with `RINGBUF_TYPE_BYTEBUF`:**

```c
#include "freertos/ringbuf.h"

// Create 256KB byte-type ring buffer in PSRAM
StaticRingbuffer_t *buf_struct =
    (StaticRingbuffer_t *)heap_caps_malloc(sizeof(StaticRingbuffer_t), MALLOC_CAP_SPIRAM);
uint8_t *buf_storage =
    (uint8_t *)heap_caps_malloc(256 * 1024, MALLOC_CAP_SPIRAM);

RingbufHandle_t audio_ringbuf = xRingbufferCreateStatic(
    256 * 1024, RINGBUF_TYPE_BYTEBUF, buf_storage, buf_struct);

// Producer (WiFi task on Core 0):
xRingbufferSend(audio_ringbuf, wifi_data, chunk_size, pdMS_TO_TICKS(100));

// Consumer (I2S task on Core 1):
size_t received_size;
uint8_t *data = (uint8_t *)xRingbufferReceiveUpTo(
    audio_ringbuf, &received_size, pdMS_TO_TICKS(20), 1024);
if (data) {
    size_t bytes_written;
    i2s_write(I2S_NUM_0, data, received_size, &bytes_written, portMAX_DELAY);
    vRingbufferReturnItem(audio_ringbuf, data);
}
```

**Why `RINGBUF_TYPE_BYTEBUF`:**
- No per-item header overhead
- Continuous byte stream — exactly what PCM audio is
- Thread-safe between tasks on different cores

**Warning:** Standard FreeRTOS `xStreamBufferCreate()` has a known bug on ESP32 — can crash when reader and writer tasks run on different cores. Use `xRingbuffer` instead.

### 8.4 Pre-Buffering Strategy

**Do not start I2S playback until the ring buffer reaches a threshold.**

| Network Quality | Pre-buffer | Pre-buffer at 44.1kHz stereo 16-bit |
|-----------------|------------|--------------------------------------|
| Excellent LAN | 100-200ms | 17-35 KB |
| Typical WiFi | 200-500ms | 35-88 KB |
| Poor WiFi / Internet | 500-1000ms | 88-176 KB |
| Internet radio | 1-2 seconds | 176-352 KB (needs PSRAM) |

```c
#define PREBUFFER_BYTES (BYTES_PER_SECOND * 2)  // 2 seconds

bool playback_started = false;
void i2s_output_task(void *param) {
    while (1) {
        if (!playback_started) {
            UBaseType_t items;
            vRingbufferGetInfo(audio_ringbuf, NULL, NULL, NULL, NULL, &items);
            if (items >= PREBUFFER_BYTES) {
                playback_started = true;
            } else {
                vTaskDelay(pdMS_TO_TICKS(10));
                continue;
            }
        }
        // ... read from ring buffer and write to I2S ...
    }
}
```

### 8.5 Chunk Boundary Handling

**Root causes of gaps between chunks:**
1. HTTP overhead between chunks (TCP ACK, new request, TLS handshake)
2. Decode pipeline stall (decoder finishes one chunk, waits for next)
3. Task scheduling (network and audio contend for CPU)
4. GC pauses (MicroPython)

**Fixes:**
- Ensure chunks are **sample-aligned** (multiple of 4 bytes for stereo 16-bit, 2 bytes for mono 16-bit)
- Ring buffer treats data as continuous byte stream, not discrete messages
- Use persistent HTTP connections (keep-alive)
- Write silence when buffer empties (don't let DMA starve)

**Crossfading at chunk boundaries (C++):**
```c
#define CROSSFADE_SAMPLES 64  // ~4ms at 16kHz
void crossfade_boundary(int16_t *end_prev, int16_t *start_next, int n) {
    for (int i = 0; i < n; i++) {
        float fade_out = (float)(n - i) / n;
        float fade_in  = (float)i / n;
        start_next[i] = (int16_t)(end_prev[i] * fade_out + start_next[i] * fade_in);
    }
}
```

---

## 9. FreeRTOS Task Architecture for Audio

### 9.1 Core Assignment

| Core | Tasks | Rationale |
|------|-------|-----------|
| Core 0 | WiFi driver (system), TCP/IP (lwIP), Network receive task | WiFi interrupts pinned to Core 0 by default |
| Core 1 | I2S output task, Audio decode task, Arduino loop() | Time-critical audio free from WiFi interrupts |

**Never run the I2S output task on Core 0.** WiFi interrupts will cause audio glitches.

### 9.2 Task Priorities

| Task | Core | Priority | Rationale |
|------|------|----------|-----------|
| WiFi stack (system) | 0 | 18 (lwIP), 23 (WiFi) | System-managed, do not change |
| WiFi receive | 0 | 10-15 | Must not starve WiFi stack |
| Audio decode | 1 | 15-17 | Below I2S output, above normal |
| **I2S output** | **1** | **17-20** | **Highest app priority — must never be starved** |
| Arduino loop() | 1 | 1 | Default; runs when nothing else needs CPU |

**Critical rule:** Audio task priority must be **at most 17** if you need network — because lwIP runs at 18. If audio has higher priority than lwIP, the network stack starves and you get gaps from the network side.

### 9.3 Producer-Consumer Implementation

```c
// Network receive task — Core 0
xTaskCreatePinnedToCore(
    wifi_receive_task, "net_recv", 8192, NULL,
    15, &net_task_handle, 0);

// Audio output task — Core 1
xTaskCreatePinnedToCore(
    audio_output_task, "audio_out", 4096, NULL,
    17, &audio_task_handle, 1);
```

**Always include `vTaskDelay(pdMS_TO_TICKS(1))` or a blocking call** in loops to prevent watchdog timer resets.

---

## 10. WiFi Optimization for Streaming

### 10.1 Power Save Mode

**Single most impactful setting.** WiFi modem sleep drops throughput from stable to erratic bursts with 100-300ms gaps.

```c
#include "esp_wifi.h"
esp_wifi_set_ps(WIFI_PS_NONE);  // Call after WiFi connects
```

**Cannot be used when Bluetooth is also active** — hard constraint from Espressif's coexistence controller.

### 10.2 TCP Buffer Tuning

Default lwIP TCP window is only ~5744 bytes. For audio streaming, increase:

**Without PSRAM:**
```
CONFIG_LWIP_TCP_WND_DEFAULT=65535
CONFIG_LWIP_TCP_SND_BUF_DEFAULT=65535
CONFIG_LWIP_TCP_RECVMBOX_SIZE=64
```

**With PSRAM (aggressive):**
```
CONFIG_LWIP_TCP_WND_DEFAULT=524288
CONFIG_ESP_WIFI_STATIC_RX_BUFFER_NUM=16
CONFIG_ESP_WIFI_DYNAMIC_RX_BUFFER_NUM=512
CONFIG_LWIP_WIFI_ALLOCATION_FROM_SPIRAM_FIRST=y
```

### 10.3 HTTP Keep-Alive

Each new HTTP request incurs TCP handshake + possibly TLS. Use persistent connections:

```c
esp_http_client_config_t config = {
    .url = "http://server/stream",
    .keep_alive_enable = true,
    .keep_alive_idle = 5,
    .buffer_size = 4096,
};
```

**Always read in large chunks (4096 bytes).** Reading one byte from WiFi takes as much time as reading 1000 bytes.

### 10.4 Protocol Selection

| Protocol | Best For | Latency | Reliability |
|----------|----------|---------|-------------|
| TCP/HTTP | Music, TTS, buffered download | 200-500ms | Excellent |
| UDP | Voice/intercom | ~5ms | No delivery guarantee |
| WebSocket | Bidirectional control + audio | Moderate | Good |
| ESP-NOW | Low-latency local ESP32-to-ESP32 | ~5ms | 250 byte limit |

**For TTS/music: TCP/HTTP is the clear winner.**

---

## 11. Audio Codec Performance

### 11.1 Benchmarks (ESP32-S3 @ 240MHz)

| Codec | Sample Rate | Channels | CPU Usage | Memory | Feasibility |
|-------|-------------|----------|-----------|--------|-------------|
| **ADPCM** | 48 kHz | 2 | 2.43% | 0.11 KB | Excellent |
| **Opus** | 48 kHz | 2 | 5.86% | 26.6 KB | Excellent |
| **AAC-LC** | 48 kHz | 2 | 6.75% | 51.2 KB | Excellent |
| **MP3** | 44.1 kHz | 2 | 8.17% | 28 KB | Excellent |
| **FLAC** | 44.1 kHz | 2 | 8.0% | 89.4 KB | Good (needs PSRAM) |
| **WAV/PCM** | Any | Any | ~0% | N/A | Excellent (no decode) |

### 11.2 Recommendations

- **Gapless music streaming:** AAC-LC or MP3 at 128-192kbps
- **Low-latency voice/TTS:** Opus — built-in packet loss concealment
- **Raw PCM over LAN:** Works if bandwidth sufficient (~384 kbps for 24kHz mono)
- **Maximum compatibility:** MP3 at 128kbps via ESP32-audioI2S
- **Avoid:** Uncompressed WAV/PCM over WiFi unless on dedicated network

### 11.3 Achievable Sample Rates over WiFi

| Format | Bitrate | WiFi Feasibility |
|--------|---------|------------------|
| MP3 44.1kHz stereo | 128-320 kbps | Excellent |
| AAC 48kHz stereo | 128-256 kbps | Excellent |
| Opus 48kHz stereo | 64-320 kbps | Excellent |
| FLAC 44.1kHz stereo | ~800 kbps | Good with PSRAM |
| **PCM 24kHz mono** | **384 kbps** | **Marginal** |
| PCM 44.1kHz stereo | 1411 kbps | Unreliable |

Raw ESP32 WiFi throughput: ~256-296 kbps over TCP. Sufficient for compressed audio, NOT reliably for uncompressed CD quality.

---

## 12. MicroPython Audio Limitations

### 12.1 machine.I2S API

```python
from machine import I2S, Pin
audio_out = I2S(
    0,                        # I2S bus ID
    sck=Pin(34),              # Serial clock (CoreS3)
    ws=Pin(33),               # Word select
    sd=Pin(13),               # Serial data
    mode=I2S.TX,              # Transmit mode
    bits=16,                  # 16-bit samples
    format=I2S.MONO,          # MONO or STEREO
    rate=24000,               # Sample rate in Hz
    ibuf=40000                # Internal DMA buffer size
)
```

Three operating modes:
- **Blocking:** `audio_out.write(buf)` — blocks until DMA accepts all data
- **Non-blocking (IRQ):** `audio_out.irq(handler)` — callback when DMA buffer empties
- **Asyncio:** `swriter = asyncio.StreamWriter(audio_out)` — cooperative multitasking

The `ibuf` parameter replaces separate `dma_buf_count`/`dma_buf_len`. Recommended: 20,000-40,000 bytes.

### 12.2 Performance Ceiling

| Aspect | MicroPython | C/Arduino |
|--------|-------------|-----------|
| WiFi + I2S concurrency | Single-threaded (asyncio cooperative) | True dual-core preemptive |
| Core pinning | Not possible | `xTaskCreatePinnedToCore()` |
| Task priorities | Not available | Fine-grained control |
| Buffer management | Limited to `ibuf` | Full DMA and ring buffer control |
| Decode (MP3/AAC) | Too slow | Native libraries available |
| GC pauses | 1-10ms unpredictable | No garbage collection |

**Measured practical limit: ~16kHz mono for WiFi streaming.** File playback from SD works at 44.1kHz (no WiFi contention).

### 12.3 Best-Effort MicroPython Streaming (≤16kHz Mono Only)

```python
import gc
gc.threshold(4096)  # Smaller, more frequent GC

import uasyncio as asyncio
from machine import I2S, Pin

audio_out = I2S(0, sck=Pin(34), ws=Pin(33), sd=Pin(13),
                mode=I2S.TX, bits=16, format=I2S.MONO,
                rate=16000, ibuf=40000)

# Pre-allocate all buffers
buf = bytearray(4096)
buf_mv = memoryview(buf)

async def stream_audio():
    swriter = asyncio.StreamWriter(audio_out)
    sock = usocket.socket()
    sock.connect(("server", 8080))
    sock.setblocking(False)

    # Pre-fill buffer
    for _ in range(10):
        n = sock.readinto(buf)
        if n:
            swriter.out_buf = buf_mv[:n]
            await swriter.drain()

    # Main loop
    while True:
        try:
            n = sock.readinto(buf)
            if n and n > 0:
                swriter.out_buf = buf_mv[:n]
                await swriter.drain()
        except OSError:
            await asyncio.sleep_ms(1)
```

---

## 13. C/Arduino Audio Libraries (Ranked)

### 1. ESP32-audioI2S (by schreibfaul1) — Easiest Path

**2400+ stars, actively maintained.** One-line internet radio.

- `connecttohost(url)` = one function call for streaming
- 655KB circular buffer with PSRAM auto-detection
- MP3, AAC, FLAC, Opus, Vorbis, WAV decoding built-in
- Has M5Stack Core2, StickCPlus, Node examples
- Streams up to 320 kbit/s
- Requires PSRAM (~1MB total recommended)

```cpp
#include <Audio.h>
Audio audio;
void setup() {
    audio.setPinout(12, 0, 2);  // BCK, LRC, DOUT
    audio.setVolume(15);
    audio.connecttohost("http://your-server/stream.mp3");
}
void loop() { audio.loop(); }
```

### 2. arduino-audio-tools (by pschatzmann) — Most Flexible

- Modular pipeline: `URLStream → Decoder → I2SStream`
- HTTP, UDP, TCP, ESP-NOW, RTSP protocols
- Explicit M5Stack/Atom Echo support
- Configurable `URLStreamBuffered` with dedicated FreeRTOS task
- Detailed low-latency streaming wiki

### 3. Squeezelite-ESP32 — Gold Standard (Complex)

- True gapless playback, multi-room sync, AirPlay, Bluetooth
- Codecs: PCM/WAV (192kHz), ALAC/FLAC (96kHz), MP3/AAC/Opus/Vorbis (48kHz)
- Requires 4MB Flash + 4MB PSRAM minimum
- M5Stack Core2 confirmed: `model=i2s,bck=12,ws=0,do=02`
- Needs Logitech Media Server infrastructure

### 4. M5Unified Speaker Class — For Custom Pipelines

- Built into M5Stack's official C++ library
- `playRaw()`, `playWav()`, `tone()` methods
- 8 virtual channels for mixing
- Configurable DMA: `dma_buf_len`, `dma_buf_count`
- Triple buffering required for gapless streaming
- Calling thread must have FreeRTOS priority >= 1

### 5. ESP-ADF (Espressif Official) — Most Comprehensive

- Official audio framework (ESP-IDF based, not Arduino)
- Pipeline architecture with audio elements connected by ring buffers
- HTTP stream reader/writer, HLS, A2DP sources
- M5Stack has official fork
- **Known issue:** Gapless playback example has unresolved gap (issue #1041)
- Steep learning curve, requires ESP-IDF build system

### 6. ESP8266Audio — Simple but Less Optimized

- MOD, WAV, FLAC, MIDI, MP3, AAC, OGG/Opus support
- Works on both ESP8266 and ESP32
- Used in M5Unified's `MP3_with_ESP8266Audio` example
- Simpler API but less optimized for streaming

---

## 14. WiFi vs Alternatives for Audio

| Approach | Throughput | Latency | Best For |
|----------|-----------|---------|----------|
| **WiFi TCP/HTTP** | ~256-296 kbps | 200-500ms | Internet radio, TTS, music |
| **WiFi UDP** | ~256-296 kbps | ~5ms | Voice/intercom |
| **Bluetooth A2DP** | 330 kbps (SBC) | Low | Phone → speaker |
| **ESP-NOW** | 33-37 KB/s | ~5ms | ESP32-to-ESP32 (250B packets) |
| **SD card playback** | SPI-limited | None | Pre-downloaded content |
| **PSRAM playback** | Memory bandwidth | None | TTS, short audio |
| **UART serial** | Up to ~200 KB/s | Deterministic | Tethered companion |

**Critical: WiFi and Bluetooth A2DP cannot coexist reliably** on ESP32. Single radio with time-division multiplexing — each gets ~33% of radio time. A2DP has "audible discontinuities" when WiFi is active.

**ESP-NOW** measured: 33-37 KB/s. Right at ceiling for 16kHz mono. Not suitable for music.

---

## 15. Music File Conversion

### Correct ffmpeg Command

```bash
ffmpeg -i input.flac -ar 24000 -ac 1 -f s16le -acodec pcm_s16le background.pcm
```

| Flag | Purpose |
|------|---------|
| `-ar 24000` | Resample to 24kHz (**MUST** match Speaker sample rate) |
| `-ac 1` | Mono |
| `-f s16le` | Raw signed 16-bit little-endian |
| `-acodec pcm_s16le` | PCM codec |

### Symptoms of Wrong Sample Rate

| Symptom | Likely Cause |
|---------|-------------|
| Audio sounds **slowed down** | Source was 44.1/48kHz, playing at 24kHz |
| Audio sounds **weak/thin** | Wrong bit depth or sample rate mismatch |
| File size too large | Not resampled (3-min song should be ~8.6MB at 24kHz) |

### Size Estimation

```
File size = 24000 × 2 × 1 × seconds = 48,000 bytes/second ≈ 2.88 MB/minute
```

### Verify

```bash
ls -la background.pcm          # 3-min song ≈ 8.6MB
ffprobe -f s16le -ar 24000 -ac 1 background.pcm
```

---

## 16. Cue Project: Current Implementation (PSRAM Download)

### Architecture (Working Solution)

```
Server (Node.js Express)                M5Stack (MicroPython)
├── GET /api/tile/music/file            ← AudioEngine.download_music()
│   ?track=background                       raw socket download at boot
│   Returns: entire PCM file                into PSRAM (6.6MB)
│   Content-Length header used
│   createReadStream().pipe(res)
│
│   (Legacy endpoints still exist:)
├── GET /api/tile/music/info            ← transport.get_music_info()
├── GET /api/tile/music/chunk           ← transport.fetch_music_chunk()
```

### Key Design: Download at Boot, Play from Memory

1. **Boot:** Connect WiFi → download entire music file into PSRAM via raw sockets
2. **Routine:** Play from PSRAM in 1MB chunks via `Speaker.playRaw(memoryview(...))`
3. **Voice:** Pause music (save position) → play voice at higher volume → resume music

### Server Endpoints (routes.ts)

**GET /api/tile/music/file?track=background** (Primary — used by raw socket downloader)
- Returns: entire PCM file as `application/octet-stream`
- Headers: `Content-Length` (critical for pre-allocation), `X-Track`
- Uses `createReadStream().pipe(res)` for efficient streaming

**GET /api/tile/music/info?track=background** (Metadata)
- Returns: `{ track, fileSize, format, sampleRate, bitDepth, channels, durationSeconds }`

**GET /api/tile/music/chunk** (Legacy — no longer used by audio engine)

### Music File Location
- Server: `server/music/background.pcm`
- Format: raw PCM, **16kHz**, 16-bit, mono (compressed for PSRAM budget)
- Convert: `ffmpeg -i song.mp3 -ar 16000 -ac 1 -f s16le background.pcm`

### Code Files & Roles

| File | Role |
|------|------|
| `firmware/m5stack/audio_engine.py` | PSRAM download, chunked playback, voice interruption state machine |
| `firmware/m5stack/tile_audio.py` | Basic speaker utilities (blocking, async, threaded playback) |
| `firmware/m5stack/transport.py` | Network abstraction (demo/serial/wifi) |
| `firmware/m5stack/main.py` | Entry point, UI, routine execution loop |
| `server/routes.ts` | HTTP API endpoints |

### Audio Engine State Machine

```
                    play_music()
    IDLE ─────────────────────────► PLAYING_MUSIC
     ▲                                  │  │
     │ stop_music()                     │  │ _pause_for_voice()
     │                     pause_music()│  │
     │                                  ▼  ▼
     │                          PAUSED_USER  PAUSED_VOICE
     │                              │            │
     │                resume_music()│  resume_music()
     │                              │            │
     └──────────────────────────────┘            │
                                                 ▼
                                          (voice plays at VOLUME_VOICE=190)
                                                 │
                                          auto-resume → PLAYING_MUSIC (VOLUME_MUSIC=110)
```

### Voice Interruption Flow
1. Music playing at `VOLUME_MUSIC` (110)
2. `_pause_for_voice()` → capture position via elapsed time, stop thread + Speaker
3. State → `PAUSED_VOICE`
4. Set `Speaker.setVolume(VOLUME_VOICE)` (190)
5. `play_voice()` or `play_voice_threaded()` plays voice clip at 24kHz
6. When voice finishes → restore `Speaker.setVolume(VOLUME_MUSIC)` (110)
7. Auto-calls `resume_music()` → music thread restarts from saved position at 16kHz

### Working PSRAM Playback Implementation

```python
PLAYBACK_CHUNK = 1048576  # 1MB = ~33s at 16kHz mono

def _music_loop_thread(self):
    data_len = len(self.music_data)
    while self.music_thread_running:
        if self.music_position >= data_len:
            self.music_position = 0  # Loop

        end_pos = min(self.music_position + PLAYBACK_CHUNK, data_len)
        chunk = memoryview(self.music_data)[self.music_position:end_pos]

        self._play_start_time = time.time()
        self._play_start_offset = self.music_position

        Speaker.playRaw(chunk, MUSIC_SAMPLE_RATE, False, 1, 0, True)

        duration = len(chunk) / (MUSIC_SAMPLE_RATE * 2)
        end_time = time.time() + duration
        while time.time() < end_time:
            if not self.music_thread_running:
                return
            time.sleep(0.1)

        while Speaker.isPlaying():
            if not self.music_thread_running:
                return
            time.sleep(0.01)  # Tight poll for minimal gap

        self.music_position = end_pos
```

### Approaches Tried (Chronological)

| Strategy | Result |
|----------|--------|
| SD card playback | **Failed** — SPI bus conflict with LCD (OSError 16) |
| WiFi chunk streaming (triple buffer) | Small gaps from network latency (~100ms/request) |
| WiFi chunk streaming (single buffer) | Large gaps at every fetch |
| Download entire file + single playRaw() | Song truncated — playRaw has buffer size limit |
| Download entire file + 64KB chunks | Perceptible choppiness every 2 seconds |
| **Download entire file + 1MB chunks** | **Working — minimal transitions, imperceptible gaps** |

### Download Optimization History

| Method | Speed | Why |
|--------|-------|-----|
| `requests` library (100 HTTP calls) | Slow | TCP overhead per request |
| Raw socket + `recv(8192)` | Moderate | Creates new bytes objects, copies |
| **Raw socket + `readinto(memoryview)` 32KB** | **Fast** | **Zero-copy into PSRAM** |

---

## 17. Cue Project: Known Bugs & Next Steps

### Bug 1: First Chunk Repeats
**Symptom:** First ~1.4s of music plays twice before continuing.
**Likely Cause:** `buffer_index = 0` causes the first buffer to be re-fetched and re-queued in the first loop iteration.
**Status:** Unresolved.

### Bug 2: Small Gaps Between Chunks
**Symptom:** Brief audible pauses (~20-50ms) at chunk boundaries.
**Causes:** Speaker queue transition time, WiFi fetch latency jitter, MicroPython GC pauses, imprecise `time.sleep(chunk_duration * 0.9)`.
**Status:** Partially mitigated by triple buffering. Likely a fundamental MicroPython limitation.

### Bug 3: Position Tracking Inaccuracy on Resume
**Symptom:** Playback position may not be perfectly accurate after pause/resume.
**Cause:** Speaker's internal queue has buffered audio beyond tracked `music_position`.
**Status:** Minor, acceptable for MVP.

### Recommended Next Steps (Priority Order)

1. **Try Download-Then-Play (Quick Win):** Download entire `background.pcm` to PSRAM before routine starts. Eliminates all streaming gaps. Limit: ~2.8 min at 24kHz or ~4.3 min at 16kHz.

2. **Fix First-Chunk Repeat Bug:** Check `_music_stream_thread()` — likely need to start `buffer_index` past the pre-queued buffers to avoid double-queuing buffer[0].

3. **Reduce Sample Rate for Music (If Needed):** Background music doesn't need 24kHz. Use 16kHz for longer playback (4.3 min). Voice clips stay at 24kHz.
   ```bash
   ffmpeg -i song.mp3 -ar 16000 -ac 1 -f s16le background_16k.pcm
   ```

4. **Consider C++/Arduino (For Production):** ESP32-audioI2S provides true gapless in one function call. Significant migration but solves the problem completely.

---

## 18. Complete Working Examples

### 18.1 MicroPython: Download-Then-Play

```python
import requests, gc
from M5 import Speaker

gc.collect()
r = requests.get("http://server/api/tile/music/chunk?offset=0&length=8640000")
audio_data = r.content
r.close()
gc.collect()

Speaker.begin()
Speaker.setVolume(150)
Speaker.playRaw(audio_data, 24000, False, 1, 0, True)
```

### 18.2 Arduino: One-Line Internet Radio (ESP32-audioI2S)

```cpp
#include <Arduino.h>
#include <WiFi.h>
#include <Audio.h>
#include "esp_wifi.h"

Audio audio;

void setup() {
    WiFi.begin("ssid", "pass");
    while (!WiFi.isConnected()) delay(500);
    esp_wifi_set_ps(WIFI_PS_NONE);

    audio.setPinout(34, 33, 13);  // CoreS3: BCK, LRC, DOUT
    audio.setVolume(15);
    audio.connecttohost("http://server/stream.mp3");
}
void loop() { audio.loop(); }
```

### 18.3 Arduino: Full Streaming Pipeline with Ring Buffer

```c
#include <Arduino.h>
#include <WiFi.h>
#include <driver/i2s.h>
#include "freertos/ringbuf.h"
#include "esp_wifi.h"

#define SAMPLE_RATE       24000
#define BYTES_PER_SECOND  (SAMPLE_RATE * 2)
#define RING_BUF_SIZE     (128 * 1024)          // 128KB = ~2.7s
#define PREBUF_BYTES      (BYTES_PER_SECOND * 2) // 2s pre-buffer
#define HTTP_READ_SIZE    4096

RingbufHandle_t audio_ringbuf;
volatile bool playback_started = false;
volatile bool stream_active = false;
TaskHandle_t playback_task_handle;

void i2s_init() {
    i2s_config_t cfg = {
        .mode = (i2s_mode_t)(I2S_MODE_MASTER | I2S_MODE_TX),
        .sample_rate = SAMPLE_RATE,
        .bits_per_sample = I2S_BITS_PER_SAMPLE_16BIT,
        .channel_format = I2S_CHANNEL_FMT_ONLY_LEFT,
        .communication_format = I2S_COMM_FORMAT_STAND_I2S,
        .intr_alloc_flags = ESP_INTR_FLAG_LEVEL1,
        .dma_buf_count = 8,
        .dma_buf_len = 512,
        .use_apll = false,
        .tx_desc_auto_clear = true,  // CRITICAL: silence on underrun
    };
    i2s_pin_config_t pins = {
        .bck_io_num = 34, .ws_io_num = 33,
        .data_out_num = 13, .data_in_num = I2S_PIN_NO_CHANGE,
    };
    i2s_driver_install(I2S_NUM_0, &cfg, 0, NULL);
    i2s_set_pin(I2S_NUM_0, &pins);
    i2s_zero_dma_buffer(I2S_NUM_0);
}

void wifi_receive_task(void *param) {
    uint8_t buf[HTTP_READ_SIZE];
    WiFiClient client;
    // ... connect and send HTTP GET ...
    while (stream_active) {
        int n = client.read(buf, sizeof(buf));
        if (n > 0) {
            n &= ~1;  // Align to 16-bit
            xRingbufferSend(audio_ringbuf, buf, n, pdMS_TO_TICKS(200));
            if (!playback_started) {
                UBaseType_t items;
                vRingbufferGetInfo(audio_ringbuf, NULL, NULL, NULL, NULL, &items);
                if (items >= PREBUF_BYTES) {
                    playback_started = true;
                    xTaskNotifyGive(playback_task_handle);
                }
            }
        } else { taskYIELD(); }
    }
    vTaskDelete(NULL);
}

void audio_playback_task(void *param) {
    static uint8_t silence[512] = {0};
    ulTaskNotifyTake(pdTRUE, portMAX_DELAY);  // Wait for pre-buffer

    while (stream_active) {
        size_t sz = 0;
        uint8_t *data = (uint8_t *)xRingbufferReceiveUpTo(
            audio_ringbuf, &sz, pdMS_TO_TICKS(5), 1024);
        if (data && sz > 0) {
            size_t written;
            i2s_write(I2S_NUM_0, data, sz, &written, portMAX_DELAY);
            vRingbufferReturnItem(audio_ringbuf, data);
        } else {
            size_t written;
            i2s_write(I2S_NUM_0, silence, sizeof(silence), &written, pdMS_TO_TICKS(50));
        }
        vTaskDelay(pdMS_TO_TICKS(1));
    }
    i2s_zero_dma_buffer(I2S_NUM_0);
    vTaskDelete(NULL);
}

void setup() {
    audio_ringbuf = xRingbufferCreate(RING_BUF_SIZE, RINGBUF_TYPE_BYTEBUF);
    WiFi.begin("ssid", "pass");
    while (!WiFi.isConnected()) delay(500);
    esp_wifi_set_ps(WIFI_PS_NONE);
    i2s_init();
    stream_active = true;
    xTaskCreatePinnedToCore(audio_playback_task, "audio", 4096, NULL, 17, &playback_task_handle, 1);
    xTaskCreatePinnedToCore(wifi_receive_task, "net", 8192, NULL, 15, NULL, 0);
}

void loop() {
    UBaseType_t items;
    vRingbufferGetInfo(audio_ringbuf, NULL, NULL, NULL, NULL, &items);
    Serial.printf("Buffer: %d/%d (%.0f%%)\n", items, RING_BUF_SIZE,
                  100.0 * items / RING_BUF_SIZE);
    delay(2000);
}
```

### 18.4 M5Unified Triple Buffer (C++)

```cpp
#include <M5Unified.h>

static constexpr size_t BUF_SAMPLES = 1536;
int16_t tri_buffer[3][BUF_SAMPLES];
int current_buf = 0;
int buf_pos = 0;

void flush_buffer() {
    if (buf_pos > 0) {
        M5.Speaker.playRaw(tri_buffer[current_buf], buf_pos, 44100,
                           false, 1, 0);
        current_buf = (current_buf + 1) % 3;
        buf_pos = 0;
    }
}

void add_sample(int16_t sample) {
    tri_buffer[current_buf][buf_pos++] = sample;
    if (buf_pos >= BUF_SAMPLES) flush_buffer();
}
```

---

## 19. Troubleshooting Quick Reference

### SD Card Errors

| Error | Cause | Fix |
|-------|-------|-----|
| `OSError: (-259, 'ESP_ERR_INVALID_STATE')` | SPI bus already initialized | Hard reset, init SD before display |
| `OSError: [Errno 19] ENODEV` | Card not detected | Check insertion + correct pins |
| `OSError: [Errno 5] EIO` | SPI failure | Lower freq to 1MHz, reformat MBR FAT32 |
| `OSError: 16` (EBUSY) | Already mounted or SPI conflict | `os.umount('/sd')`, or reset |
| `timeout waiting for v2 card` | Card not responding | Wrong pins, different card brand |

### Audio Errors

| Symptom | Cause | Fix |
|---------|-------|-----|
| Buzzing/repeating noise in gaps | DMA replays last buffer | C++: `tx_desc_auto_clear = true` |
| Periodic clicks every ~100ms | WiFi modem sleep | C++: `esp_wifi_set_ps(WIFI_PS_NONE)` |
| Gaps between `playRaw()` calls | M5Unified double-buffer only | Triple buffering (3 rotating buffers) |
| Audio slowed down/weak | Source not resampled to 24kHz | `ffmpeg -ar 24000 -ac 1 -f s16le` |
| First chunk repeats | Buffer[0] double-queued | Fix buffer_index initialization |
| Choppy with 8KB chunks | Only 170ms per chunk | Increase to 64KB (1.4s) |
| Stuttering at high sample rates | Audio + WiFi on same core | C++: pin audio to Core 1 |
| Choppy after 10+ minutes | Memory fragmentation / GC | `gc.collect()` in loop, or C++ |
| "Metallic and choppy" sound | MicroPython throughput limit | Switch to C++ or lower to 8kHz |
| Static/noise during WiFi TX | Power rail fluctuations | Download-then-play |
| Audio cuts during voice | Music not paused before voice | Use AudioEngine.play_voice() |
| SD card OSError 16 | LCD holds SPI bus | Abandon SD, use WiFi streaming |

### Common Mistakes That Cause Audio Gaps

1. **WiFi power save left enabled** — default `WIFI_PS_MIN_MODEM` causes 100ms gaps
2. **No `tx_desc_auto_clear`** — DMA replays last buffer on underrun (buzzing)
3. **Audio task on Core 0** — WiFi interrupts preempt audio
4. **Audio task priority > 18** — starves lwIP, causes network gaps
5. **Insufficient buffer depth** — need 2-4 seconds for WiFi jitter
6. **Reading WiFi byte-by-byte** — as slow as reading 1000 bytes
7. **No pre-buffering** — starting playback immediately = instant underrun
8. **GC pauses (MicroPython)** — 1-10ms freezes kill real-time audio
9. **Blocking I/O on audio thread** — never do HTTP, file I/O, or logging on audio task
10. **Chunks not sample-aligned** — must be multiple of `channels × (bits/8)` bytes
11. **Using `xStreamBuffer` cross-core** — known ESP32 crash bug; use `xRingbuffer`
12. **Not using `use_apll = true`** — less precise sample rate clock

---

## 20. Key Principles Learned

1. **MicroPython + WiFi + Audio = Fundamental Conflict.** You can't reliably do both simultaneously. Separate them temporally (download then play) or spatially (different CPU cores in C++).

2. **`playRaw()` stores pointers, not copies.** This is the #1 gotcha. Always use triple buffering when cycling. (M5Unified Issue #29)

3. **SD card is dead on CoreS3 SE with UIFlow.** SPI bus conflict with LCD. Don't try again unless switching to Arduino/C++.

4. **Always resample to target rate.** Playing 44.1kHz audio at 24kHz rate = slow-motion audio. Use ffmpeg `-ar 24000`.

5. **Pre-fetch everything before timers start.** Network latency during timer = bad UX. Cache all TTS clips first.

6. **GC pauses cause audible artifacts.** Call `gc.collect()` at predictable points (between chunks), not during playback. Or use `gc.threshold(4096)` for smaller, more frequent collections.

7. **`tx_desc_auto_clear = true` is mandatory for C++.** Without it, DMA replays the last buffer on underrun → buzzing instead of silence.

8. **WiFi power save MUST be disabled for streaming.** `esp_wifi_set_ps(WIFI_PS_NONE)` after connection. Single most impactful C++ setting.

9. **Never run I2S on Core 0.** WiFi interrupts are pinned there. Audio must be on Core 1 with priority 17 (below lwIP at 18).

10. **PSRAM is the key resource for download-then-play.** 8MB PSRAM = ~170s at 24kHz/16-bit/mono. Plan around this limit.

11. **ESP32-audioI2S solves everything in one library call** if you can switch to Arduino/C++. `connecttohost(url)` with 655KB auto-managed buffer.

12. **Use `xRingbuffer`, not `xStreamBuffer`** for cross-core audio in C++. Known ESP32 crash bug with stream buffers.

13. **The 0.9 multiplier timing hack is unreliable.** `time.sleep(chunk_duration * 0.9)` tries to wake up before the current chunk finishes, but sleep timing in MicroPython is imprecise. This is best-effort.

---

## Sources & References

- M5Unified GitHub Issue #29: playRaw pointer behavior, triple buffering
- ESP32 Bug #12955: I2S streaming clicks at >= 22050 Hz
- ESP32 Discussion #13561: ESP32-to-ESP32 audio quality issues
- Espressif ESP-ADF documentation and codec benchmarks
- schreibfaul1/ESP32-audioI2S: WiFi audio streaming library
- pschatzmann/arduino-audio-tools: Modular audio pipeline
- sle118/squeezelite-esp32: Gold standard WiFi audio
- micropython-lib sdcard.py driver
- xiaozhi-esp32: AI assistant audio implementation
- M5Stack official documentation and UIFlow 2.0 guides
