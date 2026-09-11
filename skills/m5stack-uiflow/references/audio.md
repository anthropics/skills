# Audio Playback Reference

## Table of Contents
- Two Audio Formats
- Speaker.playRaw() Parameters
- Buffer Size Limit
- Background Music (PSRAM Download)
- Fast Download with Raw Sockets
- Chunked Playback from PSRAM
- Volume Switching for Voice Interruptions
- PSRAM Budget
- Pause/Resume with Position Tracking
- What Failed (Don't Repeat)
- Voice Playback Modes
- Audio Prefetching
- Audio Concatenation
- LCD Display Quirks

## Two Audio Formats

```python
from M5 import Speaker

# Voice (OpenAI TTS): PCM 24kHz, 16-bit, Mono
VOICE_SAMPLE_RATE = 24000

# Music (background): PCM 16kHz, 16-bit, Mono (compressed to fit PSRAM)
MUSIC_SAMPLE_RATE = 16000

# Separate volumes so voice cuts through music
VOLUME_MUSIC = 110  # Softer background
VOLUME_VOICE = 190  # Louder announcements

Speaker.begin()
Speaker.setVolume(VOLUME_MUSIC)
```

Convert music with ffmpeg:
```bash
ffmpeg -i song.mp3 -ar 16000 -ac 1 -f s16le background.pcm
```

## Speaker.playRaw() Parameters

```python
Speaker.playRaw(
    data,           # Raw PCM bytes (or memoryview)
    sample_rate,    # 24000 for voice, 16000 for music
    stereo,         # False for mono
    repeat,         # 1 = play once
    channel,        # 0 = default channel
    stop_current    # True = interrupt current, False = queue
)
```

## Buffer Size Limit

`Speaker.playRaw()` cannot play a 6.6MB buffer in one call — it silently truncates.
**Feed in 1MB chunks (~33s at 16kHz).** Gap between chunks is just Python overhead (~1-2ms).

## Background Music: Download Entire File to PSRAM at Boot

**This is the working approach.** Download once at boot, play from memory. No streaming gaps.

```python
# At boot (after WiFi connects, before polling loop):
audio_engine.set_transport(transport)
audio_engine.download_music("background", loop=True, on_progress=show_progress)

# During routine:
if audio_engine.music_data is not None:
    audio_engine.play_music()  # Plays from PSRAM in 1MB chunks
```

## Fast Download with Raw Sockets + Zero-Copy

The `requests` library is slow for large files. Use raw sockets with `readinto(memoryview(...))`:

```python
import socket

# Pre-allocate buffer in PSRAM
music_data = bytearray(content_length)
mv = memoryview(music_data)

# HTTP/1.0 so server closes connection when done
s = socket.socket()
s.connect(addr)
s.send(b"GET /api/tile/music/file HTTP/1.0\r\nHost: ...\r\n\r\n")

# Zero-copy reads directly into PSRAM buffer
while offset < content_length:
    n = s.readinto(mv[offset:offset + 32768])  # 32KB reads
    if not n:
        break
    offset += n
```

`readinto(memoryview(...))` is MUCH faster than `recv()` + copy. `recv()` creates new bytes objects on every call. `readinto` writes directly into the pre-allocated buffer with zero allocations.

## Chunked Playback from PSRAM

```python
PLAYBACK_CHUNK = 1048576  # 1MB = ~33s at 16kHz

def _music_loop_thread(self):
    data_len = len(self.music_data)

    while self.music_thread_running:
        if self.music_position >= data_len:
            self.music_position = 0  # Loop

        end_pos = min(self.music_position + PLAYBACK_CHUNK, data_len)
        chunk = memoryview(self.music_data)[self.music_position:end_pos]

        Speaker.playRaw(chunk, MUSIC_SAMPLE_RATE, False, 1, 0, True)

        duration = len(chunk) / (MUSIC_SAMPLE_RATE * 2)
        end_time = time.time() + duration
        while time.time() < end_time:
            if not self.music_thread_running:
                return
            time.sleep(0.1)

        # Tight poll for minimal gap between chunks
        while Speaker.isPlaying():
            if not self.music_thread_running:
                return
            time.sleep(0.01)

        self.music_position = end_pos
```

## Volume Switching for Voice Interruptions

```python
# Before voice playback:
Speaker.setVolume(VOLUME_VOICE)  # 190
Speaker.playRaw(voice_data, VOICE_SAMPLE_RATE, ...)

# After voice finishes (in finally block):
Speaker.setVolume(VOLUME_MUSIC)  # 110
# Then resume music from saved position
```

## PSRAM Budget for Music

| Sample Rate | Duration in ~6MB |
|-------------|-----------------|
| 16kHz (current) | ~3.4 min |
| 12kHz | ~4.5 min |
| 8kHz | ~6.8 min |

Total PSRAM: 8MB. After MicroPython overhead (~2MB) and voice cache (~1MB), ~5-6MB available.

## Pause/Resume with Position Tracking

```python
def _update_position(self):
    elapsed = time.time() - self._play_start_time
    bytes_played = int(elapsed * MUSIC_SAMPLE_RATE * 2)
    pos = self._play_start_offset + bytes_played
    pos = pos & ~1  # Align to 2-byte boundary (16-bit samples)
    self.music_position = pos

def pause_music(self):
    self._update_position()       # Capture position first
    self.music_thread_running = False
    Speaker.stop()                # Stop immediately (don't wait)
    time.sleep(0.3)               # Let thread exit
```

## What Failed for Music (Don't Repeat)

1. **SD card** -- SPI bus conflict with LCD in MicroPython (OSError 16)
2. **WiFi chunk streaming (triple buffer)** -- Small gaps from network latency (~100ms/request)
3. **Full file in single playRaw()** -- Speaker has buffer size limit; 6.6MB truncates
4. **64KB playback chunks** -- Perceptible choppiness every 2 seconds
5. **`recv()` for download** -- Creates new bytes per call, slow. Use `readinto(memoryview)`

## Voice Playback Modes

```python
# 1. BLOCKING - waits for completion
Speaker.playRaw(audio_data, 24000, False, 1, 0, True)
duration = len(audio_data) / (24000 * 2)
time.sleep(duration + 0.1)

# 2. THREADED - background thread with callback
import _thread
def _play_thread():
    Speaker.playRaw(audio_data, 24000, False, 1, 0, True)
    while Speaker.isPlaying():
        time.sleep(0.1)
_thread.start_new_thread(_play_thread, ())
```

## Audio Prefetching

**Don't fetch audio on-demand during a timer!** Pre-fetch everything at routine start:

```python
audio_cache = {
    "intro": None,        # "Let's begin your morning."
    "first_step": None,   # "First step:"
    "next_step": None,    # "Next step:"
    "you_have": None,     # "You have"
    "30_seconds": None,   # "30 seconds remaining."
    "60_seconds": None,   # "1 minute remaining."
    "completion": None,   # "Congratulations!..."
}

def prefetch_routine_audio(routine):
    """Call BEFORE timer starts"""
    for clip_id in audio_cache.keys():
        audio_cache[clip_id] = fetch_audio_clip(clip_id)

    for i, step in enumerate(routine["steps"]):
        audio_cache[f"step_{i}"] = fetch_tts_audio(step["title"])
```

## Audio Concatenation

```python
def concat_audio(*audio_clips):
    """Combine clips: "Next step:" + title + "You have" + duration"""
    result = b""
    for clip in audio_clips:
        if clip:
            result += clip
    return result

combined = concat_audio(
    audio_cache["next_step"],
    audio_cache["step_2"],
    audio_cache["you_have"],
    audio_cache["duration_5min"]
)
play_audio_threaded(combined)
```

## LCD Display Quirks

### Text Background Highlight Bug

Always pass BOTH foreground AND background colors:

```python
# WRONG - leaves black highlight
Lcd.setTextColor(TEXT_COLOR)

# CORRECT - transparent background
Lcd.setTextColor(TEXT_COLOR, BG_COLOR)
```

### Clear Before Redraw

Always clear the area before redrawing text to avoid artifacts:

```python
Lcd.fillRect(x, y, width, height, BG_COLOR)
Lcd.drawString("New text", x, y)
```
