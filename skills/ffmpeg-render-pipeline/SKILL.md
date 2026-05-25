---
name: ffmpeg-render-pipeline
description: "Use when rendering video or audio with ffmpeg — parallel rendering, GPU encoding, audio mixing, checkpoint systems, live dashboards, minterpolate optical flow, color grading, and YouTube-optimized output. Trigger on any video/audio render task."
license: Complete terms in LICENSE.txt
---

# ffmpeg Render Pipeline — Complete Reference

You are an expert video/audio render engineer. This skill covers the **ffmpeg-render-pro** toolkit — a parallel rendering system optimized for YouTube Shorts and long-form videos.

**Toolkit location:** The user may have `ffmpeg-render-pro` installed locally or via npm. Check with `node -e "require('ffmpeg-render-pro')"` or look for it on the Desktop.

## Prerequisites

Before any render task, verify:
1. **Node.js >= 18** — `node --version`
2. **ffmpeg on PATH** — `ffmpeg -version`
3. If ffmpeg is missing, tell the user: "Install ffmpeg from https://ffmpeg.org/download.html and ensure it's on your PATH."

## Quick Start (for any render task)

```bash
# Check system capabilities
node bin/ffmpeg-render-pro.js info

# Run a benchmark to test the setup
node examples/render-test.js

# Render a YouTube Short (vertical, 60s)
node examples/render-test.js --width=1080 --height=1920 --fps=30 --duration=60

# Force CPU or GPU encoding
node bin/ffmpeg-render-pro.js detect-gpu --cpu
node bin/ffmpeg-render-pro.js detect-gpu --gpu
```

---

## Core Rules (ALWAYS follow)

1. **Pre-scale BEFORE heavy processing** — Never run expensive filters (minterpolate, color grading) on source resolution. Downscale to target resolution FIRST.
2. **Parallel rendering when possible** — 8-worker parallel pipeline with segment concat for procedural video. Single process for minterpolate (segment overhead dominates).
3. **GPU encoding when available** — Use `detectGPU()` to auto-detect. Use `--cpu` flag to force software encoding if GPU causes issues. Use `--gpu` flag to require hardware encoding.
4. **Live render dashboard REQUIRED** — The dashboard auto-opens in the browser before rendering starts. Every render gets a live progress view.
5. **One render at a time** — Sequential is faster than competing for cores.
6. **`-movflags +faststart` on EVERYTHING** — Required for YouTube uploads and streaming.

---

## Encoder Selection

The toolkit auto-detects the best encoder for the user's system:

| Platform | GPU Encoders Tested (in priority order) |
|----------|----------------------------------------|
| Windows  | NVENC, AMF, Quick Sync, then CPU fallback |
| macOS    | VideoToolbox, Quick Sync, then CPU fallback |
| Linux    | NVENC, VA-API, Quick Sync, then CPU fallback |

Each encoder is validated with a 1-frame test encode — not just checked for existence. Results are cached for 7 days.

### Force Modes
- `--cpu` or `forceEncoder: 'cpu'` — Skip all GPU detection, use libx264. Use this if GPU encoding produces artifacts or errors.
- `--gpu` or `forceEncoder: 'gpu'` — Require a hardware encoder. Fails with a clear error if none found. Use this when you know the user has a GPU and want maximum speed.

### Encoding Presets

| Scenario | Encoder | Settings |
|:---------|:--------|:---------|
| Parallel segments | libx264 | `-preset fast -crf 20` |
| Final grade pass | libx264 | `-preset medium -crf 18` |
| GPU single-pass | h264_nvenc | `-preset p4 -cq 20` |
| Shorts (GPU) | h264_nvenc | `-cq 18` |

### Worker Count (auto-detected)

| Resolution | Workers | Notes |
|:-----------|:--------|:------|
| 480p | 8 | ~200MB RAM per worker |
| 720p | 8 | ~400MB RAM per worker |
| 1080p | 8 | ~800MB RAM per worker |
| 4K | 4 | ~2.5GB RAM per worker |

---

## How to Use the API

```js
const {
  renderParallel,    // Core parallel rendering engine
  createEncoder,     // Raw frame pipe to ffmpeg
  detectGPU,         // Cross-platform GPU detection
  checkFFmpeg,       // Verify ffmpeg is installed
  validateResolution, // Sanity check dimensions
  getConfig,         // Auto-tune workers + codec selection
  concatSegments,    // Stream-copy segment joining (instant)
  colorGrade,        // Apply color grades
  COLOR_PRESETS,     // Built-in presets: noir, warm, cool, cinematic, vintage
  mergeAudio,        // Combine video + audio (no video re-encode)
  startDashboard,    // Live progress dashboard
  saveCheckpoint,    // Checkpoint state serialization
  loadCheckpoint,    // Checkpoint restoration
  restoreCheckpoint, // Restore systems from checkpoint
} = require('ffmpeg-render-pro');
```

### renderParallel(options)

```js
await renderParallel({
  workerScript: './my-worker.js',  // Your frame generator (required)
  outputPath: './output.mp4',      // Final output path (required)
  width: 1920,          // Frame width (max 7680)
  height: 1080,         // Frame height (max 4320)
  fps: 60,              // Framerate (1-240)
  duration: 60,         // Seconds
  seed: 42,             // RNG seed for deterministic output
  title: 'My Render',   // Dashboard title
  dashboard: true,       // Enable live dashboard
  autoOpen: true,        // Auto-open browser
  workerCount: 8,       // Override auto-detected count
  workerData: {},        // Extra data for workers
});
```

### Writing a Worker Script

Workers receive `workerData` from `worker_threads` and must:
1. Render frames from `startFrame` to `endFrame`
2. Pipe raw BGRA frames to an ffmpeg encoder
3. Report progress via `parentPort.postMessage()`
4. Signal completion with `{ type: 'done', workerId }`

See `examples/basic-worker.js` for a complete, working template.

---

## Color Grading (no external editor)

### Built-in Presets
```js
await colorGrade({ inputPath: 'raw.mp4', outputPath: 'graded.mp4', preset: 'noir' });
// Available: noir, warm, cool, cinematic, vintage
```

### Custom Filter
```js
await colorGrade({
  inputPath: 'raw.mp4',
  outputPath: 'graded.mp4',
  filter: 'eq=brightness=-0.015:contrast=1.07:saturation=0.92',
});
```

---

## Audio Pipeline

### Merge Audio (no video re-encode)
```js
await mergeAudio({
  videoPath: 'graded.mp4',
  audioPath: 'audio.mp3',
  outputPath: 'final.mp4',
  bitrate: 320,       // kbps
  loop: true,          // Loop if audio is shorter
  normalize: false,    // Apply loudnorm
});
```

### 3-Layer Audio Architecture
1. **Main Layer (100% volume)** — Close, textured, rhythmic. Long recordings (20+ min).
2. **Background Layer (45% volume)** — Diffuse atmosphere. Short loops work.
3. **Accents (12-20% volume)** — Sparse one-shots. Fade in/out. Never in first 3 min or last 2 min.

### Critical Audio Rules
- `amix normalize=0` — Prevents auto-level crushing
- `alimiter=limit=0.95` — Prevent clipping
- `loudnorm=I=-22:TP=-2:LRA=7` for YouTube normalization
- 320kbps stereo, 44100 Hz output

---

## Checkpoint System

For renders longer than ~10 minutes, use checkpoints to avoid redundant fast-forwarding:

```js
// Generate checkpoints (update-only pass, no rendering)
generateCheckpoints({
  systems: { camera, particles, weather },  // Objects with getState()/setState()/update()
  totalFrames: 432000,
  fps: 60,
  checkpointDir: './.checkpoints',
  interval: 60000,  // Every 60k frames (~16.7 min at 60fps)
});

// In worker: load nearest checkpoint
const checkpoint = loadCheckpoint('./.checkpoints', startFrame);
if (checkpoint) {
  const resumeFrame = restoreCheckpoint(checkpoint, systems);
  // Fast-forward only from resumeFrame to startFrame (instead of from 0)
}
```

---

## Minterpolate (Optical Flow)

For timelapse/slow-motion:
```bash
ffmpeg -y -i input.mp4 \
  -vf "scale=1080:1920,minterpolate=fps=30:mi_mode=mci:mc_mode=aobmc:me_mode=bidir:vsbmc=1" \
  -c:v h264_nvenc -cq 18 -movflags +faststart output.mp4
```
**Always** pre-scale to target resolution first, then minterpolate.

---

## YouTube Shorts Optimization

For Shorts (vertical, 30-60s):
- Resolution: **1080x1920** (9:16 portrait)
- FPS: **30** (YouTube Shorts standard)
- Duration: **30-60 seconds**
- Audio: **loudnorm -14 LUFS** for Shorts
- Encoding: **GPU (cq 18)** for best quality, or **CPU (crf 18)** as fallback
- Always: **`-movflags +faststart`**

```bash
node examples/render-test.js --width=1080 --height=1920 --fps=30 --duration=60
```

---

## Safety & Cross-Platform Notes

- **No external dependencies** — Zero npm packages needed. Only Node.js + ffmpeg.
- **No network calls** — Dashboard is localhost-only. No telemetry, no phone-home.
- **No CDN loads** — Dashboard uses system fonts, no external resources.
- **Path handling** — All paths use `path.join()` for cross-platform safety.
- **Graceful shutdown** — SIGINT/SIGTERM handlers clean up temp files and kill workers.
- **Input validation** — Resolution capped at 8K, fps 1-240, NaN-safe flag parsing.
- **Works offline** — Everything runs locally.
