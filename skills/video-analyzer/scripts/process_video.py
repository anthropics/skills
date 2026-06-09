#!/usr/bin/env python3
"""
process_video.py — Video pre-processing for the video-analyzer skill.

Usage:
    python3 process_video.py <video_path> [--fps 0.5] [--max-frames 30] [--output-dir /tmp/video_work]

Outputs (inside --output-dir):
    frames/          — JPEG frames (frame_0001.jpg, frame_0002.jpg, …)
    audio.wav        — extracted mono 16kHz audio
    transcript.txt   — Whisper transcription (or "NO_AUDIO" if silent/no audio)
    metadata.json    — ffprobe metadata as JSON
    manifest.json    — list of frame paths + timestamps
"""

import argparse
import json
import os
import subprocess
import sys
import tempfile

# ── Args ─────────────────────────────────────────────────────────────────────
parser = argparse.ArgumentParser()
parser.add_argument("video", help="Path to the video file")
parser.add_argument("--fps", type=float, default=0.5,
                    help="Frames per second to extract (default 0.5 = 1 every 2 s)")
parser.add_argument("--max-frames", type=int, default=30,
                    help="Hard cap on frames extracted (default 30)")
parser.add_argument("--output-dir", default="/tmp/video_work",
                    help="Working directory for extracted assets")
parser.add_argument("--model", default="base",
                    help="Whisper model: tiny/base/small/medium (default base)")
args = parser.parse_args()

VIDEO = args.video
OUTDIR = args.output_dir
FRAMES_DIR = os.path.join(OUTDIR, "frames")
os.makedirs(FRAMES_DIR, exist_ok=True)

def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)

# ── 1. Metadata ───────────────────────────────────────────────────────────────
print("[1/4] Extracting metadata …", flush=True)
meta = run([
    "ffprobe", "-v", "quiet", "-print_format", "json", "-show_format",
    "-show_streams", VIDEO
])
metadata = json.loads(meta.stdout) if meta.returncode == 0 else {}

# Parse useful fields
fmt = metadata.get("format", {})
streams = metadata.get("streams", [])
video_stream = next((s for s in streams if s.get("codec_type") == "video"), {})
audio_stream = next((s for s in streams if s.get("codec_type") == "audio"), {})

duration_s = float(fmt.get("duration", 0))
h, rem = divmod(int(duration_s), 3600)
m, s = divmod(rem, 60)
duration_fmt = f"{h:02d}:{m:02d}:{s:02d}"

# Limit frame count based on duration
max_frames = args.max_frames
fps = min(args.fps, max_frames / max(duration_s, 1))

summary_meta = {
    "filename": os.path.basename(VIDEO),
    "duration_seconds": round(duration_s, 2),
    "duration_formatted": duration_fmt,
    "size_mb": round(int(fmt.get("size", 0)) / 1024**2, 2),
    "video_codec": video_stream.get("codec_name", "unknown"),
    "width": video_stream.get("width"),
    "height": video_stream.get("height"),
    "fps_original": eval(video_stream.get("r_frame_rate", "0/1")),
    "audio_codec": audio_stream.get("codec_name", "none"),
    "audio_sample_rate": audio_stream.get("sample_rate"),
    "bitrate_kbps": round(int(fmt.get("bit_rate", 0)) / 1000, 1),
}
with open(os.path.join(OUTDIR, "metadata.json"), "w") as f:
    json.dump(summary_meta, f, indent=2)
print(f"    Duration: {duration_fmt}  |  {summary_meta['width']}x{summary_meta['height']}  |  {summary_meta['video_codec']}", flush=True)

# ── 2. Frames ─────────────────────────────────────────────────────────────────
print(f"[2/4] Extracting frames at {fps:.3f} fps (max {max_frames}) …", flush=True)
frame_pattern = os.path.join(FRAMES_DIR, "frame_%04d.jpg")
run([
    "ffmpeg", "-y", "-i", VIDEO,
    "-vf", f"fps={fps},scale='min(1280,iw):-2'",
    "-q:v", "3",
    "-frames:v", str(max_frames),
    frame_pattern
])

frames = sorted(f for f in os.listdir(FRAMES_DIR) if f.endswith(".jpg"))
interval = 1.0 / fps if fps > 0 else 0
manifest = []
for i, fname in enumerate(frames):
    ts = i * interval
    h2, rem2 = divmod(int(ts), 3600)
    m2, s2 = divmod(rem2, 60)
    manifest.append({
        "path": os.path.join(FRAMES_DIR, fname),
        "timestamp_seconds": round(ts, 2),
        "timestamp_formatted": f"{h2:02d}:{m2:02d}:{s2:02d}",
    })
with open(os.path.join(OUTDIR, "manifest.json"), "w") as f:
    json.dump(manifest, f, indent=2)
print(f"    Extracted {len(frames)} frames", flush=True)

# ── 3. Audio ──────────────────────────────────────────────────────────────────
print("[3/4] Extracting audio …", flush=True)
AUDIO_PATH = os.path.join(OUTDIR, "audio.wav")
audio_res = run([
    "ffmpeg", "-y", "-i", VIDEO,
    "-vn", "-acodec", "pcm_s16le",
    "-ar", "16000", "-ac", "1",
    AUDIO_PATH
])
has_audio = audio_res.returncode == 0 and os.path.exists(AUDIO_PATH) and os.path.getsize(AUDIO_PATH) > 1000

# ── 4. Transcription ──────────────────────────────────────────────────────────
TRANSCRIPT_PATH = os.path.join(OUTDIR, "transcript.txt")
if has_audio:
    print(f"[4/4] Transcribing audio with Whisper ({args.model}) …", flush=True)
    try:
        import whisper
        model = whisper.load_model(args.model)
        result = model.transcribe(AUDIO_PATH, fp16=False, verbose=False)
        transcript = result.get("text", "").strip()
        # Also save timestamped segments
        segments = result.get("segments", [])
        lines = []
        for seg in segments:
            t0 = int(seg["start"])
            h3, rem3 = divmod(t0, 3600)
            m3, s3 = divmod(rem3, 60)
            lines.append(f"[{h3:02d}:{m3:02d}:{s3:02d}] {seg['text'].strip()}")
        with open(TRANSCRIPT_PATH, "w") as f:
            f.write("\n".join(lines) if lines else transcript)
        print(f"    Transcription done ({len(transcript)} chars)", flush=True)
    except Exception as e:
        print(f"    Whisper error: {e}", flush=True)
        with open(TRANSCRIPT_PATH, "w") as f:
            f.write("TRANSCRIPTION_ERROR: " + str(e))
else:
    print("[4/4] No audio track found — skipping transcription", flush=True)
    with open(TRANSCRIPT_PATH, "w") as f:
        f.write("NO_AUDIO")

# ── Done ──────────────────────────────────────────────────────────────────────
print("\n✅ Pre-processing complete!", flush=True)
print(f"   Output dir : {OUTDIR}")
print(f"   Frames     : {len(frames)}")
print(f"   Transcript : {TRANSCRIPT_PATH}")
print(f"   Metadata   : {os.path.join(OUTDIR, 'metadata.json')}")
