# Video Analyzer Skill

> *Converts any video file into a comprehensive AI-readable report — because Claude Projects don't accept MP4 uploads.*

---

## What It Does

Upload any video and get back a complete structured report Claude can actually use:

- **Audio transcript** with timestamps (OpenAI Whisper, 99 languages, auto-detected)
- **Character/scene detection** — visual clustering via HSV histogram, no ML model required
- **Visual timeline** — frame-by-frame description via Claude Vision
- **Dual output** — human-readable Markdown + machine-readable JSON (schema v1.0)

---

## Why This Exists

Claude Projects don't support MP4 uploads. This skill bridges the gap: process the video once locally, get a structured report you can paste into any Claude project as a plain document.

---

## Supported Formats

MP4, MOV, AVI, MKV, WebM, M4V

---

## Dependencies

Auto-installed on first run:

| Dependency | Purpose |
|------------|---------|
| `ffmpeg` (system) | Frame extraction, audio demux, metadata |
| `openai-whisper` | Audio transcription (local inference, no API) |
| `opencv-python-headless` | Frame fingerprinting for character clustering |
| `numpy`, `Pillow` | Array ops and image I/O |

No external API calls beyond `pip install`. No credentials required.

---

## Quick Start

Just say: *"analyze this video"* / *"analizza questo video"* — the skill handles the rest.

Or trigger it explicitly when you have a video file at a known path:

```bash
python3 scripts/process_video.py /path/to/video.mp4     --fps 0.5 --max-frames 30 --output-dir /tmp/video_work
```

---

## Output

| File | Contents |
|------|----------|
| `<basename>_report.md` | Human-readable Markdown with metadata, transcript, timeline |
| `<basename>_report.json` | Structured JSON (schema v1.0) for downstream processing |

### JSON schema snapshot

```json
{
  "schema_version": "1.0",
  "metadata": { "duration_formatted": "00:02:44", "width": 1080, "height": 1920 },
  "characters": { "count": 4, "list": [ { "character_id": 1, "name": "Gioggia", "appearances": 12 } ] },
  "audio": { "has_audio": true, "transcript_segments": [ { "timestamp": "00:00:03", "text": "..." } ] },
  "visual_timeline": [ { "timestamp": "00:00:00", "description": "..." } ],
  "summary": "...",
  "key_observations": [ "..." ]
}
```

---

## Technical Approach

1. **ffprobe** extracts metadata (duration, codec, resolution, bitrate)
2. **ffmpeg** samples frames at configurable FPS (default 0.5 = 1 every 2 s) and extracts mono 16 kHz WAV
3. **Whisper** transcribes audio locally with per-segment timestamps
4. **HSV histogram clustering** groups frames by visual similarity — each cluster = one recurring "character slot"; no face recognition, no ML model, no API
5. **Claude Vision** describes each representative frame, building the visual timeline
6. **build_json_report.py** assembles everything into the final structured JSON

---

## Scripts

| Script | Purpose |
|--------|---------|
| `scripts/process_video.py` | Metadata, frame extraction, audio extraction, Whisper transcription |
| `scripts/detect_characters.py` | HSV histogram fingerprinting and greedy clustering |
| `scripts/build_json_report.py` | Assembles final JSON report from all sources |

---

## Tuning

| Parameter | Default | When to Change |
|-----------|---------|----------------|
| `--fps` | 0.5 | Increase for fast-cut videos (1.0); decrease for slow/static (0.2) |
| `--max-frames` | 30 | Increase for long videos (up to 60) |
| `--model` | base | Use `small` or `medium` for better transcription accuracy |
| `--similarity-threshold` | 0.72 | Raise to 0.80 if too many clusters; lower to 0.60 if too few |

---

## Works On

- Live-action video
- AI-generated animation (SHOWRUNNER, Sora, etc.)
- Screen recordings and tutorials
- Vertical Reels/Shorts format

---

## License

Apache 2.0 — see [LICENSE.txt](./LICENSE.txt)

## Author

Created by **Albert** ([@VjAlbert](https://github.com/VjAlbert))
