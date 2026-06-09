---
name: video-analyzer
description: >
  Analyze a video file and produce a comprehensive AI-readable report (Markdown + JSON).
  Use this skill whenever the user uploads or references a video file (.mp4, .mov, .avi,
  .mkv, .webm, .m4v) and wants to: understand its content, create a report from it,
  extract what is said or shown, describe what happens, count or identify characters,
  summarize the video for use in a Claude project (where direct MP4 upload is not
  supported), or generate any written analysis of video content.
  Trigger even for casual phrasing like "what's in this video", "read this mp4",
  "make a report from this video", "transcribe this video", "describe this clip",
  "how many characters are in this video", "who appears in this video".
compatibility: >
  bash_tool (ffmpeg, Python 3.x), view tool (image inspection), Anthropic Vision API.
  Required pip packages: openai-whisper, opencv-python-headless, numpy, Pillow.
---

# Video Analyzer Skill

Converts a video file into a complete, structured report (Markdown **and** JSON) that
captures everything an AI or human needs to understand the video without watching it.
Includes automatic character detection, audio transcription (Whisper), and visual
analysis of key frames.

---

## Step 0 — Find the video file

```bash
ls /mnt/user-data/uploads/
```

If no video is present, ask the user to upload via the 📎 icon.

---

## Step 1 — Install dependencies & run pre-processing

```bash
pip3 install openai-whisper opencv-python-headless numpy Pillow \
    --break-system-packages -q 2>/dev/null || true

python3 /home/claude/video-analyzer/scripts/process_video.py \
    "<VIDEO_PATH>" \
    --fps 0.5 \
    --max-frames 30 \
    --output-dir /tmp/video_work \
    --model base
```

**Parameter guide:**

| Parameter | Default | When to change |
|-----------|---------|----------------|
| `--fps` | 0.5 | Increase for fast-cut videos (try 1.0); decrease for slow/static (try 0.2) |
| `--max-frames` | 30 | Increase for long videos (up to 60) |
| `--model` | base | Use `small` or `medium` for better transcription accuracy |

---

## Step 2 — Run character detection

```bash
python3 /home/claude/video-analyzer/scripts/detect_characters.py \
    --frames-dir /tmp/video_work/frames \
    --output /tmp/video_work/characters.json \
    --manifest /tmp/video_work/manifest.json
```

This clusters all frames by visual similarity (HSV histogram) and outputs
`characters.json` with: `character_count_detected`, a list of character slots
each with `appearances`, `first_seen`, `last_seen`, and a `representative_frame` path.

---

## Step 3 — Read metadata, transcript, characters

```bash
cat /tmp/video_work/metadata.json
cat /tmp/video_work/transcript.txt
cat /tmp/video_work/characters.json
cat /tmp/video_work/manifest.json
```

---

## Step 4 — Visually analyze representative frames

Use `view` on each character's `representative_frame` to identify who/what it is.
Then sweep through the full manifest, grouping near-identical consecutive frames.

```
view: /tmp/video_work/frames/frame_0001.jpg
view: /tmp/video_work/frames/frame_0009.jpg
…
```

For each frame write a 2–4 sentence description: who is present, setting, action,
any on-screen text. Keep a running list:

```
[00:00:00] <description>
[00:00:05] <description>
…
```

Also assign a name/label to each character cluster (e.g. "Character 1 = Gioggia –
bionda, completo bianco, ufficio"). This will be used in the JSON.

---

## Step 5 — Build the JSON report

Collect the following inputs then run:

```bash
python3 /home/claude/video-analyzer/scripts/build_json_report.py \
    --work-dir /tmp/video_work \
    --output /mnt/user-data/outputs/<basename>_report.json \
    --visual-timeline '<JSON_ARRAY>' \
    --character-names '<JSON_OBJECT>' \
    --summary "<SUMMARY_TEXT>" \
    --key-observations '<JSON_ARRAY>'
```

Example values:
```
--visual-timeline '[{"timestamp":"00:00:00","description":"Donna bionda..."}]'
--character-names '{"1":"Gioggia","2":"Antoni","3":"Marina","4":"Anziano"}'
--summary "Video di satira politica AI-generated..."
--key-observations '["Prodotto con SHOWRUNNER.XYZ","4 personaggi distinti"]'
```

---

## Step 6 — Build the Markdown report

Save to `/mnt/user-data/outputs/<basename>_report.md` using this template:

```markdown
# 📹 Video Report: <filename>
> Auto-generato dalla skill video-analyzer.

## 1. Metadata
| Proprietà | Valore |
|-----------|--------|
| Filename | `...` |
| Durata | `HH:MM:SS` |
| Risoluzione | `WxH` |
| Video codec | `...` |
| Audio codec | `...` |
| Dimensione | `N MB` |
| FPS | `N` |
| Bitrate | `N kbps` |

## 2. Personaggi Rilevati
*(N personaggi distinti rilevati automaticamente)*

| ID | Nome/Label | Presenze | Prima apparizione | Ultima apparizione |
|----|-----------|----------|-------------------|-------------------|
| 1  | ...        | N frame  | HH:MM:SS          | HH:MM:SS          |

## 3. Trascrizione Audio
*(Timestamped — [HH:MM:SS] testo)*
```
<trascrizione>
```

## 4. Timeline Visiva
### [HH:MM:SS] — Scena N
<descrizione 2-4 frasi>

## 5. Sommario AI
<150–300 parole>

## 6. Osservazioni Chiave
- ...
```

---

## Step 7 — Present both files

```python
present_files([
    "/mnt/user-data/outputs/<basename>_report.md",
    "/mnt/user-data/outputs/<basename>_report.json"
])
```

---

## Tips & edge cases

- **No audio**: set transcript a "No audio track detected."
- **Screen recordings**: presta attenzione a UI, testo sullo schermo, titoli finestre
- **Video veloce**: `--fps 1.0`; **molto lungo (>30 min)**: `--fps 0.1 --max-frames 60`
- **Audio straniero**: Whisper è multilingue, nessuna configurazione necessaria
- **Troppi cluster (>8)**: aumenta `--similarity-threshold` a 0.80 nel detect_characters
- **Troppo pochi cluster**: abbassa `--similarity-threshold` a 0.60
