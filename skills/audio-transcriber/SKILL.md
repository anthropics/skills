---
name: audio-transcriber
description: "Transcribes audio/video/YouTube to professional Markdown with speaker diarization. Accepts local files (MP3, MP4, WAV, M4A, etc.) or YouTube links. For YouTube, uses MCP youtube-transcript for instant captions; if unavailable, downloads audio with yt-dlp. For local files, uses MLX Whisper (Apple Silicon GPU) + SpeechBrain for lightweight diarization. Supports model selection (tiny/base/small/medium). Automatically generates meeting minutes."
---

## Purpose

Transcribes audio, video, and YouTube videos to professional Markdown text with:
- **YouTube** — extracts transcription/captions instantly via MCP `youtube-transcript` (no video download needed)
- **Local transcription optimized for Apple Silicon** via MLX Whisper (GPU/Neural Engine)
- **Lightweight diarization** via SpeechBrain ECAPA-TDNN (speaker identification without HuggingFace token)
- **Interactive speaker identification** — after diarization, asks the user to name each SPEAKER
- Rich metadata (duration, language, speakers, timestamps)
- Automatic meeting minutes/summary generation via LLM

## When to Use

Invoke this skill when:

- User needs to transcribe audio/video files to text
- User shares a **YouTube link** and wants the transcript/transcription
- User wants meeting minutes automatically generated from recordings
- User requires speaker identification (diarization) in conversations
- User wants executive summaries of long audio content
- User asks variations of "transcribe this audio", "convert audio to text", "generate meeting notes from recording", "transcribe this YouTube video", "get the transcript from this link"
- User has audio files in common formats (MP3, MP4, WAV, M4A, OGG, FLAC, WEBM)
- User has YouTube URLs (youtube.com, youtu.be)

## Input Sources

| Source | Method | Speed | Requirements |
|--------|--------|-------|-------------|
| **YouTube URL** | MCP `youtube-transcript` (captions) | **Instant** | MCP installed |
| **YouTube URL (no captions)** | `yt-dlp` + MLX Whisper | Moderate | `yt-dlp` installed |
| **Local file** | MLX Whisper + SpeechBrain | Fast | Python dependencies |

## Engines (Priority Order)

| Engine | Platform | Diarization | Speed | Installation |
|--------|----------|-------------|-------|-------------|
| **MCP youtube-transcript** | Any | Not native | Instant | `claude mcp add youtube-transcript -- npx -y @sinco-lab/mcp-youtube-transcript` |
| **MLX Whisper** (default) | Apple Silicon | Via SpeechBrain | Very fast | `pip install mlx-whisper` |
| WhisperX | Any (CPU/GPU) | Via pyannote | Moderate | `pip install whisperx` |
| Faster-Whisper | Any | Not native | Fast | `pip install faster-whisper` |
| Whisper | Any | Not native | Baseline | `pip install openai-whisper` |

## Available Models (MLX Whisper)

| Model | Size | RAM needed | Quality | HuggingFace Repo |
|-------|------|-----------|---------|-------------------|
| `tiny` | ~75 MB | ~500 MB | Basic | `mlx-community/whisper-tiny-mlx` |
| `base` | ~140 MB | ~800 MB | Good | `mlx-community/whisper-base-mlx` |
| **`small`** (default) | **~460 MB** | **~1.5 GB** | **Very good** | **`mlx-community/whisper-small-mlx`** |
| `medium` | ~1.5 GB | ~3 GB | Excellent | `mlx-community/whisper-medium-mlx` |
| `large-v3-turbo` | ~1.5 GB | ~4 GB | Superior | `mlx-community/whisper-large-v3-turbo` |

**Note:** `medium` and `large-v3-turbo` models require Macs with 16GB+ RAM.

## Diarization (Speaker Identification)

Uses **SpeechBrain ECAPA-TDNN** (~80 MB) with agglomerative clustering:
- No HuggingFace token required
- ~3 min for 85 min of audio (CPU)
- Generates SPEAKER_00, SPEAKER_01, etc. labels
- After diarization, the skill **interactively asks** the user to name each speaker

Dependencies: `pip install speechbrain scikit-learn soundfile`

## Workflow

### Step 0: Greeting and Model Selection

**Goal:** Inform the user about available models and confirm the choice.

**Actions:**

1. When starting, ALWAYS inform the user:

```
Audio Transcriber — MLX Whisper (Apple Silicon)

Available models:
  tiny   (~75 MB)  — Fast, basic quality
  base   (~140 MB) — Fast, good quality
  small  (~460 MB) — Recommended default, very good quality
  medium (~1.5 GB) — Excellent quality (requires 16GB+ RAM)
  large  (~1.5 GB) — Superior (requires 16GB+ RAM)

Current model: small (default)
```

2. If the user passed `--model <name>` in arguments, use that model
3. If not specified, use `small` as default without asking
4. If the user asked for "simplest model" or similar, use `tiny` or `base`

### Step Y: YouTube — Transcription via MCP (if input is a URL)

**Goal:** Extract transcription from YouTube videos without downloading the video.

**When to use:** If the user's input is a YouTube link (youtube.com, youtu.be).

**Decision flow:**

```
Is input a YouTube URL?
  |-- YES -> Try MCP youtube-transcript (get_transcript)
  |     |-- Success -> Format markdown (skip Steps 1-4)
  |     |     \-- If multiple speakers -> Manual diarization or ask user
  |     \-- Fail (no captions) -> Download audio with yt-dlp -> Follow Steps 1-6
  \-- NO -> Follow Steps 1-6 (local file)
```

**Actions (MCP path):**

1. Detect that the input is a YouTube URL
2. Use the MCP tool `get_transcript` with the URL and desired language:
   - Try first with the detected/requested language
   - If it fails, try without specifying language (gets default caption)
3. If the transcription comes with timestamps, preserve them in markdown
4. If the video has multiple speakers and the user requested identification:
   - Ask the user if they want diarization
   - If yes: download audio with yt-dlp, convert to WAV 16kHz, run SpeechBrain (Step 4)
5. Generate final markdown (Step 6)

**Actions (yt-dlp fallback — when MCP fails or no captions available):**

```bash
# Check if yt-dlp is installed
which yt-dlp || python3 -m yt_dlp --version

# Try to download existing captions first (to /tmp/)
yt-dlp --write-auto-subs --sub-lang pt --skip-download --convert-subs srt -o "/tmp/youtube-sub" "URL"

# If no captions, download audio only (to /tmp/)
yt-dlp -x --audio-format wav --audio-quality 0 -o "/tmp/youtube-audio.%(ext)s" "URL"

# Convert to 16kHz mono (for diarization, to /tmp/)
ffmpeg -i "/tmp/youtube-audio.wav" -ar 16000 -ac 1 -f wav "/tmp/youtube-audio-16k.wav" -y
```

After downloading audio, follow the normal flow (Steps 3-6).

**YouTube output template:**

```markdown
# Video Transcription (YouTube)

## Metadata

| Field | Value |
|-------|-------|
| **Title** | {video_title} |
| **URL** | {youtube_url} |
| **Duration** | {duration} |
| **Language** | {language} |
| **Date** | {date} |
| **Source** | YouTube (automatic/manual captions) |

---

## Transcription

{transcription_content}
```

### Step 1: Discovery (Auto-detect Tools)

**Goal:** Detect installed tools.

**Actions:**

```python
# Priority: MLX Whisper > WhisperX > Faster-Whisper > Whisper
engines = []
try:
    import mlx_whisper
    engines.append("mlx-whisper")
except: pass
try:
    import whisperx
    engines.append("whisperx")
except: pass
try:
    import faster_whisper
    engines.append("faster-whisper")
except: pass
try:
    import whisper
    engines.append("whisper")
except: pass

# Check diarization
try:
    from speechbrain.inference.speaker import EncoderClassifier
    diarization_available = True
except:
    diarization_available = False

# Check ffmpeg
import shutil
ffmpeg_available = shutil.which("ffmpeg") is not None
```

**If MLX Whisper is not installed:**

```
pip install mlx-whisper speechbrain scikit-learn soundfile
```

### Step 2: Validate File and Extract Metadata

**Goal:** Verify file, format and duration.

**IMPORTANT — Intermediate files:**
- All temporary files (converted WAV, transcription/diarization JSONs) must be saved to `/tmp/`, NEVER in the original file's directory.
- The only files saved in the original file's directory are the **final markdown** (transcript + minutes).
- At the end of the process, **clean up all temporary files** from `/tmp/`.

**Actions:**

1. Verify the file exists
2. Extract metadata via ffprobe (duration, format, size)
3. If format is not WAV and diarization is enabled, convert to WAV 16kHz mono **in /tmp/**:

```bash
ffmpeg -i "input.mp4" -ar 16000 -ac 1 -f wav "/tmp/input-16k.wav" -y
```

4. Intermediate JSONs also in `/tmp/`:
   - `/tmp/transcription.json`
   - `/tmp/diarization.json`

### Step 3: Transcription with MLX Whisper

**Goal:** Transcribe audio using Apple Silicon GPU.

```python
import mlx_whisper

# Model map
MODELS = {
    "tiny": "mlx-community/whisper-tiny-mlx",
    "base": "mlx-community/whisper-base-mlx",
    "small": "mlx-community/whisper-small-mlx",
    "medium": "mlx-community/whisper-medium-mlx",
    "large": "mlx-community/whisper-large-v3-turbo",
}

result = mlx_whisper.transcribe(
    audio_file,
    path_or_hf_repo=MODELS[model_name],
    language="pt",  # or None for auto-detect
    word_timestamps=True
)
```

### Step 4: Diarization with SpeechBrain

**Goal:** Identify speakers using embeddings + clustering.

**Method:**
1. Load WAV audio 16kHz mono
2. Extract embeddings in 3-second windows (1.5s hop) using SpeechBrain ECAPA-TDNN
3. Normalize embeddings
4. Cluster with AgglomerativeClustering (n_clusters=5 by default, or distance_threshold if unknown)
5. Map each transcription segment to the nearest speaker by timestamp

```python
from speechbrain.inference.speaker import EncoderClassifier
from sklearn.cluster import AgglomerativeClustering
from sklearn.preprocessing import normalize
import soundfile as sf
import torch
import numpy as np

# Load model (~80 MB)
classifier = EncoderClassifier.from_hparams(
    source="speechbrain/spkrec-ecapa-voxceleb",
    savedir="/tmp/speechbrain_spkrec"
)

# Load WAV audio
signal_np, sr = sf.read("input-16k.wav")
signal = torch.tensor(signal_np, dtype=torch.float32).unsqueeze(0)

# Extract embeddings in 3s windows
window_size = 3 * sr
hop_size = int(1.5 * sr)
embeddings, window_times = [], []

pos = 0
while pos + window_size < signal.shape[1]:
    chunk = signal[:, pos:pos+window_size]
    with torch.no_grad():
        emb = classifier.encode_batch(chunk)
        embeddings.append(emb.squeeze().numpy())
        window_times.append(pos / sr)
    pos += hop_size

# Clustering
emb_matrix = normalize(np.array(embeddings))
clustering = AgglomerativeClustering(n_clusters=5, metric="cosine", linkage="average")
labels = clustering.fit_predict(emb_matrix)

# Map speaker to each transcription segment
speaker_map = {t: f"SPEAKER_{labels[i]:02d}" for i, t in enumerate(window_times)}
for seg in segments:
    seg_mid = (seg["start"] + seg["end"]) / 2
    best_t = min(window_times, key=lambda t: abs(t - seg_mid))
    seg["speaker"] = speaker_map[best_t]
```

### Step 5: Interactive Speaker Identification

**Goal:** Ask the user the real name of each speaker.

**IMPORTANT: This step is MANDATORY when diarization is enabled.**

**Actions:**

1. Count segments per speaker and show a representative excerpt from each
2. Ask the user, listing each SPEAKER with segment count
3. The user responds with real names (e.g., "SPEAKER_00 is John, SPEAKER_01 is Mary")
4. Find/replace all SPEAKER_XX labels with real names in the final markdown

**Example interaction:**

```
Identified speakers:

  SPEAKER_00 (1320 segments) — Main speaker
    Excerpt: "...I'm a software architect, requirements engineer..."

  SPEAKER_01 (61 segments) — Second most active
    Excerpt: "...I don't know, I'm not sure if Prisma is part of Adonis..."

  SPEAKER_02 (27 segments)
    Excerpt: "...it's going up..."

Who is each speaker? (e.g., "SPEAKER_00 is John, SPEAKER_01 is Mary")
```

5. After receiving names, replace in markdown:
   - `### SPEAKER_00` -> `### John (Architect)`
   - In metadata, list participants with real names

### Step 6: Generate Final Markdown

**Goal:** Create formatted markdown file with transcription, speakers and metadata.

**Template:**

```markdown
# Audio Transcription

## Metadata

| Field | Value |
|-------|-------|
| **File** | {filename} |
| **Duration** | {duration} |
| **Language** | {language} |
| **Date** | {date} |
| **Engine** | MLX Whisper (model: {model}) |
| **Diarization** | SpeechBrain ECAPA-TDNN |
| **Speakers** | {n_speakers} |

## Participants

- **{real_name_1}** ({n} segments) — role/description
- **{real_name_2}** ({n} segments)

---

## Transcription

### {real_name_1}

**[00:02 -> 00:14]** segment text...

### {real_name_2}

**[13:01 -> 13:07]** segment text...
```

**Naming:** `transcript-YYYYMMDD-HHMMSS.md`

### Step 7: Generate Meeting Minutes/Summary

**ALWAYS generate meeting minutes automatically** after transcription (no need to ask the user).

1. Read the generated transcription
2. Use the LLM (Claude) to generate:
   - Meeting context and objective
   - Participants and roles
   - Topics discussed
   - Decisions made
   - Action items defined
3. Save as `minutes-YYYYMMDD-HHMMSS.md` **in the same directory as the original file**

### Step 8: Clean Up Temporary Files

**MANDATORY:** At the end of the entire process, remove all intermediate files:

```bash
rm -f /tmp/transcription.json /tmp/diarization.json /tmp/*-16k.wav /tmp/youtube-audio.*
```

**General output rules:**
- In the original file's directory, ONLY keep:
  - `transcript-YYYYMMDD-HHMMSS.md` (transcription with speakers)
  - `minutes-YYYYMMDD-HHMMSS.md` (summary/minutes)
- Everything else (WAV, JSON, SRT) goes to `/tmp/` and is deleted at the end

## Benchmarks (Apple M2, 8GB RAM)

Test audio: ~85 min meeting recording

| Engine + Model | Transcription | Diarization | Total | Quality |
|----------------|--------------|-------------|-------|---------|
| WhisperX tiny (CPU) | ~7 min | ~84 min (pyannote) | **~91 min** | Poor |
| MLX Whisper base (GPU) | ~5.7 min | ~3 min (SpeechBrain) | **~9 min** | Good |
| **MLX Whisper small (GPU)** | **~6.5 min** | **~3 min (SpeechBrain)** | **~9.5 min** | **Very good** |

## Requirements

```bash
# Main engine (Apple Silicon)
pip install mlx-whisper

# Lightweight diarization
pip install speechbrain scikit-learn soundfile

# Format conversion (recommended)
brew install ffmpeg

# YouTube (transcription via captions)
claude mcp add youtube-transcript -- npx -y @sinco-lab/mcp-youtube-transcript

# YouTube (fallback — download audio when no captions available)
pip install yt-dlp
```

## Fallback (non-Apple Silicon)

If not on Apple Silicon, the skill automatically uses:
1. WhisperX (if installed) — with pyannote for diarization
2. Faster-Whisper
3. OpenAI Whisper

For WhisperX with diarization, a HuggingFace token is needed:
1. Create account at https://huggingface.co
2. Generate token at https://huggingface.co/settings/tokens
3. Accept terms at https://huggingface.co/pyannote/speaker-diarization-community-1
4. Save token: `echo "hf_xxx" > ~/.hftoken`
