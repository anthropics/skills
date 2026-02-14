---
name: indic-voice-pipeline
description: |
  Download, transcribe, and translate audio/video in 12 Indian languages locally using fine-tuned Whisper models.
  Use when the user mentions: transcribe, transcription, speech to text, audio to text, translate audio,
  download video, subtitle, caption, detect language, whisper, dictation, Indian language,
  Telugu, Hindi, Kannada, Tamil, Bengali, Malayalam, Marathi, Gujarati, Odia, Punjabi, Sanskrit, Urdu.
  Works with any audio (mp3, wav, m4a, ogg, flac) or video (mp4, mkv, webm, mov) file.
  Downloads from YouTube, Twitter/X, TikTok, Instagram, and 1000+ sites via yt-dlp.
  Supports 12 Indian languages with fine-tuned models from vasista22 (IIT Madras) and AI4Bharat IndicWhisper.
  Runs 100% locally — no API keys needed.
license: MIT
---

# Indic Voice Pipeline

Download, transcribe, and translate audio/video in 12 Indian languages — entirely on your machine. No cloud APIs, no data leaving your machine, no API keys.

**By [HumanCTO](https://github.com/humancto) | [GitHub](https://github.com/humancto/indic-voice-pipeline) | [Documentation](https://humancto.github.io/indic-voice-pipeline/)**

## Prerequisites

Run once to install dependencies:

```bash
pip install yt-dlp openai-whisper "transformers==4.46.3" accelerate "numpy<2" --quiet
brew install ffmpeg  # macOS
```

## Step-by-Step Workflow

**For ANY download, transcription, or translation request, follow these steps:**

### Step 1: Determine intent and run the appropriate command

**User wants to download a video:**

```bash
python3 {SKILL_PATH}/scripts/video_downloader.py download "<URL>" --output-dir ~/Downloads
```

**User wants audio only:**

```bash
python3 {SKILL_PATH}/scripts/video_downloader.py audio "<URL>" --output-dir ~/Downloads --audio-format mp3
```

**User wants to transcribe audio/video to text:**

```bash
python3 {SKILL_PATH}/scripts/whisper_transcribe.py transcribe "<FILE_PATH>" --output-dir ~/Downloads
```

**User wants to transcribe with a specific Indian language (uses fine-tuned model automatically):**

```bash
python3 {SKILL_PATH}/scripts/whisper_transcribe.py transcribe "<FILE_PATH>" --language te --output-dir ~/Downloads
```

**User wants to translate audio/video to English:**

```bash
python3 {SKILL_PATH}/scripts/whisper_transcribe.py translate "<FILE_PATH>" --output-dir ~/Downloads
```

**User wants to detect the language:**

```bash
python3 {SKILL_PATH}/scripts/whisper_transcribe.py detect "<FILE_PATH>"
```

**User wants video/audio info without processing:**

```bash
python3 {SKILL_PATH}/scripts/video_downloader.py info "<URL>"
python3 {SKILL_PATH}/scripts/whisper_transcribe.py info "<FILE_PATH>"
```

### Step 2: Report results

Tell the user:

- Where files were saved (full paths)
- Detected language and confidence
- The full transcription text
- Processing time
- Output files: .txt (plain text), .srt (subtitles), .json (structured)

## Supported Indian Languages

The skill auto-selects the best fine-tuned model when you pass `--language <code>`:

### vasista22 Models (HuggingFace — auto-downloaded)

| Language | Code | Model                             |
| -------- | ---- | --------------------------------- |
| Telugu   | `te` | vasista22/whisper-telugu-large-v2 |
| Hindi    | `hi` | vasista22/whisper-hindi-large-v2  |
| Kannada  | `kn` | vasista22/whisper-kannada-medium  |
| Gujarati | `gu` | vasista22/whisper-gujarati-medium |
| Tamil    | `ta` | vasista22/whisper-tamil-medium    |

### AI4Bharat IndicWhisper Models (ZIP download — cached at ~/.cache/indicwhisper/)

| Language  | Code |
| --------- | ---- |
| Bengali   | `bn` |
| Malayalam | `ml` |
| Marathi   | `mr` |
| Odia      | `or` |
| Punjabi   | `pa` |
| Sanskrit  | `sa` |
| Urdu      | `ur` |

## Full Pipeline Example

Download a Telugu video and transcribe it:

```bash
# Download
python3 {SKILL_PATH}/scripts/video_downloader.py download "https://youtube.com/watch?v=..." --output-dir ~/Downloads

# Transcribe with fine-tuned Telugu model
python3 {SKILL_PATH}/scripts/whisper_transcribe.py transcribe ~/Downloads/video.mp4 --language te --output-dir ~/Downloads

# Translate to English
python3 {SKILL_PATH}/scripts/whisper_transcribe.py translate ~/Downloads/video.mp4 --language te --output-dir ~/Downloads
```

## Important Notes

- Default output: `~/Downloads`
- Three output files per transcription: `.txt`, `.srt` (subtitles), `.json` (structured)
- Video files have audio extracted automatically (ffmpeg, 16kHz mono WAV)
- Smart chunking: 25s windows with 5s overlap — no words lost at boundaries
- Hardware: Apple Silicon (MPS), NVIDIA GPU (CUDA), or CPU — auto-detected
- Translation always outputs English (Whisper limitation)
- First run downloads the model — subsequent runs use cache
- IndicWhisper models (~600 MB each) are downloaded and cached on first use
- Use `--model medium` or `--model large` for better accuracy on noisy audio
- Use `--hf-model` to specify any custom HuggingFace Whisper model
