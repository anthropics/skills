````skill
---
name: groq-speech-to-text
description: Transcribe audio files using Groq API (Whisper models).
---

# Groq Speech-to-Text Skill

This skill uploads an audio file to the Groq Speech-to-Text API and saves the transcription.

## Usage

```bash
# set your API key (or use .env in the repo root)
export GROQ_API_KEY=your_api_key_here

# run the script with a path to an audio file
node scripts/transcribe.mjs /path/to/audio.mp4
```

## Output

- Writes a `{filename}_transcript.txt` next to the input file.

## Notes

- Uses the `whisper-large-v3-turbo` model by default.
- Supported file types: flac, mp3, mp4, mpeg, mpga, m4a, ogg, wav, webm
````
