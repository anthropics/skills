---
name: suno-music
description: "Generate AI music with Suno via AceDataCloud API. TRIGGER when: user asks to create a song, generate music, write lyrics, extend a track, create a cover, separate vocals, or any music generation task. DO NOT TRIGGER when: playing local audio files, music theory questions, or non-generation audio tasks."
---

# Suno Music Generation

Generate AI-powered music through AceDataCloud's Suno API. Supports text-to-music, custom lyrics, song extension, covers, vocal separation, and format conversion (MP3, WAV, MIDI, MP4).

## Authentication

Set the `ACEDATACLOUD_API_TOKEN` environment variable. Get a token at https://platform.acedata.cloud

```bash
export ACEDATACLOUD_API_TOKEN="your-token-here"
```

All requests go to `https://api.acedata.cloud` with `Authorization: Bearer $ACEDATACLOUD_API_TOKEN`.

## Quick Start — Generate a Song

```bash
curl -X POST https://api.acedata.cloud/suno/audios \
  -H "Authorization: Bearer $ACEDATACLOUD_API_TOKEN" \
  -H "Content-Type: application/json" \
  -d '{"prompt": "a happy pop song about coding", "model": "chirp-v4-5", "wait": true}'
```

## Available Models

| Model | Best For |
|-------|---------|
| `chirp-v5` | Latest, highest quality |
| `chirp-v4-5-plus` | Enhanced v4.5 |
| `chirp-v4-5` | Good balance of quality and speed |
| `chirp-v4` | Fast, reliable |
| `chirp-v3-5` | Legacy, stable |

## Core Workflows

### 1. Quick Generation (Inspiration Mode)

Generate a song from a text description. Suno creates lyrics, style, and music automatically.

```json
POST /suno/audios
{
  "prompt": "an upbeat electronic track about the future of AI",
  "model": "chirp-v4-5",
  "instrumental": false
}
```

### 2. Custom Generation (Full Control)

Provide your own lyrics, title, and style for precise control.

```json
POST /suno/audios
{
  "action": "custom",
  "lyric": "[Verse]\nCode is poetry in motion\n[Chorus]\nWe build the future tonight",
  "title": "Digital Dreams",
  "style": "Synthwave, Electronic, Dreamy",
  "model": "chirp-v4-5"
}
```

### 3. Extend a Song

Continue an existing song from a specific timestamp.

```json
POST /suno/audios
{
  "action": "extend",
  "audio_id": "existing-audio-id",
  "lyric": "[Bridge]\nNew section lyrics here",
  "continue_at": 120.0,
  "style": "Same style as original"
}
```

### 4. Cover / Remix

Create a new version of an existing song in a different style.

```json
POST /suno/audios
{
  "action": "cover",
  "audio_id": "existing-audio-id",
  "style": "Jazz, Acoustic, Mellow"
}
```

### 5. Full Song Creation Workflow

For best results follow this multi-step workflow:

1. **Generate lyrics** — `POST /suno/lyrics` with a topic/prompt
2. **Optimize style** — `POST /suno/style` to refine style description
3. **Generate music** — `POST /suno/audios` with custom action, lyrics + style
4. **Poll task** — `POST /suno/tasks` with task_id until status is complete
5. **Extend** — Use extend action to add more sections (optional)
6. **Convert** — Get WAV (`/suno/wav`), MIDI (`/suno/midi`), or MP4 (`/suno/mp4`) (optional)

## Auxiliary Endpoints

| Endpoint | Method | Purpose |
|----------|--------|---------|
| `/suno/lyrics` | POST | Generate structured lyrics from a prompt |
| `/suno/style` | POST | Optimize/refine a style description |
| `/suno/mp4` | POST | Get MP4 video version of a song |
| `/suno/wav` | POST | Convert to lossless WAV format |
| `/suno/midi` | POST | Extract MIDI data for DAW editing |
| `/suno/vox` | POST | Extract vocal track (stem separation) |
| `/suno/timing` | POST | Get word-level timing/subtitles |
| `/suno/persona` | POST | Save a vocal style as a reusable persona |
| `/suno/upload` | POST | Upload external audio for extend/cover |
| `/suno/tasks` | POST | Query task status and results |

## Task Polling

All generation is async. Either use `"wait": true` for synchronous mode, or poll:

```json
POST /suno/tasks
{"task_id": "your-task-id"}
```

Poll every 3–5 seconds until `status` is `"complete"`.

## Lyrics Format

Use section markers in square brackets:

```
[Verse 1]
Your verse lyrics here

[Chorus]
Catchy chorus lyrics

[Bridge]
Bridge section

[Outro]
Ending lyrics
```

## MCP Server

For tool-use with Claude, install the MCP server:

```bash
pip install mcp-suno
```

Or use the hosted endpoint: `https://suno.mcp.acedata.cloud/mcp`

Key tools: `suno_generate_music`, `suno_generate_custom_music`, `suno_extend_music`, `suno_cover_music`, `suno_generate_lyrics`, `suno_optimize_style`

## Gotchas

- All generation is **async** — always poll `/suno/tasks` or use `"wait": true`
- Lyrics max ~3000 characters. For longer songs, use the **extend** workflow
- Style tags are descriptive phrases, not enum values (e.g., "Synthwave, Electronic, Dreamy")
- The `concat` action merges extended song segments — requires audio_id of the extended track
- Upload external audio via `/suno/upload` before using it with extend/cover

## Links

- GitHub: [AceDataCloud/Skills](https://github.com/AceDataCloud/Skills)
- Docs: [docs.acedata.cloud](https://docs.acedata.cloud)
- MCP on PyPI: [mcp-suno](https://pypi.org/project/mcp-suno/)
