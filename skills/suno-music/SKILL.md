---
name: suno-music
description: "Use this skill when the user wants to generate music, write lyrics for a song, extend an existing AI-generated track, create a cover/remix, extract vocals, or convert generated music into other formats through the AceDataCloud Suno API. This skill makes external network requests to api.acedata.cloud and requires an ACEDATACLOUD_API_TOKEN. Do NOT use it for local audio playback, music theory discussion, or non-generation audio editing tasks."
---

# Suno Music Generation

Use this skill to drive Suno music generation through AceDataCloud's external API.

## Before Starting

- This skill performs external network requests to `https://api.acedata.cloud`
- It requires `ACEDATACLOUD_API_TOKEN`
- If the user has not provided a token or does not want to use a third-party API, stop and ask before continuing
- Prefer the smallest workflow that satisfies the user's request

## Authentication

Set the `ACEDATACLOUD_API_TOKEN` environment variable. Get a token at https://platform.acedata.cloud

```bash
export ACEDATACLOUD_API_TOKEN="your-token-here"
```

All requests go to `https://api.acedata.cloud` with `Authorization: Bearer $ACEDATACLOUD_API_TOKEN`.

## Quick Reference

| User goal | Endpoint | Notes |
|-----------|----------|-------|
| Generate a song from a prompt | `POST /suno/audios` | Use default generation |
| Generate a song from explicit lyrics/style | `POST /suno/audios` with `action: "custom"` | Best when user provides lyrics |
| Continue an existing track | `POST /suno/audios` with `action: "extend"` | Requires `audio_id` |
| Make a cover or remix | `POST /suno/audios` with `action: "cover"` | Requires `audio_id` |
| Generate lyrics first | `POST /suno/lyrics` | Good for vague music requests |
| Refine style text | `POST /suno/style` | Helps produce better prompts |
| Poll long-running tasks | `POST /suno/tasks` | Use when `wait` is false or omitted |
| Extract stems or convert output | `/suno/vox`, `/suno/wav`, `/suno/midi`, `/suno/mp4` | Post-processing |

## Recommended Workflow

1. Confirm the user wants to use an external API and that a token is available.
2. Choose the generation mode based on the request:
   - vague request -> quick generation
   - user supplied lyrics/style -> custom generation
   - continue an existing song -> extend
   - transform an existing song -> cover
3. If the prompt is weak, generate lyrics first or refine the style.
4. Submit the generation request.
5. If the response is asynchronous, poll `/suno/tasks` every 3-5 seconds until complete.
6. Return the resulting audio URLs, task status, or follow-up actions.

## Quick Start

```bash
curl -X POST https://api.acedata.cloud/suno/audios \
  -H "Authorization: Bearer $ACEDATACLOUD_API_TOKEN" \
  -H "Content-Type: application/json" \
  -d '{"prompt": "a happy pop song about coding", "model": "chirp-v4-5", "wait": true}'
```

## Models

| Model | Best For |
|-------|---------|
| `chirp-v5` | Latest, highest quality |
| `chirp-v4-5-plus` | Enhanced v4.5 |
| `chirp-v4-5` | Good balance of quality and speed |
| `chirp-v4` | Fast, reliable |
| `chirp-v3-5` | Legacy, stable |

## Core Workflows

### 1. Quick Generation (Inspiration Mode)

Use this when the user gives a concept and wants the system to invent lyrics and style.

```json
POST /suno/audios
{
  "prompt": "an upbeat electronic track about the future of AI",
  "model": "chirp-v4-5",
  "instrumental": false
}
```

### 2. Custom Generation (Full Control)

Use this when the user already knows the lyrics, title, or style.

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

Use this when the user wants to continue an existing track from a specific time offset.

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

Use this when the user wants the same song idea reinterpreted in another style.

```json
POST /suno/audios
{
  "action": "cover",
  "audio_id": "existing-audio-id",
  "style": "Jazz, Acoustic, Mellow"
}
```

### 5. Lyrics-First Workflow

Use this when the original prompt is too vague to produce a good song directly.

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

Generation is usually asynchronous. Either use `"wait": true` for synchronous mode, or poll:

```json
POST /suno/tasks
{"task_id": "your-task-id"}
```

Poll every 3–5 seconds until `status` is `"complete"`.

If polling fails repeatedly, report the last known task state instead of pretending the generation succeeded.

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

## Using the MCP Server Instead

If the environment is already set up for MCP-based tool use, use the hosted Suno MCP endpoint or the published package instead of raw HTTP.

```bash
pip install mcp-suno
```

Hosted endpoint:

`https://suno.mcp.acedata.cloud/mcp`

Typical tools include:

- `suno_generate_music`
- `suno_generate_custom_music`
- `suno_extend_music`
- `suno_cover_music`
- `suno_generate_lyrics`
- `suno_optimize_style`

## Failure Handling

- If the user does not provide enough information, ask for genre, mood, instrumentation, or lyrical theme
- If `audio_id` is missing, do not attempt extend/cover workflows
- If the API is slow, prefer explicit task polling rather than long blocking waits
- If the token is missing or invalid, stop and surface the auth issue clearly
- If the user asks for copyrighted music imitation, artist mimicry, or unsafe content, do not proceed blindly; keep the request within the provider's allowed policy boundaries

## Gotchas

- All generation is async unless `wait` is enabled
- Lyrics over roughly 3000 characters should usually be split into an extend workflow
- Style tags are descriptive phrases, not enum values
- `cover`, `extend`, and some post-processing flows require an existing `audio_id`
- Upload external audio via `/suno/upload` before using it with extend/cover
- Return URLs and task IDs cleanly so the user can continue from the result later

## References

- GitHub: [AceDataCloud/Skills](https://github.com/AceDataCloud/Skills)
- Docs: [docs.acedata.cloud](https://docs.acedata.cloud)
- PyPI: [mcp-suno](https://pypi.org/project/mcp-suno/)
