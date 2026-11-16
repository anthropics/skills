# Xiaozhi AI Media Skill

Generate videos (Seedance), images (Seedream), speech (TTS), and chat
(OpenAI-compatible) through the Xiaozhi AI (xzai.me) API, from any agent
that supports skills: Claude Code, Codex, Cursor, OpenCode, and similar.

The skill ships a single dependency-free Python CLI (`scripts/xiaozhi.py`)
plus this instruction file. Everything is plain `urllib` — no SDK, no pip
installs. You only pay for what you generate; the skill itself is free.

## When to Use

- "Generate a video from this prompt / make this image move"
- "Generate an image of …" / product shots, posters, illustrations
- "Convert this text to speech"
- You need a multimodal chat model via an OpenAI-compatible endpoint

Don't use for: music generation, lip-sync, digital humans (not exposed via
the API yet), or video editing of existing footage.

## Prerequisites

Two environment variables:

```bash
export XIAOZHI_API_KEY="your-key"        # from xzai.me 个人中心 → API接口
export XIAOZHI_BASE_URL="https://xzai.me"  # optional, this is the default
```

**No key yet?** Run any command anyway — the CLI prints the URL
`https://xzai.me` and a 4-step guide (register → 个人中心 → API接口 → copy
key → send it back to the agent). No browser popup; the agent relays the
URL and saves the key once the user provides it.

## How to Run

All operations go through the CLI:

```bash
python scripts/xiaozhi.py video "a corgi running through snow" --ratio 16:9 --out clip.mp4
python scripts/xiaozhi.py image "minimalist poster, blue and white" --ratio 1:1 --out poster.jpg
python scripts/xiaozhi.py tts "你好，这是语音测试" --voice Cherry --out hello.wav
python scripts/xiaozhi.py chat "reply with ok" 
python scripts/xiaozhi.py models
```

## Quick Reference

| Command | What it does | Typical wait |
|---|---|---|
| `video` | Seedance text-to-video / image-to-video | 4–20 min |
| `image` | Seedream 5.0 text-to-image / image reference | ~1 min |
| `tts` | Text to speech (WAV) | seconds |
| `chat` | OpenAI-compatible chat (glm-5.3-flash) | seconds |
| `models` | List available models | — |
| `status <task_id>` | Check a video/image task | — |

## Video Models (the #1 mistake is here)

| `--model` | duration | notes |
|---|---|---|
| *(omit)* | 10 s | Seedance 2.0 Fast, the default, cheapest |
| `seedance-2.0-fast-15` | 15 s | must be spelled exactly |
| `seedance-2.0-mini` | 15 s | must pass `--duration 15` too |
| `seedance-2.5` | 30 s | only 30 s; also supports 21:9 |

**The API silently falls back to the 10-second Fast model if the model name
is wrong or `--duration` is missing for mini.** The CLI validates the
combination and refuses to submit an inconsistent pair — never bypass it by
calling the raw endpoint with unvalidated values.

Ratios: `16:9 / 9:16 / 1:1 / 3:4 / 4:3` (plus `21:9` for 2.5 and fast-15).
Reference images: pass `--images url1 url2` (max 10). One image = first
frame; multiple = multi-reference.

## Procedure

1. **Confirm the key works**: `python scripts/xiaozhi.py models`. If this
   fails with 401, the key is wrong — stop and check before submitting paid
   jobs.
2. **Choose parameters deliberately**: video or image; ratio; duration
   (video). State them in your reply so the user can correct before you
   submit — generation consumes credits.
3. **Submit and wait**: the CLI polls automatically and prints progress.
   Videos take 4–20 minutes; do not re-submit while a task is pending —
   duplicate submissions burn credits. Use `status <task_id>` in a new call
   instead.
4. **Download immediately**: the CLI saves output to `--out`. Result URLs on
   the CDN expire; a local copy is the only durable deliverable. Completion
   criterion: the file exists on disk and is non-empty.
5. **Report the local path**, not the remote URL, to the user.

## Image Notes

- Output size approximates but does not exactly match the requested ratio
  (16:9 came out 2848×1600 in testing). If exact dimensions matter, check
  the file after download.
- Up to 10 reference image URLs per job via `--images`.
- Styles: pass `--style web_image_style_2D` (also `_3D`, `_portrait`, …).

## Pitfalls

- **Two auth schemes**: `api.php` endpoints use the `x-token` header;
  `/v1/*` endpoints use `Authorization: Bearer`. The CLI handles this; if
  you ever call the API directly, don't mix them.
- **Failed tasks auto-refund** (state 2), so a failed video doesn't cost
  credits — but a *duplicate* submission while waiting does.
- **TTS limit**: 1–500 characters per call; longer text must be split.
  Audio URLs expire in ~24 h.
- **Context window** of the chat model is 1,048,576 tokens — don't assume
  small-context limits, but do not send more than ~1M tokens.
- Errors are standard OpenAI-shaped JSON; 402 means insufficient credits.

## Verification

- After any generation, confirm the output file exists and open/inspect it
  (e.g. `ffprobe` for video, image dimensions for images).
- `python scripts/xiaozhi.py status <task_id>` returns authoritative task
  state: 0=pending, 1=done, 2=failed (refunded), -1=not found.
