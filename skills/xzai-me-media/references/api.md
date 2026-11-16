# Xiaozhi AI API reference (for direct integration)

The CLI covers common cases. This file documents the raw endpoints for
agents that prefer calling the API directly (SDKs, MCP servers, workflows).

## Auth (two schemes — never mix)

| Endpoint family | Header |
|---|---|
| `https://xzai.me/api.php/*` | `x-token: <KEY>` |
| `https://xzai.me/v1/*` (OpenAI-compatible) | `Authorization: Bearer <KEY>` |

## Endpoints

| Capability | Endpoint |
|---|---|
| Model list | `GET /v1/models` (Bearer) |
| Chat (OpenAI-compatible: tools, stream, multimodal) | `POST /v1/chat/completions` (Bearer) |
| Chat (native) | `POST /api.php/chat/sendText` (x-token) |
| Image gen (Seedream 5.0) | `POST /api.php/draw_seedream/seedreamSubmit` → `/api.php/draw_seedream/getResult` |
| Video gen (Seedance) | `POST /api.php/video/submit` → `/api.php/video/getResult` |
| TTS | `POST /api.php/tts/text2audio` |
| Image upload (get reference URL) | `POST /api.php/upload/image` (multipart, field `image`) |

## Image submit

```json
{
  "message": "prompt text (max 2000 chars)",
  "aspect_ratio": "1:1 | 16:9 | 9:16 | 3:4 | 4:3 | 2:3 | 3:2",
  "style_key": "web_image_style_2D | web_image_style_3D | web_image_style_portrait | ...",
  "images": ["https://.../ref.jpg"],
  "cate_id": 0,
  "is_share": 0
}
```

Response: `{"errno":0,"data":{"draw_id":3305}}`. Poll getResult with
`{"draw_id": N}`.

Output size approximates the ratio but is not exact (16:9 → 2848×1600 in
testing; 1:1 → 2048×2048).

## Video submit

```json
{
  "prompt": "...",
  "platform": "seedance",
  "model": "seedance-2.0-mini",
  "aspect_ratio": "16:9",
  "duration": 15,
  "images": ["https://.../first_frame.jpg"]
}
```

- Omitting `model` = Seedance 2.0 Fast 10s (cheapest).
- `seedance-2.0-fast-15` / `seedance-2.0-mini`: 15 s, must be exact; wrong
  or missing params silently fall back to fast-10s.
- `seedance-2.5`: 30 s only; also allows 21:9; takes 4–7 min.
- fast-15 / mini take 10–20 min.
- `images`: omitted = t2v; 1 image = first-frame drive; up to 10 = multi-ref.

## Task states (video & image)

`state: 0 = generating, 1 = done (video_url / images[]), 2 = failed (auto-refund), -1 = not found`

## TTS

`{"text": "1-500 chars", "voice": "Cherry|Ethan|Chelsie|Nofish|Jennifer|Ryan|Katerina"}`
→ `data.audio_url` (WAV, expires ~24 h), `data.price`. 10 credits / 10k
chars, min 1 credit per call, no charge on failure.

## Billing

- Failed generation tasks auto-refund (state 2).
- Chat: charged only on success; text35 tier (native) / text40 per request
  (OpenAI-compatible path).
- OpenAI-compatible errors are standard OpenAI error JSON:
  400 invalid params, 401 bad key, 402 insufficient_balance, 403 channel
  closed, 404 model_not_found, 429 rate limit, 502/504 upstream.

## Chat model

Currently `glm-5.3-flash`. Context window: 1,048,576 tokens (verified
empirically; 1024k-token inputs succeed, ~1.15M rejected with 400).
Supports function calling, SSE streaming, multimodal `content` arrays.

Use with the OpenAI SDK: `base_url="https://xzai.me/v1"`,
`api_key=<XIAOZHI key>`.
