---
name: vap-media
description: Use this skill whenever the user wants to generate or edit AI media content including images, videos, and music. This includes creating images from text descriptions, generating video content, producing music tracks, editing images (inpainting, upscaling, background removal), and video editing (trimming, merging). Use for both free trial generations (3 per day without API key) and full-featured generation with a VAP_API_KEY.
---

# VAP Media - AI Media Generation & Editing

Generate images, videos, and music using state-of-the-art AI models (Flux for images, Veo 3.1 for video, Suno V5 for music). Edit media with inpainting, AI editing, upscaling, background removal, video trimming, and merging.

## Mode Selection

Check if `VAP_API_KEY` environment variable is set:

- **VAP_API_KEY not set** → Use Free Mode (images only, 3 per day)
- **VAP_API_KEY set** → Use Full Mode (all features, unlimited)

---

## Free Mode (No API Key Required)

Generate images for free without signup. Limited to 3 generations per day.

### Generate Image

```bash
curl -s -X POST https://api.vapagent.com/v3/trial/generate \
  -H "Content-Type: application/json" \
  -d '{"prompt":"PROMPT"}'
```

Returns: `{"task_id":"UUID","status":"pending","remaining":2}`

### Poll for Result

```bash
curl -s https://api.vapagent.com/v3/trial/status/TASK_ID
```

Returns: `{"status":"completed","image_url":"https://..."}` when done.

### Free Mode Error Handling

- `429` → Daily limit reached. Suggest upgrading to full mode with API key.
- `503` → Trial service temporarily unavailable.

---

## Full Mode (Requires VAP_API_KEY)

Unlimited access to all features including video generation, music creation, and editing operations.

### Create Task

```bash
curl -s -X POST https://api.vapagent.com/v3/tasks \
  -H "Authorization: Bearer $VAP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"type":"TYPE","params":{"description":"PROMPT"}}'
```

Returns: `{"task_id":"UUID","status":"pending"}`

### Poll Task Result

```bash
curl -s https://api.vapagent.com/v3/tasks/TASK_ID \
  -H "Authorization: Bearer $VAP_API_KEY"
```

Returns: `{"status":"completed","result":{"output_url":"https://..."}}` when done.

### Task Types and Parameters

#### Image Generation (`image` or `image_generation`)

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `description` | string | required | Detailed image description |
| `aspect_ratio` | enum | `1:1` | `1:1`, `16:9`, `9:16`, `4:3`, `3:4`, `3:2`, `2:3`, `21:9`, `9:21` |
| `quality` | enum | `standard` | `standard` or `high` |

**Tip:** Aspect ratio is auto-detected from prompt keywords like "widescreen", "portrait", "16:9".

#### Video Generation (`video` or `video_generation`) — Tier 2+

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `description` | string | required | Video scene description |
| `duration` | int | `8` | `4`, `6`, or `8` seconds |
| `aspect_ratio` | enum | `16:9` | `16:9` (landscape) or `9:16` (portrait) |
| `generate_audio` | bool | `true` | Include AI-generated audio |
| `resolution` | enum | `720p` | `720p` or `1080p` |
| `negative_prompt` | string | `""` | Elements to exclude |

#### Music Generation (`music` or `music_generation`) — Tier 2+

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `description` | string | required | Genre, mood, instruments description |
| `duration` | int | `120` | 30-480 seconds |
| `instrumental` | bool | `false` | Generate without vocals |
| `audio_format` | enum | `mp3` | `mp3` or `wav` (lossless) |
| `loudness_preset` | enum | `streaming` | `streaming`, `apple`, or `broadcast` |
| `style` | string | none | Genre/style (max 1000 chars) |
| `title` | string | none | Song title |
| `custom_mode` | bool | `false` | Enable custom lyrics mode |

### Full Mode Error Handling

- `401` → Invalid API key. Check VAP_API_KEY value.
- `402` → Insufficient balance. User needs to add funds.
- `403` → Tier too low. Upgrade required for video/music.

---

## Media Editing Operations

Post-production editing for existing media. Requires Tier 1+.

### Create Operation

```bash
curl -s -X POST https://api.vapagent.com/v3/operations \
  -H "Authorization: Bearer $VAP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"operation":"OPERATION","media_url":"URL","prompt":"INSTRUCTION"}'
```

### Poll Operation Result

```bash
curl -s https://api.vapagent.com/v3/operations/OPERATION_ID \
  -H "Authorization: Bearer $VAP_API_KEY"
```

### Available Operations

| Operation | Required Parameters | Description |
|-----------|---------------------|-------------|
| `inpaint` | `media_url`, `prompt` | AI-powered image editing with mask support |
| `ai_edit` | `media_url`, `prompt` | Text-guided image editing |
| `background_remove` | `media_url` | Automatic background removal |
| `upscale` | `media_url` | Resolution enhancement (`scale`: 2 or 4) |
| `video_trim` | `media_url`, `start_time`, `end_time` | Extract video segment |
| `video_merge` | `media_urls` (array, min 2) | Combine multiple videos |

---

## Production Presets (Multi-Asset Campaigns)

Generate complete content packages from a single prompt using `/v3/execute`:

```bash
curl -s -X POST https://api.vapagent.com/v3/execute \
  -H "Authorization: Bearer $VAP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"preset":"streaming_campaign","prompt":"PROMPT"}'
```

Returns all assets: `{"status":"completed","outputs":{"video":"...","music":"...","thumbnail":"..."}}`

| Preset | Output |
|--------|--------|
| `streaming_campaign` | video + music + thumbnail + metadata |
| `full_production` | video + music + thumbnail + metadata + SEO |
| `video.basic` | video only |
| `music.basic` | music only |
| `image.basic` | image only |

---

## Usage Instructions

### For Image/Video/Music Generation:

1. **Enhance the prompt** — Add style, lighting, composition, and mood details
2. **Check mode** — Determine if VAP_API_KEY is available
3. **Select endpoint:**
   - Single asset → `/v3/tasks` (or `/v3/trial/generate` for free mode)
   - Multi-asset campaign → `/v3/execute` with preset
4. **Choose aspect ratio** — Match content platform (9:16 for TikTok/Reels, 16:9 for YouTube)
5. **Poll for completion** — Check status until `completed`
6. **Return media URL** to user
7. **Handle limits** — If free mode limit hit, guide user to get API key

### For Media Editing:

1. **Identify operation** — inpaint, upscale, background_remove, trim, merge
2. **Get source media URL** — From previous generation or user-provided
3. **Submit to `/v3/operations`**
4. **Poll and return output URL**

---

## Code Examples

### Free Mode Image Generation

```bash
# Generate image
curl -s -X POST https://api.vapagent.com/v3/trial/generate \
  -H "Content-Type: application/json" \
  -d '{"prompt":"A serene mountain lake at sunrise, mist rising, photorealistic, golden hour lighting"}'

# Poll for result
curl -s https://api.vapagent.com/v3/trial/status/TASK_ID
```

### Full Mode Examples

```bash
# Widescreen image for desktop wallpaper
curl -s -X POST https://api.vapagent.com/v3/tasks \
  -H "Authorization: Bearer $VAP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"type":"image","params":{"description":"Cyberpunk cityscape at night, neon lights reflecting on wet streets, high detail","aspect_ratio":"21:9","quality":"high"}}'

# Portrait video for social media
curl -s -X POST https://api.vapagent.com/v3/tasks \
  -H "Authorization: Bearer $VAP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"type":"video","params":{"description":"Aerial drone shot rising above tropical beach, crystal clear water","duration":8,"aspect_ratio":"9:16","resolution":"1080p"}}'

# Background music for content
curl -s -X POST https://api.vapagent.com/v3/tasks \
  -H "Authorization: Bearer $VAP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"type":"music","params":{"description":"Energetic electronic dance track, festival vibes, driving bass","duration":180,"instrumental":true}}'

# Remove background from product photo
curl -s -X POST https://api.vapagent.com/v3/operations \
  -H "Authorization: Bearer $VAP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"operation":"background_remove","media_url":"https://example.com/product.jpg"}'

# Upscale image 4x
curl -s -X POST https://api.vapagent.com/v3/operations \
  -H "Authorization: Bearer $VAP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"operation":"upscale","media_url":"https://example.com/photo.jpg","options":{"scale":4}}'
```

---

## Prompt Engineering Tips

### Style Keywords
- Visual: "oil painting", "3D render", "watercolor", "photograph", "flat illustration", "anime"
- Lighting: "golden hour", "neon lights", "soft diffused", "dramatic shadows", "studio lighting"
- Composition: "close-up", "aerial view", "wide angle", "rule of thirds", "macro shot"
- Mood: "serene", "energetic", "mysterious", "whimsical", "melancholic", "epic"

### Music Prompts
- Genre: "lo-fi hip hop", "cinematic orchestral", "ambient electronic", "acoustic folk"
- Mood: "upbeat and cheerful", "dark and brooding", "relaxing meditation", "intense action"
- Instruments: "piano and strings", "synthesizers and drums", "acoustic guitar"

---

## Setup

### Free Mode
No setup required. Start generating immediately with rate limits.

### Full Mode

1. Sign up at: https://vapagent.com/dashboard/signup.html
2. Get API key from dashboard
3. Set environment variable:
   ```bash
   export VAP_API_KEY=vap_xxxxxxxxxxxxxxxxxxxx
   ```

---

## Resources

- Free Trial: https://vapagent.com/try
- API Documentation: https://api.vapagent.com/docs
- GitHub: https://github.com/vapagentmedia/vap-showcase
