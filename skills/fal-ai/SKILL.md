---
name: fal-ai
description: Generate images, videos, and audio using the fal.ai API. Use when the user works with fal.ai, fal_client, @fal-ai/client, Flux Pro, Kling video, or mentions AI image/video generation with fal.
license: MIT
compatibility: Designed for Claude Code on macOS and Linux
---

# fal.ai — Image, Video & Audio Generation

Generate images, videos, and audio using fal.ai's model library (600+ models). Covers Python and JavaScript SDKs, model selection, prompt engineering, and production patterns.

## Setup

**Python:**
```bash
pip install fal-client
```
```python
import fal_client
# Requires FAL_KEY environment variable
```

**JavaScript/TypeScript:**
```bash
npm install @fal-ai/client
```
```javascript
import * as fal from "@fal-ai/client";
// Requires FAL_KEY environment variable
```

## Models — Quick Reference

### Image Generation
| Model | ID | Speed | Best For |
|-------|-----|-------|----------|
| Flux Pro v1.1 | `fal-ai/flux-pro/v1.1` | ~3-6s | Production images |
| Flux Pro Ultra | `fal-ai/flux-pro/v1.1-ultra` | ~8-12s | Maximum detail |
| Flux Schnell | `fal-ai/flux/schnell` | ~1-4s | Fast prototyping |
| Flux Dev | `fal-ai/flux/dev` | ~3-5s | Balanced quality/speed |

### Video Generation
| Model | ID | Best For |
|-------|-----|----------|
| Kling 1.6 T2V | `fal-ai/kling-video/v1.6/standard/text-to-video` | Text to video |
| Kling 1.6 I2V | `fal-ai/kling-video/v1.6/standard/image-to-video` | Animate a still image |
| Kling 2.6 Pro | `fal-ai/kling-video/v2.6/pro/image-to-video` | Professional quality |

### Audio
| Model | ID | Best For |
|-------|-----|----------|
| ElevenLabs TTS | `fal-ai/elevenlabs/tts/multilingual-v2` | Text to speech |

## Image Generation

### Python
```python
result = fal_client.subscribe(
    "fal-ai/flux-pro/v1.1",
    arguments={
        "prompt": "dark figure dissolving into void, motion blur, crushed blacks, cinematic B&W",
        "image_size": "square_hd",
        "num_images": 1,
        "num_inference_steps": 28,
        "guidance_scale": 3.5,
        "enable_safety_checker": False,
    },
)
image_url = result["images"][0]["url"]
```

### JavaScript
```javascript
const result = await fal.run("fal-ai/flux-pro/v1.1", {
  input: {
    prompt: "dark figure dissolving into void, motion blur, crushed blacks, cinematic B&W",
    image_size: "square_hd",
    num_images: 1,
    num_inference_steps: 28,
    guidance_scale: 3.5,
    enable_safety_checker: false,
  },
});
const imageUrl = result.images[0].url;
```

### Image Size Options
- Presets: `square_hd`, `square`, `portrait_4_3`, `portrait_16_9`, `landscape_4_3`, `landscape_16_9`
- Custom: `{ "width": 1080, "height": 1350 }` (must be multiples of 8)

### Parameters
| Param | Default | Range | Effect |
|-------|---------|-------|--------|
| `num_inference_steps` | 28 | 10-50 | Quality (higher = slower + better) |
| `guidance_scale` | 3.5 | 1-10 | Prompt adherence (lower = creative) |
| `num_images` | 1 | 1-4 | Batch size |
| `seed` | random | any int | Reproducibility |

## Video Generation

### Image-to-Video (recommended — better quality)
```python
result = fal_client.subscribe(
    "fal-ai/kling-video/v1.6/standard/image-to-video",
    arguments={
        "prompt": "slow camera drift, subtle motion blur, atmospheric",
        "image_url": "https://v3.fal.media/files/...",
        "duration": "5",
        "aspect_ratio": "9:16",
    },
)
video_url = result["video"]["url"]
```

### Text-to-Video
```python
result = fal_client.subscribe(
    "fal-ai/kling-video/v1.6/standard/text-to-video",
    arguments={
        "prompt": "dark figure walking through fog, cinematic slow motion",
        "duration": "5",
        "aspect_ratio": "16:9",
    },
)
```

### Duration & Aspect
- Duration: `"5"` or `"10"` seconds (5s produces more focused results)
- Aspect: `"16:9"`, `"9:16"`, `"1:1"`

## File Upload

Upload local files to fal CDN for use in image-to-video or image-to-image:

```python
cdn_url = fal_client.upload_file("path/to/image.png")
# Returns: https://v3.fal.media/files/{prefix}/{id}.{ext}
```

```javascript
const cdnUrl = await fal.storage.upload(file);
```

## Async / Queue Pattern

For long-running tasks (video generation), use the queue:

### Python
```python
# Submit to queue
handle = fal_client.submit(
    "fal-ai/kling-video/v1.6/standard/image-to-video",
    arguments={...},
)

# Check status
status = fal_client.status("fal-ai/kling-video/v1.6/standard/image-to-video", handle.request_id)

# Get result when done
result = fal_client.result("fal-ai/kling-video/v1.6/standard/image-to-video", handle.request_id)
```

### JavaScript
```javascript
const handle = await fal.queue.submit("fal-ai/kling-video/v1.6/standard/image-to-video", {
  input: {...},
});

// Stream status updates
for await (const status of fal.queue.streamStatus(handle.request_id)) {
  console.log(status);
}

const result = await fal.queue.result(handle.request_id);
```

## Webhook Pattern

```python
fal_client.subscribe(
    "fal-ai/flux-pro/v1.1",
    arguments={...},
    webhook_url="https://your-server.com/webhook/fal",
)
# Server receives POST with:
# Header: X-Fal-Webhook-Signature (verify for security)
# Body: { "request_id": "...", "status": "OK", "result": {...} }
```

## Timeout & Error Handling

### Python — Timeout Wrapper
```python
import concurrent.futures

def fal_with_timeout(model, arguments, timeout=300):
    with concurrent.futures.ThreadPoolExecutor(max_workers=1) as executor:
        future = executor.submit(fal_client.subscribe, model, arguments=arguments)
        try:
            return future.result(timeout=timeout)
        except concurrent.futures.TimeoutError:
            raise TimeoutError(f"fal.ai {model} timed out after {timeout}s")
```

### Error Types
```python
try:
    result = fal_client.subscribe(model, arguments=args)
except fal_client.ValidationError:
    # Content policy violation or bad params — don't retry
    pass
except fal_client.RateLimitError:
    # Too many requests — exponential backoff
    import time, random
    time.sleep((2 ** attempt) + random.uniform(0, 1))
except fal_client.FalClientTimeoutError:
    # Timeout — may be transient, retry
    pass
```

The platform auto-retries up to 10 times on 503/504/connection errors.

## Rate Limits

- New accounts: 2 concurrent requests
- Scales up to 40 as you purchase credits
- Requests exceeding the limit are queued automatically

## Prompt Engineering

### Structure
```
[Subject] + [Environment/Mood] + [Style] + [Technical/Camera]
```

### Example
```
dark figure dissolving into void, motion blur and ghosting,
crushed blacks and high contrast | moody electronic aesthetic |
wide frame from waist up | 28mm lens, cinematic, B&W editorial
```

### Tips
- Keep under 100 words — every word should serve a purpose
- Be specific about lighting: "golden hour", "dramatic side lighting", "soft diffused"
- Style modifiers: "cinematic", "photorealistic", "editorial", "minimalist"
- Camera language: "28mm lens", "macro", "aerial view", "shallow depth of field"
- Flux models don't support `negative_prompt` — describe what you want, not what to avoid

## Response Structure

### Image
```json
{
  "images": [{ "url": "https://v3.fal.media/...", "width": 1024, "height": 1024 }],
  "seed": 12345
}
```

### Video
```json
{
  "video": { "url": "https://v3.fal.media/...", "content_type": "video/mp4" }
}
```

CDN URLs persist and are reusable across requests.
