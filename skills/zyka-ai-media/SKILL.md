---
name: zyka-ai-media
description: Generate AI videos, images, and voice using the Zyka SDK (npm package 'zyka-sdk'). Use this skill when users want to create AI-generated media — videos (Sora, Veo, Kling, WAN, Seedance), images (DALL·E, GPT Image, Flux, Nano Banana, Stable Diffusion), text-to-speech (ElevenLabs, Chatterbox, Qwen3), or talking head videos. The SDK handles local file uploads, auto-polling, and auto-download automatically.
---

# Zyka AI Media Generation

Generate AI videos, images, and voice programmatically using Zyka's unified SDK. One package, 30+ AI models.

## Setup

Install the SDK from npm:
```bash
npm install zyka-sdk
```

Authentication — set your Zyka API key (get one at https://zyka.ai/settings/api-keys):
```bash
export ZYKA_API_KEY=zk_live_...
```

Or pass it directly:
```js
const { ZykaClient } = require('zyka-sdk');
const client = new ZykaClient({ apiKey: 'zk_live_...' });
```

## Key Behaviors
- **Local files** are auto-uploaded. Pass `'./photo.png'` instead of a URL.
- **Auto-wait** is on by default. `await client.createVideo(...)` returns when the video is ready.
- **Auto-download** with the `output` option: `{ output: './result.mp4' }`.

---

## Video Generation

```js
const result = await client.createVideo({
  model: 'MODEL_NAME',
  prompt: 'description of what to generate',
});
console.log(result.outputUrl);
```

### Available Video Models

| Model | `model` value | Key params |
|---|---|---|
| OpenAI Sora | `sora` | `sub_model: 'sora-2'`, `seconds: '4'/'8'/'12'`, `size: '1280x720'` |
| Google Veo | `veo` | `sub_model: 'veo-3.0-generate-001'`, `seconds: '4'-'8'`, `aspect_ratio: '16:9'/'9:16'` |
| Kling AI | `kling` | `sub_model: 'kling-v2-master'`, `duration: '5'/'10'`, `aspect_ratio: '16:9'` |
| ByteDance Seedance | `bytedance` | `sub_model: 'Seedance V1.5 Pro'`, `duration: '4'-'12'`, `resolution: '1080p'` |
| Alibaba WAN | `wan` | `sub_model: 'wan-2-6-t2v'`, `duration: 5/10/15` |
| Talking Head | `infinite_talk` | `image_url: './face.jpg'`, `audio_url: './speech.mp3'` |

### Examples

**Text to video:**
```js
await client.createVideo({
  model: 'wan',
  prompt: 'A cinematic sunset over mountains with golden light',
  duration: 5
});
```

**Image to video (animate a photo):**
```js
await client.createVideo({
  model: 'kling',
  sub_model: 'kling-v2-master',
  prompt: 'gentle camera zoom in with wind blowing',
  image_url: './photo.jpg',
  duration: '5',
  aspect_ratio: '16:9'
});
```

**Talking head (lip sync a face with audio):**
```js
await client.createVideo({
  model: 'infinite_talk',
  image_url: './face.jpg',
  audio_url: './speech.mp3'
});
```

---

## Image Generation

```js
const result = await client.createImage({
  model: 'MODEL_NAME',
  prompt: 'description',
}, { output: './result.png' });
```

### Available Image Models

| Model | `model` value | Notes |
|---|---|---|
| Nano Banana | `nano_banana` | Sub-models: `nano-banana-1`, `nano-banana-pro`. Great for edits. |
| DALL·E 3 | `dall_e_3` | Quality: `'standard'`/`'hd'` |
| GPT Image 1 | `gpt_image_1` | Supports `background: 'transparent'` |
| GPT Image 1.5 | `gpt_image_1_5` | Latest OpenAI model |
| Flux Schnell | `flux_1_schnell` | Fast generation |
| Flux 2 Dev | `flux_2_dev` | High quality |
| Kling Image | `kling` | Sub-models: `kling-v1` to `kling-image-v3` |
| Stable Diffusion XL | `stable_diffusion_xl_base_1_0` | Classic SD |
| SD 1.5 img2img | `stable_diffusion_v1_5_img2img` | Requires `image` input |
| Z Image Turbo | `z_image_turbo` | Fast |

### Examples

**Generate from text:**
```js
await client.createImage({
  model: 'gpt_image_1',
  prompt: 'A neon-lit cyberpunk cityscape at night'
}, { output: './city.png' });
```

**Edit an existing image:**
```js
await client.createImage({
  model: 'nano_banana',
  sub_model: 'nano-banana-pro',
  image: './photo.png',
  prompt: 'make the background a tropical beach'
}, { output: './edited.png' });
```

**Transparent background:**
```js
await client.createImage({
  model: 'gpt_image_1',
  prompt: 'a cute cartoon cat mascot',
  background: 'transparent'
}, { output: './mascot.png' });
```

---

## Text-to-Speech (TTS)

```js
const result = await client.createTTS({
  provider: 'PROVIDER_NAME',
  script: 'Text to speak',
});
```

### Available TTS Providers

| Provider | `provider` value | Notes |
|---|---|---|
| ElevenLabs | `elevenlabs` | Requires `voice_id` |
| Qwen3 | `qwen3` | Voice design, clone, custom |
| Chatterbox | `chatterbox` | Voice cloning + emotion control |
| VoxCPM | `voxcpm` | Voice cloning |
| MiniMax | `minimax` | 17 preset voices |

### Examples

**Generate speech:**
```js
await client.createTTS({
  provider: 'elevenlabs',
  voice_id: 'voice-id-here',
  script: 'Welcome to Zyka, the AI media generation platform.'
}, { output: './speech.mp3' });
```

**Clone a voice:**
```js
await client.createTTS({
  provider: 'chatterbox',
  actual_voice_url: './my-voice.mp3',
  script: 'This sounds just like me!',
  exaggeration: 0.5
}, { output: './cloned.mp3' });
```

---

## Guidelines

- Always install `zyka-sdk` from npm before using it: `npm install zyka-sdk`
- Always set `ZYKA_API_KEY` environment variable or pass `apiKey` in the constructor
- Prefer passing local file paths (e.g., `'./photo.png'`) — the SDK auto-uploads them
- Use the `output` option to automatically download results to disk
- All generation methods auto-wait for completion by default — no polling code needed
- When the user asks to edit an image, use `nano_banana` with `sub_model: 'nano-banana-pro'`
- When the user asks for a video from text, default to the `wan` model
- When the user asks for image-to-video, default to the `kling` model

## API Reference

| Method | Description |
|---|---|
| `client.createVideo(params, opts?)` | Video generation (auto-waits for completion) |
| `client.createImage(params, opts?)` | Image generation (auto-waits for completion) |
| `client.createTTS(params, opts?)` | Text-to-speech generation (auto-waits for completion) |

**Options:** `{ waitForCompletion?: boolean, output?: string, timeoutMs?: number }`

## Auth Priority
1. `config.apiKey` → 2. `ZYKA_API_KEY` env → 3. `config.token` → 4. `ZYKA_API_TOKEN` env → 5. `~/.zyka/config.json`
