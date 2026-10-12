---
name: zyka-ai-media
description: Generate AI videos, images, and voice using the Zyka CLI (npm package 'zyka'). Use this skill when users want to create AI-generated media — videos (Sora, Veo, Kling, WAN, Seedance), images (DALL·E, GPT Image, Flux, Nano Banana, Stable Diffusion), text-to-speech (ElevenLabs, Chatterbox, Qwen3), or talking head videos. Run CLI commands directly — no code needed.
---

# Zyka AI Media Generation

Generate AI videos, images, and voice directly from the terminal using the `zyka` CLI. One command, 30+ AI models. No code writing required.

## Setup

The CLI is available via npx (no install needed) or can be installed globally:
```bash
npx zyka --help
# or install globally:
npm install -g zyka
```

Set your API key:
```bash
export ZYKA_API_KEY=zk_live_...
```

Users can get an API key at https://zyka.ai/settings/api-keys

## IMPORTANT: Always use CLI commands, never write code scripts

When a user asks to generate media, **run the `npx zyka generate` command directly** — do NOT write JavaScript files or scripts. The CLI handles everything: file uploads, waiting for completion, and downloading results.

---

## Generate Videos

```bash
npx zyka generate video -m MODEL -p "prompt" [options]
```

### Video Models
| Model | `-m` value | Key options |
|---|---|---|
| OpenAI Sora | `sora` | `-s sora-2`, `-d 4/8/12` |
| Google Veo | `veo` | `-s veo-3.0-generate-001`, `-d 4-8`, `-a 16:9/9:16` |
| Kling AI | `kling` | `-s kling-v2-master`, `-d 5/10`, `-a 16:9` |
| ByteDance Seedance | `bytedance` | `-s "Seedance V1.5 Pro"`, `-d 4-12` |
| Alibaba WAN | `wan` | `-s wan-2-6-t2v`, `-d 5/10/15` |
| Talking Head | `infinite_talk` | `--image ./face.jpg --audio ./speech.mp3` |

### Video Examples

**Text to video:**
```bash
npx zyka generate video -m wan -p "A cinematic sunset over mountains" -d 5 -o ./sunset.mp4
```

**Image to video (animate a photo):**
```bash
npx zyka generate video -m kling -s kling-v2-master -p "gentle zoom in with wind" --image ./photo.jpg -d 5 -a 16:9 -o ./animated.mp4
```

**Talking head (lip sync):**
```bash
npx zyka generate video -m infinite_talk -p "lip sync" --image ./face.jpg --audio ./speech.mp3 -o ./talking.mp4
```

---

## Generate Images

```bash
npx zyka generate image -m MODEL -p "prompt" [options]
```

### Image Models
| Model | `-m` value | Notes |
|---|---|---|
| Nano Banana | `nano_banana` | `-s nano-banana-pro` for edits |
| DALL·E 3 | `dall_e_3` | High quality |
| GPT Image 1 | `gpt_image_1` | Supports transparency |
| GPT Image 1.5 | `gpt_image_1_5` | Latest OpenAI |
| Flux Schnell | `flux_1_schnell` | Fast |
| Flux 2 Dev | `flux_2_dev` | High quality |
| Kling Image | `kling` | `-s kling-image-v3` |
| Stable Diffusion XL | `stable_diffusion_xl_base_1_0` | Classic SD |
| SD img2img | `stable_diffusion_v1_5_img2img` | Needs `--image` |
| Z Image Turbo | `z_image_turbo` | Fast |

### Image Examples

**Generate from text:**
```bash
npx zyka generate image -m gpt_image_1 -p "A neon cyberpunk cityscape" -o ./city.png
```

**Edit an existing image:**
```bash
npx zyka generate image -m nano_banana -s nano-banana-pro -p "make the hair straight" --image ./me.png -o ./result.png
```

**Edit a photo (change style):**
```bash
npx zyka generate image -m nano_banana -s nano-banana-pro -p "make it look cinematic" --image ./photo.png -o ./cinematic.png
```

---

## Generate Text-to-Speech

```bash
npx zyka generate tts --script "text" [options]
```

### TTS Providers
| Provider | `--provider` value | Notes |
|---|---|---|
| ElevenLabs | `elevenlabs` | Needs `--voice-id` |
| Qwen3 | `qwen3` | Voice design/clone |
| Chatterbox | `chatterbox` | Clone + emotion |
| MiniMax | `minimax` | 17 preset voices |

### TTS Examples

**Generate speech:**
```bash
npx zyka generate tts --provider elevenlabs --voice-id VOICE_ID --script "Welcome to Zyka" -o ./speech.mp3
```

**Clone a voice:**
```bash
npx zyka generate tts --provider chatterbox --voice ./my-voice.mp3 --script "This sounds like me" -o ./cloned.mp3
```

---

## Guidelines

- **ALWAYS use `npx zyka generate` CLI commands** — never write JavaScript files
- Set `ZYKA_API_KEY` env var before running commands
- Use `-o ./filename` to save results to disk (auto-downloads)
- Use `--image ./path` to pass local image files (auto-uploads)
- Use `--audio ./path` to pass local audio files (auto-uploads)
- All commands auto-wait for completion — no polling needed
- When editing images, default to `-m nano_banana -s nano-banana-pro`
- When generating videos from text, default to `-m wan`
- When animating images to video, default to `-m kling`

## CLI Options Reference

| Flag | Description |
|---|---|
| `-m, --model` | Model name (required for video/image) |
| `-p, --prompt` | Text prompt (required) |
| `-s, --sub-model` | Model variant |
| `-d, --duration` | Video duration in seconds |
| `-a, --aspect-ratio` | Aspect ratio (16:9, 9:16, 1:1) |
| `--image` | Input image path (for editing/animating) |
| `--audio` | Input audio path (for talking heads) |
| `-o, --output` | Save result to this file path |
| `--no-wait` | Don't wait for completion |
