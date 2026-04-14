---
name: dlazy-generate
version: 1.0.0
description: A comprehensive generation skill. Can generate images, videos, and audio by automatically selecting the appropriate dlazy CLI model.
metadata: {"clawdbot":{"emoji":"🤖","requires":{"bins":["npm","npx"]},"install":"npm install -g @dlazy/cli"},"openclaw":{"systemPrompt":"When this skill is called, automatically select the corresponding dlazy subcommand."}}
---

# dlazy-generate

A comprehensive generation skill. Can generate images, videos, and audio by automatically selecting the appropriate dlazy CLI model.

## Trigger Keywords

- generate
- create image, video, audio
- multimodal generation

## Usage

This is a comprehensive skill that routes generation requests to the appropriate `dlazy` model based on the user's intent.

### Available Models by Category

**Image Generation:**
- `dlazy seedream-4.5`: High-quality realism/posters.
- `dlazy seedream-5.0-lite`: Fast, low-cost sketches.
- `dlazy banana2`, `dlazy banana-pro`: General text-to-image.
- `dlazy grok-4.2`: Minimalist.
- `dlazy recraft-v3`: Stylized (illustration).
- `dlazy recraft-v3-svg`: SVG/vector.
- `dlazy mj.imagine`: Midjourney style.
- `dlazy kling-image-o1`, `dlazy viduq2-t2i`, `dlazy jimeng-t2i`: Other specific high-quality image models.

**Video Generation:**
- `dlazy veo-3.1`, `dlazy veo-3.1-fast`: High-quality cinematic sequences.
- `dlazy sora-2`, `dlazy sora-2-pro`: Narrative clips.
- `dlazy kling-v3`, `dlazy kling-v3-omni`: General short clips.
- `dlazy seedance-1.5-pro`: Narrative shorts with transitions.
- `dlazy wan2.6-r2v`, `dlazy wan2.6-r2v-flash`: General/fast video production.
- `dlazy viduq2-i2v`, `dlazy jimeng-i2v-first`, `dlazy jimeng-i2v-first-tail`, `dlazy jimeng-dream-actor`, `dlazy jimeng-omnihuman-1.5`: Image-to-video, digital human, action transfer.

**Audio Generation:**
- `dlazy gemini-2.5-tts`, `dlazy doubao-tts`, `dlazy keling-tts`: Text-to-speech.
- `dlazy suno.music`: Music generation.
- `dlazy keling-sfx`: Sound effects.
- `dlazy vidu-audio-clone`, `dlazy kling-audio-clone`: Voice cloning.

**CRITICAL INSTRUCTION FOR AGENT**: 
1. Determine the media type (image, video, or audio) requested by the user.
2. Select the most appropriate model from the list above.
3. Run `dlazy <model_name> -h` to check the required parameters for that specific model.
4. Execute the command (e.g., `dlazy seedream-4.5 --prompt "..."`).
5. If the output returns `code: 503` and indicates insufficient balance, you MUST inform the user that their credits are insufficient and provide them with this link to recharge: [https://dlazy.com/zh-CN/dashboard/organization/settings?tab=credits](https://dlazy.com/zh-CN/dashboard/organization/settings?tab=credits)


## Error Handling

| Code | Error Type                         | Example Message                                                                                                          |
| ---- | ---------------------------------- | ------------------------------------------------------------------------------------------------------------------------ |
| 501  | Missing required parameter         | `error: required option '--prompt <prompt>' not specified`                                                              |
| 502  | Local file read error              | `Error: Image file/Video file not found: C:\path\to\your\file`                                                          |
| 503  | API request failed (no balance)    | `Error during API request: Request failed with status code 400` / `Response details: {"error": "Insufficient balance"}` |
| 503  | API request failed (server error)  | `HTTP status code error (500 server crash)`                                                                             |
| 504  | Asynchronous task execution failed | `=== Generation Failed ===` / `{Specific error reason returned by backend, for example "Prompt violates safety policy"}` |

## Tips

Visit https://dlazy.com for more information.
