# OpenRouter

Read when the user picks `--provider openrouter`. Default model is `google/gemini-3.1-flash-image`.

## Common Models

Use full OpenRouter model IDs:

- `google/gemini-3.1-flash-image` (recommended — supports image output and reference-image workflows)
- `google/gemini-2.5-flash-image-preview`
- `black-forest-labs/flux.2-pro`
- Any other OpenRouter image-capable model ID

## Behavior Notes

- OpenRouter image generation uses `/chat/completions`, not the OpenAI `/images` endpoints
- `--ref` requires a multimodal model that supports both image input and image output
- `--imageSize` maps to `imageGenerationOptions.size`
- `--size <WxH>` is converted to the nearest supported OpenRouter size, and the aspect ratio is inferred when possible
