# Replicate

Read when the user picks `--provider replicate`. Replicate support is intentionally scoped to model families baoyu-image-gen can validate locally and save without dropping outputs.

## Supported Families

**`google/nano-banana*`** (default: `google/nano-banana-2`)

- Supports prompt-only and reference-image generation
- Uses Replicate `aspect_ratio`, `resolution`, and `output_format`
- `--size <WxH>` is accepted only as a shorthand for a documented `aspect_ratio` plus `1K` / `2K`

**`bytedance/seedream-4.5`**

- Supports prompt-only and reference-image generation
- Uses Replicate `size`, `aspect_ratio`, and `image_input`
- Local validation blocks unsupported `1K` requests before the API call

**`bytedance/seedream-5-lite`**

- Supports prompt-only and reference-image generation
- Uses Replicate `size`, `aspect_ratio`, and `image_input`
- Local validation currently accepts `2K` / `3K` only

**`wan-video/wan-2.7-image`**

- Supports prompt-only and reference-image generation
- Uses Replicate `size` and `images`
- Max output is 2K

**`wan-video/wan-2.7-image-pro`**

- Supports prompt-only and reference-image generation
- Uses Replicate `size` and `images`
- 4K is allowed only for text-to-image; local validation blocks `4K + --ref`

## Guardrails

- Replicate currently supports only single-output save semantics in this tool — keep `--n 1`
- If a model is outside the compatibility list above, baoyu-image-gen treats it as prompt-only and rejects advanced local options instead of guessing a nano-banana-style schema

## Examples

```bash
# Default model
${BUN_X} {baseDir}/scripts/main.ts --prompt "A cat" --image out.png --provider replicate

# Explicit model
${BUN_X} {baseDir}/scripts/main.ts --prompt "A cat" --image out.png --provider replicate --model google/nano-banana
```
