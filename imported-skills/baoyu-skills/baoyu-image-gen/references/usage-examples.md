# Usage Examples

Extended CLI examples. SKILL.md shows the minimum set; read this file when the user asks about provider-specific invocation, batch generation, or less-common flags.

## Core Patterns

```bash
# Basic text-to-image
${BUN_X} {baseDir}/scripts/main.ts --prompt "A cat" --image cat.png

# With aspect ratio
${BUN_X} {baseDir}/scripts/main.ts --prompt "A landscape" --image out.png --ar 16:9

# High quality
${BUN_X} {baseDir}/scripts/main.ts --prompt "A cat" --image out.png --quality 2k

# Prompt from files
${BUN_X} {baseDir}/scripts/main.ts --promptfiles system.md content.md --image out.png

# With reference images (any provider family that supports refs)
${BUN_X} {baseDir}/scripts/main.ts --prompt "Make blue" --image out.png --ref source.png
```

## Per-Provider

```bash
# OpenAI
${BUN_X} {baseDir}/scripts/main.ts --prompt "A cat" --image out.png --provider openai --model gpt-image-2

# Azure OpenAI (model = deployment name)
${BUN_X} {baseDir}/scripts/main.ts --prompt "A cat" --image out.png --provider azure --model gpt-image-2

# OpenAI GPT Image 2 custom 4K size
${BUN_X} {baseDir}/scripts/main.ts --prompt "A cinematic landscape" --image out.png --provider openai --model gpt-image-2 --size 3840x2160

# Google with explicit model
${BUN_X} {baseDir}/scripts/main.ts --prompt "Make blue" --image out.png --provider google --model gemini-3-pro-image --ref source.png

# OpenRouter (recommended default)
${BUN_X} {baseDir}/scripts/main.ts --prompt "A cat" --image out.png --provider openrouter

# OpenRouter with reference
${BUN_X} {baseDir}/scripts/main.ts --prompt "Make blue" --image out.png --provider openrouter --model google/gemini-3.1-flash-image --ref source.png

# DashScope (default model)
${BUN_X} {baseDir}/scripts/main.ts --prompt "一只可爱的猫" --image out.png --provider dashscope

# DashScope Qwen-Image 2.0 Pro (custom size, Chinese text)
${BUN_X} {baseDir}/scripts/main.ts --prompt "为咖啡品牌设计一张 21:9 横幅海报，包含清晰中文标题" --image out.png --provider dashscope --model qwen-image-2.0-pro --size 2048x872

# DashScope legacy fixed-size
${BUN_X} {baseDir}/scripts/main.ts --prompt "一张电影感海报" --image out.png --provider dashscope --model qwen-image-max --size 1664x928

# DashScope Wan 2.7 Image Pro (4K text-to-image)
${BUN_X} {baseDir}/scripts/main.ts --prompt "一间有着精致窗户的花店" --image out.png --provider dashscope --model wan2.7-image-pro --size 4096x4096

# DashScope Wan 2.7 Image with reference image (multi-image fusion)
${BUN_X} {baseDir}/scripts/main.ts --prompt "把图2的涂鸦喷绘在图1的汽车上" --image out.png --provider dashscope --model wan2.7-image-pro --ref car.webp paint.webp

# Z.AI GLM-image
${BUN_X} {baseDir}/scripts/main.ts --prompt "一张带清晰中文标题的科技海报" --image out.png --provider zai

# Z.AI with custom size
${BUN_X} {baseDir}/scripts/main.ts --prompt "A science illustration with labels" --image out.png --provider zai --model glm-image --size 1472x1088

# MiniMax
${BUN_X} {baseDir}/scripts/main.ts --prompt "A fashion editorial portrait" --image out.jpg --provider minimax

# MiniMax with subject reference (character/portrait consistency)
${BUN_X} {baseDir}/scripts/main.ts --prompt "A girl by the library window" --image out.jpg --provider minimax --model image-01 --ref portrait.png --ar 16:9

# Replicate (default: google/nano-banana-2)
${BUN_X} {baseDir}/scripts/main.ts --prompt "A cat" --image out.png --provider replicate

# Replicate Seedream 4.5
${BUN_X} {baseDir}/scripts/main.ts --prompt "A cinematic portrait" --image out.png --provider replicate --model bytedance/seedream-4.5 --ar 3:2

# Replicate Wan 2.7 Image Pro
${BUN_X} {baseDir}/scripts/main.ts --prompt "A concept frame" --image out.png --provider replicate --model wan-video/wan-2.7-image-pro --size 2048x1152

# Codex CLI (uses Codex / ChatGPT subscription — no OPENAI_API_KEY; requires `codex` on PATH and `codex login`)
${BUN_X} {baseDir}/scripts/main.ts --prompt "A cinematic portrait" --image out.png --provider codex-cli --ar 16:9

# Codex CLI with reference images (style/composition guidance)
${BUN_X} {baseDir}/scripts/main.ts --prompt "Match this color palette" --image out.png --provider codex-cli --ref source.png --ar 1:1

# Agnes (default model)
${BUN_X} {baseDir}/scripts/main.ts --prompt "A detailed infographic" --image out.png --provider agnes

# Agnes with aspect ratio and URL output
${BUN_X} {baseDir}/scripts/main.ts --prompt "A cinematic scene" --image out.txt --provider agnes --ar 16:9 --response-format url

# Agnes with reference image
${BUN_X} {baseDir}/scripts/main.ts --prompt "Apply this style" --image out.png --provider agnes --ref source.png
```

Notes on `codex-cli`:
- Never auto-selected — pin via `--provider codex-cli` or `default_provider: codex-cli` in EXTEND.md.
- Only `n=1` supported (Codex `image_gen` returns one image per call); `--size`, `--imageSize`, `--quality`, and `--imageApiDialect` are ignored or rejected.
- Typically 5–10× slower than direct OpenAI / Google API calls (except on cache hits). Tune via `BAOYU_CODEX_IMAGEGEN_TIMEOUT_MS`, `BAOYU_CODEX_IMAGEGEN_RETRIES`, and `BAOYU_CODEX_IMAGEGEN_CACHE_DIR`.

## Batch Mode

```bash
# Batch from saved prompt files
${BUN_X} {baseDir}/scripts/main.ts --batchfile batch.json

# Batch with explicit worker count
${BUN_X} {baseDir}/scripts/main.ts --batchfile batch.json --jobs 4 --json
```

### Batch File Format

```json
{
  "jobs": 4,
  "tasks": [
    {
      "id": "hero",
      "promptFiles": ["prompts/hero.md"],
      "image": "out/hero.png",
      "provider": "replicate",
      "model": "google/nano-banana-2",
      "ar": "16:9",
      "quality": "2k"
    },
    {
      "id": "diagram",
      "promptFiles": ["prompts/diagram.md"],
      "image": "out/diagram.png",
      "ref": ["references/original.png"]
    }
  ]
}
```

Paths in `promptFiles`, `image`, and `ref` are resolved relative to the batch file's directory. `jobs` is optional (overridden by CLI `--jobs`). A top-level array without the `jobs` wrapper is also accepted.
