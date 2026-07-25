---
name: first-time-setup
description: First-time setup and default model selection flow for baoyu-image-gen
---

# First-Time Setup

## Overview

Triggered when:
1. No EXTEND.md found → full setup (provider + model + preferences)
2. EXTEND.md found but `default_model.[provider]` is null → model selection only

## Setup Flow

```
No EXTEND.md found          EXTEND.md found, model null
        │                            │
        ▼                            ▼
┌─────────────────────┐    ┌──────────────────────┐
│ AskUserQuestion     │    │ AskUserQuestion      │
│ (full setup)        │    │ (model only)         │
└─────────────────────┘    └──────────────────────┘
        │                            │
        ▼                            ▼
┌─────────────────────┐    ┌──────────────────────┐
│ Create EXTEND.md    │    │ Update EXTEND.md     │
└─────────────────────┘    └──────────────────────┘
        │                            │
        ▼                            ▼
    Continue                     Continue
```

## Flow 1: No EXTEND.md (Full Setup)

**Language**: Use user's input language or saved language preference.

Use AskUserQuestion with ALL questions in ONE call:

### Question 1: Default Provider

```yaml
header: "Provider"
question: "Default image generation provider?"
options:
  - label: "Google (Recommended)"
    description: "Gemini multimodal - high quality, reference images, flexible sizes"
  - label: "OpenAI"
    description: "GPT Image 2 - latest OpenAI image model, reference-image workflows"
  - label: "Azure OpenAI"
    description: "Azure-hosted GPT Image deployments with resource-specific routing"
  - label: "OpenRouter"
    description: "Router for Gemini/FLUX/OpenAI-compatible image models"
  - label: "DashScope"
    description: "Alibaba Cloud - Qwen-Image, strong Chinese/English text rendering"
  - label: "Z.AI"
    description: "GLM-image, strong poster and text-heavy image generation"
  - label: "MiniMax"
    description: "MiniMax image generation with subject-reference character workflows"
  - label: "Replicate"
    description: "Curated Replicate image families - nano-banana-2, Seedream, and Wan image models"
  - label: "Agnes"
    description: "Sapiens AI Agnes - optimized for high information density, complex layouts, reference-image support"
```

### Question 2: Default Google Model

Only show if user selected Google or auto-detect (no explicit provider).

```yaml
header: "Google Model"
question: "Default Google image generation model?"
options:
  - label: "gemini-3-pro-image (Recommended)"
    description: "Highest quality, best for production use"
  - label: "gemini-3.1-flash-image"
    description: "Fast generation, good quality, lower cost"
  - label: "gemini-3-flash-preview"
    description: "Fast generation, balanced quality and speed"
```

### Question 2b: Default OpenRouter Model

Only show if user selected OpenRouter.

```yaml
header: "OpenRouter Model"
question: "Default OpenRouter image generation model?"
options:
  - label: "google/gemini-3.1-flash-image (Recommended)"
    description: "Best general-purpose OpenRouter image model with reference-image workflows"
  - label: "google/gemini-2.5-flash-image-preview"
    description: "Fast Gemini preview model on OpenRouter"
  - label: "black-forest-labs/flux.2-pro"
    description: "Strong text-to-image quality through OpenRouter"
```

### Question 2c: Default Azure Deployment

Only show if user selected Azure OpenAI.

```yaml
header: "Azure Deploy"
question: "Default Azure image deployment name?"
options:
  - label: "gpt-image-2 (Recommended)"
    description: "Use if your Azure deployment uses the GPT Image 2 model name"
  - label: "gpt-image-1.5"
    description: "Previous GPT Image deployment name"
  - label: "gpt-image-1"
    description: "Earlier GPT Image deployment name"
```

### Question 2d: Default MiniMax Model

Only show if user selected MiniMax.

```yaml
header: "MiniMax Model"
question: "Default MiniMax image generation model?"
options:
  - label: "image-01 (Recommended)"
    description: "Best default, supports aspect ratios and custom width/height"
  - label: "image-01-live"
    description: "Faster variant, use aspect ratio instead of custom size"
```

### Question 2e: Default Z.AI Model

Only show if user selected Z.AI.

```yaml
header: "Z.AI Model"
question: "Default Z.AI image generation model?"
options:
  - label: "glm-image (Recommended)"
    description: "Best default for posters, diagrams, and text-heavy images"
  - label: "cogview-4-250304"
    description: "Legacy Z.AI image model on the same endpoint"
```

### Question 3: Default Quality

```yaml
header: "Quality"
question: "Default image quality?"
options:
  - label: "2k (Recommended)"
    description: "2048px - covers, illustrations, infographics"
  - label: "normal"
    description: "1024px - quick previews, drafts"
```

### Question 4: Save Location

```yaml
header: "Save"
question: "Where to save preferences?"
options:
  - label: "Project (Recommended)"
    description: ".baoyu-skills/ (this project only)"
  - label: "User"
    description: "~/.baoyu-skills/ (all projects)"
```

### Save Locations

| Choice | Path | Scope |
|--------|------|-------|
| Project | `.baoyu-skills/baoyu-image-gen/EXTEND.md` | Current project |
| User | `$HOME/.baoyu-skills/baoyu-image-gen/EXTEND.md` | All projects |

### EXTEND.md Template

```yaml
---
version: 1
default_provider: [selected provider or null]
default_quality: [selected quality]
default_aspect_ratio: null
default_image_size: null
default_image_api_dialect: null
default_model:
  google: [selected google model or null]
  openai: null
  azure: [selected azure deployment or null]
  openrouter: [selected openrouter model or null]
  dashscope: null
  zai: [selected Z.AI model or null]
  minimax: [selected minimax model or null]
  replicate: null
  agnes: null
---
```

If the user selects `OpenAI` but says their endpoint is only OpenAI-compatible and fronts another image model family, save `default_image_api_dialect: ratio-metadata` when they explicitly confirm the gateway expects aspect-ratio `size` plus metadata-based resolution. Otherwise leave it `null` / `openai-native`.

## Flow 2: EXTEND.md Exists, Model Null

When EXTEND.md exists but `default_model.[current_provider]` is null, ask ONLY the model question for the current provider.

### Google Model Selection

```yaml
header: "Google Model"
question: "Choose a default Google image generation model?"
options:
  - label: "gemini-3-pro-image (Recommended)"
    description: "Highest quality, best for production use"
  - label: "gemini-3.1-flash-image"
    description: "Fast generation, good quality, lower cost"
  - label: "gemini-3-flash-preview"
    description: "Fast generation, balanced quality and speed"
```

### OpenAI Model Selection

```yaml
header: "OpenAI Model"
question: "Choose a default OpenAI image generation model?"
options:
  - label: "gpt-image-2 (Recommended)"
    description: "Latest GPT Image model, flexible sizes up to 4K, high-fidelity image inputs"
  - label: "gpt-image-1.5"
    description: "Previous GPT Image model"
  - label: "gpt-image-1"
    description: "Earlier GPT Image model"
```

### Azure Deployment Selection

```yaml
header: "Azure Deploy"
question: "Choose a default Azure image deployment name?"
options:
  - label: "gpt-image-2 (Recommended)"
    description: "Use when your Azure deployment name matches the GPT Image 2 model"
  - label: "gpt-image-1.5"
    description: "Use when your Azure deployment name matches the GPT Image 1.5 model"
  - label: "gpt-image-1"
    description: "Use when your Azure deployment name matches GPT-image-1"
```

Notes for Azure setup:

- In `baoyu-image-gen`, Azure `--model` / `default_model.azure` should be the Azure deployment name, not just the underlying model family.
- If the deployment name is custom, save that exact deployment name in `default_model.azure`.

### OpenRouter Model Selection

```yaml
header: "OpenRouter Model"
question: "Choose a default OpenRouter image generation model?"
options:
  - label: "google/gemini-3.1-flash-image (Recommended)"
    description: "Recommended for image output and reference-image edits"
  - label: "google/gemini-2.5-flash-image-preview"
    description: "Fast preview-oriented image generation"
  - label: "black-forest-labs/flux.2-pro"
    description: "High-quality text-to-image through OpenRouter"
```

### DashScope Model Selection

```yaml
header: "DashScope Model"
question: "Choose a default DashScope image generation model?"
options:
  - label: "qwen-image-2.0-pro (Recommended)"
    description: "Best DashScope model for text rendering and custom sizes"
  - label: "qwen-image-2.0"
    description: "Faster 2.0 variant with flexible output size"
  - label: "qwen-image-max"
    description: "Legacy Qwen model with five fixed output sizes"
  - label: "qwen-image-plus"
    description: "Legacy Qwen model, same current capability as qwen-image"
  - label: "wan2.7-image-pro"
    description: "Wan 2.7 Pro — supports up to 4K text-to-image and reference-image editing"
  - label: "wan2.7-image"
    description: "Wan 2.7 base — faster generation, up to 2K, supports reference-image editing"
  - label: "z-image-turbo"
    description: "Legacy DashScope model for compatibility"
  - label: "z-image-ultra"
    description: "Legacy DashScope model, higher quality but slower"
```

Notes for DashScope setup:

- Prefer `qwen-image-2.0-pro` when the user needs custom `--size`, uncommon ratios like `21:9`, or strong Chinese/English text rendering.
- `qwen-image-max` / `qwen-image-plus` / `qwen-image` only support five fixed sizes: `1664*928`, `1472*1104`, `1328*1328`, `1104*1472`, `928*1664`.
- `wan2.7-image-pro` and `wan2.7-image` are the only DashScope models that accept `--ref`. Pick one of these when the user wants reference-image editing or multi-image fusion via DashScope.
- In `baoyu-image-gen`, `quality` is a compatibility preset. It is not a native DashScope parameter.

### Z.AI Model Selection

```yaml
header: "Z.AI Model"
question: "Choose a default Z.AI image generation model?"
options:
  - label: "glm-image (Recommended)"
    description: "Current flagship image model with better text rendering and poster layouts"
  - label: "cogview-4-250304"
    description: "Legacy model on the sync image endpoint"
```

Notes for Z.AI setup:

- Prefer `glm-image` for posters, diagrams, and Chinese/English text-heavy layouts.
- In `baoyu-image-gen`, Z.AI currently exposes text-to-image only; reference images are not wired for this provider.
- The sync Z.AI image API returns a downloadable image URL, which the runtime saves locally after download.

### Replicate Model Selection

```yaml
header: "Replicate Model"
question: "Choose a default Replicate image generation model?"
options:
  - label: "google/nano-banana-2 (Recommended)"
    description: "Current default for general Replicate image generation in baoyu-image-gen"
  - label: "bytedance/seedream-4.5"
    description: "Replicate Seedream 4.5 with validated local size/ref guardrails"
  - label: "bytedance/seedream-5-lite"
    description: "Replicate Seedream 5 Lite with validated local size/ref guardrails"
  - label: "wan-video/wan-2.7-image-pro"
    description: "Replicate Wan 2.7 Image Pro with 4K text-to-image support"
```

### MiniMax Model Selection

```yaml
header: "MiniMax Model"
question: "Choose a default MiniMax image generation model?"
options:
  - label: "image-01 (Recommended)"
    description: "Best general-purpose MiniMax image model with custom width/height support"
  - label: "image-01-live"
    description: "Lower-latency MiniMax image model using aspect ratios"
```

Notes for MiniMax setup:

- `image-01` is the safest default. It supports official `aspect_ratio` values and documented custom `width` / `height` output sizes.
- `image-01-live` is useful when the user prefers faster generation and can work with aspect-ratio-based sizing.
- MiniMax subject reference currently uses `subject_reference[].type = character`; docs recommend front-facing portrait references in JPG/JPEG/PNG under 10MB.

### Update EXTEND.md

After user selects a model:

1. Read existing EXTEND.md
2. If `default_model:` section exists → update the provider-specific key
3. If `default_model:` section missing → add the full section:

```yaml
default_model:
  google: [value or null]
  openai: [value or null]
  azure: [value or null]
  openrouter: [value or null]
  dashscope: [value or null]
  zai: [value or null]
  minimax: [value or null]
  replicate: [value or null]
  agnes: [value or null]
```

Only set the selected provider's model; leave others as their current value or null.

## After Setup

1. Create directory if needed
2. Write/update EXTEND.md with frontmatter
3. Confirm: "Preferences saved to [path]"
4. Continue with image generation
