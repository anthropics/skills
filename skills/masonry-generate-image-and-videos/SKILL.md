---
name: masonry-generate-image-and-videos
description: AI-powered image and video generation using the Masonry CLI. Generate images from text prompts with models like Imagen 3.0, generate videos with Veo 3.1, check job status, download results, and discover available AI models. Use when user wants to create AI-generated images or videos.
license: Apache-2.0
metadata:
  author: masonry-ai
  version: "1.0"
compatibility: Requires masonry CLI installed (curl -sSL https://media.masonry.so/cli/install.sh | sh)
---

# Masonry CLI

The `masonry` CLI provides AI-powered image and video generation capabilities.

## When to use this skill

Use this skill when the user wants to:
- Generate images from text prompts
- Generate videos from text prompts
- Check status of generation jobs
- Download generated media
- List available AI models
- View generation history

## Installation

If the masonry command is not available, install it:

```bash
npm i -g @masonryai/cli
```

Then authenticate:

```bash
npx @masonryai/cli  login
```

## Quick Commands

```bash
# Generate image
npx @masonryai/cli  image "your prompt here" --aspect 16:9

# Generate video
npx @masonryai/cli  video "your prompt here" --duration 4

# Check job status
npx @masonryai/cli  job status <job-id>

# Download result
npx @masonryai/cli  job download <job-id> -o ./output.png

# List available models
npx @masonryai/cli  models list --type image
npx @masonryai/cli  models list --type video
```

## Detailed Workflows

### Image Generation

```bash
# Basic generation
npx @masonryai/cli  image "a sunset over mountains, photorealistic"

# With options
npx @masonryai/cli  image "cyberpunk cityscape" --aspect 16:9 --model imagen-3.0-generate-002

# Available flags
#   --aspect, -a     Aspect ratio (16:9, 9:16, 1:1)
#   --dimension, -d  Exact size (1920x1080)
#   --model, -m      Model key
#   --output, -o     Output path
#   --negative-prompt What to avoid
#   --seed           Reproducibility seed
```

### Video Generation

```bash
# Basic generation
npx @masonryai/cli  video "ocean waves crashing on rocks"

# With options
npx @masonryai/cli  video "drone shot of forest" --duration 6 --aspect 16:9

# Available flags
#   --duration       Length in seconds (4, 6, 8)
#   --aspect, -a     Aspect ratio (16:9, 9:16)
#   --model, -m      Model key
#   --image, -i      First frame image
#   --no-audio       Disable audio generation
```

### Job Management

```bash
# List recent jobs
npx @masonryai/cli  job list

# Check specific job
npx @masonryai/cli  job status <job-id>

# Wait for completion and download
npx @masonryai/cli  job wait <job-id> --download -o ./result.png

# View local history
npx @masonryai/cli  history list
npx @masonryai/cli  history pending --sync
```

### Model Discovery

```bash
# List all models
npx @masonryai/cli  models list

# Filter by type
npx @masonryai/cli  models list --type video

# Get model parameters
npx @masonryai/cli  models params veo-3.1-fast-generate-preview
```

## Response Format

All commands return JSON:

```json
{
  "success": true,
  "job_id": "abc-123",
  "status": "pending",
  "check_after_seconds": 10,
  "check_command": "masonry job status abc-123"
}
```

## Authentication

If commands fail with auth errors:

```bash
npx @masonryai/cli login
```

