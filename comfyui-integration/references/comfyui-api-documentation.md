# ComfyUI API Documentation

## Overview

ComfyUI exposes a REST API for programmatic workflow execution. The API is HTTP-based, uses JSON for request/response format, and requires no authentication by default.

## Base URL

```
http://localhost:8188
```

The port can be configured with `--port` flag when starting ComfyUI.

## Core Endpoints

### GET /api/object_info

Returns information about all available node classes in ComfyUI.

**Response:**
```json
{
  "CheckpointLoaderSimple": {
    "input": {
      "required": {
        "ckpt_name": ["STRING", {"content_type": "model"}]
      }
    },
    "output": ["MODEL", "CLIP", "VAE"],
    "output_node": false
  }
}
```

**Usage:** Discover available nodes and their input/output specifications.

### POST /api/prompt

Execute a workflow. This endpoint accepts a JSON workflow and queues it for execution.

**Request Body:**
```json
{
  "client_id": "unique-client-identifier",
  "prompt": {
    "1": {
      "class_type": "CheckpointLoaderSimple",
      "inputs": {
        "ckpt_name": "model.safetensors"
      }
    }
  }
}
```

**Response:**
```json
{
  "prompt_id": "abc123def456",
  "number": 1,
  "node_errors": {}
}
```

**Error Responses:**
```json
{
  "prompt_id": null,
  "number": 1,
  "node_errors": {
    "1": ["Missing required input: ckpt_name"]
  }
}
```

### GET /api/history

Retrieve execution history and results.

**Query Parameters:**
- `prompt_id` (optional) - Filter by specific prompt

**Response:**
```json
{
  "abc123def456": {
    "prompt": {...},
    "outputs": {
      "8": {
        "images": [
          {
            "filename": "ComfyUI_00001_.png",
            "subfolder": "",
            "type": "output"
          }
        ]
      }
    },
    "status": {
      "status_str": "success",
      "completed": true,
      "value": 1.0
    }
  }
}
```

### GET /queue

Get current execution queue status.

**Response:**
```json
{
  "queue_pending": [
    ["prompt_id_1", 1, {...}],
    ["prompt_id_2", 2, {...}]
  ],
  "queue_running": []
}
```

### GET /upload/image

Retrieve uploaded or generated images.

**Query Parameters:**
- `filename` - Image filename
- `subfolder` (optional) - Subfolder path
- `type` - "output", "input", or "temp"

**Response:** Binary image file

## WebSocket API

Connect to `/ws` for real-time execution events.

**Connection:**
```javascript
const ws = new WebSocket('ws://localhost:8188/ws?clientId=unique-id');
```

**Event Types:**

```json
{
  "type": "execution_start",
  "data": {
    "prompt_id": "abc123"
  }
}
```

```json
{
  "type": "execution_progress",
  "data": {
    "value": 5,
    "max": 20,
    "prompt_id": "abc123",
    "node": "3"
  }
}
```

```json
{
  "type": "execution_cached",
  "data": {
    "nodes": ["1", "2"],
    "prompt_id": "abc123"
  }
}
```

```json
{
  "type": "execution_error",
  "data": {
    "prompt_id": "abc123",
    "node_id": "3",
    "exception_message": "...",
    "exception_type": "ValueError"
  }
}
```

```json
{
  "type": "execution_cached",
  "data": {
    "nodes": ["1"],
    "prompt_id": "abc123"
  }
}
```

## Workflow Format

### Structure

Workflows are JSON objects where keys are node IDs (numeric strings) and values are node definitions:

```json
{
  "1": {
    "class_type": "LoadImage",
    "inputs": {
      "image": "input.png"
    }
  },
  "2": {
    "class_type": "VAEEncode",
    "inputs": {
      "pixels": ["1", 0],
      "vae": ["3", 0]
    }
  }
}
```

### Node Reference Format

Input references to other nodes use a 2-element array:
```json
["node_id", output_index]
```

- `node_id` - String ID of the node to reference
- `output_index` - Integer index of the output (0-based)

## Data Types

Common input/output types:

- `MODEL` - Diffusion model (Stable Diffusion, SDXL, Flux, etc.)
- `CLIP` - Text encoder (CLIP, T5, BERT)
- `VAE` - Variational autoencoder for latent encoding
- `LATENT` - Compressed image representation
- `IMAGE` - Full-resolution image tensor
- `CONDITIONING` - Encoded text conditioning
- `INT`, `FLOAT`, `STRING` - Scalar types
- `MASK` - Binary mask for inpainting
- `COMBO` - Enumerated choice type

## Common Node Types

### Model Loading
- `CheckpointLoaderSimple` - Load CKPT/safetensors models
- `CheckpointLoader` - Advanced model loading with VAE selection
- `LoraLoader` - Load LoRA adapters
- `ControlNetLoader` - Load ControlNet models

### Text Encoding
- `CLIPTextEncode` - Encode text prompt with CLIP
- `CLIPTextEncodeSDXL` - SDXL-specific text encoding
- `T5TextEncode` - Encode with T5 (Flux, Dall-E)

### Sampling
- `KSampler` - Standard sampling
- `KSamplerAdvanced` - Advanced sampling with more options
- `DPMSolverSampler` - Alternative sampler with different noise schedule

### Image Processing
- `VAEDecode` - Decode latents to images
- `VAEEncode` - Encode images to latents
- `LoaderImage` - Load images from filesystem
- `SaveImage` - Save generated images

### Control
- `ControlNetLoader` - Load ControlNet models
- `ACNWeighter` - ControlNet weighting and processing
- `ACNAdvanced` - Advanced ControlNet features

## Example: Simple Text-to-Image Workflow

```python
import json
import requests
import websocket

# Workflow definition
workflow = {
    "1": {
        "class_type": "CheckpointLoaderSimple",
        "inputs": {"ckpt_name": "sdxl.safetensors"}
    },
    "2": {
        "class_type": "CLIPTextEncodeSDXL",
        "inputs": {
            "text": "a beautiful landscape",
            "clip": ["1", 1]
        }
    },
    "3": {
        "class_type": "CLIPTextEncodeSDXL",
        "inputs": {
            "text": "",
            "clip": ["1", 1]
        }
    },
    "4": {
        "class_type": "KSamplerAdvanced",
        "inputs": {
            "seed": 12345,
            "steps": 30,
            "cfg": 8.0,
            "sampler_name": "dpmpp_2m",
            "scheduler": "karras",
            "denoise": 1.0,
            "model": ["1", 0],
            "positive": ["2", 0],
            "negative": ["3", 0],
            "latent_image": ["5", 0]
        }
    },
    "5": {
        "class_type": "EmptyLatentImage",
        "inputs": {"width": 1024, "height": 1024, "batch_size": 1}
    },
    "6": {
        "class_type": "VAEDecode",
        "inputs": {
            "samples": ["4", 0],
            "vae": ["1", 2]
        }
    },
    "7": {
        "class_type": "SaveImage",
        "inputs": {
            "filename_prefix": "output",
            "images": ["6", 0]
        }
    }
}

# Submit workflow
response = requests.post(
    "http://localhost:8188/api/prompt",
    json={"client_id": "my-app", "prompt": workflow}
)

result = response.json()
prompt_id = result["prompt_id"]
print(f"Execution queued: {prompt_id}")

# Check history
history = requests.get("http://localhost:8188/api/history").json()
if prompt_id in history:
    print("Workflow completed!")
    print(history[prompt_id]["outputs"])
```

## Error Handling

### Validation Errors

Returned immediately with 400 status:
```json
{
  "prompt_id": null,
  "number": 1,
  "node_errors": {
    "3": ["Unknown sampler: invalid_sampler"]
  }
}
```

### Execution Errors

Reported in WebSocket events or history:
```json
{
  "type": "execution_error",
  "data": {
    "prompt_id": "abc123",
    "node_id": "3",
    "exception_message": "CUDA out of memory",
    "exception_type": "RuntimeError"
  }
}
```

## Performance Tips

1. **Batch Requests** - Group multiple workflows to amortize startup cost
2. **Model Caching** - Reuse loaded models across workflows
3. **Use Caching** - ComfyUI caches node outputs automatically
4. **Monitor Queue** - Poll `/queue` to avoid overloading
5. **Connection Pooling** - Reuse HTTP connections
6. **Select Hardware** - Use CUDA for NVIDIA, Metal for Apple, DirectML for Windows

## API Versioning

ComfyUI does not use semantic versioning for the API. Breaking changes may occur in releases. Always test after updating ComfyUI.
