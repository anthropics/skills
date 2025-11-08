---
name: comfyui-integration
description: Integrate ComfyUI as primary inference engine via API with GPL licensing safety. Use when implementing ComfyUI workflows, managing custom nodes with permissive licenses, optimizing inference performance, handling GGUF models, or maintaining API-only separation for GPL compliance.
---

# ComfyUI Integration & Workflows Skill

## Skill Overview

This skill provides production-ready guidance for integrating ComfyUI as a node-based inference backend while maintaining GPL licensing compliance and achieving optimal performance. ComfyUI enables complex AI workflows through a visual node-based editor with a powerful REST API.

### Key Capabilities

- **ComfyUI API Integration** - JSON-based REST API for stateless inference without GPL contamination
- **Workflow Design & Validation** - JSON workflow format with comprehensive validation tools
- **Custom Node Management** - Vetted permissive-license nodes (MIT, Apache 2.0, BSD)
- **GGUF Model Support** - ComfyUI-GGUF node integration for quantized model inference
- **GPL Compliance** - API-only architecture ensuring legal separation from GPL-licensed components
- **Performance Optimization** - Inference acceleration, batching, and resource management

## ComfyUI Architecture

ComfyUI is a node-based GUI and API for stable diffusion and other generative models. It provides:

- **Weekly Release Cycle** - Rapid feature updates and improvements (check https://github.com/comfyanonymous/ComfyUI/releases)
- **Node-Based Workflow** - Visual composition with JSON serialization
- **HTTP API** - Stateless REST endpoints for programmatic access
- **Custom Node Ecosystem** - Extensible architecture with community contributions
- **GPU/CPU Inference** - Support for NVIDIA, AMD, Intel, and Apple silicon

## Integration Patterns

### API-Only Architecture (Recommended for GPL Compliance)

The safest approach uses ComfyUI as a backend service accessed exclusively via HTTP API:

```
Your Application (Python/Node.js/etc)
    ↓ HTTP Requests (JSON)
ComfyUI API Server
    ↓ Node-Based Processing
ComfyUI Core & Custom Nodes
    ↓ Model Inference
ML Models (Diffusers, Transformers, GGUF)
```

This separation ensures your application code never links against GPL libraries.

### Licensing Considerations

- **ComfyUI Core** - GPL-compatible (contains GPL-licensed dependencies)
- **Custom Nodes** - Audit for license compatibility
- **Models** - Various licenses (Flux, SDXL, Llama, etc.)
- **API Layer** - Non-GPL code; safe to license proprietary

## Technology Stack

### ComfyUI Versions
- Latest: Check https://github.com/comfyanonymous/ComfyUI/releases for weekly updates
- Breaking changes documented in release notes
- Stable enough for production with proper testing

### Custom Node Ecosystem

**Recommended Permissive Licenses:**
- MIT License
- Apache 2.0 License
- BSD 2/3-Clause License

**Nodes to Avoid:**
- GPL-licensed nodes (unless API separation is guaranteed)
- AGPL-licensed nodes (network copyleft)
- Unclear license attribution

## Workflow Format

ComfyUI workflows are JSON objects where keys are node indices and values are node configurations:

```json
{
  "1": {
    "class_type": "CheckpointLoaderSimple",
    "inputs": {
      "ckpt_name": "model.safetensors"
    }
  },
  "2": {
    "class_type": "CLIPTextEncode",
    "inputs": {
      "text": "a beautiful landscape",
      "clip": ["1", 0]
    }
  },
  "3": {
    "class_type": "KSampler",
    "inputs": {
      "seed": 12345,
      "steps": 20,
      "cfg": 7.5,
      "sampler_name": "euler",
      "scheduler": "normal",
      "denoise": 1.0,
      "model": ["1", 0],
      "positive": ["2", 0],
      "negative": ["2", 0],
      "latent_image": ["4", 0]
    }
  }
}
```

## GGUF Model Integration

ComfyUI-GGUF nodes enable inference with quantized GGUF models for reduced memory/compute:

- **Model Format** - GGUF (optimized for CPU and GPU inference)
- **Frameworks** - llama.cpp, ollama integration
- **Quantization** - 2-bit, 3-bit, 4-bit, 5-bit, 6-bit, 8-bit variants
- **Performance** - 10-100x smaller models with acceptable quality trade-offs
- **Use Cases** - Text-to-image, image-to-image with local quantized models

## Custom Node Development

When creating custom nodes:

1. **License** - Use permissive licenses (MIT/Apache 2.0)
2. **Dependencies** - Audit all transitive dependencies for GPL
3. **Node Registration** - Implement `NODE_CLASS_MAPPINGS` and `NODE_DISPLAY_NAME_MAPPINGS`
4. **API Compatibility** - Ensure serializable inputs/outputs
5. **Documentation** - Include node class type and input/output specifications

## Performance Optimization

### Inference Acceleration
- **CUDA** - NVIDIA GPU acceleration (fastest, requires CUDA toolkit)
- **DirectML** - Windows GPU acceleration (AMD/Intel integrated)
- **Metal** - Apple Silicon optimization (MPS)
- **ROCm** - AMD GPU support (RDNA2+)
- **CPU** - Fallback with reduced performance

### Resource Management
- Batch processing for throughput
- Model caching and preloading
- Queue management for concurrent requests
- Memory optimization with fp16/int8 quantization
- Monitor VRAM usage and implement fallback strategies

## Quick Start

1. **Install ComfyUI**
   ```bash
   git clone https://github.com/comfyanonymous/ComfyUI
   cd ComfyUI
   pip install -r requirements.txt
   python main.py --listen 0.0.0.0
   ```

2. **Create Workflow** - Use JSON API or visual editor

3. **Validate** - Use provided `comfyui-workflow-validator.py`

4. **Execute**
   ```bash
   curl -X POST http://localhost:8188/api/prompt \
     -H "Content-Type: application/json" \
     -d @workflow.json
   ```

5. **Monitor** - WebSocket or polling `/api/history`

## Resources

- **API Documentation** - `references/comfyui-api-documentation.md`
- **Custom Nodes** - `references/comfyui-custom-nodes.md`
- **GGUF Integration** - `references/comfyui-gguf-integration.md`
- **GPL Guidelines** - `references/gpl-licensing-guidelines.md`
- **Workflow Validator** - `scripts/comfyui-workflow-validator.py`
- **Production Workflow** - `assets/flux-kontext-workflow.json`

## Best Practices

- Always validate workflows before execution
- Audit custom node licenses before deployment
- Use API-only pattern for GPL compliance
- Implement queue management for production loads
- Cache model weights and CLIP encoders
- Monitor GPU memory and implement fallback strategies
- Use environment variables for API endpoints and model paths
- Implement error handling for network timeouts and inference failures
