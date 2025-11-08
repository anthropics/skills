---
name: flux-kontext-model
description: Integrate FLUX.1 Kontext (12B parameters) for stable aspect ratio image editing with context preservation. Use when implementing in-context editing, multi-image control, prompt engineering for FLUX, GGUF quantization for FLUX models, or optimizing inference performance for miniature painting workflows.
---

# FLUX.1 Kontext Model Integration

## Overview

FLUX.1 Kontext is a specialized 12-billion parameter variant of the FLUX.1 model designed for in-context editing and multi-image control. Unlike the base FLUX.1 model, Kontext can maintain aspect ratios reliably, preserve visual context across multiple images, and support advanced editing workflows. This skill provides comprehensive guidance for integrating FLUX.1 Kontext into miniature painting applications, including optimization techniques, prompt engineering patterns, and integration strategies for both ComfyUI and Hugging Face Diffusers.

## Core Capabilities

### 1. In-Context Editing
FLUX.1 Kontext excels at understanding and preserving existing image content while making targeted edits. It can:
- Understand spatial relationships and preserve untouched areas
- Maintain artistic consistency across edited regions
- Support iterative refinement workflows for miniature painting details
- Accept context images to influence the generation process

### 2. Multi-Image Control
Support for multiple input images enables:
- Reference-based generation using existing miniature paintings
- Style transfer between different painting techniques
- Consistency enforcement across image sets
- Context-aware editing with multiple reference images

### 3. Aspect Ratio Stability
FLUX.1 Kontext provides:
- Reliable aspect ratio preservation (critical for product photography)
- Consistent image dimensions without unpredictable letterboxing
- Support for common miniature photography ratios (1:1, 4:3, 16:9)
- Predictable composition for gallery displays

## Integration Patterns

### ComfyUI Integration
FLUX.1 Kontext is fully supported in ComfyUI with specialized nodes for in-context editing:
- Use `CLIPTextEncode` nodes for context-aware prompting
- Configure `KSampler` with context-specific settings
- Chain nodes to enable multi-image workflows
- Leverage LoRA nodes for miniature-specific styling

See `references/flux-kontext-comfyui-workflow.md` for complete workflow examples and node configurations.

### Hugging Face Diffusers Integration
Direct Python integration using the Diffusers library:
- Load model via `AutoPipelineForInpainting` for editing workflows
- Configure inference parameters for optimal quality/speed tradeoffs
- Use `torch.compile()` for performance optimization
- Implement GGUF loading for quantized inference

See `references/flux-kontext-optimization.md` for code examples and performance benchmarks.

## Prompt Engineering for Miniatures

Optimal prompts for FLUX.1 Kontext when working with miniature paintings follow specific patterns:

**Effective Format:**
```
[Material][Style] miniature of [Subject], [Lighting], [Camera Details]
```

**Example:**
```
Acrylic [wet blending] miniature of fantasy knight, warm golden sidelighting,
macro photography 1:1, shallow depth of field, studio backdrop
```

Key principles:
- Specify painting material (acrylic, oil, watercolor, mixed media)
- Include painting technique (wet blending, glazing, drybrushing, stippling)
- Describe the subject clearly with fantasy/historical context
- Specify lighting direction and temperature
- Include camera/macro details for authentic miniature photography
- Mention backdrop and composition preferences

See `references/flux-kontext-prompting.md` for comprehensive prompt templates and quality optimization tips.

## Performance Optimization

### GGUF Quantization
FLUX.1 Kontext can be quantized to GGUF format for efficient inference:
- **Q4_K (Recommended):** 4-bit quantization with K-quants, optimal quality/size balance
- **Q5_K:** 5-bit quantization for highest quality
- **Q3_K:** 3-bit quantization for memory-constrained environments

GGUF quantization typically achieves 75% reduction in model size with minimal quality loss.

### Lightning LoRA
Combine FLUX.1 Kontext with Lightning LoRA adapters for 2-4x inference speedup:
- Load pre-trained Lightning LoRA weights
- Adjust guidance scales (typically 1.5-2.0 with Lightning LoRA)
- Batch multiple editing requests for efficiency
- Cache context encodings for iterative edits

### Memory Optimization
For desktop deployment:
- Use 8-bit quantization if VRAM is limited (<16GB)
- Enable attention slicing with `enable_attention_slicing()`
- Implement image tiling for large format outputs
- Cache context embeddings across batch operations

See `references/flux-kontext-optimization.md` for detailed implementation guidance.

## Capability Reference

### Supported Editing Modes
- **In-context editing:** Full image editing with context awareness
- **Inpainting:** Selective region editing with mask support
- **Outpainting:** Extending images beyond original boundaries
- **Style transfer:** Applying artistic styles while preserving content

### Multi-Image Features
- Support for 2-8 reference images simultaneously
- Context blending with configurable influence weights
- Consistency enforcement across image batches
- Reference-based prompt generation

### Output Controls
- Aspect ratio lock (1:1, 4:3, 16:9, custom)
- Resolution up to 1536x1536 pixels
- Guidance scale tuning (3.5-7.5 recommended range)
- Deterministic generation with seed control

See `references/flux-kontext-capabilities.md` for detailed feature documentation.

## Quick Start Example

```python
from diffusers import AutoPipelineForInpainting
import torch

# Load FLUX.1 Kontext model
pipeline = AutoPipelineForInpainting.from_pretrained(
    "black-forest-labs/FLUX.1-Kontext-dev",
    torch_dtype=torch.bfloat16
).to("cuda")

# Prepare images and mask
base_image = load_image("miniature_base.png")
context_image = load_image("reference_style.png")
mask = create_mask("region_to_edit.png")

# Generate in-context edit
result = pipeline(
    prompt="detailed acrylic miniature knight, warm lighting, macro photography",
    image=base_image,
    mask_image=mask,
    guidance_scale=5.0,
    num_inference_steps=28,
    height=768,
    width=768,
).images[0]
```

## Testing and Validation

Use `scripts/test-flux-kontext.py` to validate:
- Model loading and GPU memory allocation
- In-context editing consistency
- Aspect ratio preservation
- Multi-image support functionality
- Quantization accuracy (for GGUF workflows)

Run validation: `python scripts/test-flux-kontext.py`

## Resources

This skill includes comprehensive bundled resources:

### scripts/
- **test-flux-kontext.py:** Validation script with test cases for all major capabilities

### references/
- **flux-kontext-capabilities.md:** Feature documentation for in-context editing, multi-image support, and output controls
- **flux-kontext-prompting.md:** Optimal prompt formats, techniques for miniature painting, quality enhancement tips
- **flux-kontext-optimization.md:** GGUF quantization guide, Lightning LoRA integration, memory optimization strategies
- **flux-kontext-comfyui-workflow.md:** ComfyUI node configuration, workflow examples, best practices

### assets/
- **flux-kontext-examples/:** Reference images, example prompts, and quality benchmarks
