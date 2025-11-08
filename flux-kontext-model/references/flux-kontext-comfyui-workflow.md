# FLUX.1 Kontext ComfyUI Integration Guide

## Overview

ComfyUI provides a node-based visual interface for FLUX.1 Kontext workflows. This guide covers node configuration, workflow patterns, and optimization techniques for miniature painting applications.

## Installation and Setup

### Step 1: Install ComfyUI
```bash
# Clone ComfyUI repository
git clone https://github.com/comfyanonymous/ComfyUI.git
cd ComfyUI

# Install dependencies
pip install -r requirements.txt

# For GPU optimization
pip install xformers  # Recommended for faster inference
```

### Step 2: Download FLUX.1 Kontext Model
```bash
# Models directory structure
ComfyUI/
  models/
    checkpoints/
      flux-1-Kontext-dev-fp16.safetensors  (or .gguf for quantized)
    text_encoders/
      clip_l.safetensors
      t5xxl_fp16.safetensors
```

### Step 3: Add Custom Nodes
```bash
# Navigate to custom nodes directory
cd ComfyUI/custom_nodes

# Clone helpful node collections
git clone https://github.com/ltdrdata/ComfyUI-Manager.git
git clone https://github.com/Kosinkadink/ComfyUI-Advanced-ControlNet.git
git clone https://github.com/jags111/efficient-webui.git
```

## Core Node Configuration

### FLUX.1 Kontext Model Loader Node

**Configuration:**
- **Model:** flux-1-Kontext-dev-fp16 (or quantized variant)
- **Optional VAE:** flux_vae.safetensors (if using custom VAE)
- **Memory Type:** CPU/GPU selection

```
┌─────────────────────────┐
│  FLUX Model Loader      │
│─────────────────────────│
│ Model: flux-kontext-dev │
│ fp: fp16                │
│ memory_type: GPU        │
└────────────┬────────────┘
             │
        [Model Output]
```

### Text Encoding Nodes

#### CLIPTextEncode (Prompt Input)
```
┌────────────────────────────┐
│ CLIPTextEncode             │
│────────────────────────────│
│ clip: [from loader]        │
│ text: [prompt input]       │
└────────┬───────────────────┘
         │
    [Conditioning Output]
```

**Example Prompts in Node:**
```
Acrylic wet blending miniature of fantasy paladin knight, intricate
armor details, warm golden sidelighting, macro photography 1:1,
shallow depth of field, studio backdrop, professional lighting
```

#### T5XXL Encoder (for Context)
```
┌────────────────────────────┐
│ T5XXL Text Encode          │
│────────────────────────────│
│ t5_model: [loaded]         │
│ text: [context prompt]     │
└────────┬───────────────────┘
         │
    [Conditioning Output]
```

### Image Processing Nodes

#### Load Image Node
```
┌──────────────────────────────┐
│ Load Image (Base Image)      │
│──────────────────────────────│
│ image: base_miniature.png    │
│ JPEG quality: 95             │
└────────┬─────────────────────┘
         │
    [Image Output]
```

#### Create Mask Node (for Inpainting)
```
┌──────────────────────────────┐
│ Load Image (Mask)            │
│──────────────────────────────│
│ image: edit_mask.png         │
│ (grayscale, white=edit area) │
└────────┬─────────────────────┘
         │
    [Mask Output]
```

### Sampler Node (Core Generation)

#### KSampler Configuration
```
┌────────────────────────────────────┐
│ KSampler (Advanced)                │
│────────────────────────────────────│
│ model: [flux model]                │
│ positive: [prompt conditioning]    │
│ negative: "" (empty for FLUX)      │
│ latent_image: [prepared latent]   │
│ seed: [seed value]                 │
│ steps: 28                          │
│ cfg: 5.0                           │
│ sampler_name: euler               │
│ scheduler: normal                  │
│ denoise: 1.0 (0.8-0.9 for inpaint)│
└────────┬─────────────────────────┘
         │
   [Latent Output]
```

**Key Parameters:**
- **steps:** 28 (standard), 20 (Q4_K), 8 (with Lightning LoRA)
- **cfg (Guidance Scale):** 5.0-7.0 (standard), 1.5-2.0 (Lightning LoRA)
- **sampler_name:** "euler" recommended for FLUX
- **denoise:** 1.0 (full generation), 0.85 (strong edit), 0.5 (light touch)

### VAE Decoder

#### VAE Decode Node
```
┌────────────────────────────────┐
│ VAE Decode                     │
│────────────────────────────────│
│ samples: [from KSampler]       │
│ vae: [flux VAE or custom]      │
└────────┬─────────────────────┘
         │
   [Image Output]
```

### Output Node

#### Save Image
```
┌──────────────────────────────┐
│ Save Image                   │
│──────────────────────────────│
│ images: [from VAE Decode]    │
│ filename_prefix: miniature   │
│ format: PNG                  │
└──────────────────────────────┘
```

## Complete Workflow Examples

### Workflow 1: In-Context Editing (Recommended)

**Use Case:** Edit specific regions while preserving context

```
[Load Image: base.png]    [Load Image: mask.png]
        │                         │
        ├──────────────────────────┤
        │                          │
    [Prepare Latent]         [Inpainting Prep]
        │                          │
        └──────────────┬───────────┘
                       │
        ┌──────────────┼──────────────┐
        │              │              │
  [FLUX Loader]   [CLIPTextEncode]  [VAE Encode]
        │              │              │
        └──────┬───────┴──────┬───────┘
               │              │
         [KSampler (denoise=0.85)]
               │
           [VAE Decode]
               │
          [Save Image]
```

**Workflow JSON Configuration:**
```json
{
  "1": {
    "class_type": "CheckpointLoaderSimple",
    "inputs": {
      "ckpt_name": "flux-1-Kontext-dev-fp16.safetensors"
    }
  },
  "2": {
    "class_type": "CLIPTextEncode",
    "inputs": {
      "text": "Acrylic wet blending miniature of detailed dragon, warm backlighting, macro photography",
      "clip": ["1", 1]
    }
  },
  "3": {
    "class_type": "KSampler",
    "inputs": {
      "seed": 42,
      "steps": 28,
      "cfg": 5.0,
      "sampler_name": "euler",
      "scheduler": "normal",
      "denoise": 0.85,
      "model": ["1", 0],
      "positive": ["2", 0],
      "negative": ["2", 0],
      "latent_image": ["4", 0]
    }
  },
  "5": {
    "class_type": "VAEDecode",
    "inputs": {
      "samples": ["3", 0],
      "vae": ["1", 2]
    }
  }
}
```

### Workflow 2: Multi-Image Consistency

**Use Case:** Generate variations while maintaining style consistency

```
[Base Image]  [Reference 1]  [Reference 2]  [Reference 3]
     │             │              │              │
     └─────────────┴──────────────┴──────────────┤
                                                  │
                            ┌─────────────────────┤
                            │                     │
                      [Encode References]     [Main Image]
                            │                     │
              [CLIPTextEncode]  [CLIPTextEncode]  │
                     │               │            │
                     └──────┬────────┴────────────┤
                            │                     │
                    [KSampler (multi-image)]     │
                            │                     │
                       [VAE Decode]────────────────
                            │
                      [Save Image]
```

**Key Configuration:**
```
Steps: 28
Guidance Scale: 6.0 (higher for consistency)
Sampler: euler (recommended)
Multi-image weight: 0.7 (configurable per reference)
```

### Workflow 3: Rapid Iteration with Lightning LoRA

**Use Case:** Fast preview generation with Lightning LoRA

```
[Load Image]    [Create Mask]
     │               │
     └───────┬───────┘
             │
      [Load LoRA Model]
             │
      [CLIPTextEncode]
             │
      [KSampler]
      (steps: 8, cfg: 1.8)
             │
        [VAE Decode]
             │
       [Save Image]
```

**Configuration:**
- Steps: 8 (vs 28 standard)
- Guidance: 1.8 (vs 5.0 standard)
- LoRA Strength: 1.0
- Speed: 8s per image (vs 45s)

## Advanced Node Techniques

### Context Blending Node

**Purpose:** Blend multiple reference images with weights

```
┌──────────────────────────────┐
│ Image Blend (Custom)         │
│──────────────────────────────│
│ images: [ref1, ref2, ref3]   │
│ weights: [0.4, 0.35, 0.25]  │
│ blend_mode: context_blend    │
└────────┬─────────────────────┘
         │
   [Blended Image]
```

### Mask Refinement Node

**Purpose:** Smooth and refine mask edges

```
┌──────────────────────────────┐
│ Mask Filter                  │
│──────────────────────────────│
│ mask: [raw mask]             │
│ operation: gaussian_blur     │
│ strength: 3.0                │
└────────┬─────────────────────┘
         │
   [Refined Mask]
```

### Batch Processing Node

**Purpose:** Process multiple prompts efficiently

```
┌──────────────────────────────┐
│ Batch Processor              │
│──────────────────────────────│
│ base_image: [image]          │
│ prompts: [list of prompts]   │
│ count: 5                     │
│ mode: sequential             │
└────────┬─────────────────────┘
         │
   [Multiple Outputs]
```

## Performance Optimization in ComfyUI

### GPU Memory Optimization

**Enable Xformers Attention:**
```
# In ComfyUI settings
Edit: web/extensions/core/apiTools.js
Add: "xformers": true
```
Benefits:
- 20% VRAM reduction
- 10-15% speed improvement
- Better for long sequences

**VAE Half Precision:**
```
# In VAE settings
Set: fp16 or "bfloat16"
Results in:
- 50% VAE VRAM reduction
- Imperceptible quality loss
```

### Node Optimization Tips

1. **Disable unused text encoders** when not needed
   - T5XXL: Required for advanced prompts, ~2GB
   - CLIP: Always needed, ~1GB
   - Option: Load only one encoder if workflow doesn't require both

2. **Batch similar operations**
   - Process multiple prompts on same base image
   - Reuse latent encodings
   - Cache conditioning tensors

3. **Use appropriate denoise values**
   - Inpainting: denoise 0.75-0.85
   - Style transfer: denoise 0.6-0.75
   - Subtle refinement: denoise 0.3-0.5

### Sampling Algorithm Selection

**For FLUX.1 Kontext:**
```
Euler (Recommended):
- Stable convergence
- Good quality/speed balance
- Predictable results

DPM++ 2M Karras:
- Slightly better quality
- Slightly slower
- Good for high guidance scales

DDIM:
- Fast but may have artifacts
- Lower quality than Euler
- Not recommended for FLUX
```

## Workflow Patterns for Miniature Painting

### Pattern 1: Detail Enhancement
```
Base Miniature → Light Inpainting (denoise 0.4)
                 ↓
            Enhanced Details

Configuration:
- Small mask around detail area
- Prompt: "More intricate details on [region]"
- Denoise: 0.4 (light touch)
- Guidance: 6.0
```

### Pattern 2: Style Transfer
```
Existing Style Ref → Extract Style
Base Miniature    → CLIPTextEncode combined style
                    ↓
            Style-transferred output

Configuration:
- High context weight (0.8)
- Prompt includes style description
- Multiple reference images for consistency
```

### Pattern 3: Consistency Enforcement
```
Previous Output → Reference Image
New Subject    → CLIPTextEncode
                ↓
        Consistent New Subject

Configuration:
- Load previous output as reference
- Adjust prompt for new subject
- Use same guidance scale
- Maintain denoise at 1.0
```

### Pattern 4: Aspect Ratio Lock
```
Base 1:1 Image → Latent Preparation
              ↓
        [KSampler] (fixed 768x768)
              ↓
        [VAE Decode]

Configuration:
- Explicitly set latent dimensions
- Sampler output: 768×768 (1:1)
- Enable aspect ratio lock in node
```

## Troubleshooting Common Issues

### Issue: Inconsistent Results
**Solution:**
- Set explicit seed value
- Use same guidance scale
- Maintain consistent step count
- Reference previous image in context

### Issue: Blurry Edges in Inpainting
**Solution:**
- Use feathered mask (gaussian_blur kernel)
- Increase denoise slightly (0.85-0.9)
- Use larger context area around edit region
- Reduce guidance scale (5.0-5.5)

### Issue: Out of Memory
**Solution:**
- Enable Xformers attention
- Use 512x512 instead of 768x768
- Reduce batch size to 1
- Enable VAE half precision
- Use Q4_K quantization

### Issue: Slow Inference
**Solution:**
- Reduce steps: 28 → 20 (acceptable quality)
- Use Lightning LoRA: 8 steps instead of 28
- Enable Xformers
- Use smaller resolution (512x512)
- Quantize model to GGUF

### Issue: Style Inconsistency Across Batch
**Solution:**
- Use reference blending node
- Pre-encode reference images
- Keep guidance scale constant
- Use identical sampler settings
- Add explicit style descriptors to prompts

## Workflow Export and Sharing

### Save Workflow
```
ComfyUI Web UI → Menu → Save Workflow
Outputs: workflow.json (contains all settings)
```

### Load Workflow
```
ComfyUI Web UI → Menu → Load Workflow
Select: workflow.json
All nodes and settings restored
```

### Share Workflow
```json
{
  "name": "Miniature In-Context Editing",
  "description": "FLUX.1 Kontext inpainting for detail enhancement",
  "version": "1.0",
  "nodes": { /* ... */ },
  "links": { /* ... */ },
  "groups": [],
  "config": {},
  "extra": {},
  "version": 0.4
}
```

## Best Practices for Production

1. **Version Control Workflows**
   - Save workflow.json to git
   - Document prompt templates
   - Track quantization/LoRA versions

2. **Batch Processing Optimization**
   - Process multiple miniatures sequentially
   - Reuse loaded model across batches
   - Cache reference encodings

3. **Quality Assurance**
   - Save preview at low quality first
   - Iterate on promising results
   - Final pass at high quality

4. **Performance Monitoring**
   - Log generation times
   - Track VRAM usage
   - Monitor quality scores

5. **Documentation**
   - Document successful prompt formulas
   - Record working node configurations
   - Archive reference images

## Integration with External Tools

### Exporting to Batch Processing Scripts
```python
import json

# Load ComfyUI workflow
with open("workflow.json") as f:
    workflow = json.load(f)

# Extract prompt and settings
prompts = [node["inputs"]["text"] for node in workflow.values()
           if node["class_type"] == "CLIPTextEncode"]

steps = workflow["3"]["inputs"]["steps"]  # KSampler node
guidance = workflow["3"]["inputs"]["cfg"]
```

### Importing Results to Image Management
```python
# Move generated images to organized directory
import shutil
from pathlib import Path

output_dir = Path("ComfyUI/output")
archive_dir = Path("./miniature_gallery/generated")

for image_file in output_dir.glob("*.png"):
    shutil.move(str(image_file), str(archive_dir / image_file.name))
```
