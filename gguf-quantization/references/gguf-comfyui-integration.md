# ComfyUI GGUF Integration Guide

## Overview

ComfyUI-GGUF is a custom node package that enables direct loading and inference of GGUF-quantized models within ComfyUI workflows. This guide covers setup, configuration, and optimization.

## Installation

### Prerequisites

- ComfyUI installed and working
- Python 3.8+ (same environment as ComfyUI)
- GPU with 8GB+ VRAM (or CPU if desired)
- GGUF quantized model files ready

### Step 1: Install ComfyUI-GGUF

```bash
# Navigate to ComfyUI custom nodes directory
cd ComfyUI/custom_nodes

# Clone ComfyUI-GGUF repository
git clone https://github.com/city96/ComfyUI-GGUF.git
cd ComfyUI-GGUF

# Install Python dependencies
pip install -r requirements.txt

# Return to ComfyUI root
cd ../..
```

### Step 2: Verify Installation

```bash
# Restart ComfyUI or refresh in web UI
# Check Node Selector for new GGUF nodes:
# - GGUF Loader
# - GGUF Model Loader
# - GGUF Sampler

# In web console, look for loading messages
```

### Step 3: Prepare Model Directory

```bash
# Create dedicated GGUF models directory
mkdir -p models/gguf

# Copy or move GGUF files
cp /path/to/unet-q4_k.gguf models/gguf/
cp /path/to/unet-q5_k.gguf models/gguf/

# Verify file permissions
chmod 644 models/gguf/*.gguf
ls -lh models/gguf/
```

## Configuration

### ComfyUI Settings

Edit `web/settings.js` or use web UI settings:

```javascript
{
  "gguf": {
    "gpu_layers": -1,  // -1 = all layers on GPU, 0 = CPU only
    "gpu_memory": "auto",  // auto or specific MB value
    "mmap": true,  // Memory map for reduced RAM
    "precision": "auto",  // auto, fp32, fp16, or bfloat16
    "tensor_split": [],  // For multi-GPU setups
    "optimized_matmul": true
  }
}
```

### Environment Variables

```bash
# Set before running ComfyUI
export CUDA_VISIBLE_DEVICES=0  # GPU to use
export GGML_NUM_THREADS=8  # CPU threads
export GGML_GPU_MEMORY=12000  # MB limit for GPU
export OMP_NUM_THREADS=8  # OpenMP threads

# For Mac with Metal acceleration
export GGML_METAL_DEVICE_MEMORY=8000

# Then start ComfyUI
python main.py
```

## GGUF Node Types

### GGUF Model Loader

**Purpose**: Load GGUF model file into memory

**Inputs:**
- `gguf_model`: File selection dropdown
- `gpu_layers`: Number of layers to GPU (0 = CPU only, -1 = all)
- `tensor_split`: Multi-GPU split ratio
- `n_ctx`: Context size (usually 512 for diffusion)

**Outputs:**
- `GGUF_MODEL`: Loaded model object

**Example Workflow Connection:**
```
[GGUF Model Loader] → Model
    ↓
    → GGUF Sampler (connected to KSampler input)
```

### GGUF Sampler

**Purpose**: Run inference on GGUF model

**Inputs:**
- `model`: From GGUF Model Loader
- `positive`: Positive prompt conditioning
- `negative`: Negative prompt conditioning
- `seed`: Random seed for reproducibility
- `steps`: Number of diffusion steps (20-50 typical)
- `cfg`: Classifier-free guidance scale (7.0-15.0 typical)
- `sampler`: Sampling method (euler, dpmpp, ddim, etc.)
- `scheduler`: Noise scheduler (normal, karras, etc.)

**Outputs:**
- `LATENT`: Generated latent representation

**Configuration Tips:**
```
- steps: 25-30 for Q4_K (good balance)
- cfg: 7.0-10.0 for quality
- sampler: DPM++ 2M Karras (fast)
- scheduler: Karras (smooth progression)
```

### GGUF Decoder

**Purpose**: Decode latent to image

**Inputs:**
- `LATENT`: From GGUF Sampler
- `vae`: VAE model (can be standard VAE or GGUF)

**Outputs:**
- `IMAGE`: Final generated image

## Basic Workflow Setup

### Simple Text-to-Image Workflow

```json
{
  "1": {
    "class_type": "CheckpointLoaderSimple",
    "inputs": {
      "ckpt_name": "vae-fp32.safetensors"
    }
  },
  "2": {
    "class_type": "CLIPTextEncode",
    "inputs": {
      "text": "a beautiful sunset over mountains",
      "clip": ["1", 0]
    }
  },
  "3": {
    "class_type": "CLIPTextEncode",
    "inputs": {
      "text": "blurry, distorted",
      "clip": ["1", 1]
    }
  },
  "4": {
    "class_type": "GGUFLoader",
    "inputs": {
      "gguf_model": "unet-q4_k.gguf",
      "gpu_layers": -1
    }
  },
  "5": {
    "class_type": "GGUFSampler",
    "inputs": {
      "model": ["4", 0],
      "positive": ["2", 0],
      "negative": ["3", 0],
      "seed": 42,
      "steps": 25,
      "cfg": 7.0,
      "sampler": "dpmpp_2m_karras",
      "scheduler": "karras"
    }
  },
  "6": {
    "class_type": "VAEDecode",
    "inputs": {
      "samples": ["5", 0],
      "vae": ["1", 0]
    }
  },
  "7": {
    "class_type": "SaveImage",
    "inputs": {
      "images": ["6", 0],
      "filename_prefix": "gguf_output"
    }
  }
}
```

## Performance Optimization

### VRAM Usage Reduction

**GPU Layers Configuration:**

```
RTX 3060 (12GB) + SD1.5 Q4_K:
- All GPU (-1): Uses ~10-11GB VRAM
- Partial (20 layers): Uses ~8-9GB VRAM
- CPU only (0): Uses ~2-3GB VRAM

Recommendation for RTX 3060: gpu_layers = -1 (safe)
```

**Memory Map (mmap) Settings:**

```bash
# Enable memory mapping for reduced RAM footprint
# Automatically enabled for GGUF files
# Reduces peak memory usage by 30-40%
```

### Speed Optimization

**Sampler Selection for Different Targets:**

```
Real-time (>1 img/sec):
- Sampler: Euler
- Steps: 15-20
- Scheduler: Linear

Balanced (0.5-1 img/sec):
- Sampler: DPM++ 2M Karras
- Steps: 25
- Scheduler: Karras

Quality (>5 min per image):
- Sampler: DPM++ 3M SDE Karras
- Steps: 50
- Scheduler: Karras
```

### Multi-GPU Setup

For systems with multiple GPUs:

```javascript
// In settings
{
  "gguf": {
    "tensor_split": [0.4, 0.6],  // 40% GPU 0, 60% GPU 1
    "multi_gpu": true
  }
}

// Or via environment
export CUDA_VISIBLE_DEVICES=0,1
```

## Advanced Configuration

### Mixed Precision

```python
# In custom node configuration
precision_config = {
    "fp32": "Full precision (slowest, best quality)",
    "fp16": "Half precision (2x faster, slight quality loss)",
    "bfloat16": "Google Brain Float (good balance)",
    "auto": "Let system decide based on GPU"
}
```

### Tensor Operations

**Optimization Options:**

```
flash_attention: True  # For RTX 30/40 series
xformers: False  # Not compatible with GGUF
memory_efficient_attention: True
```

### Custom Sampling

For advanced workflows, create custom sampler nodes:

```python
# Custom sampler combining multiple techniques
class GGUFAdvancedSampler:
    def __init__(self):
        self.model = None
        self.accelerator = "auto"

    def sample(self, model, prompt_cond, steps, cfg):
        # Custom sampling logic
        # Can combine Q4_K model with FP32 attention layers
        pass
```

## Troubleshooting

### Issue: "Model not found" Error

**Solutions:**
1. Check GGUF file is in `models/gguf/` directory
2. Verify filename exactly matches dropdown
3. Check file permissions (should be readable)
4. Restart ComfyUI to refresh model list

### Issue: "CUDA out of memory"

**Solutions:**
1. Reduce `gpu_layers` (use fewer GPU layers)
2. Enable memory mapping (`mmap: true`)
3. Switch to CPU inference (`gpu_layers: 0`)
4. Use lower quantization (Q4_K → Q3_K)

### Issue: "Slow inference" (5+ min per image)

**Solutions:**
1. Increase `gpu_layers` if VRAM allows
2. Switch sampler to Euler (faster)
3. Reduce steps (20-25 sufficient for most)
4. Check that GPU acceleration is active
5. Verify CUDA driver is up to date

### Issue: "Poor quality output"

**Solutions:**
1. Verify correct GGUF model loaded
2. Try higher quantization (Q4_K → Q5_K)
3. Increase steps (25 → 30)
4. Adjust CFG scale (try 7.0-12.0)
5. Test with original FP32 to compare

### Issue: "File corrupted" message

**Solutions:**
1. Re-download or reconvert GGUF model
2. Verify original SafeTensors file
3. Check conversion completed fully
4. Try with different quantization level

## Best Practices

### Workflow Organization

1. **Keep models separate**
   - Text encoder as FP32 or Q5_K
   - UNet as Q4_K (primary inference)
   - VAE as FP32 or Q6_K

2. **Group similar operations**
   - All prompt encoding together
   - Sampling operations sequential
   - Decode and save at end

3. **Use meaningful names**
   - Label nodes clearly
   - Document expected inputs/outputs
   - Add comments for non-obvious parameters

### Memory Management

1. **Monitor VRAM during generation**
   - Use nvidia-smi on command line
   - Watch for spikes during sampling
   - Plan for 30-50% headroom

2. **Batch processing safely**
   - Generate one image first
   - Monitor peak usage
   - Batch size typically 1-4

### Quality Assurance

1. **Test each configuration**
   - Generate test images
   - Compare against FP32 baseline
   - Document quality/speed tradeoffs

2. **Validate model integrity**
   - Generate with known seeds
   - Compare outputs across GPUs
   - Check for consistency

## Performance Benchmarks

### RTX 3060 (12GB VRAM)

```
Model: SD 1.5 UNet Q4_K
Speed: 3-4 img/sec at 512x512
VRAM: ~10-11 GB peak
Quality: Excellent (imperceptible loss)
Recommended: Daily use, production
```

### RTX 4080 (16GB VRAM)

```
Model: SDXL UNet Q5_K
Speed: 2-3 img/sec at 1024x1024
VRAM: ~13-14 GB peak
Quality: Near-lossless
Recommended: Professional work
```

### RTX 4090 (24GB VRAM)

```
Model: SDXL UNet Q6_K
Speed: 2-2.5 img/sec at 1024x1024
VRAM: ~15-16 GB peak
Quality: Lossless
Recommended: Research, quality priority
```

## Integration with Other Nodes

### With ControlNet

```python
# ControlNet + GGUF
# ControlNet layer uses standard attention
# GGUF model handles full diffusion
# Fully compatible, no special config needed
```

### With LoRA

```python
# LoRA + GGUF Q4_K Model
# Load LoRA as FP32 adapter
# Apply to quantized GGUF base model
# Works seamlessly in ComfyUI
```

### With IP-Adapter

```python
# IP-Adapter + GGUF
# Image prompt adapters work with GGUF
# Use standard IP-Adapter nodes
# Fully compatible
```

## Advanced Workflows

### A/B Testing Quantization Levels

```json
{
  "branch_a": {
    "loader": "GGUFLoader with Q4_K",
    "sampler": "GGUFSampler"
  },
  "branch_b": {
    "loader": "GGUFLoader with Q5_K",
    "sampler": "GGUFSampler"
  },
  "compare": {
    "difference_node": "Compare output quality"
  }
}
```

### Batch Processing

```python
# Efficient batch processing with GGUF
model = load_gguf_once()
for prompt in prompts_list:
    # Reuse loaded model
    output = sample(model, prompt)
    # VRAM remains stable across batch
```

## Summary

- ComfyUI-GGUF enables efficient GGUF inference in workflows
- Q4_K offers best balance for most users
- Configure GPU layers based on VRAM availability
- Monitor performance and adjust sampler settings
- Fully compatible with existing ComfyUI nodes and workflows
- Enable significant VRAM savings (2-4x reduction)
