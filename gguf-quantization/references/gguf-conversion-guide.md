# GGUF Conversion Guide: SafeTensors to GGUF

## Overview

This guide walks through the complete process of converting SafeTensors diffusion models (from Hugging Face) to GGUF format with quantization optimization.

## Prerequisites

### Required Software
- Python 3.8+ (3.10+ recommended)
- llama.cpp (for GGUF conversion tools)
- CUDA Toolkit 11.8+ (for GPU acceleration, optional)
- 10-20 GB free disk space (for conversion process)

### Installation

```bash
# Clone llama.cpp repository
git clone https://github.com/ggerganov/llama.cpp
cd llama.cpp

# Install Python dependencies
pip install -r requirements.txt

# Build llama.cpp (optional, for GPU support)
mkdir build && cd build
cmake .. -DLLAMA_CUDA=ON  # For NVIDIA GPU
cmake .. -DLLAMA_METAL=ON  # For Apple Silicon
cmake ..                     # CPU only
make -j4
cd ..
```

### Python Dependencies
```bash
pip install torch torchvision torchaudio --index-url https://download.pytorch.org/whl/cu118
pip install transformers diffusers accelerate safetensors
```

## Step 1: Download Model

### From Hugging Face

```bash
# Download Stable Diffusion 1.5
huggingface-cli download runwayml/stable-diffusion-v1-5 \
  --local-dir ./models/sd15-fp32 \
  --local-dir-use-symlinks False

# Download SDXL
huggingface-cli download stabilityai/stable-diffusion-xl-base-1.0 \
  --local-dir ./models/sdxl-fp32 \
  --local-dir-use-symlinks False
```

### Model Structure

```
model_directory/
├── unet/
│   ├── diffusion_pytorch_model.safetensors
│   └── config.json
├── text_encoder/
│   ├── pytorch_model.safetensors
│   └── config.json
├── vae/
│   ├── diffusion_pytorch_model.safetensors
│   └── config.json
├── model_index.json
├── scheduler/
│   └── scheduler_config.json
└── tokenizer/
    └── vocab.json (varies by model)
```

## Step 2: Prepare Model for Conversion

### Extract Model Components

Diffusion models have multiple components that can be quantized separately:

```python
from diffusers import StableDiffusionPipeline
import torch
from safetensors.torch import save_file

# Load full model
pipe = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5",
    torch_dtype=torch.float32
)

# Extract individual components
unet_state = pipe.unet.state_dict()
text_encoder_state = pipe.text_encoder.state_dict()
vae_state = pipe.vae.state_dict()

# Save as SafeTensors for conversion
save_file(unet_state, "unet.safetensors")
save_file(text_encoder_state, "text_encoder.safetensors")
save_file(vae_state, "vae.safetensors")
```

### Single Model Conversion (Recommended for GGUF)

For GGUF, it's easiest to convert the UNet (main inference component):

```bash
# Move to model directory
cd models/sd15-fp32/unet

# Verify SafeTensors file exists
ls -lh diffusion_pytorch_model.safetensors
```

## Step 3: Convert SafeTensors to GGUF

### Using llama.cpp convert.py

```bash
# Navigate to llama.cpp directory
cd llama.cpp

# Convert SafeTensors to GGUF (no quantization yet)
python convert.py \
  --model-path /path/to/diffusion_pytorch_model.safetensors \
  --outfile /path/to/unet-fp32.gguf
```

### Using Specialized Diffusion Script

For diffusion models, specialized scripts provide better results:

```bash
# Clone diffusers-to-gguf conversion tools
git clone https://github.com/ggerganov/ggml.git

# Conversion with model info preservation
python convert-diffusers-to-ggml.py \
  --model-path runwayml/stable-diffusion-v1-5 \
  --output-dir ./gguf-models/ \
  --model-type unet
```

### Conversion Options

**Important Conversion Parameters:**

```bash
# Full conversion with all options
python convert.py \
  --model-path ./models/sd15/unet/diffusion_pytorch_model.safetensors \
  --outfile ./gguf-models/unet-fp32.gguf \
  --precision f32 \
  --verbose \
  --progress
```

**Parameters:**
- `--model-path`: Path to input SafeTensors file
- `--outfile`: Output GGUF file path
- `--precision`: fp32 or fp16 (default: fp32)
- `--verbose`: Show detailed conversion info
- `--progress`: Display conversion progress

### Conversion Time Expectations

| Model | Size | Time (CPU) | Time (GPU) |
|-------|------|-----------|-----------|
| SD 1.5 UNet | 3.5 GB | 10-15 min | 2-3 min |
| SDXL UNet | 5.2 GB | 15-25 min | 3-5 min |
| Text Encoder | 1.4 GB | 5-10 min | 1-2 min |
| VAE | 0.3 GB | 2-3 min | <1 min |

## Step 4: Quantize GGUF Model

### Quantization Utility

```bash
# Using llama.cpp quantization tool
cd llama.cpp

# List available quantization levels
./quantize --help

# Quantize to Q4_K (recommended)
./quantize ./unet-fp32.gguf ./unet-q4_k.gguf Q4_K

# Quantize to Q5_K (high quality)
./quantize ./unet-fp32.gguf ./unet-q5_k.gguf Q5_K

# Quantize to Q3_K (maximum compression)
./quantize ./unet-fp32.gguf ./unet-q3_k.gguf Q3_K
```

### Quantization Levels Available

```
Q2_K    2-bit   ~90% reduction (extreme compression)
Q3_K    3-bit   ~85% reduction (aggressive compression)
Q4_0    4-bit   ~75% reduction (original Q4)
Q4_1    4-bit   ~75% reduction (Q4 variant)
Q4_K    4-bit   ~75% reduction (K-quant, recommended)
Q5_K    5-bit   ~60% reduction (high quality)
Q6_K    6-bit   ~50% reduction (very high quality)
Q8_K    8-bit   ~25% reduction (near-lossless)
```

### Quantization Time Expectations

```
Base Model: 3.5 GB UNet

Q2_K: 5-10 seconds
Q3_K: 10-15 seconds
Q4_K: 15-20 seconds (recommended)
Q5_K: 20-30 seconds
Q6_K: 30-45 seconds
```

### Batch Quantization Script

```bash
#!/bin/bash
# quantize-all.sh - Quantize same model to multiple levels

MODEL_FP32="unet-fp32.gguf"
OUTPUT_DIR="./quantized-models/"

mkdir -p $OUTPUT_DIR

LLAMA_CPP="./llama.cpp/quantize"

for level in Q3_K Q4_K Q5_K Q6_K; do
    echo "Quantizing to $level..."
    $LLAMA_CPP $MODEL_FP32 $OUTPUT_DIR/unet-$level.gguf $level
    ls -lh $OUTPUT_DIR/unet-$level.gguf
done

echo "Quantization complete!"
ls -lh $OUTPUT_DIR
```

## Step 5: Validation and Testing

### File Verification

```bash
# Check output file properties
ls -lh unet-q4_k.gguf

# Inspect GGUF metadata (if tools available)
gguf-info unet-q4_k.gguf

# Compare file sizes
echo "Original:"
ls -lh unet-fp32.gguf
echo "Quantized Q4_K:"
ls -lh unet-q4_k.gguf
echo "Size reduction:"
du -h unet-fp32.gguf unet-q4_k.gguf | awk '{print $1}'
```

### Test Inference (Python)

```python
# Test with llama-cpp-python or similar
from llama_cpp import Llama

# Load quantized model
model = Llama(
    model_path="./unet-q4_k.gguf",
    n_gpu_layers=-1,  # Use GPU
    verbose=False
)

# Check model info
print(f"Model loaded successfully")
print(f"Parameters: {model.metadata}")
```

### Benchmark Quality

```python
import torch
from PIL import Image
import numpy as np

# Load original and quantized models
# Compare outputs with identical seed and inputs

seed = 42
prompt = "a beautiful sunset over mountains"

# Generate with original (FP32)
# Generate with quantized (Q4_K)
# Compute LPIPS or visual difference

# Simple comparison: compute MSE
original_output = ...
quantized_output = ...
mse = np.mean((original_output - quantized_output) ** 2)
print(f"MSE between FP32 and Q4_K: {mse}")
```

## Step 6: Integration with ComfyUI

### Setup ComfyUI-GGUF

```bash
# Clone ComfyUI if not already done
git clone https://github.com/comfyui/ComfyUI.git
cd ComfyUI

# Install ComfyUI-GGUF custom nodes
cd custom_nodes
git clone https://github.com/city96/ComfyUI-GGUF.git
cd ..

# Install node dependencies
pip install -r custom_nodes/ComfyUI-GGUF/requirements.txt
```

### Organize Models

```bash
# Create GGUF models directory
mkdir -p ./models/gguf

# Copy quantized models
cp unet-q4_k.gguf ./models/gguf/
cp unet-q5_k.gguf ./models/gguf/

# Create metadata (optional but recommended)
cat > ./models/gguf/unet-q4_k.yaml << EOF
name: "Stable Diffusion 1.5 UNet Q4_K"
description: "4-bit quantized UNet from SD 1.5"
format: "gguf"
quantization: "Q4_K"
source: "runwayml/stable-diffusion-v1-5"
filesize: "~1.1 GB"
vram: "~3.5 GB"
quality: "Excellent"
notes: "Recommended for most users"
EOF
```

### Load in ComfyUI

In ComfyUI workflow JSON:

```json
{
  "1": {
    "class_type": "CheckpointLoaderSimple",
    "inputs": {
      "ckpt_name": "unet-q4_k.gguf"
    }
  },
  "2": {
    "class_type": "GGUFLoader",
    "inputs": {
      "gguf_name": "unet-q4_k.gguf",
      "weight_dtype": "auto"
    }
  }
}
```

## Step 7: Performance Tuning

### Memory Optimization

```python
# Reduce VRAM usage further if needed

# Option 1: Load model in lower precision
torch.set_float32_matmul_precision('medium')

# Option 2: Enable memory-efficient attention
from torch.nn import functional as F
# Use flash attention if available

# Option 3: Memory map tensor data
# (Handled automatically by GGUF)
```

### Speed Optimization

```bash
# Enable GPU acceleration in ComfyUI
export CUDA_VISIBLE_DEVICES=0

# Use fp16 computation where supported
# Use tensor cores for RTX 30/40 series

# Batch processing for throughput
# Generate multiple images in sequence
```

## Troubleshooting

### Issue: "Conversion fails with Out of Memory"

**Solutions:**
1. Use GPU-accelerated conversion if available
2. Reduce batch size during conversion
3. Convert individual components separately
4. Use smaller intermediate models first

### Issue: "GGUF file corrupted"

**Solutions:**
1. Verify input SafeTensors file integrity
2. Re-download model from Hugging Face
3. Use different conversion tool
4. Check disk space availability

### Issue: "Poor quality after quantization"

**Solutions:**
1. Try higher quantization level (Q4_K → Q5_K)
2. Verify conversion completed fully
3. Test with multiple prompts/seeds
4. Compare against unquantized baseline

### Issue: "Model won't load in ComfyUI"

**Solutions:**
1. Verify GGUF file format (use `file` command)
2. Check ComfyUI-GGUF version compatibility
3. Verify metadata preservation
4. Try test loading with Python first

## Conversion Checklist

- [ ] Model downloaded and verified
- [ ] Python environment set up with dependencies
- [ ] llama.cpp installed and built
- [ ] Input SafeTensors file accessible
- [ ] Output directory created
- [ ] Conversion command tested with --help
- [ ] Initial FP32 GGUF created successfully
- [ ] File size reduced and verified
- [ ] Quantization applied to FP32 GGUF
- [ ] Quantized file tested for corruption
- [ ] Metadata preserved and accessible
- [ ] Quality validated with test generation
- [ ] ComfyUI integration tested
- [ ] Performance meets expectations

## Summary

The conversion process:
1. Download model from Hugging Face
2. Convert SafeTensors to GGUF (unquantized)
3. Quantize GGUF to desired level (Q4_K recommended)
4. Validate output file and test quality
5. Integrate with ComfyUI or inference engine
6. Optimize for your hardware and use case

Typical result: **4x-8x file size reduction** with **imperceptible quality loss** at Q4_K quantization.
