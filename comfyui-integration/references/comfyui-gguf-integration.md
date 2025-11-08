# ComfyUI GGUF Integration Guide

## Overview

GGUF (GPT-Generated Unified Format) enables inference with quantized models on consumer hardware. ComfyUI-GGUF provides nodes for text generation, embedding, and other inference tasks using llama.cpp as the backend.

## GGUF Advantages

- **Reduced Model Size** - 4-8x smaller through quantization (Q4_K, Q5_K, etc.)
- **CPU Inference** - Run on CPU with acceptable performance
- **Low Memory** - 8B models fit on devices with 8GB RAM
- **Fast Inference** - Optimized C++ implementation via llama.cpp
- **Quantization Options** - Multiple precision levels (2-8 bit)

## Disadvantages

- **Quality Loss** - Reduced precision impacts output quality
- **Limited Model Support** - Not all architectures available in GGUF
- **Slower than GPU** - CPU inference is slower than GPU
- **Precision Trade-offs** - Requires testing to find acceptable quantization level

## Installation

### Prerequisites

```bash
# Install ComfyUI
git clone https://github.com/comfyanonymous/ComfyUI
cd ComfyUI
pip install -r requirements.txt

# Install GGUF support
cd custom_nodes
git clone https://github.com/city96/ComfyUI-GGUF.git
cd ComfyUI-GGUF
pip install -r requirements.txt
```

### Dependencies

The ComfyUI-GGUF node requires:
- `llama-cpp-python` - Python bindings for llama.cpp
- `numpy` - Array processing
- Optional: `ctransformers` - Alternative backend

### GPU Acceleration (Optional)

For GPU-accelerated GGUF inference:

```bash
# NVIDIA (CUDA)
pip install llama-cpp-python --force-reinstall --no-cache-dir \
  --compile=cuda

# AMD (ROCm)
pip install llama-cpp-python --force-reinstall --no-cache-dir \
  --compile=rocm

# Apple (Metal)
pip install llama-cpp-python --force-reinstall --no-cache-dir \
  --compile=metal
```

## Available GGUF Models

### Language Models

**Llama 2 (7B-70B)**
- Source: Meta, available on Hugging Face
- Quantizations: Q4_K_M, Q5_K_M, Q6_K, Q8_0
- Use Cases: Text generation, code completion, chat

**Mistral (7B)**
- Source: Mistral AI
- Quantizations: Q4_K_M (fastest), Q5_K_M (balanced), Q8_0 (highest quality)
- Use Cases: Fast inference, instruction-following

**Llamavision (Multimodal)**
- Image understanding with text
- Quantizations: Q4_K, Q5_K
- Use Cases: Image-to-text, visual question answering

**Phi (2.7B-14B)**
- Microsoft lightweight models
- Quantizations: Q4_K, Q5_K
- Use Cases: Resource-constrained environments

### Embedding Models

**BERT (small, base, large)**
- Text embedding generation
- Quantizations: Q4_K, Q5_K, Q8_0
- Use Cases: Semantic search, clustering

**E5 (small, base, large)**
- High-quality embeddings
- Quantizations: Q4_K, Q5_K
- Use Cases: Retrieval-augmented generation

### Download Sources

**Hugging Face:**
```bash
# Use huggingface-cli
huggingface-cli download TheBloke/Mistral-7B-GGUF \
  mistral-7b.Q4_K_M.gguf \
  --local-dir ./models/gguf
```

**GGUF Model Database:**
- https://huggingface.co/TheBloke (thousands of quantized models)
- https://huggingface.co/models?search=gguf

## Quantization Levels

| Level | Size | Speed | Quality | Use Case |
|-------|------|-------|---------|----------|
| Q2_K | 2-3 bits | Very Fast | Poor | Prototype/Testing |
| Q3_K | 3 bits | Fast | Fair | Lightweight deployment |
| Q4_K_M | 4 bits | Good | Good | **Recommended** |
| Q5_K_M | 5 bits | Slower | Very Good | High quality, 8GB+ RAM |
| Q6_K | 6 bits | Slow | Excellent | Best quality |
| Q8_0 | 8 bits | Slower | Perfect | Reference/Fine-tuning |

**Recommendation:** Start with Q4_K_M for best speed/quality balance.

## ComfyUI GGUF Nodes

### GGUF_Loader

Load a GGUF model into memory.

**Inputs:**
- `model_path` - Path to .gguf file
- `n_gpu_layers` - Layers to offload to GPU (0 = CPU only)
- `n_ctx` - Context window size (default 2048, max depends on model)
- `n_threads` - CPU threads (default 4)
- `use_mmap` - Use memory mapping (faster loading)

**Outputs:**
- `GGUF_MODEL` - Loaded model handle

**Example Workflow Node:**
```json
{
  "1": {
    "class_type": "GGUF_Loader",
    "inputs": {
      "model_path": "models/gguf/mistral-7b.Q4_K_M.gguf",
      "n_gpu_layers": 0,
      "n_ctx": 2048,
      "n_threads": 4,
      "use_mmap": true
    }
  }
}
```

### GGUF_Sampler

Generate text from a GGUF model.

**Inputs:**
- `model` - GGUF_MODEL from loader
- `prompt` - Input text prompt
- `max_tokens` - Maximum output length
- `temperature` - Sampling temperature (0.7-1.0 typical)
- `top_p` - Nucleus sampling parameter
- `top_k` - Keep top-k tokens
- `repeat_penalty` - Penalize repeated tokens
- `seed` - Random seed for reproducibility

**Outputs:**
- `TEXT` - Generated text
- `STATISTICS` - Generation metadata (tokens, time, etc.)

**Example Workflow Node:**
```json
{
  "2": {
    "class_type": "GGUF_Sampler",
    "inputs": {
      "model": ["1", 0],
      "prompt": "Once upon a time",
      "max_tokens": 256,
      "temperature": 0.8,
      "top_p": 0.95,
      "top_k": 50,
      "repeat_penalty": 1.1,
      "seed": 12345
    }
  }
}
```

## Performance Optimization

### CPU Settings

```json
{
  "n_threads": 4,           # Match CPU cores (4-8 typical)
  "n_batch": 512,           # Batch size (higher = faster, more VRAM)
  "use_mmap": true,         # Memory-mapped file I/O
  "use_mlock": false        # Lock in RAM (only if system RAM available)
}
```

### GPU Acceleration

```json
{
  "n_gpu_layers": 33,       # Layer count (varies by model size)
  "use_flash_attention": true,  # For supported GPUs
  "tensor_split": [0.5, 0.5]    # Multi-GPU distribution
}
```

### Context Window Tuning

```json
{
  "n_ctx": 2048,            # Default sufficient for most tasks
  "n_ctx": 4096,            # Longer context (uses more memory)
  "n_ctx": 512              # Shorter context (faster, less VRAM)
}
```

## Memory Requirements

### Estimation Formula

```
VRAM (GB) ≈ (Model Size in B * Precision Bits) / 8 + Overhead
```

**Examples:**

| Model | Quantization | Size | VRAM Needed |
|-------|--------------|------|-------------|
| 7B | Q4_K | ~3.5 GB | 4 GB |
| 7B | Q5_K | ~4.2 GB | 5 GB |
| 13B | Q4_K | ~7 GB | 8 GB |
| 70B | Q4_K | ~35 GB | 40 GB |

**Overhead:** ~500 MB for model loading, context, batch processing.

## Practical Workflows

### Simple Text Generation

```json
{
  "1": {
    "class_type": "GGUF_Loader",
    "inputs": {
      "model_path": "models/gguf/mistral-7b.Q4_K_M.gguf",
      "n_gpu_layers": 0
    }
  },
  "2": {
    "class_type": "GGUF_Sampler",
    "inputs": {
      "model": ["1", 0],
      "prompt": "Write a Python function to calculate Fibonacci numbers",
      "max_tokens": 512,
      "temperature": 0.7,
      "top_p": 0.9
    }
  }
}
```

### Retrieval-Augmented Generation (RAG)

```json
{
  "1": {
    "class_type": "GGUF_Loader",
    "inputs": {"model_path": "models/gguf/e5-large.Q5_K.gguf"}
  },
  "2": {
    "class_type": "GGUF_Sampler",
    "inputs": {
      "model": ["1", 0],
      "prompt": "[QUERY] What is machine learning?",
      "max_tokens": 128
    }
  }
}
```

## Troubleshooting

### Out of Memory Errors

```python
# Reduce context window
"n_ctx": 512  # from 2048

# Reduce batch size
"n_batch": 128  # from 512

# Use higher quantization
# Q4_K_M instead of Q5_K
```

### Slow Inference

```python
# Increase GPU layers (if GPU available)
"n_gpu_layers": 33

# Increase batch size
"n_batch": 1024

# Reduce context window if not needed
"n_ctx": 512
```

### Poor Output Quality

```python
# Use higher precision quantization
# Q5_K_M instead of Q4_K

# Adjust sampling parameters
"temperature": 0.8      # Increase for more diversity
"top_p": 0.95           # Increase for more tokens considered

# Longer context for coherence
"n_ctx": 4096
```

## Best Practices

1. **Test Quantizations** - Try Q4_K, Q5_K on your data
2. **Monitor Memory** - Watch VRAM/RAM during inference
3. **Cache Models** - Preload models for repeated use
4. **Batch Requests** - Process multiple prompts together
5. **Use Seeds** - Set seeds for reproducible outputs
6. **Document Settings** - Save working configurations
7. **Profile Performance** - Measure latency and throughput

## Model Conversion

To create your own GGUF models:

```bash
# Install conversion tools
pip install llama-cpp-python

# Convert to GGUF
python -m llama_cpp.convert-huggingface-to-gguf \
  --model-id mistralai/Mistral-7B \
  --outfile mistral-7b-original.gguf

# Quantize to Q4
llama-quantize mistral-7b-original.gguf \
  mistral-7b.Q4_K_M.gguf Q4_K_M
```

## Licensing Notes

- **GGUF Format** - Proprietary but widely used, implementation is open-source
- **Models** - Check individual model licenses (Llama, Mistral, etc.)
- **llama.cpp** - MIT License
- **llama-cpp-python** - MIT License

Safe to use in proprietary applications via API-only pattern.

## References

- **ComfyUI-GGUF GitHub:** https://github.com/city96/ComfyUI-GGUF
- **llama.cpp Project:** https://github.com/ggerganov/llama.cpp
- **GGUF Model Database:** https://huggingface.co/TheBloke
- **Quantization Guide:** https://github.com/ggerganov/llama.cpp/wiki/Quantization
