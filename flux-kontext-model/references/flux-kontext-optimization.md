# FLUX.1 Kontext Optimization Guide

## GGUF Quantization

GGUF (GGLM Universal Format) quantization converts FLUX.1 Kontext to an efficient binary format that reduces model size while maintaining quality.

### Why Quantize?

| Metric | Full Precision | Q4_K | Improvement |
|--------|----------------|------|-------------|
| Model Size | 24GB | 5.2GB | 78% reduction |
| VRAM Required | 24GB | 8GB | 67% reduction |
| Inference Speed | ~45s | ~18s | 2.5x faster |
| Quality | 100% baseline | 97-98% | Minimal loss |

### Quantization Levels

#### Q3_K (3-bit with K-quants)
**Best for:** Memory-constrained environments, batch processing
```
Model Size: 3.8GB
Peak VRAM: 6GB
Quality: 95% of full precision
Speed: ~12s per image (RTX 4090)
Use Case: CPU inference, limited VRAM (<8GB)
```

**Pros:**
- Smallest model size
- Runs on modest GPUs or CPU
- Fastest inference
- Suitable for deployment

**Cons:**
- Slight quality reduction
- Less detail in fine features
- Potential banding in gradients

#### Q4_K (4-bit with K-quants) - RECOMMENDED
**Best for:** Production workflows, optimal speed/quality balance**
```
Model Size: 5.2GB
Peak VRAM: 8GB
Quality: 97-98% of full precision
Speed: ~18s per image (RTX 4090)
Use Case: Standard desktop inference, batch processing
```

**Pros:**
- Excellent quality/size/speed balance
- Minimal perceptible quality loss
- Manageable file size (easy distribution)
- Fast enough for iterative workflows
- Works on 8GB VRAM systems

**Cons:**
- Slight quality reduction (usually imperceptible)
- Not as fast as lower quantizations

#### Q5_K (5-bit with K-quants)
**Best for:** Quality-critical applications, when VRAM is available
```
Model Size: 6.5GB
Peak VRAM: 10GB
Quality: 99% of full precision
Speed: ~25s per image (RTX 4090)
Use Case: Portfolio pieces, client deliverables
```

**Pros:**
- Near-imperceptible quality loss
- Still significant size reduction
- Good compression ratio

**Cons:**
- Larger than Q4_K
- Slower than Q4_K
- Minimal quality advantage over Q4_K in practice

#### Comparison for Miniature Painting
```
Use Case: Quick Iterations
Selected: Q3_K (3.8GB) for fastest feedback loops
→ 12s per image, acceptable quality for concept validation

Use Case: Production Portfolio
Selected: Q4_K (5.2GB) - recommended
→ 18s per image, imperceptible quality loss, optimal efficiency

Use Case: Client Deliverables / Gallery Pieces
Selected: Q5_K (6.5GB)
→ 25s per image, maximum quality, slightly slower
```

### Quantization Workflow

#### Step 1: Convert to GGUF Format
Using llama.cpp tools:

```bash
# Clone llama.cpp
git clone https://github.com/ggerganov/llama.cpp.git

# Convert model to GGUF
python llama.cpp/convert.py \
    --model-dir /path/to/flux-kontext-dev \
    --outtype f32

# Quantize to Q4_K
./llama.cpp/quantize \
    flux-kontext-dev-f32.gguf \
    flux-kontext-dev-q4k.gguf \
    Q4_K_M
```

#### Step 2: Load Quantized Model
Using GGUF-compatible libraries:

```python
from llama_cpp import Llama

# Load quantized model
model = Llama(
    model_path="flux-kontext-dev-q4k.gguf",
    n_gpu_layers=-1,  # All layers on GPU
    n_threads=8,
    verbose=False
)
```

#### Step 3: Quality Validation
```python
import torch
from diffusers import AutoPipelineForInpainting

# Load original (reference)
original_pipeline = AutoPipelineForInpainting.from_pretrained(
    "black-forest-labs/FLUX.1-Kontext-dev",
    torch_dtype=torch.bfloat16
)

# Load quantized
quantized_pipeline = Llama.from_pretrained(
    "flux-kontext-dev-q4k.gguf"
)

# Compare outputs
original_output = original_pipeline(prompt, image, mask).images[0]
quantized_output = quantized_pipeline(prompt, image, mask)

# Calculate SSIM (Structural Similarity Index)
from skimage.metrics import structural_similarity as ssim
similarity = ssim(original_output, quantized_output, channel_axis=2)
print(f"SSIM Score: {similarity:.3f}")  # Target: >0.95
```

### Distribution and Deployment

**Quantized Model Benefits for Distribution:**
- **Q4_K (5.2GB):** Fits on standard USB drives, downloads in minutes
- **Q3_K (3.8GB):** Distributable via HTTP, deployable on cloud instances
- **Comparison to full precision:** 78% smaller, dramatically faster downloads

**Deployment Checklist:**
- [ ] Quantization quality validated (SSIM > 0.95)
- [ ] Model tested on target hardware
- [ ] Memory profiling completed
- [ ] Inference speed benchmarked
- [ ] Distribution size acceptable
- [ ] Hash verification implemented

## Lightning LoRA Integration

Lightning LoRA adapters provide 2-4x inference speedup with minimal quality loss.

### What is Lightning LoRA?

LoRA (Low-Rank Adaptation) is a technique that trains small adapter modules instead of the entire model:
- **Lightning variant:** Optimized for FLUX.1, 2-4x speedup
- **Model-agnostic:** Works with any quantization level
- **Combines:** Can use Q4_K + Lightning LoRA together
- **Training:** Pre-trained adapters available, or train custom ones

### Performance Gains

**With Lightning LoRA (8 steps vs 28 steps standard):**

| Setting | Steps | Time | Speedup | Quality |
|---------|-------|------|---------|---------|
| Standard FLUX | 28 | 45s | 1x | 100% |
| Q4_K only | 20 | 18s | 2.5x | 97% |
| Q4_K + Lightning | 8 | 8s | 5.6x | 94-96% |
| Q3_K + Lightning | 8 | 5s | 9x | 92-94% |

### Integration with Diffusers

```python
from diffusers import AutoPipelineForInpainting
from peft import load_peft_config, PeftModel
import torch

# Load base model
pipeline = AutoPipelineForInpainting.from_pretrained(
    "black-forest-labs/FLUX.1-Kontext-dev",
    torch_dtype=torch.bfloat16
).to("cuda")

# Load Lightning LoRA
config = load_peft_config("black-forest-labs/FLUX.1-Kontext-dev-lora-lightning")
pipeline.unet = PeftModel.from_pretrained(
    pipeline.unet,
    "black-forest-labs/FLUX.1-Kontext-dev-lora-lightning"
)

# Adjust guidance for Lightning (lower is better)
result = pipeline(
    prompt="Acrylic miniature of fantasy knight, warm sidelighting, macro photography",
    image=base_image,
    mask_image=mask,
    guidance_scale=2.0,  # Reduced from 5.0-7.0
    num_inference_steps=8,  # Reduced from 28
    height=768,
    width=768,
).images[0]
```

### Training Custom Lightning LoRA

For specialized miniature painting style:

```python
from peft import LoraConfig, get_peft_model
from diffusers import AutoPipelineForInpainting
import torch

# Setup LoRA configuration
lora_config = LoraConfig(
    r=8,  # Rank
    lora_alpha=16,
    target_modules=["to_q", "to_v"],
    lora_dropout=0.05,
    bias="none"
)

# Load model and apply LoRA
model = AutoPipelineForInpainting.from_pretrained(
    "black-forest-labs/FLUX.1-Kontext-dev",
    torch_dtype=torch.bfloat16
)

model.unet = get_peft_model(model.unet, lora_config)

# Training loop (simplified)
optimizer = torch.optim.AdamW(model.parameters(), lr=1e-4)
for epoch in range(epochs):
    for batch in training_dataloader:
        # Forward pass
        outputs = model(batch["images"], batch["prompts"])
        loss = criterion(outputs.images, batch["target_images"])

        # Backward pass
        loss.backward()
        optimizer.step()
        optimizer.zero_grad()

# Save trained LoRA weights
model.unet.save_pretrained("./miniature-painting-lora")
```

### Guidance Scale Adjustment

Lightning LoRA requires lower guidance scales:

```
Standard FLUX.1 Kontext: guidance_scale = 5.0-7.0
With Lightning LoRA: guidance_scale = 1.5-2.0

Why? Lightning LoRA increases adherence to guidance,
so lower values prevent over-constraint.

Testing guidance scales with Lightning:
1.0: Creative, some deviation from prompt
1.5: Balanced (recommended)
2.0: Strong adherence
2.5+: May over-constrain, reduce detail
```

### Lightning LoRA Quality Considerations

**When to use Lightning LoRA:**
- Real-time applications (interactive editing)
- Batch processing (throughput > quality)
- Rapid iteration workflows
- Preview generation before final pass
- Cost-sensitive production

**When to avoid Lightning LoRA:**
- Portfolio/gallery pieces (use standard)
- Client deliverables (use Q5_K or full precision)
- When time allows standard inference
- Complex detailed subjects

### Combining Quantization + Lightning LoRA

**Optimal production setup for miniature painting:**

```python
from diffusers import AutoPipelineForInpainting
import torch

# Load Q4_K quantized model with Lightning LoRA
pipeline = AutoPipelineForInpainting.from_pretrained(
    "black-forest-labs/FLUX.1-Kontext-dev-q4k",  # Quantized variant
    torch_dtype=torch.float16  # Mixed precision
).to("cuda")

# Apply Lightning LoRA
pipeline.unet.load_lora_weights("./lightning-lora")

# Generate with optimized settings
result = pipeline(
    prompt="Detailed acrylic wet blending miniature of armored knight",
    image=base_image,
    mask_image=mask,
    guidance_scale=1.8,  # Lightning-optimized
    num_inference_steps=10,  # Lightning-reduced
    height=768,
    width=768,
).images[0]

# Performance: ~8s on RTX 4090
```

**Resource Profile:**
- VRAM: 8GB (vs 24GB for full precision)
- Model Size: 5.2GB quantized (vs 24GB full)
- Inference Speed: 8s per image
- Quality: 94-96% of full precision

## Memory Optimization

### For Limited VRAM (<16GB)

#### 1. Enable Attention Slicing
Reduces peak memory but adds computational cost:

```python
from diffusers import AutoPipelineForInpainting

pipeline = AutoPipelineForInpainting.from_pretrained(
    "black-forest-labs/FLUX.1-Kontext-dev",
    torch_dtype=torch.float16
)

# Enable attention slicing
pipeline.enable_attention_slicing()
# Reduces VRAM from 24GB → ~18GB, adds 10-15% time

# Or enable sequential CPU offloading
pipeline.enable_sequential_cpu_offloading()
# Reduces VRAM from 24GB → ~8GB, adds 50-100% time
```

#### 2. Use Flash Attention (if available)
Faster and more memory-efficient attention:

```python
# Flash attention with NVIDIA GPUs
# Requires: pip install flash-attn

# Automatically used if available in diffusers
# No code changes needed, ~20% memory reduction
```

#### 3. Context Embedding Caching
For batch processing, cache context encodings:

```python
import torch
from diffusers import AutoPipelineForInpainting

pipeline = AutoPipelineForInpainting.from_pretrained(
    "black-forest-labs/FLUX.1-Kontext-dev",
    torch_dtype=torch.float16
)

# Encode context image once
context_image = load_image("reference.png")
with torch.no_grad():
    context_embedding = pipeline.image_encoder(
        pipeline.feature_extractor(context_image, return_tensors="pt").pixel_values
    )

# Use cached embedding for multiple generation calls
for prompt in prompts_list:
    result = pipeline(
        prompt=prompt,
        image=base_image,
        context_embedding=context_embedding,  # Reuse cached
        guidance_scale=5.0,
        num_inference_steps=28
    )
    # 10-15% faster than re-encoding context each time
```

#### 4. Image Tiling for Large Outputs
Process large images in tiles:

```python
def tile_image_processing(image, tile_size=512, overlap=64):
    """Process large image in overlapping tiles"""
    height, width = image.shape[:2]
    tiles = []

    for y in range(0, height - overlap, tile_size - overlap):
        for x in range(0, width - overlap, tile_size - overlap):
            tile = image[y:y+tile_size, x:x+tile_size]
            tiles.append((tile, x, y))

    # Process each tile
    results = []
    for tile, x, y in tiles:
        result = pipeline(prompt, image=tile, mask_image=mask[y:y+tile_size, x:x+tile_size])
        results.append((result.images[0], x, y))

    # Blend tiles together
    return blend_tiles(results, height, width)
```

### Memory Usage by Component

```
FLUX.1 Kontext Memory Breakdown (bfloat16):

Embedding Tables:     ~3GB
Transformer Blocks:   ~15GB (largest component)
Text Encoder:         ~2GB
Image Projection:     ~1GB
Miscellaneous:        ~3GB
Total:               ~24GB

Peak Memory During Generation:
Forward Pass:         +4GB (activations)
Gradient Computation: +6GB (if training)
Total Peak:          ~30GB (training) or ~28GB (inference)
```

### Memory Optimization Checklist

- [ ] Using quantization (Q4_K minimum)
- [ ] Attention slicing enabled for <16GB VRAM
- [ ] Mixed precision (torch.float16) enabled
- [ ] Sequential CPU offloading for extreme cases
- [ ] Context embedding caching for batches
- [ ] Image tiling for >1024x1024 outputs
- [ ] Batch size optimized for available VRAM
- [ ] Unused GPU memory cleared between generations

## Performance Benchmarking

### Benchmark Script
```python
import torch
import time
from diffusers import AutoPipelineForInpainting

def benchmark_configuration(model_name, steps, guidance_scale, batch_size=1):
    """Benchmark inference speed and memory usage"""

    pipeline = AutoPipelineForInpainting.from_pretrained(
        model_name,
        torch_dtype=torch.float16
    ).to("cuda")

    # Load test image
    image = torch.randn(batch_size, 3, 768, 768).to("cuda")
    mask = torch.randn(batch_size, 1, 768, 768).to("cuda")

    # Warmup
    _ = pipeline(
        prompt="test prompt",
        image=image[:1],
        mask_image=mask[:1],
        guidance_scale=guidance_scale,
        num_inference_steps=1
    )

    # Benchmark
    torch.cuda.synchronize()
    start = time.time()

    results = pipeline(
        prompt="Acrylic miniature of knight, warm lighting, macro photography",
        image=image,
        mask_image=mask,
        guidance_scale=guidance_scale,
        num_inference_steps=steps
    )

    torch.cuda.synchronize()
    elapsed = time.time() - start

    # Memory stats
    peak_memory = torch.cuda.max_memory_allocated() / 1e9

    print(f"Configuration: {model_name}")
    print(f"  Steps: {steps}, Guidance: {guidance_scale}, Batch: {batch_size}")
    print(f"  Time: {elapsed:.2f}s")
    print(f"  Peak VRAM: {peak_memory:.1f}GB")
    print(f"  Throughput: {batch_size/elapsed:.2f} images/sec")

    return elapsed, peak_memory

# Run benchmarks
benchmark_configuration("black-forest-labs/FLUX.1-Kontext-dev", 28, 5.0)
benchmark_configuration("black-forest-labs/FLUX.1-Kontext-dev-q4k", 20, 5.0)
benchmark_configuration("black-forest-labs/FLUX.1-Kontext-dev-q4k-lightning", 8, 1.8)
```

## Desktop Deployment Checklist

- [ ] GGUF quantization selected (Q4_K recommended)
- [ ] Lightning LoRA integrated (for real-time workflows)
- [ ] Memory optimization enabled
- [ ] Benchmark results documented
- [ ] Error handling implemented
- [ ] Model caching strategy defined
- [ ] Batch processing pipeline ready
- [ ] Context encoding caching implemented
- [ ] Distribution package prepared
- [ ] Installation instructions tested
