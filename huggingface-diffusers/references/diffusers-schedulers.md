# Diffusers Schedulers: Complete Reference & Optimization Guide

## Scheduler Overview

The scheduler controls the denoising process by defining how noise is added and removed during sampling. The choice of scheduler significantly impacts inference speed, quality, and perceived artifacts.

### What Schedulers Do

1. **Noise Schedule**: Defines the noise level at each timestep
2. **Sampling Method**: Determines how to estimate the denoised image
3. **Timestep Ordering**: Controls progression through the denoising process
4. **Step Configuration**: Sets number and spacing of denoising steps

## Scheduler Comparison Matrix

| Scheduler | Speed | Quality | Artifacts | Use Case |
|-----------|-------|---------|-----------|----------|
| DDIM | 2-3x faster | Good | Slight banding | Fast preview |
| Euler | Normal | Excellent | Minimal | Balanced production |
| Euler Ancestral | Normal | Excellent | Minimal | Highest quality |
| DPM++ | 1.5-2x faster | Very Good | None | Quality + speed balance |
| DPM SDE | Normal | Very Good | Minimal | Stochastic sampling |
| PNDM | Normal | Good | Banding | Alternative sampler |
| LMSDiscrete | Normal | Good | Slight banding | Legacy support |
| UniPC | 2-3x faster | Good | Minor | Recent innovation |
| Heun | Normal | Very Good | Minimal | High-order method |

## Detailed Scheduler Guide

### 1. DDIM Scheduler (Denoising Diffusion Implicit Models)

**Characteristics**:
- Deterministic (no randomness)
- Fast inference (20-50% of steps needed)
- Slight quality loss compared to full diffusion
- Consistent results with same seed

```python
from diffusers import StableDiffusionPipeline, DDIMScheduler
import torch

pipe = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5",
    torch_dtype=torch.float16,
)

# Configure DDIM scheduler
pipe.scheduler = DDIMScheduler.from_config(pipe.scheduler.config)

# DDIM-specific parameters
pipe.scheduler.set_timesteps(num_inference_steps=30)

output = pipe(
    prompt="a photo of a dog",
    num_inference_steps=30,  # Lower than Euler
    guidance_scale=7.5,
)
```

**Best For**:
- Real-time preview generation
- Interactive applications
- Batch processing with speed priority
- Testing workflows quickly

**Performance**: 30 steps DDIM ≈ 50 steps Euler

---

### 2. Euler Discrete Scheduler

**Characteristics**:
- Single-step solver (fast, deterministic)
- Excellent quality at reasonable step counts
- No randomness (deterministic output)
- Good default choice

```python
from diffusers import StableDiffusionPipeline, EulerDiscreteScheduler

pipe = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5"
)

pipe.scheduler = EulerDiscreteScheduler.from_config(
    pipe.scheduler.config
)

output = pipe(
    prompt="a landscape",
    num_inference_steps=50,
)
```

**Best For**:
- Default production inference
- Balanced quality and speed
- When reproducibility matters
- Most general use cases

**Recommended Steps**: 40-50

---

### 3. Euler Ancestral Discrete Scheduler

**Characteristics**:
- Adds stochastic sampling (randomness)
- Highest perceived quality
- Requires more steps than Euler
- Slight variation between identical prompts

```python
from diffusers import StableDiffusionPipeline, EulerAncestralDiscreteScheduler

pipe = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5"
)

pipe.scheduler = EulerAncestralDiscreteScheduler.from_config(
    pipe.scheduler.config
)

output = pipe(
    prompt="an oil painting",
    num_inference_steps=50,  # More steps recommended
)
```

**Best For**:
- High-quality final output
- When quality > consistency
- Professional generation
- Artistic applications

**Recommended Steps**: 50-75

---

### 4. DPM++ Scheduler (DPMSolver++)

**Characteristics**:
- Higher-order multistep solver
- Fast convergence
- Excellent quality/speed tradeoff
- Becoming new standard

```python
from diffusers import StableDiffusionPipeline, DPMPlusPlannerScheduler

pipe = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5"
)

# Multiple DPM variants available
pipe.scheduler = DPMPlusPlannerScheduler.from_config(
    pipe.scheduler.config,
    use_karras_sigmas=True,  # Stability improvement
)

output = pipe(
    prompt="a photo",
    num_inference_steps=30,  # Effective at lower step counts
)
```

**DPM++ Variants**:

```python
from diffusers import (
    DPMPlusPlannerScheduler,      # MultiStep (recommended)
    DPMPlusSinglestepScheduler,   # SingleStep variant
    DPMPlusSolverScheduler,       # Original DPMSolver
)

# DPMPlus with Karras sigmas (improved stability)
scheduler = DPMPlusPlannerScheduler.from_config(
    config,
    use_karras_sigmas=True,
    algorithm_type="dpmsolver++"
)
```

**Best For**:
- New projects (becoming standard)
- Balanced quality and speed
- When efficiency matters
- Modern best practice

**Recommended Steps**: 25-30

---

### 5. DPM SDE Scheduler (Stochastic Differential Equation)

**Characteristics**:
- Stochastic variant of DPM++
- Highest quality at cost of consistency
- Slower than deterministic variant
- Good for final quality passes

```python
from diffusers import StableDiffusionPipeline, DPMSolverSDEScheduler

pipe = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5"
)

pipe.scheduler = DPMSolverSDEScheduler.from_config(
    pipe.scheduler.config
)

output = pipe(
    prompt="a photo",
    num_inference_steps=30,
)
```

**Best For**:
- Final quality output
- Research and experimentation
- When slight variation is acceptable
- Gallery-quality generation

---

### 6. UniPC Scheduler (Unified Predictor-Corrector)

**Characteristics**:
- Recent advancement (2024)
- Fast convergence
- Unified framework for multiple solvers
- Predictive correction

```python
from diffusers import StableDiffusionPipeline, UniPCMultistepScheduler

pipe = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5"
)

pipe.scheduler = UniPCMultistepScheduler.from_config(
    pipe.scheduler.config
)

output = pipe(
    prompt="a photo",
    num_inference_steps=20,  # Very efficient
)
```

**Best For**:
- Cutting-edge applications
- Mobile/edge inference
- When speed is critical
- Experimentation with new methods

**Performance**: 20 steps UniPC often rivals 30 steps Euler

---

### 7. PNDM Scheduler (Pseudo Numerical Methods)

**Characteristics**:
- Linear multistep solver
- Good quality but slower convergence
- Requires more steps
- Legacy but still effective

```python
from diffusers import StableDiffusionPipeline, PNDMScheduler

pipe = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5"
)

pipe.scheduler = PNDMScheduler.from_config(pipe.scheduler.config)

output = pipe(
    prompt="a photo",
    num_inference_steps=50,
)
```

**Best For**:
- Legacy compatibility
- When other methods fail
- Research comparisons
- Not recommended for new projects

---

## Scheduler Configuration Deep Dive

### Step Control and Timestep Ordering

```python
from diffusers import StableDiffusionPipeline, EulerDiscreteScheduler

pipe = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5"
)

pipe.scheduler = EulerDiscreteScheduler.from_config(
    pipe.scheduler.config
)

# Method 1: Direct step setting
pipe.scheduler.set_timesteps(num_inference_steps=30)
# Timesteps are now evenly distributed from 1000 to 0

# Method 2: Custom timestep spacing
import torch
timesteps = torch.linspace(1000, 0, 30)  # Custom spacing
pipe.scheduler.set_timesteps(timesteps=timesteps)

# Method 3: Non-uniform spacing (karras sigmas)
pipe.scheduler = DPMPlusPlannerScheduler.from_config(
    config,
    use_karras_sigmas=True,  # Logarithmic spacing
)
```

### Guidance Scale Interaction

Different schedulers interact differently with classifier-free guidance:

```python
from diffusers import StableDiffusionPipeline

pipe = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5"
)

# Test different schedulers with guidance
schedulers = [
    DDIMScheduler,
    EulerDiscreteScheduler,
    DPMPlusPlannerScheduler,
]

for scheduler_class in schedulers:
    pipe.scheduler = scheduler_class.from_config(
        pipe.scheduler.config
    )

    # Guidance scale tuning by scheduler
    guidance_scale = 7.5 if scheduler_class == DPMPlusPlannerScheduler else 7.5

    output = pipe(
        prompt="a photo",
        num_inference_steps=30,
        guidance_scale=guidance_scale,
    )
```

### Memory and Speed Trade-offs

```python
from diffusers import StableDiffusionPipeline, DDIMScheduler, DPMPlusPlannerScheduler

pipe = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5",
    torch_dtype=torch.float16,
)

# Speed-optimized configuration
pipe.scheduler = DDIMScheduler.from_config(pipe.scheduler.config)
pipe.enable_xformers_memory_efficient_attention()
output_fast = pipe(
    prompt="a photo",
    num_inference_steps=20,  # Very fast
    height=512,
    width=512,
)

# Quality-optimized configuration
pipe.scheduler = EulerAncestralDiscreteScheduler.from_config(
    pipe.scheduler.config
)
output_quality = pipe(
    prompt="a photo",
    num_inference_steps=50,  # Higher quality
    height=512,
    width=512,
)
```

## Scheduler Selection Decision Tree

```
┌─ Speed Critical?
│  ├─ YES → DDIM (20 steps) or UniPC (20 steps)
│  └─ NO → Continue
│
├─ Consistency Required?
│  ├─ YES → Euler or DPM++ Deterministic
│  └─ NO → Continue
│
├─ Quality Priority?
│  ├─ YES → Euler Ancestral or DPM SDE
│  └─ NO → Continue
│
├─ GPU Memory Limited?
│  ├─ YES → DPM++ (efficient) or DDIM
│  └─ NO → Any option works
│
└─ Production vs Research?
   ├─ PRODUCTION → DPM++ (new standard)
   └─ RESEARCH → Try multiple, compare results
```

## Practical Step Count Recommendations

### By Use Case

| Use Case | Scheduler | Steps | Time (3060 Ti) |
|----------|-----------|-------|----------------|
| Preview | DDIM | 20 | 2-3s |
| Real-time | DDIM | 30 | 3-5s |
| Good Quality | Euler | 40 | 8-10s |
| High Quality | Euler Ancestral | 50 | 10-12s |
| Professional | Euler Ancestral | 75 | 15-20s |

### By Model Size

```python
# SD 1.5 (4GB)
fast_steps = 20    # DDIM, UniPC
normal_steps = 30  # DPM++, Euler
quality_steps = 50 # Euler Ancestral

# SD 2.1 (5GB)
fast_steps = 25
normal_steps = 40
quality_steps = 60

# SDXL (7GB)
fast_steps = 30    # Fewer steps needed
normal_steps = 40
quality_steps = 50
```

## Performance Benchmarks

### Inference Time Comparison (512x512, Single Image)

```
DDIM 20 steps:         ~2.5s
UniPC 20 steps:        ~2.8s
DPM++ 30 steps:        ~5s
Euler 30 steps:        ~5.5s
Euler Ancestral 50:    ~9s
PNDM 50 steps:         ~10s
```

### Memory Usage Comparison

```
All schedulers use identical peak memory usage (~6GB for SD 1.5).
Differences are minimal and driven by model/precision, not scheduler.
```

## Scheduler Selection in Code

```python
from diffusers import (
    StableDiffusionPipeline,
    DDIMScheduler,
    EulerDiscreteScheduler,
    EulerAncestralDiscreteScheduler,
    DPMPlusPlannerScheduler,
)
import torch

def create_pipeline(scheduler_name: str = "dpm++"):
    pipe = StableDiffusionPipeline.from_pretrained(
        "runwayml/stable-diffusion-v1-5",
        torch_dtype=torch.float16,
    )

    scheduler_map = {
        "ddim": DDIMScheduler,
        "euler": EulerDiscreteScheduler,
        "euler_ancestral": EulerAncestralDiscreteScheduler,
        "dpm++": DPMPlusPlannerScheduler,
    }

    scheduler_class = scheduler_map.get(scheduler_name, DPMPlusPlannerScheduler)
    pipe.scheduler = scheduler_class.from_config(pipe.scheduler.config)

    return pipe.to("cuda")

# Usage
pipe = create_pipeline("dpm++")
output = pipe(prompt="a photo", num_inference_steps=30)
```

## Troubleshooting Scheduler Issues

### Banding Artifacts

**Symptoms**: Visible bands of color instead of smooth gradients

**Solution**:
```python
# Use Euler instead of DDIM
pipe.scheduler = EulerDiscreteScheduler.from_config(
    pipe.scheduler.config
)

# Or increase steps with DDIM
output = pipe(prompt, num_inference_steps=50)
```

### Slow Convergence

**Symptoms**: Poor quality even with many steps

**Solution**:
```python
# Try DPM++ which converges faster
pipe.scheduler = DPMPlusPlannerScheduler.from_config(
    pipe.scheduler.config,
    use_karras_sigmas=True,
)

# Reduce steps but improve quality
output = pipe(prompt, num_inference_steps=30)
```

### Inconsistent Results

**Symptoms**: Different outputs with same prompt and seed

**Solution**:
```python
# Use deterministic scheduler
pipe.scheduler = EulerDiscreteScheduler.from_config(
    pipe.scheduler.config
)

# Set seed explicitly
generator = torch.Generator(device="cuda").manual_seed(42)
output = pipe(prompt, generator=generator)
```
