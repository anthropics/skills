# Model Loading in Diffusers: Complete Guide

## Three Model Loading Strategies

The Diffusers library supports three primary methods for loading models, each with distinct advantages for different deployment scenarios.

## 1. from_pretrained (HuggingFace Hub)

### Overview

`from_pretrained()` is the primary method for loading models from HuggingFace Hub. It automatically handles downloading, caching, and version management.

### Basic Usage

```python
from diffusers import StableDiffusionPipeline
import torch

# Load from HuggingFace Hub
pipeline = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5",
    torch_dtype=torch.float16,
)
pipeline = pipeline.to("cuda")

# Generate
output = pipeline(prompt="a dog")
```

### HuggingFace Hub Models

Popular models available on Hub:

**Stable Diffusion Series**:
- `runwayml/stable-diffusion-v1-5` - Classic model (4GB)
- `stabilityai/stable-diffusion-2-1` - Improved version (5GB)
- `stabilityai/stable-diffusion-xl-base-1.0` - Larger model (6.9GB)

**Community Fine-tunes**:
- `dreamlike-art/dreamlike-photoreal-2.0` - Photorealistic
- `Lykon/DreamShaper` - Artistic style
- `stabilityai/stable-diffusion-3-medium` - Newer generation

### Configuration Options

```python
from diffusers import StableDiffusionPipeline
import torch

pipeline = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5",

    # Data type selection
    torch_dtype=torch.float16,      # Faster, less memory (recommended)
    torch_dtype=torch.float32,      # Higher precision, more memory
    torch_dtype=torch.bfloat16,     # Good balance (requires newer GPUs)

    # Format selection
    use_safetensors=True,           # Safer format (recommended)
    use_safetensors=False,          # Older .ckpt format

    # Version control
    revision="main",                # Latest version
    revision="fp16",                # Specific revision

    # Access control
    use_auth_token=True,            # For private models
    use_auth_token="hf_xxxxx",      # Explicit token

    # GPU/CPU selection
    device_map="auto",              # Auto GPU detection
    device_map={"": "cpu"},         # Force CPU

    # Component-level control
    text_encoder=None,              # Load without text encoder
    vae=None,                       # Load without VAE
)
```

### Version Management

```python
from diffusers import StableDiffusionPipeline

# Load specific version by revision
pipeline = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5",
    revision="fp16"  # Loads FP16 weights directly
)

# Load by commit hash
pipeline = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5",
    revision="abc123def456"  # Specific commit
)

# Load from branch
pipeline = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5",
    revision="my-custom-branch"
)
```

### Caching and Offline Usage

```python
import os
from diffusers import StableDiffusionPipeline

# Configure cache directory
os.environ["HF_HOME"] = "/path/to/cache"

# Load from cache if available, download otherwise
pipeline = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5",
    cache_dir="/custom/cache/path"
)

# Load only from cache (offline mode)
from huggingface_hub import hf_hub_download
import torch
from diffusers import StableDiffusionPipeline

try:
    pipeline = StableDiffusionPipeline.from_pretrained(
        "runwayml/stable-diffusion-v1-5",
        local_files_only=True,  # Don't download
        cache_dir="/path/to/cache"
    )
except Exception as e:
    print(f"Model not in cache: {e}")
```

### Private Models

```python
from diffusers import DiffusionPipeline
from huggingface_hub import login

# Authenticate with HuggingFace
login(token="hf_xxxxxxxxxxxxx")  # Or use HF_TOKEN env var

# Load private model
pipeline = DiffusionPipeline.from_pretrained(
    "username/private-model-name",
    use_auth_token=True,
)
```

### Model Discovery and Listing

```python
from huggingface_hub import list_repo_files, model_info

# List available files in model
files = list_repo_files("runwayml/stable-diffusion-v1-5")

# Get model information
info = model_info("runwayml/stable-diffusion-v1-5")
print(f"Model size: {info.siblings}")
print(f"Created: {info.created_at}")
print(f"Last modified: {info.last_modified}")

# Search for models
from huggingface_hub import list_models

models = list_models(
    task="text-to-image",
    library="diffusers"
)
for model in models:
    print(model.id)
```

---

## 2. from_single_file (Checkpoint Loading)

### Overview

`from_single_file()` loads models from individual checkpoint files (.safetensors, .ckpt, .pth) without requiring the full HuggingFace Hub structure. Useful for community models and fine-tunes.

### Basic Usage

```python
from diffusers import StableDiffusionPipeline
import torch

# Load from checkpoint file
pipeline = StableDiffusionPipeline.from_single_file(
    "./model_weights/model.safetensors",
    torch_dtype=torch.float16,
)
pipeline = pipeline.to("cuda")

output = pipeline(prompt="a dog")
```

### Supported File Formats

```python
from diffusers import StableDiffusionPipeline

# SafeTensors format (recommended)
pipeline = StableDiffusionPipeline.from_single_file(
    "model.safetensors",
    safety_checker=None,
)

# PyTorch checkpoint format
pipeline = StableDiffusionPipeline.from_single_file(
    "model.ckpt",
    torch_dtype=torch.float16,
)

# Pickle format (legacy)
pipeline = StableDiffusionPipeline.from_single_file(
    "model.pth",
    torch_dtype=torch.float16,
)
```

### Configuration for Community Models

```python
from diffusers import StableDiffusionPipeline
import torch

# Loading fine-tuned models
pipeline = StableDiffusionPipeline.from_single_file(
    "dreamshaper_7.safetensors",

    # Specify architecture if different from base
    original_config_file="config.yaml",

    # Use original VAE from base model
    vae=None,  # Don't load VAE from checkpoint

    # Type conversion
    torch_dtype=torch.float16,

    # Safety features
    safety_checker=None,  # Disable if not in checkpoint
    requires_safety_checker=False,
)
```

### Workflow: Download and Load Community Model

```python
import os
import requests
from diffusers import StableDiffusionPipeline
import torch

# Download model
model_url = "https://example.com/model.safetensors"
model_path = "./models/custom_model.safetensors"

os.makedirs("./models", exist_ok=True)

if not os.path.exists(model_path):
    print(f"Downloading {model_url}...")
    response = requests.get(model_url, stream=True)
    with open(model_path, 'wb') as f:
        for chunk in response.iter_content(chunk_size=8192):
            f.write(chunk)

# Load checkpoint
pipeline = StableDiffusionPipeline.from_single_file(
    model_path,
    torch_dtype=torch.float16,
)
pipeline = pipeline.to("cuda")

# Use pipeline
output = pipeline(prompt="a dog")
```

### Merging Multiple Checkpoints

```python
from diffusers import StableDiffusionPipeline
import torch

# Load base model
pipeline = StableDiffusionPipeline.from_single_file(
    "base_model.safetensors",
    torch_dtype=torch.float16,
)

# Merge with another checkpoint
# (Load components and manually merge weights)
merged_state_dict = {}

base_state = torch.load("base_model.safetensors")
override_state = torch.load("override_model.safetensors")

# Simple average merge
for key in base_state:
    merged_state_dict[key] = (base_state[key] + override_state[key]) / 2

# Apply merged weights (requires manual loading)
# This is a simplified example; actual implementation depends on model structure
```

---

## 3. GGUF (Quantized Models)

### Overview

GGUF (GPT-Generated Unified Format) provides integer-quantized weights (8-bit, 4-bit) for efficient inference. Reduces memory usage 4-8x with minimal quality loss.

### Advantages of GGUF

```
Memory Usage (SD 1.5):
- FP32: 4.2 GB
- FP16: 2.1 GB
- GGUF Q8:  1.0 GB
- GGUF Q4:  0.5 GB

Speed (relative):
- FP32: 1.0x (baseline)
- FP16: 2.0x
- GGUF Q8: 3.0x
- GGUF Q4: 4.0x
```

### Loading GGUF Models

```python
from diffusers import DiffusionPipeline
import torch

# Load GGUF quantized model
pipeline = DiffusionPipeline.from_pretrained(
    "mys/ggml-model-f16",  # Example GGUF model on Hub
    torch_dtype=torch.float16,
    use_safetensors=True,
)
```

### GGUF Quantization Levels

```
Q8 (Quantize 8-bit): ~95% quality, 50% reduction
Q6 (Mixed 6-bit):    ~90% quality, 60% reduction
Q5 (Mixed 5-bit):    ~85% quality, 70% reduction
Q4 (Quantize 4-bit): ~80% quality, 75% reduction
Q3 (Mixed 3-bit):    ~75% quality, 80% reduction
Q2 (Quantize 2-bit): ~60% quality, 90% reduction (rarely used)
```

### Example: CPU Inference with GGUF

```python
from diffusers import DiffusionPipeline
import torch

# Load GGUF model for CPU
pipeline = DiffusionPipeline.from_pretrained(
    "TheBloke/Stable-Diffusion-v1-5-GGUF",
)

# Configure for CPU
pipeline = pipeline.to("cpu")

# Optional: Use float32 for CPU stability
pipeline.unet = pipeline.unet.to(torch.float32)

# Generation (slower but memory-efficient)
output = pipeline(
    prompt="a dog",
    num_inference_steps=30,
    guidance_scale=7.5,
)

image = output.images[0]
image.save("output.png")
```

### Converting to GGUF

```python
# Using llama.cpp or similar tools
# This is typically done externally, not in Diffusers

# Example using GGML tools:
# python convert_huggingface_to_ggml.py \
#     --model-name runwayml/stable-diffusion-v1-5 \
#     --output-dir ./ggml-models/
```

---

## Practical Model Loading Patterns

### Pattern 1: Memory-Constrained Environment

```python
from diffusers import DiffusionPipeline
import torch

# Load GGUF model for minimal memory
pipeline = DiffusionPipeline.from_pretrained(
    "TheBloke/Stable-Diffusion-v1-5-GGUF",
    torch_dtype=torch.float16,
    use_safetensors=True,
)

# Move to available device
device = "cuda" if torch.cuda.is_available() else "cpu"
pipeline = pipeline.to(device)

# Enable memory optimizations
if device == "cuda":
    pipeline.enable_sequential_cpu_offload()
    pipeline.enable_attention_slicing()

output = pipeline(prompt="a dog", num_inference_steps=20)
```

### Pattern 2: Fast Local Development

```python
from diffusers import StableDiffusionPipeline
from pathlib import Path
import torch

# Use local checkpoint during development
model_path = Path("./models/local_model.safetensors")

if model_path.exists():
    # Load local checkpoint
    pipeline = StableDiffusionPipeline.from_single_file(
        str(model_path),
        torch_dtype=torch.float16,
    )
else:
    # Fall back to Hub
    pipeline = StableDiffusionPipeline.from_pretrained(
        "runwayml/stable-diffusion-v1-5",
        torch_dtype=torch.float16,
    )

pipeline = pipeline.to("cuda")
output = pipeline(prompt="test")
```

### Pattern 3: Offline Deployment

```python
from diffusers import DiffusionPipeline
import torch
import os

# Set cache directory before loading
cache_dir = "/models/cache"
os.environ["HF_HOME"] = cache_dir

# Load from cache only (no downloads)
pipeline = DiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5",
    torch_dtype=torch.float16,
    local_files_only=True,  # Essential for offline
    cache_dir=cache_dir,
)

pipeline = pipeline.to("cuda")
output = pipeline(prompt="deployment test")
```

### Pattern 4: Multi-Model Management

```python
from diffusers import DiffusionPipeline
import torch

class ModelManager:
    def __init__(self, cache_dir="/models"):
        self.cache_dir = cache_dir
        self.pipelines = {}

    def load_model(self, model_id, force_reload=False):
        """Load or retrieve cached pipeline."""
        if model_id in self.pipelines and not force_reload:
            return self.pipelines[model_id]

        pipeline = DiffusionPipeline.from_pretrained(
            model_id,
            torch_dtype=torch.float16,
            cache_dir=self.cache_dir,
        )
        pipeline = pipeline.to("cuda")

        self.pipelines[model_id] = pipeline
        return pipeline

    def unload_model(self, model_id):
        """Free GPU memory for a model."""
        if model_id in self.pipelines:
            del self.pipelines[model_id]
            torch.cuda.empty_cache()

    def switch_model(self, from_id, to_id):
        """Efficient model switching."""
        self.unload_model(from_id)
        return self.load_model(to_id)

# Usage
manager = ModelManager()
pipeline_a = manager.load_model("runwayml/stable-diffusion-v1-5")
output_a = pipeline_a(prompt="a dog")

# Switch models
pipeline_b = manager.switch_model(
    "runwayml/stable-diffusion-v1-5",
    "stabilityai/stable-diffusion-2-1"
)
output_b = pipeline_b(prompt="a cat")
```

---

## Comparison Matrix

| Method | Speed | Memory | Flexibility | Best For |
|--------|-------|--------|-------------|----------|
| from_pretrained | Fast | Normal | High | General use, Hub models |
| from_single_file | Medium | Normal | Medium | Community models, fine-tunes |
| GGUF | Slow | Low (4-8x reduction) | Low | CPU inference, edge devices |

## Troubleshooting Model Loading

### "Model not found" Error

```python
from diffusers import DiffusionPipeline
from huggingface_hub import hf_hub_download

# Option 1: Check model exists
try:
    pipeline = DiffusionPipeline.from_pretrained(
        "username/nonexistent-model"
    )
except Exception as e:
    print(f"Model loading failed: {e}")

# Option 2: Download manually first
hf_hub_download(
    repo_id="runwayml/stable-diffusion-v1-5",
    filename="model_index.json"
)

# Option 3: Use alternative model
pipeline = DiffusionPipeline.from_pretrained(
    "stabilityai/stable-diffusion-2-1"
)
```

### Out of Memory with from_pretrained

```python
from diffusers import DiffusionPipeline
import torch

# Solution 1: Use GGUF quantized version
pipeline = DiffusionPipeline.from_pretrained(
    "TheBloke/Stable-Diffusion-v1-5-GGUF"
)

# Solution 2: Use FP16 instead of FP32
pipeline = DiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5",
    torch_dtype=torch.float16,
)

# Solution 3: CPU offloading
pipeline.enable_sequential_cpu_offload()
```

### Checkpoint File Compatibility

```python
from diffusers import StableDiffusionPipeline
import torch

# Test checkpoint compatibility
try:
    pipeline = StableDiffusionPipeline.from_single_file(
        "mystery_model.safetensors"
    )
except ValueError as e:
    # Likely incompatible format
    print(f"Compatibility issue: {e}")

    # Try specifying original config
    pipeline = StableDiffusionPipeline.from_single_file(
        "mystery_model.safetensors",
        original_config_file="config.json"
    )
```
