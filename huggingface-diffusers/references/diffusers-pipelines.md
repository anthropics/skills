# DiffusionPipeline Architecture & Customization

## Pipeline Overview

The `DiffusionPipeline` class is the core abstraction in Diffusers that coordinates all components of a diffusion model inference. It handles model loading, component orchestration, and provides a unified API for generation tasks.

### Pipeline Hierarchy

```
DiffusionPipeline (base class)
├── StableDiffusionPipeline (text2img)
├── StableDiffusionImg2ImgPipeline (img2img)
├── StableDiffusionInpaintPipeline (inpainting)
├── StableDiffusionDepthPipeline (depth-guided)
├── ControlNetPipeline (ControlNet conditioning)
├── DiffusionPipeline (fully custom)
└── StableVideoDiffusionPipeline (video generation)
```

## Core Pipeline Architecture

### 1. Text2Img Pipeline (Most Common)

```python
from diffusers import StableDiffusionPipeline
import torch

# Load from HuggingFace Hub
pipe = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5",
    torch_dtype=torch.float16,
    use_safetensors=True,
)

# Move to GPU
pipe = pipe.to("cuda")

# Generate
output = pipe(
    prompt="a oil painting of a wizard",
    negative_prompt="blurry, low quality",
    num_inference_steps=50,
    guidance_scale=7.5,
    height=768,
    width=512,
    num_images_per_prompt=2,
)

# Access outputs
images = output.images
nsfw_detected = output.nsfw_content_detected  # Safety checker
```

**Core Components**:

- **text_encoder**: CLIP or similar model that converts text to embeddings
- **tokenizer**: Text preprocessing (usually associated with text_encoder)
- **unet**: U-Net denoising model (the core generative component)
- **vae**: Variational Autoencoder for latent space compression
- **scheduler**: Noise scheduling algorithm
- **safety_checker**: NSFW content detection (optional)

### 2. Image-to-Image Pipeline

```python
from diffusers import StableDiffusionImg2ImgPipeline
from PIL import Image

pipe = StableDiffusionImg2ImgPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5",
    torch_dtype=torch.float16,
)
pipe = pipe.to("cuda")

init_image = Image.open("input.png").resize((512, 512))

output = pipe(
    prompt="impressionist painting",
    image=init_image,
    strength=0.75,  # 0=no change, 1=full generation
    num_inference_steps=50,
    guidance_scale=7.5,
).images
```

**Key Parameters**:
- `strength`: How much to transform the image (0.75 typical)
- `image`: PIL Image or tensor input

### 3. Inpainting Pipeline

```python
from diffusers import StableDiffusionInpaintPipeline
from PIL import Image

pipe = StableDiffusionInpaintPipeline.from_pretrained(
    "runwayml/stable-diffusion-inpainting",
    torch_dtype=torch.float16,
)

init_image = Image.open("image.png").resize((512, 512))
mask_image = Image.open("mask.png").resize((512, 512))

output = pipe(
    prompt="a cat wearing a hat",
    image=init_image,
    mask_image=mask_image,  # White = inpaint area, black = preserve
    num_inference_steps=50,
    guidance_scale=7.5,
).images
```

**Mask Format**:
- White (255): Areas to generate
- Black (0): Areas to preserve

### 4. ControlNet Pipeline

```python
from diffusers import StableDiffusionControlNetPipeline, ControlNetModel
import torch
from PIL import Image

controlnet = ControlNetModel.from_pretrained(
    "lllyasviel/sd-controlnet-canny"
)

pipe = StableDiffusionControlNetPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5",
    controlnet=controlnet,
    torch_dtype=torch.float16,
)
pipe = pipe.to("cuda")

control_image = Image.open("canny_edges.png")

output = pipe(
    prompt="a landscape",
    image=control_image,
    num_inference_steps=50,
    guidance_scale=7.5,
).images
```

**ControlNet Types**:
- **canny**: Edge detection
- **depth**: Depth maps
- **pose**: Human pose estimation
- **scribble**: User sketches
- **normal**: Surface normal maps
- **openpose**: Pose detection

## Custom Pipeline Creation

### Building a Custom Pipeline from Scratch

```python
from diffusers import DiffusionPipeline
from diffusers.utils import BaseOutput
from typing import Union, Optional
import torch
from dataclasses import dataclass

@dataclass
class CustomOutput(BaseOutput):
    images: list
    latents: Optional[torch.Tensor] = None

class CustomDiffusionPipeline(DiffusionPipeline):
    def __init__(self, unet, scheduler, vae, text_encoder, tokenizer, feature_extractor=None):
        super().__init__()

        self.register_modules(
            unet=unet,
            scheduler=scheduler,
            vae=vae,
            text_encoder=text_encoder,
            tokenizer=tokenizer,
            feature_extractor=feature_extractor,
        )

    def encode_prompt(self, prompt, device, num_images_per_prompt):
        """Convert prompt to embeddings."""
        text_inputs = self.tokenizer(
            prompt,
            padding="max_length",
            max_length=self.tokenizer.model_max_length,
            truncation=True,
            return_tensors="pt",
        )

        text_embeddings = self.text_encoder(text_inputs.input_ids.to(device))[0]
        return text_embeddings

    @torch.no_grad()
    def __call__(
        self,
        prompt: Union[str, list],
        height: int = 512,
        width: int = 512,
        num_inference_steps: int = 50,
        guidance_scale: float = 7.5,
        num_images_per_prompt: int = 1,
        generator: Optional[torch.Generator] = None,
        **kwargs,
    ):
        # Device and dtype
        device = self._execution_device
        do_classifier_free_guidance = guidance_scale > 1.0

        # Encode prompts
        text_embeddings = self.encode_prompt(
            prompt, device, num_images_per_prompt
        )

        if do_classifier_free_guidance:
            uncond_embeddings = self.encode_prompt(
                "", device, num_images_per_prompt
            )
            text_embeddings = torch.cat([uncond_embeddings, text_embeddings])

        # Prepare latents
        num_channels_latents = self.unet.config.in_channels
        latents = torch.randn(
            (len(prompt) if isinstance(prompt, list) else 1,
             num_channels_latents, height // 8, width // 8),
            generator=generator,
            device=device,
            dtype=text_embeddings.dtype,
        )

        # Denoising loop
        self.scheduler.set_timesteps(num_inference_steps, device=device)

        for t in self.scheduler.timesteps:
            # Classifier-free guidance
            if do_classifier_free_guidance:
                latent_model_input = torch.cat([latents] * 2)
            else:
                latent_model_input = latents

            latent_model_input = self.scheduler.scale_model_input(
                latent_model_input, t
            )

            # Predict noise
            noise_pred = self.unet(
                latent_model_input,
                t,
                encoder_hidden_states=text_embeddings,
            ).sample

            # Classifier-free guidance
            if do_classifier_free_guidance:
                noise_pred_uncond, noise_pred_text = noise_pred.chunk(2)
                noise_pred = (
                    noise_pred_uncond +
                    guidance_scale * (noise_pred_text - noise_pred_uncond)
                )

            # Update latents
            latents = self.scheduler.step(
                noise_pred, t, latents
            ).prev_sample

        # Decode latents to images
        latents = 1 / self.vae.config.scaling_factor * latents
        images = self.vae.decode(latents).sample

        # Post-processing
        images = (images / 2 + 0.5).clamp(0, 1)
        images = images.cpu().permute(0, 2, 3, 1).numpy()
        images = (images * 255).round().astype("uint8")

        images = [Image.fromarray(image) for image in images]

        return CustomOutput(images=images, latents=latents)


# Usage
# pipeline = CustomDiffusionPipeline.from_pretrained(
#     "runwayml/stable-diffusion-v1-5"
# )
# output = pipeline("a photo of a dog")
```

### Component-Level Customization

```python
from diffusers import StableDiffusionPipeline
from diffusers.models import UNet2DConditionModel

# Load pipeline
pipe = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5"
)

# Replace scheduler
from diffusers import DPMPlusSolverScheduler
pipe.scheduler = DPMPlusSolverScheduler.from_config(
    pipe.scheduler.config
)

# Replace VAE with more efficient variant
from diffusers import AutoencoderKL
pipe.vae = AutoencoderKL.from_pretrained(
    "stabilityai/sd-vae-ft-ema",
    torch_dtype=pipe.unet.dtype,
)

# Hook into denoising loop
original_call = pipe.__call__

def custom_inference_with_hooks(prompt, **kwargs):
    # Pre-processing hook
    print(f"Generating: {prompt}")

    # Call original
    output = original_call(prompt, **kwargs)

    # Post-processing hook
    print("Generation complete")
    return output

pipe.__call__ = custom_inference_with_hooks
```

## Pipeline Optimization Patterns

### Memory-Efficient Pattern

```python
from diffusers import StableDiffusionPipeline
import torch

pipe = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5",
    torch_dtype=torch.float16,
)

# Optimization stack
pipe.enable_sequential_cpu_offload()  # Move to CPU when not needed
pipe.enable_attention_slicing()  # Reduce peak memory
pipe.enable_vae_slicing()  # Batch VAE operations

# Optional: Flash attention
try:
    pipe.enable_flash_attention_2()
except:
    pass

pipe = pipe.to("cuda")

output = pipe("a photo", height=768, width=512, num_inference_steps=50)
```

### Speed-Optimized Pattern

```python
from diffusers import StableDiffusionPipeline, DDIMScheduler
import torch

pipe = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5",
    torch_dtype=torch.float16,
    use_safetensors=True,
)

# Use DDIM scheduler (faster but slightly lower quality)
pipe.scheduler = DDIMScheduler.from_config(pipe.scheduler.config)

# Flash attention if available
try:
    pipe.enable_flash_attention_2()
except:
    pipe.enable_xformers_memory_efficient_attention()

pipe = pipe.to("cuda")

# Fast generation
output = pipe(
    "a photo",
    num_inference_steps=20,  # Reduced steps
    guidance_scale=5.0,  # Lower guidance
)
```

### Quality-Optimized Pattern

```python
from diffusers import StableDiffusionPipeline, EulerAncestralDiscreteScheduler
import torch

pipe = StableDiffusionPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5",
    torch_dtype=torch.float32,  # Higher precision
)

# Euler Ancestral for best quality
pipe.scheduler = EulerAncestralDiscreteScheduler.from_config(
    pipe.scheduler.config
)

pipe = pipe.to("cuda")

output = pipe(
    "a photo",
    num_inference_steps=50,  # More steps
    guidance_scale=7.5,
)
```

## Advanced Usage Patterns

### Batch Processing

```python
from diffusers import StableDiffusionPipeline

pipe = StableDiffusionPipeline.from_pretrained("runwayml/stable-diffusion-v1-5")
pipe = pipe.to("cuda")

prompts = [
    "a red car",
    "a blue car",
    "a green car",
]

outputs = pipe(
    prompts,
    num_images_per_prompt=2,
    num_inference_steps=30,
)

# outputs.images now contains 6 images (3 prompts x 2 per prompt)
```

### Seed Management for Reproducibility

```python
import torch
from diffusers import StableDiffusionPipeline

pipe = StableDiffusionPipeline.from_pretrained("runwayml/stable-diffusion-v1-5")

generator = torch.Generator(device="cuda").manual_seed(42)

output1 = pipe("a cat", generator=generator, num_inference_steps=30)

# Reset generator for same seed
generator = torch.Generator(device="cuda").manual_seed(42)
output2 = pipe("a cat", generator=generator, num_inference_steps=30)

# output1 and output2 are identical
```

### Progress Callbacks

```python
from diffusers import StableDiffusionPipeline
from tqdm import tqdm

def progress_callback(step, timestep, latents):
    print(f"Step {step}/{num_steps}")

pipe = StableDiffusionPipeline.from_pretrained("runwayml/stable-diffusion-v1-5")

output = pipe(
    "a photo",
    callback=progress_callback,
    callback_steps=1,
)
```

## Pipeline Comparison Matrix

| Pipeline | Use Case | Key Features | Memory | Speed |
|----------|----------|--------------|--------|-------|
| Text2Img | General generation | Prompt-based, versatile | High | Normal |
| Img2Img | Style transfer, variation | Guided generation | Medium | Normal |
| Inpainting | Object removal/addition | Mask-based editing | Medium | Normal |
| ControlNet | Spatial control | Edge/pose/depth guidance | High | Slow |
| Upscaler | Resolution enhancement | Single image enhancement | Low | Fast |
| DepthPipeline | 3D-aware generation | Depth map integration | High | Slow |
| Video | Animation generation | Temporal coherence | Very High | Very Slow |

## Best Practices for Pipeline Selection

1. **Start with Text2Img**: Most versatile and well-tested
2. **Match task to pipeline**: Use inpainting for editing, not text2img
3. **Consider ControlNet**: When spatial control is needed
4. **Profile memory usage**: Test with actual resolution and batch size
5. **Use quantization**: For resource-constrained environments
6. **Cache pipelines**: Reuse loaded pipelines across multiple generations
7. **Monitor VRAM**: Use `torch.cuda.memory_allocated()` to track usage
