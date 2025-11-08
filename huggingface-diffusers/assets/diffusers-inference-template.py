#!/usr/bin/env python3
"""
Production-Ready HuggingFace Diffusers Inference Template

This script provides a complete inference pipeline with:
- Error handling and fallback mechanisms
- Memory optimization strategies
- Progress tracking and callbacks
- Configuration flexibility
- Logging and debugging
- LoRA support
- GPU memory management

Usage:
    python diffusers-inference-template.py --prompt "a dog" --output output.png
"""

import argparse
import json
import logging
import os
import sys
import torch
from pathlib import Path
from typing import Optional, Callable, List
from dataclasses import dataclass, asdict
from datetime import datetime

from diffusers import (
    StableDiffusionPipeline,
    DPMPlusPlannerScheduler,
    EulerDiscreteScheduler,
    DDIMScheduler,
)
from PIL import Image


# Logging configuration
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
)
logger = logging.getLogger(__name__)


@dataclass
class InferenceConfig:
    """Configuration for inference pipeline."""
    model_id: str = "runwayml/stable-diffusion-v1-5"
    prompt: str = "a dog"
    negative_prompt: str = "blurry, low quality"
    height: int = 512
    width: int = 512
    num_inference_steps: int = 30
    guidance_scale: float = 7.5
    num_images_per_prompt: int = 1
    scheduler: str = "dpm++"
    seed: Optional[int] = None
    device: str = "cuda"
    dtype: str = "float16"
    enable_offloading: bool = False
    enable_attention_slicing: bool = False
    enable_vae_slicing: bool = False
    lora_paths: Optional[List[str]] = None
    checkpoint_path: Optional[str] = None
    output_dir: str = "outputs"
    save_config: bool = True
    dry_run: bool = False

    def to_dict(self):
        """Convert to dictionary."""
        return asdict(self)


class DiffusersInferencePipeline:
    """Production-ready inference pipeline."""

    SCHEDULER_MAP = {
        "dpm++": DPMPlusPlannerScheduler,
        "euler": EulerDiscreteScheduler,
        "ddim": DDIMScheduler,
    }

    def __init__(self, config: InferenceConfig):
        """Initialize pipeline."""
        self.config = config
        self.pipeline = None
        self.device = config.device if torch.cuda.is_available() else "cpu"

        logger.info(f"Using device: {self.device}")

    def setup_pipeline(self) -> None:
        """Load and configure the diffusion pipeline."""
        try:
            logger.info(f"Loading model: {self.config.model_id}")

            # Determine data type
            dtype_map = {
                "float32": torch.float32,
                "float16": torch.float16,
                "bfloat16": torch.bfloat16,
            }
            dtype = dtype_map.get(self.config.dtype, torch.float16)

            # Load pipeline
            if self.config.checkpoint_path:
                logger.info(f"Loading from checkpoint: {self.config.checkpoint_path}")
                self.pipeline = StableDiffusionPipeline.from_single_file(
                    self.config.checkpoint_path,
                    torch_dtype=dtype,
                )
            else:
                self.pipeline = StableDiffusionPipeline.from_pretrained(
                    self.config.model_id,
                    torch_dtype=dtype,
                    use_safetensors=True,
                )

            # Configure scheduler
            self._setup_scheduler()

            # Move to device
            self.pipeline = self.pipeline.to(self.device)

            # Memory optimizations
            self._setup_memory_optimizations()

            # Load LoRA adapters
            if self.config.lora_paths:
                self._load_lora_adapters()

            logger.info("Pipeline setup complete")

        except Exception as e:
            logger.error(f"Failed to setup pipeline: {e}")
            raise

    def _setup_scheduler(self) -> None:
        """Configure the scheduler."""
        scheduler_name = self.config.scheduler.lower()
        scheduler_class = self.SCHEDULER_MAP.get(
            scheduler_name, DPMPlusPlannerScheduler
        )

        logger.info(f"Using scheduler: {scheduler_class.__name__}")

        if scheduler_class == DPMPlusPlannerScheduler:
            self.pipeline.scheduler = scheduler_class.from_config(
                self.pipeline.scheduler.config,
                use_karras_sigmas=True,
            )
        else:
            self.pipeline.scheduler = scheduler_class.from_config(
                self.pipeline.scheduler.config
            )

    def _setup_memory_optimizations(self) -> None:
        """Apply memory optimization techniques."""
        if self.config.enable_offloading:
            logger.info("Enabling sequential CPU offloading")
            self.pipeline.enable_sequential_cpu_offload()

        if self.config.enable_attention_slicing:
            logger.info("Enabling attention slicing")
            self.pipeline.enable_attention_slicing()

        if self.config.enable_vae_slicing:
            logger.info("Enabling VAE slicing")
            self.pipeline.enable_vae_slicing()

        # Try to enable Flash Attention if available
        if self.device == "cuda":
            try:
                logger.info("Attempting to enable Flash Attention 2")
                self.pipeline.enable_flash_attention_2()
            except Exception:
                logger.debug("Flash Attention 2 not available, skipping")
                try:
                    logger.info("Attempting xformers memory efficient attention")
                    self.pipeline.enable_xformers_memory_efficient_attention()
                except Exception:
                    logger.debug("xformers not available, using default attention")

    def _load_lora_adapters(self) -> None:
        """Load LoRA adapter weights."""
        if not self.config.lora_paths:
            return

        for lora_path in self.config.lora_paths:
            try:
                logger.info(f"Loading LoRA: {lora_path}")
                self.pipeline.load_lora_weights(lora_path)
            except Exception as e:
                logger.warning(f"Failed to load LoRA {lora_path}: {e}")

    def generate(self, progress_callback: Optional[Callable] = None) -> List[Image.Image]:
        """Generate images."""
        if self.pipeline is None:
            raise RuntimeError("Pipeline not initialized. Call setup_pipeline() first.")

        logger.info(
            f"Generating: {self.config.num_images_per_prompt} images "
            f"({self.config.height}x{self.config.width})"
        )
        logger.info(f"Prompt: {self.config.prompt}")
        logger.info(f"Negative prompt: {self.config.negative_prompt}")
        logger.info(f"Steps: {self.config.num_inference_steps}, "
                   f"Guidance: {self.config.guidance_scale}")

        # Setup generator for reproducibility
        generator = None
        if self.config.seed is not None:
            logger.info(f"Using seed: {self.config.seed}")
            generator = torch.Generator(device=self.device).manual_seed(
                self.config.seed
            )

        try:
            # Generate
            with torch.no_grad():
                output = self.pipeline(
                    prompt=self.config.prompt,
                    negative_prompt=self.config.negative_prompt,
                    height=self.config.height,
                    width=self.config.width,
                    num_inference_steps=self.config.num_inference_steps,
                    guidance_scale=self.config.guidance_scale,
                    num_images_per_prompt=self.config.num_images_per_prompt,
                    generator=generator,
                    callback=progress_callback,
                    callback_steps=1,
                )

            images = output.images
            logger.info(f"Generated {len(images)} image(s)")

            # Check for NSFW content
            if hasattr(output, 'nsfw_content_detected'):
                for i, nsfw in enumerate(output.nsfw_content_detected):
                    if nsfw:
                        logger.warning(f"Image {i}: NSFW content detected")

            return images

        except torch.cuda.OutOfMemoryError:
            logger.error("Out of GPU memory. Try:")
            logger.error("  - Reducing image resolution")
            logger.error("  - Reducing num_inference_steps")
            logger.error("  - Enabling CPU offloading")
            raise
        except Exception as e:
            logger.error(f"Generation failed: {e}")
            raise

    def save_images(self, images: List[Image.Image]) -> List[str]:
        """Save generated images."""
        output_dir = Path(self.config.output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)

        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        saved_paths = []

        for i, image in enumerate(images):
            filename = f"{timestamp}_image_{i:02d}.png"
            filepath = output_dir / filename

            try:
                image.save(filepath)
                logger.info(f"Saved: {filepath}")
                saved_paths.append(str(filepath))
            except Exception as e:
                logger.error(f"Failed to save {filepath}: {e}")

        return saved_paths

    def save_config(self) -> None:
        """Save configuration used for generation."""
        if not self.config.save_config:
            return

        output_dir = Path(self.config.output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)

        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        config_path = output_dir / f"{timestamp}_config.json"

        try:
            with open(config_path, 'w') as f:
                json.dump(self.config.to_dict(), f, indent=2, default=str)
            logger.info(f"Saved config: {config_path}")
        except Exception as e:
            logger.error(f"Failed to save config: {e}")

    def cleanup(self) -> None:
        """Clean up GPU memory."""
        if self.device == "cuda":
            torch.cuda.empty_cache()
            logger.info("GPU cache cleared")


def create_progress_callback(total_steps: int) -> Callable:
    """Create a progress callback function."""
    def callback(step: int, timestep: int, latents: torch.Tensor) -> None:
        progress = (step + 1) / total_steps * 100
        bar_length = 40
        filled = int(bar_length * (step + 1) / total_steps)
        bar = "█" * filled + "░" * (bar_length - filled)
        print(f"\r[{bar}] {progress:.1f}%", end="", flush=True)

    return callback


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Production-ready Diffusers inference",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Basic text-to-image
  python script.py --prompt "a photo of a dog"

  # With custom parameters
  python script.py \\
    --prompt "a landscape" \\
    --scheduler euler \\
    --steps 50 \\
    --guidance 7.5

  # Using checkpoint file
  python script.py \\
    --checkpoint ./model.safetensors \\
    --prompt "a cat"

  # With LoRA adapters
  python script.py \\
    --prompt "a photo" \\
    --lora ./style_lora.safetensors
        """,
    )

    # Model configuration
    parser.add_argument(
        "--model-id",
        default="runwayml/stable-diffusion-v1-5",
        help="HuggingFace model ID",
    )
    parser.add_argument(
        "--checkpoint",
        help="Path to local checkpoint file",
    )

    # Inference parameters
    parser.add_argument(
        "--prompt",
        required=True,
        help="Text prompt for generation",
    )
    parser.add_argument(
        "--negative-prompt",
        default="blurry, low quality",
        help="Negative prompt",
    )
    parser.add_argument(
        "--steps",
        type=int,
        default=30,
        help="Number of inference steps",
    )
    parser.add_argument(
        "--guidance",
        type=float,
        default=7.5,
        help="Classifier-free guidance scale",
    )
    parser.add_argument(
        "--height",
        type=int,
        default=512,
        help="Image height",
    )
    parser.add_argument(
        "--width",
        type=int,
        default=512,
        help="Image width",
    )
    parser.add_argument(
        "--num-images",
        type=int,
        default=1,
        help="Number of images to generate",
    )
    parser.add_argument(
        "--seed",
        type=int,
        help="Random seed for reproducibility",
    )

    # Scheduler and optimization
    parser.add_argument(
        "--scheduler",
        choices=["dpm++", "euler", "ddim"],
        default="dpm++",
        help="Sampling scheduler",
    )
    parser.add_argument(
        "--dtype",
        choices=["float32", "float16", "bfloat16"],
        default="float16",
        help="Data type for computation",
    )
    parser.add_argument(
        "--offloading",
        action="store_true",
        help="Enable CPU offloading (slower but less memory)",
    )
    parser.add_argument(
        "--attention-slicing",
        action="store_true",
        help="Enable attention slicing (reduces peak memory)",
    )
    parser.add_argument(
        "--vae-slicing",
        action="store_true",
        help="Enable VAE slicing",
    )

    # LoRA support
    parser.add_argument(
        "--lora",
        nargs="+",
        dest="lora_paths",
        help="Path to LoRA adapter files",
    )

    # Output options
    parser.add_argument(
        "--output-dir",
        default="outputs",
        help="Output directory for images",
    )
    parser.add_argument(
        "--save-config",
        action="store_true",
        help="Save generation config",
    )

    # Debugging
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Load pipeline but don't generate",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Enable verbose logging",
    )

    args = parser.parse_args()

    # Setup logging
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)

    # Create configuration
    config = InferenceConfig(
        model_id=args.model_id,
        checkpoint_path=args.checkpoint,
        prompt=args.prompt,
        negative_prompt=args.negative_prompt,
        height=args.height,
        width=args.width,
        num_inference_steps=args.steps,
        guidance_scale=args.guidance,
        num_images_per_prompt=args.num_images,
        scheduler=args.scheduler,
        seed=args.seed,
        dtype=args.dtype,
        enable_offloading=args.offloading,
        enable_attention_slicing=args.attention_slicing,
        enable_vae_slicing=args.vae_slicing,
        lora_paths=args.lora_paths,
        output_dir=args.output_dir,
        save_config=args.save_config,
        dry_run=args.dry_run,
    )

    # Initialize pipeline
    try:
        pipeline = DiffusersInferencePipeline(config)
        pipeline.setup_pipeline()

        if args.dry_run:
            logger.info("Dry run complete (pipeline loaded successfully)")
            return

        # Generate images
        progress_callback = create_progress_callback(config.num_inference_steps)
        images = pipeline.generate(progress_callback=progress_callback)
        print()  # Newline after progress bar

        # Save images
        saved_paths = pipeline.save_images(images)

        # Save configuration
        pipeline.save_config()

        logger.info(f"Generated {len(images)} image(s)")
        logger.info(f"Saved to: {config.output_dir}")

    except KeyboardInterrupt:
        logger.info("Generation interrupted by user")
        sys.exit(0)
    except Exception as e:
        logger.error(f"Fatal error: {e}", exc_info=args.verbose)
        sys.exit(1)
    finally:
        # Cleanup
        if 'pipeline' in locals():
            pipeline.cleanup()


if __name__ == "__main__":
    main()
