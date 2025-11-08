#!/usr/bin/env python3
"""
Convert ComfyUI workflow JSON to HuggingFace Diffusers Python code.

This tool analyzes ComfyUI node graphs and generates equivalent Diffusers
inference code with proper pipeline selection, model loading, and scheduling.

Usage:
    python convert-workflow-to-diffusers.py workflow.json --output inference.py
"""

import json
import argparse
import sys
from typing import Dict, List, Any, Optional
from dataclasses import dataclass


@dataclass
class DiffusersConfig:
    """Configuration for generated Diffusers code."""
    pipeline_class: str = "StableDiffusionPipeline"
    model_id: Optional[str] = None
    scheduler: str = "DPMPlusPlannerScheduler"
    num_inference_steps: int = 30
    guidance_scale: float = 7.5
    enable_offloading: bool = False
    enable_attention_slicing: bool = False
    dtype: str = "float16"
    device: str = "cuda"


class ComfyUIWorkflowConverter:
    """Convert ComfyUI workflows to Diffusers code."""

    # Mapping of ComfyUI node types to Diffusers operations
    NODE_TYPE_MAPPING = {
        "CheckpointLoaderSimple": "model_loader",
        "CLIPTextEncode": "text_encoder",
        "KSampler": "sampler",
        "VAEDecode": "vae_decoder",
        "VAEEncode": "vae_encoder",
        "LoraLoader": "lora_loader",
        "SaveImage": "image_save",
        "PrimitiveNode": "primitive",
    }

    def __init__(self):
        self.nodes: Dict[str, Dict[str, Any]] = {}
        self.links: List[tuple] = []
        self.config = DiffusersConfig()

    def load_workflow(self, workflow_path: str) -> None:
        """Load and parse ComfyUI workflow JSON."""
        with open(workflow_path, 'r') as f:
            workflow = json.load(f)

        # Extract nodes and their connections
        for node_id, node_data in workflow.items():
            if isinstance(node_data, dict) and 'class_type' in node_data:
                self.nodes[node_id] = node_data

    def analyze_workflow(self) -> None:
        """Analyze workflow to determine pipeline configuration."""
        for node_id, node_data in self.nodes.items():
            class_type = node_data.get('class_type', '')

            # Detect model loading
            if 'Checkpoint' in class_type:
                ckpt_name = node_data.get('inputs', {}).get('ckpt_name', '')
                if ckpt_name:
                    self.config.model_id = ckpt_name.replace('.safetensors', '').replace('.ckpt', '')

            # Detect sampling parameters
            if 'KSampler' in class_type:
                inputs = node_data.get('inputs', {})
                self.config.num_inference_steps = int(inputs.get('steps', 30))
                self.config.guidance_scale = float(inputs.get('cfg', 7.5))

            # Detect scheduler
            sampler_name = node_data.get('inputs', {}).get('sampler_name', '').lower()
            if 'ddim' in sampler_name:
                self.config.scheduler = "DDIMScheduler"
            elif 'euler' in sampler_name:
                self.config.scheduler = "EulerDiscreteScheduler"
            elif 'dpm' in sampler_name:
                self.config.scheduler = "DPMPlusPlannerScheduler"

            # Detect LoRA usage
            if 'LoraLoader' in class_type:
                self.config.enable_offloading = True

    def generate_imports(self) -> str:
        """Generate Python import statements."""
        imports = [
            "import torch",
            "from PIL import Image",
            "from diffusers import DiffusionPipeline, "
            f"{self.config.pipeline_class}, {self.config.scheduler}",
        ]
        return "\n".join(imports)

    def generate_model_loading(self) -> str:
        """Generate model loading code."""
        model_id = self.config.model_id or "runwayml/stable-diffusion-v1-5"

        code = [
            "# Load pipeline",
            f'pipeline = DiffusionPipeline.from_pretrained(',
            f'    "{model_id}",',
            f'    torch_dtype=torch.{self.config.dtype},',
            f'    use_safetensors=True,',
            f')',
            f'pipeline.scheduler = {self.config.scheduler}.from_config('
            f'pipeline.scheduler.config)',
        ]

        if self.config.enable_offloading:
            code.extend([
                "# Enable memory optimizations for LoRA loading",
                "pipeline.enable_sequential_cpu_offload()",
            ])

        if self.config.enable_attention_slicing:
            code.append("pipeline.enable_attention_slicing()")

        code.extend([
            f'pipeline = pipeline.to("{self.config.device}")',
        ])

        return "\n".join(code)

    def generate_inference(self) -> str:
        """Generate inference code."""
        code = [
            "# Generate image",
            'prompt = "Your prompt here"',
            'negative_prompt = "blurry, low quality"',
            "",
            "output = pipeline(",
            '    prompt=prompt,',
            '    negative_prompt=negative_prompt,',
            f'    num_inference_steps={self.config.num_inference_steps},',
            f'    guidance_scale={self.config.guidance_scale},',
            '    generator=torch.Generator(device="cuda")'
            '.manual_seed(42),',
            ")",
            "",
            "# Save image",
            'image = output.images[0]',
            'image.save("output.png")',
        ]

        return "\n".join(code)

    def generate_lora_code(self) -> str:
        """Generate LoRA loading code if detected."""
        lora_nodes = [n for n in self.nodes.values()
                     if 'LoraLoader' in n.get('class_type', '')]

        if not lora_nodes:
            return ""

        code = ["# Load LoRA adapters", ""]
        for i, node in enumerate(lora_nodes, 1):
            lora_name = node.get('inputs', {}).get('lora_name', f'adapter_{i}')
            strength = node.get('inputs', {}).get('strength', 1.0)
            code.append(f'pipeline.load_lora_weights("{lora_name}")')
            code.append(f"# Strength: {strength}")

        code.extend([
            "",
            "# Unload LoRA when done",
            "# pipeline.unload_lora_weights()",
            ""
        ])

        return "\n".join(code)

    def generate_full_code(self) -> str:
        """Generate complete Diffusers inference script."""
        sections = [
            self.generate_imports(),
            "",
            "# Device configuration",
            f'device = "{self.config.device}"',
            f'dtype = torch.{self.config.dtype}',
            "",
            self.generate_model_loading(),
            "",
            self.generate_lora_code(),
            self.generate_inference(),
        ]

        return "\n\n".join(s for s in sections if s)

    def convert(self, workflow_path: str, output_path: Optional[str] = None) -> str:
        """Convert workflow to Diffusers code."""
        self.load_workflow(workflow_path)
        self.analyze_workflow()
        code = self.generate_full_code()

        if output_path:
            with open(output_path, 'w') as f:
                f.write(code)
            print(f"Generated: {output_path}")
        else:
            print(code)

        return code


def main():
    """CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Convert ComfyUI workflows to HuggingFace Diffusers code"
    )
    parser.add_argument("workflow", help="Path to ComfyUI workflow JSON")
    parser.add_argument(
        "-o", "--output",
        help="Output Python file path (default: print to stdout)"
    )
    parser.add_argument(
        "--scheduler",
        default="DPMPlusPlannerScheduler",
        help="Scheduler class name"
    )
    parser.add_argument(
        "--steps",
        type=int,
        default=30,
        help="Number of inference steps"
    )
    parser.add_argument(
        "--guidance",
        type=float,
        default=7.5,
        help="Classifier-free guidance scale"
    )
    parser.add_argument(
        "--offloading",
        action="store_true",
        help="Enable CPU offloading"
    )
    parser.add_argument(
        "--attention-slicing",
        action="store_true",
        help="Enable attention slicing"
    )

    args = parser.parse_args()

    converter = ComfyUIWorkflowConverter()
    if args.scheduler:
        converter.config.scheduler = args.scheduler
    if args.steps:
        converter.config.num_inference_steps = args.steps
    if args.guidance:
        converter.config.guidance_scale = args.guidance
    if args.offloading:
        converter.config.enable_offloading = True
    if args.attention_slicing:
        converter.config.enable_attention_slicing = True

    try:
        converter.convert(args.workflow, args.output)
    except FileNotFoundError:
        print(f"Error: Workflow file not found: {args.workflow}", file=sys.stderr)
        sys.exit(1)
    except json.JSONDecodeError:
        print(f"Error: Invalid JSON in workflow file: {args.workflow}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
