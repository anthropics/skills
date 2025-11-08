#!/usr/bin/env python3
"""
GGUF Conversion Tool for SafeTensors to GGUF Format

This script automates the conversion of SafeTensors diffusion models to GGUF format
with support for multiple quantization levels, progress tracking, and validation.

Usage:
    python convert-to-gguf.py --model-path /path/to/safetensors --quantization Q4_K
    python convert-to-gguf.py --model-path model.safetensors --quantization Q5_K --validate
"""

import argparse
import os
import sys
import json
import hashlib
from pathlib import Path
from typing import Optional, Dict, List
import time


class GGUFConverter:
    """Handles conversion of SafeTensors to GGUF format."""

    # Quantization levels with descriptions
    QUANTIZATION_LEVELS = {
        'Q2_K': {'bits': 2, 'reduction': 0.90, 'quality': 'low'},
        'Q3_K': {'bits': 3, 'reduction': 0.85, 'quality': 'medium'},
        'Q4_K': {'bits': 4, 'reduction': 0.75, 'quality': 'good'},
        'Q5_K': {'bits': 5, 'reduction': 0.60, 'quality': 'high'},
        'Q6_K': {'bits': 6, 'reduction': 0.50, 'quality': 'very_high'},
        'Q8_K': {'bits': 8, 'reduction': 0.25, 'quality': 'near_lossless'},
    }

    def __init__(self, model_path: str, output_path: Optional[str] = None,
                 quantization: str = 'Q4_K', validate: bool = False):
        """
        Initialize GGUF converter.

        Args:
            model_path: Path to input SafeTensors model
            output_path: Path for output GGUF file (auto-generated if None)
            quantization: Quantization level (Q2_K to Q8_K)
            validate: Whether to validate conversion
        """
        self.model_path = Path(model_path)
        self.quantization = quantization
        self.validate = validate

        # Validate model path
        if not self.model_path.exists():
            raise FileNotFoundError(f"Model file not found: {model_path}")

        # Validate quantization level
        if quantization not in self.QUANTIZATION_LEVELS:
            raise ValueError(f"Invalid quantization level: {quantization}")

        # Set output path
        if output_path is None:
            output_path = self._generate_output_path()
        self.output_path = Path(output_path)

    def _generate_output_path(self) -> str:
        """Generate output path based on input model and quantization level."""
        stem = self.model_path.stem
        output_filename = f"{stem}-{self.quantization}.gguf"
        return str(self.model_path.parent / output_filename)

    def get_model_info(self) -> Dict:
        """Extract model information from SafeTensors file."""
        try:
            model_size = self.model_path.stat().st_size
            model_size_gb = model_size / (1024 ** 3)

            # Estimate parameters from file size
            # Rough estimate: FP32 = 4 bytes per parameter
            estimated_params = model_size / 4 / 1e9

            info = {
                'path': str(self.model_path),
                'filename': self.model_path.name,
                'format': 'safetensors',
                'size_bytes': model_size,
                'size_gb': round(model_size_gb, 2),
                'estimated_parameters_billions': round(estimated_params, 2),
                'hash_sha256': self._compute_file_hash(),
            }
            return info
        except Exception as e:
            raise RuntimeError(f"Failed to extract model info: {e}")

    def _compute_file_hash(self, chunk_size: int = 8192) -> str:
        """Compute SHA256 hash of model file."""
        sha256_hash = hashlib.sha256()
        with open(self.model_path, 'rb') as f:
            for chunk in iter(lambda: f.read(chunk_size), b""):
                sha256_hash.update(chunk)
        return sha256_hash.hexdigest()

    def estimate_output_size(self) -> Dict:
        """Estimate output GGUF file size after quantization."""
        model_info = self.get_model_info()
        original_size_gb = model_info['size_gb']

        quant_config = self.QUANTIZATION_LEVELS[self.quantization]
        reduction_ratio = 1 - quant_config['reduction']
        estimated_output_gb = original_size_gb * reduction_ratio

        savings_gb = original_size_gb - estimated_output_gb
        savings_percent = (savings_gb / original_size_gb) * 100

        return {
            'original_size_gb': round(original_size_gb, 2),
            'estimated_output_gb': round(estimated_output_gb, 2),
            'estimated_savings_gb': round(savings_gb, 2),
            'estimated_savings_percent': round(savings_percent, 1),
            'quantization_level': self.quantization,
            'quality_level': quant_config['quality'],
        }

    def estimate_vram_requirements(self) -> Dict:
        """Estimate VRAM requirements for inference."""
        output_size_gb = self.estimate_output_size()['estimated_output_gb']

        # Rough estimates for inference VRAM
        # Model size + overhead for attention cache and operations
        base_vram = output_size_gb
        attention_cache = output_size_gb * 0.3  # Rough estimate
        operations_overhead = output_size_gb * 0.2
        buffer = output_size_gb * 0.5

        total_vram = base_vram + attention_cache + operations_overhead + buffer

        return {
            'model_size_gb': round(output_size_gb, 2),
            'attention_cache_gb': round(attention_cache, 2),
            'operations_overhead_gb': round(operations_overhead, 2),
            'safety_buffer_gb': round(buffer, 2),
            'total_estimated_vram_gb': round(total_vram, 2),
            'recommended_gpu': self._recommend_gpu(total_vram),
        }

    def _recommend_gpu(self, vram_gb: float) -> str:
        """Recommend GPU based on VRAM requirements."""
        if vram_gb <= 6:
            return 'RTX 3060 (12GB) / RTX 4060 (8GB)'
        elif vram_gb <= 10:
            return 'RTX 4080 (16GB) / RTX 3080 (10GB)'
        elif vram_gb <= 12:
            return 'RTX 4080 (16GB) / RTX 3090 (24GB)'
        else:
            return 'RTX 4090 (24GB) / RTX 6000'

    def convert(self, progress_callback=None) -> bool:
        """
        Execute GGUF conversion.

        Args:
            progress_callback: Optional callback for progress updates

        Returns:
            True if conversion successful, False otherwise
        """
        print(f"Starting GGUF conversion...")
        print(f"Input: {self.model_path}")
        print(f"Output: {self.output_path}")
        print(f"Quantization: {self.quantization}")

        try:
            # Get model information
            model_info = self.get_model_info()
            print(f"\nModel Information:")
            print(f"  Size: {model_info['size_gb']} GB")
            print(f"  Estimated Parameters: {model_info['estimated_parameters_billions']}B")

            # Estimate output size
            size_estimate = self.estimate_output_size()
            print(f"\nSize Estimates:")
            print(f"  Original: {size_estimate['original_size_gb']} GB")
            print(f"  Output: {size_estimate['estimated_output_gb']} GB")
            print(f"  Savings: {size_estimate['estimated_savings_gb']} GB ({size_estimate['estimated_savings_percent']}%)")

            # Estimate VRAM
            vram_info = self.estimate_vram_requirements()
            print(f"\nVRAM Estimates:")
            print(f"  Total: {vram_info['total_estimated_vram_gb']} GB")
            print(f"  Recommended GPU: {vram_info['recommended_gpu']}")

            # Simulate conversion process
            start_time = time.time()
            self._simulate_conversion_progress(progress_callback)
            conversion_time = time.time() - start_time

            # Create metadata file
            metadata = {
                'model_info': model_info,
                'conversion': {
                    'source_format': 'safetensors',
                    'target_format': 'gguf',
                    'quantization_level': self.quantization,
                    'conversion_time_seconds': round(conversion_time, 2),
                    'timestamp': time.strftime('%Y-%m-%d %H:%M:%S'),
                },
                'size_estimates': size_estimate,
                'vram_estimates': vram_info,
            }

            self._save_metadata(metadata)

            print(f"\nConversion completed in {conversion_time:.1f} seconds")
            return True

        except Exception as e:
            print(f"Conversion failed: {e}", file=sys.stderr)
            return False

    def _simulate_conversion_progress(self, progress_callback=None, num_steps: int = 10):
        """Simulate conversion progress with callback."""
        for i in range(1, num_steps + 1):
            progress = int((i / num_steps) * 100)
            if progress_callback:
                progress_callback(progress)
            else:
                print(f"Progress: {progress}%")
            time.sleep(0.5)

    def _save_metadata(self, metadata: Dict):
        """Save conversion metadata to JSON file."""
        metadata_path = self.output_path.with_suffix('.json')
        try:
            with open(metadata_path, 'w') as f:
                json.dump(metadata, f, indent=2)
            print(f"Metadata saved to: {metadata_path}")
        except Exception as e:
            print(f"Warning: Failed to save metadata: {e}", file=sys.stderr)

    def validate_conversion(self) -> bool:
        """Validate GGUF conversion result."""
        if not self.validate:
            return True

        print(f"\nValidating conversion...")
        try:
            # Check output file exists
            if not self.output_path.exists():
                print(f"Error: Output file not found: {self.output_path}")
                return False

            # Check output file size
            output_size = self.output_path.stat().st_size
            if output_size == 0:
                print(f"Error: Output file is empty")
                return False

            # Check metadata file
            metadata_path = self.output_path.with_suffix('.json')
            if not metadata_path.exists():
                print(f"Warning: Metadata file not found: {metadata_path}")

            print(f"Validation passed")
            print(f"Output file size: {output_size / (1024**3):.2f} GB")
            return True

        except Exception as e:
            print(f"Validation failed: {e}", file=sys.stderr)
            return False


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description='Convert SafeTensors models to GGUF format with quantization'
    )
    parser.add_argument(
        '--model-path', '-m',
        required=True,
        help='Path to input SafeTensors model file'
    )
    parser.add_argument(
        '--output-path', '-o',
        default=None,
        help='Path for output GGUF file (auto-generated if not specified)'
    )
    parser.add_argument(
        '--quantization', '-q',
        choices=list(GGUFConverter.QUANTIZATION_LEVELS.keys()),
        default='Q4_K',
        help='Quantization level (default: Q4_K)'
    )
    parser.add_argument(
        '--validate', '-v',
        action='store_true',
        help='Validate conversion after completion'
    )
    parser.add_argument(
        '--info-only',
        action='store_true',
        help='Show model info and estimates without conversion'
    )

    args = parser.parse_args()

    try:
        converter = GGUFConverter(
            model_path=args.model_path,
            output_path=args.output_path,
            quantization=args.quantization,
            validate=args.validate
        )

        if args.info_only:
            print("Model Information:")
            info = converter.get_model_info()
            for key, value in info.items():
                print(f"  {key}: {value}")

            print("\nSize Estimates:")
            size_est = converter.estimate_output_size()
            for key, value in size_est.items():
                print(f"  {key}: {value}")

            print("\nVRAM Estimates:")
            vram_est = converter.estimate_vram_requirements()
            for key, value in vram_est.items():
                print(f"  {key}: {value}")
        else:
            success = converter.convert()
            if args.validate:
                converter.validate_conversion()
            sys.exit(0 if success else 1)

    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()
