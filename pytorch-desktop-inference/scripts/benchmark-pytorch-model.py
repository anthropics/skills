#!/usr/bin/env python3
"""
PyTorch Model Benchmarking and Profiling Script

Comprehensive tool for profiling PyTorch models on desktop systems.
Measures latency, throughput, memory usage, and identifies bottlenecks.

Requirements:
    - torch>=2.9.0
    - numpy
    - pyyaml (optional, for config files)

Usage:
    python benchmark-pytorch-model.py --model resnet50 --device cuda
    python benchmark-pytorch-model.py --checkpoint model.pt --batch-size 32
"""

import argparse
import time
import json
import gc
import warnings
from pathlib import Path
from typing import Dict, Tuple, Any
import numpy as np

try:
    import torch
    from torch.profiler import profile, record_function, ProfilerActivity
except ImportError:
    print("PyTorch not installed. Please install: pip install torch")
    exit(1)


class PyTorchBenchmark:
    """Comprehensive PyTorch model benchmarking utility."""

    def __init__(
        self,
        model: torch.nn.Module,
        device: str = "cuda" if torch.cuda.is_available() else "cpu",
        batch_size: int = 1,
        input_shape: Tuple[int, ...] = (1, 3, 224, 224),
    ):
        """Initialize benchmark.

        Args:
            model: PyTorch model to benchmark
            device: Device to run on ('cuda' or 'cpu')
            batch_size: Batch size for inference
            input_shape: Input tensor shape
        """
        self.model = model.to(device).eval()
        self.device = torch.device(device)
        self.batch_size = batch_size
        self.input_shape = (batch_size,) + input_shape[1:]
        self.results = {}

    def warmup(self, num_warmup: int = 10) -> None:
        """Warmup GPU with dummy runs."""
        dummy_input = torch.randn(self.input_shape, device=self.device)
        with torch.inference_mode():
            for _ in range(num_warmup):
                _ = self.model(dummy_input)
        torch.cuda.synchronize() if self.device.type == "cuda" else None

    def benchmark_latency(
        self, num_runs: int = 100, num_warmup: int = 10
    ) -> Dict[str, float]:
        """Benchmark inference latency.

        Args:
            num_runs: Number of runs for averaging
            num_warmup: Number of warmup runs

        Returns:
            Dictionary with latency statistics
        """
        self.warmup(num_warmup)
        dummy_input = torch.randn(self.input_shape, device=self.device)

        torch.cuda.synchronize() if self.device.type == "cuda" else None
        start = time.perf_counter()

        with torch.inference_mode():
            for _ in range(num_runs):
                _ = self.model(dummy_input)

        torch.cuda.synchronize() if self.device.type == "cuda" else None
        elapsed = time.perf_counter() - start

        latency_ms = (elapsed / num_runs) * 1000
        throughput = num_runs / elapsed

        self.results["latency"] = {
            "mean_ms": latency_ms,
            "throughput_samples_per_sec": throughput,
            "total_time_sec": elapsed,
            "num_runs": num_runs,
        }

        return self.results["latency"]

    def benchmark_memory(self) -> Dict[str, float]:
        """Benchmark peak memory usage.

        Returns:
            Dictionary with memory statistics
        """
        if self.device.type == "cuda":
            torch.cuda.reset_peak_memory_stats()
            torch.cuda.empty_cache()

        dummy_input = torch.randn(self.input_shape, device=self.device)

        with torch.inference_mode():
            output = self.model(dummy_input)

        if self.device.type == "cuda":
            peak_memory = torch.cuda.max_memory_allocated() / 1e9
            allocated = torch.cuda.memory_allocated() / 1e9
            reserved = torch.cuda.memory_reserved() / 1e9

            self.results["memory"] = {
                "peak_memory_gb": peak_memory,
                "allocated_gb": allocated,
                "reserved_gb": reserved,
            }
        else:
            self.results["memory"] = {
                "device": "cpu",
                "peak_memory_gb": 0.0,
                "note": "Memory profiling on CPU requires external tools",
            }

        return self.results["memory"]

    def profile_model(self, num_runs: int = 10) -> None:
        """Profile model with PyTorch profiler.

        Args:
            num_runs: Number of runs for profiling
        """
        dummy_input = torch.randn(self.input_shape, device=self.device)
        activities = [ProfilerActivity.CPU]
        if self.device.type == "cuda":
            activities.append(ProfilerActivity.CUDA)

        with profile(
            activities=activities,
            record_shapes=True,
            profile_memory=True,
            with_stack=False,
        ) as prof:
            with torch.inference_mode():
                for _ in range(num_runs):
                    _ = self.model(dummy_input)

        # Extract key statistics
        key_avg = prof.key_averages()
        top_events = sorted(
            key_avg, key=lambda x: x.self_cuda_time_total, reverse=True
        )[:5]

        profile_stats = []
        for event in top_events:
            profile_stats.append(
                {
                    "name": event.key,
                    "cpu_ms": event.self_cpu_time_total / 1e3,
                    "cuda_ms": event.self_cuda_time_total / 1e3,
                }
            )

        self.results["profiling"] = profile_stats

    def benchmark_with_compile(self) -> Dict[str, Any]:
        """Benchmark torch.compile() speedup (if available).

        Returns:
            Dictionary with compile vs non-compile comparison
        """
        try:
            original_latency = self.benchmark_latency(num_runs=50)["mean_ms"]

            model_compiled = torch.compile(
                self.model, backend="inductor", dynamic=False
            )
            self.model = model_compiled

            torch.cuda.empty_cache() if self.device.type == "cuda" else None
            compiled_latency = self.benchmark_latency(num_runs=50)["mean_ms"]

            speedup = original_latency / compiled_latency

            self.results["torch_compile"] = {
                "original_latency_ms": original_latency,
                "compiled_latency_ms": compiled_latency,
                "speedup": speedup,
                "backend": "inductor",
            }

            return self.results["torch_compile"]
        except Exception as e:
            self.results["torch_compile"] = {"error": str(e)}
            return self.results["torch_compile"]

    def benchmark_quantization(self) -> Dict[str, Any]:
        """Benchmark dynamic quantization speedup.

        Returns:
            Dictionary with quantization comparison
        """
        try:
            original_latency = self.benchmark_latency(num_runs=50)["mean_ms"]

            quantized_model = torch.quantization.quantize_dynamic(
                self.model, {torch.nn.Linear}, dtype=torch.qint8
            )
            quantized_model = quantized_model.to(self.device)
            quantized_model.eval()

            self.model = quantized_model
            torch.cuda.empty_cache() if self.device.type == "cuda" else None

            quantized_latency = self.benchmark_latency(num_runs=50)["mean_ms"]
            speedup = original_latency / quantized_latency

            self.results["quantization"] = {
                "original_latency_ms": original_latency,
                "quantized_latency_ms": quantized_latency,
                "speedup": speedup,
            }

            return self.results["quantization"]
        except Exception as e:
            self.results["quantization"] = {"error": str(e)}
            return self.results["quantization"]

    def run_full_benchmark(self) -> Dict[str, Any]:
        """Run comprehensive benchmark suite.

        Returns:
            Complete benchmark results
        """
        print("Starting comprehensive benchmark...")

        print("  - Benchmarking latency...")
        self.benchmark_latency()

        print("  - Benchmarking memory...")
        self.benchmark_memory()

        print("  - Profiling model...")
        self.profile_model()

        if self.device.type == "cuda":
            print("  - Testing torch.compile()...")
            self.benchmark_with_compile()

        print("  - Testing quantization...")
        self.benchmark_quantization()

        return self.results

    def print_results(self) -> None:
        """Print formatted benchmark results."""
        print("\n" + "=" * 60)
        print("PYTORCH BENCHMARK RESULTS")
        print("=" * 60)

        if "latency" in self.results:
            print("\nLatency:")
            for key, value in self.results["latency"].items():
                if isinstance(value, float):
                    print(f"  {key}: {value:.4f}")
                else:
                    print(f"  {key}: {value}")

        if "memory" in self.results:
            print("\nMemory Usage:")
            for key, value in self.results["memory"].items():
                if isinstance(value, float):
                    print(f"  {key}: {value:.4f} GB")
                else:
                    print(f"  {key}: {value}")

        if "torch_compile" in self.results and "speedup" in self.results["torch_compile"]:
            print(
                f"\ntorch.compile() Speedup: {self.results['torch_compile']['speedup']:.2f}x"
            )

        if "quantization" in self.results and "speedup" in self.results["quantization"]:
            print(
                f"Quantization Speedup: {self.results['quantization']['speedup']:.2f}x"
            )

        print("\n" + "=" * 60)

    def save_results(self, filepath: str) -> None:
        """Save results to JSON file.

        Args:
            filepath: Path to save JSON results
        """
        with open(filepath, "w") as f:
            json.dump(self.results, f, indent=2, default=str)
        print(f"Results saved to {filepath}")


def load_model(model_path: str, device: str) -> torch.nn.Module:
    """Load model from checkpoint.

    Args:
        model_path: Path to model checkpoint
        device: Device to load model on

    Returns:
        Loaded PyTorch model
    """
    model = torch.load(model_path, map_location=device)
    return model


def create_dummy_model(name: str = "resnet50", device: str = "cuda") -> torch.nn.Module:
    """Create dummy model for testing.

    Args:
        name: Model name (resnet50, mobilenet_v2, etc.)
        device: Device to create model on

    Returns:
        PyTorch model
    """
    try:
        import torchvision.models as models

        if hasattr(models, name):
            model = getattr(models, name)(pretrained=False)
        else:
            raise ValueError(f"Model {name} not found in torchvision")
    except ImportError:
        print("torchvision not installed. Creating simple CNN instead.")
        model = torch.nn.Sequential(
            torch.nn.Conv2d(3, 64, 3, padding=1),
            torch.nn.ReLU(),
            torch.nn.Conv2d(64, 128, 3, padding=1),
            torch.nn.AdaptiveAvgPool2d((1, 1)),
            torch.nn.Flatten(),
            torch.nn.Linear(128, 1000),
        )

    return model.to(device).eval()


def main():
    parser = argparse.ArgumentParser(description="Benchmark PyTorch models")
    parser.add_argument(
        "--model", default="resnet50", help="Model name from torchvision"
    )
    parser.add_argument(
        "--checkpoint", help="Path to model checkpoint (overrides --model)"
    )
    parser.add_argument(
        "--device",
        default="cuda" if torch.cuda.is_available() else "cpu",
        choices=["cuda", "cpu"],
        help="Device to benchmark on",
    )
    parser.add_argument("--batch-size", type=int, default=1, help="Batch size")
    parser.add_argument(
        "--input-shape",
        type=int,
        nargs="+",
        default=[3, 224, 224],
        help="Input shape (C H W)",
    )
    parser.add_argument("--num-runs", type=int, default=100, help="Number of runs")
    parser.add_argument(
        "--save-results", help="Path to save JSON results"
    )

    args = parser.parse_args()

    # Load model
    if args.checkpoint:
        print(f"Loading model from {args.checkpoint}...")
        model = load_model(args.checkpoint, args.device)
    else:
        print(f"Creating {args.model} model...")
        model = create_dummy_model(args.model, args.device)

    # Run benchmark
    benchmark = PyTorchBenchmark(
        model,
        device=args.device,
        batch_size=args.batch_size,
        input_shape=tuple(args.input_shape),
    )

    benchmark.run_full_benchmark()
    benchmark.print_results()

    if args.save_results:
        benchmark.save_results(args.save_results)


if __name__ == "__main__":
    main()
