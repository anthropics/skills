#!/usr/bin/env python3
"""
Inference Optimizer

Analyzes and benchmarks vision models, and provides optimization recommendations.
Supports PyTorch, ONNX, and TensorRT models.

Usage:
    python inference_optimizer.py model.pt --benchmark
    python inference_optimizer.py model.pt --export onnx --output model.onnx
    python inference_optimizer.py model.onnx --analyze
"""

import os
import sys
import json
import argparse
import logging
import time
from pathlib import Path
from typing import Dict, List, Optional, Any, Tuple
from datetime import datetime
import statistics

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


# Model format signatures
MODEL_FORMATS = {
    '.pt': 'pytorch',
    '.pth': 'pytorch',
    '.onnx': 'onnx',
    '.engine': 'tensorrt',
    '.trt': 'tensorrt',
    '.xml': 'openvino',
    '.mlpackage': 'coreml',
    '.mlmodel': 'coreml',
}

# Optimization recommendations
OPTIMIZATION_PATHS = {
    ('pytorch', 'gpu'): ['onnx', 'tensorrt_fp16'],
    ('pytorch', 'cpu'): ['onnx', 'onnxruntime'],
    ('pytorch', 'edge'): ['onnx', 'tensorrt_int8'],
    ('pytorch', 'mobile'): ['onnx', 'tflite'],
    ('pytorch', 'apple'): ['coreml'],
    ('pytorch', 'intel'): ['onnx', 'openvino'],
    ('onnx', 'gpu'): ['tensorrt_fp16'],
    ('onnx', 'cpu'): ['onnxruntime'],
}


class InferenceOptimizer:
    """Analyzes and optimizes vision model inference."""

    def __init__(self, model_path: str):
        self.model_path = Path(model_path)
        self.model_format = self._detect_format()
        self.model_info = {}
        self.benchmark_results = {}

    def _detect_format(self) -> str:
        """Detect model format from file extension."""
        suffix = self.model_path.suffix.lower()
        if suffix in MODEL_FORMATS:
            return MODEL_FORMATS[suffix]
        raise ValueError(f"Unknown model format: {suffix}")

    def analyze_model(self) -> Dict[str, Any]:
        """Analyze model structure and size."""
        logger.info(f"Analyzing model: {self.model_path}")

        analysis = {
            'path': str(self.model_path),
            'format': self.model_format,
            'file_size_mb': self.model_path.stat().st_size / 1024 / 1024,
            'parameters': None,
            'layers': [],
            'input_shape': None,
            'output_shape': None,
            'ops_count': None,
        }

        if self.model_format == 'onnx':
            analysis.update(self._analyze_onnx())
        elif self.model_format == 'pytorch':
            analysis.update(self._analyze_pytorch())

        self.model_info = analysis
        return analysis

    def _analyze_onnx(self) -> Dict[str, Any]:
        """Analyze ONNX model."""
        try:
            import onnx
            model = onnx.load(str(self.model_path))
            onnx.checker.check_model(model)

            # Count parameters
            total_params = 0
            for initializer in model.graph.initializer:
                param_count = 1
                for dim in initializer.dims:
                    param_count *= dim
                total_params += param_count

            # Get input/output shapes
            inputs = []
            for inp in model.graph.input:
                shape = [d.dim_value if d.dim_value else -1
                        for d in inp.type.tensor_type.shape.dim]
                inputs.append({'name': inp.name, 'shape': shape})

            outputs = []
            for out in model.graph.output:
                shape = [d.dim_value if d.dim_value else -1
                        for d in out.type.tensor_type.shape.dim]
                outputs.append({'name': out.name, 'shape': shape})

            # Count operators
            op_counts = {}
            for node in model.graph.node:
                op_type = node.op_type
                op_counts[op_type] = op_counts.get(op_type, 0) + 1

            return {
                'parameters': total_params,
                'inputs': inputs,
                'outputs': outputs,
                'operator_counts': op_counts,
                'num_nodes': len(model.graph.node),
                'opset_version': model.opset_import[0].version if model.opset_import else None,
            }

        except ImportError:
            logger.warning("onnx package not installed, skipping detailed analysis")
            return {}
        except Exception as e:
            logger.error(f"Error analyzing ONNX model: {e}")
            return {'error': str(e)}

    def _analyze_pytorch(self) -> Dict[str, Any]:
        """Analyze PyTorch model."""
        try:
            import torch

            # Try to load as checkpoint
            checkpoint = torch.load(str(self.model_path), map_location='cpu')

            # Handle different checkpoint formats
            if isinstance(checkpoint, dict):
                if 'model' in checkpoint:
                    state_dict = checkpoint['model']
                elif 'state_dict' in checkpoint:
                    state_dict = checkpoint['state_dict']
                else:
                    state_dict = checkpoint
            else:
                # Assume it's the model itself
                if hasattr(checkpoint, 'state_dict'):
                    state_dict = checkpoint.state_dict()
                else:
                    return {'error': 'Could not extract state dict'}

            # Count parameters
            total_params = 0
            layer_info = []
            for name, param in state_dict.items():
                if hasattr(param, 'numel'):
                    param_count = param.numel()
                    total_params += param_count
                    layer_info.append({
                        'name': name,
                        'shape': list(param.shape),
                        'params': param_count,
                        'dtype': str(param.dtype)
                    })

            return {
                'parameters': total_params,
                'layers': layer_info[:20],  # First 20 layers
                'num_layers': len(layer_info),
            }

        except ImportError:
            logger.warning("torch package not installed, skipping detailed analysis")
            return {}
        except Exception as e:
            logger.error(f"Error analyzing PyTorch model: {e}")
            return {'error': str(e)}

    def benchmark(self, input_size: Tuple[int, int] = (640, 640),
                  batch_sizes: List[int] = None,
                  num_iterations: int = 100,
                  warmup: int = 10) -> Dict[str, Any]:
        """Benchmark model inference speed."""
        if batch_sizes is None:
            batch_sizes = [1, 4, 8, 16]

        logger.info(f"Benchmarking model with input size {input_size}")

        results = {
            'input_size': input_size,
            'num_iterations': num_iterations,
            'warmup_iterations': warmup,
            'batch_results': [],
            'device': 'cpu',
        }

        try:
            if self.model_format == 'onnx':
                results.update(self._benchmark_onnx(input_size, batch_sizes,
                                                    num_iterations, warmup))
            elif self.model_format == 'pytorch':
                results.update(self._benchmark_pytorch(input_size, batch_sizes,
                                                       num_iterations, warmup))
            else:
                results['error'] = f"Benchmarking not supported for {self.model_format}"

        except Exception as e:
            results['error'] = str(e)
            logger.error(f"Benchmark failed: {e}")

        self.benchmark_results = results
        return results

    def _benchmark_onnx(self, input_size: Tuple[int, int],
                        batch_sizes: List[int],
                        num_iterations: int, warmup: int) -> Dict[str, Any]:
        """Benchmark ONNX model."""
        import numpy as np

        try:
            import onnxruntime as ort

            # Try GPU first, fall back to CPU
            providers = ['CPUExecutionProvider']
            try:
                if 'CUDAExecutionProvider' in ort.get_available_providers():
                    providers = ['CUDAExecutionProvider'] + providers
            except:
                pass

            session = ort.InferenceSession(str(self.model_path), providers=providers)
            input_name = session.get_inputs()[0].name
            device = 'cuda' if 'CUDA' in session.get_providers()[0] else 'cpu'

            results = {'device': device, 'provider': session.get_providers()[0]}
            batch_results = []

            for batch_size in batch_sizes:
                # Create dummy input
                dummy = np.random.randn(batch_size, 3, *input_size).astype(np.float32)

                # Warmup
                for _ in range(warmup):
                    session.run(None, {input_name: dummy})

                # Benchmark
                latencies = []
                for _ in range(num_iterations):
                    start = time.perf_counter()
                    session.run(None, {input_name: dummy})
                    latencies.append((time.perf_counter() - start) * 1000)

                batch_result = {
                    'batch_size': batch_size,
                    'mean_latency_ms': statistics.mean(latencies),
                    'std_latency_ms': statistics.stdev(latencies) if len(latencies) > 1 else 0,
                    'min_latency_ms': min(latencies),
                    'max_latency_ms': max(latencies),
                    'p50_latency_ms': sorted(latencies)[len(latencies) // 2],
                    'p95_latency_ms': sorted(latencies)[int(len(latencies) * 0.95)],
                    'p99_latency_ms': sorted(latencies)[int(len(latencies) * 0.99)],
                    'throughput_fps': batch_size * 1000 / statistics.mean(latencies),
                }
                batch_results.append(batch_result)

                logger.info(f"Batch {batch_size}: {batch_result['mean_latency_ms']:.2f}ms, "
                           f"{batch_result['throughput_fps']:.1f} FPS")

            results['batch_results'] = batch_results
            return results

        except ImportError:
            return {'error': 'onnxruntime not installed'}

    def _benchmark_pytorch(self, input_size: Tuple[int, int],
                          batch_sizes: List[int],
                          num_iterations: int, warmup: int) -> Dict[str, Any]:
        """Benchmark PyTorch model."""
        try:
            import torch
            import numpy as np

            # Load model
            device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
            checkpoint = torch.load(str(self.model_path), map_location=device)

            # Handle different checkpoint formats
            if isinstance(checkpoint, dict) and 'model' in checkpoint:
                model = checkpoint['model']
            elif hasattr(checkpoint, 'forward'):
                model = checkpoint
            else:
                return {'error': 'Could not load model for benchmarking'}

            model.to(device)
            model.train(False)

            results = {'device': str(device)}
            batch_results = []

            with torch.no_grad():
                for batch_size in batch_sizes:
                    dummy = torch.randn(batch_size, 3, *input_size, device=device)

                    # Warmup
                    for _ in range(warmup):
                        _ = model(dummy)
                    if device.type == 'cuda':
                        torch.cuda.synchronize()

                    # Benchmark
                    latencies = []
                    for _ in range(num_iterations):
                        if device.type == 'cuda':
                            torch.cuda.synchronize()
                        start = time.perf_counter()
                        _ = model(dummy)
                        if device.type == 'cuda':
                            torch.cuda.synchronize()
                        latencies.append((time.perf_counter() - start) * 1000)

                    batch_result = {
                        'batch_size': batch_size,
                        'mean_latency_ms': statistics.mean(latencies),
                        'std_latency_ms': statistics.stdev(latencies) if len(latencies) > 1 else 0,
                        'min_latency_ms': min(latencies),
                        'max_latency_ms': max(latencies),
                        'throughput_fps': batch_size * 1000 / statistics.mean(latencies),
                    }
                    batch_results.append(batch_result)

                    logger.info(f"Batch {batch_size}: {batch_result['mean_latency_ms']:.2f}ms, "
                               f"{batch_result['throughput_fps']:.1f} FPS")

            results['batch_results'] = batch_results
            return results

        except ImportError:
            return {'error': 'torch not installed'}
        except Exception as e:
            return {'error': str(e)}

    def get_optimization_recommendations(self, target: str = 'gpu') -> List[Dict[str, Any]]:
        """Get optimization recommendations for target platform."""
        recommendations = []

        key = (self.model_format, target)
        if key in OPTIMIZATION_PATHS:
            path = OPTIMIZATION_PATHS[key]
            for step in path:
                rec = {
                    'step': step,
                    'description': self._get_step_description(step),
                    'expected_speedup': self._get_expected_speedup(step),
                    'command': self._get_step_command(step),
                }
                recommendations.append(rec)

        # Add general recommendations
        if self.model_info:
            params = self.model_info.get('parameters', 0)
            if params and params > 50_000_000:
                recommendations.append({
                    'step': 'pruning',
                    'description': f'Model has {params/1e6:.1f}M parameters. '
                                 'Consider structured pruning to reduce size.',
                    'expected_speedup': '1.5-2x',
                })

            file_size = self.model_info.get('file_size_mb', 0)
            if file_size > 100:
                recommendations.append({
                    'step': 'quantization',
                    'description': f'Model size is {file_size:.1f}MB. '
                                 'INT8 quantization can reduce by 75%.',
                    'expected_speedup': '2-4x',
                })

        return recommendations

    def _get_step_description(self, step: str) -> str:
        """Get description for optimization step."""
        descriptions = {
            'onnx': 'Export to ONNX format for framework-agnostic deployment',
            'tensorrt_fp16': 'Convert to TensorRT with FP16 precision for NVIDIA GPUs',
            'tensorrt_int8': 'Convert to TensorRT with INT8 quantization for edge devices',
            'onnxruntime': 'Use ONNX Runtime for optimized CPU/GPU inference',
            'openvino': 'Convert to OpenVINO for Intel CPU/GPU optimization',
            'coreml': 'Convert to CoreML for Apple Silicon acceleration',
            'tflite': 'Convert to TensorFlow Lite for mobile deployment',
        }
        return descriptions.get(step, step)

    def _get_expected_speedup(self, step: str) -> str:
        """Get expected speedup for optimization step."""
        speedups = {
            'onnx': '1-1.5x',
            'tensorrt_fp16': '2-4x',
            'tensorrt_int8': '3-6x',
            'onnxruntime': '1.2-2x',
            'openvino': '1.5-3x',
            'coreml': '2-5x (on Apple Silicon)',
            'tflite': '1-2x',
        }
        return speedups.get(step, 'varies')

    def _get_step_command(self, step: str) -> str:
        """Get command for optimization step."""
        model_name = self.model_path.stem
        commands = {
            'onnx': f'yolo export model={model_name}.pt format=onnx',
            'tensorrt_fp16': f'trtexec --onnx={model_name}.onnx --saveEngine={model_name}.engine --fp16',
            'tensorrt_int8': f'trtexec --onnx={model_name}.onnx --saveEngine={model_name}.engine --int8',
            'onnxruntime': f'pip install onnxruntime-gpu',
            'openvino': f'mo --input_model {model_name}.onnx --output_dir openvino/',
            'coreml': f'yolo export model={model_name}.pt format=coreml',
        }
        return commands.get(step, '')

    def print_summary(self):
        """Print analysis and benchmark summary."""
        print("\n" + "=" * 70)
        print("MODEL ANALYSIS SUMMARY")
        print("=" * 70)

        if self.model_info:
            print(f"Path:        {self.model_info.get('path', 'N/A')}")
            print(f"Format:      {self.model_info.get('format', 'N/A')}")
            print(f"File Size:   {self.model_info.get('file_size_mb', 0):.2f} MB")

            params = self.model_info.get('parameters')
            if params:
                print(f"Parameters:  {params:,} ({params/1e6:.2f}M)")

            if 'num_nodes' in self.model_info:
                print(f"Nodes:       {self.model_info['num_nodes']}")

        if self.benchmark_results and 'batch_results' in self.benchmark_results:
            print("\n" + "-" * 70)
            print("BENCHMARK RESULTS")
            print("-" * 70)
            print(f"Device:      {self.benchmark_results.get('device', 'N/A')}")
            print(f"Input Size:  {self.benchmark_results.get('input_size', 'N/A')}")
            print()
            print(f"{'Batch':<8} {'Latency (ms)':<15} {'Throughput (FPS)':<18} {'P99 (ms)':<12}")
            print("-" * 55)

            for result in self.benchmark_results['batch_results']:
                print(f"{result['batch_size']:<8} "
                      f"{result['mean_latency_ms']:<15.2f} "
                      f"{result['throughput_fps']:<18.1f} "
                      f"{result.get('p99_latency_ms', 0):<12.2f}")

        print("=" * 70 + "\n")


def main():
    parser = argparse.ArgumentParser(
        description="Analyze and optimize vision model inference"
    )
    parser.add_argument('model_path', help='Path to model file')
    parser.add_argument('--analyze', action='store_true',
                       help='Analyze model structure')
    parser.add_argument('--benchmark', action='store_true',
                       help='Benchmark inference speed')
    parser.add_argument('--input-size', type=int, nargs=2, default=[640, 640],
                       metavar=('H', 'W'), help='Input image size')
    parser.add_argument('--batch-sizes', type=int, nargs='+', default=[1, 4, 8],
                       help='Batch sizes to benchmark')
    parser.add_argument('--iterations', type=int, default=100,
                       help='Number of benchmark iterations')
    parser.add_argument('--warmup', type=int, default=10,
                       help='Number of warmup iterations')
    parser.add_argument('--target', choices=['gpu', 'cpu', 'edge', 'mobile', 'apple', 'intel'],
                       default='gpu', help='Target deployment platform')
    parser.add_argument('--recommend', action='store_true',
                       help='Show optimization recommendations')
    parser.add_argument('--json', action='store_true',
                       help='Output as JSON')
    parser.add_argument('--output', '-o', help='Output file path')

    args = parser.parse_args()

    if not Path(args.model_path).exists():
        logger.error(f"Model not found: {args.model_path}")
        sys.exit(1)

    try:
        optimizer = InferenceOptimizer(args.model_path)
    except ValueError as e:
        logger.error(str(e))
        sys.exit(1)

    results = {}

    # Analyze model
    if args.analyze or not (args.benchmark or args.recommend):
        results['analysis'] = optimizer.analyze_model()

    # Benchmark
    if args.benchmark:
        results['benchmark'] = optimizer.benchmark(
            input_size=tuple(args.input_size),
            batch_sizes=args.batch_sizes,
            num_iterations=args.iterations,
            warmup=args.warmup
        )

    # Recommendations
    if args.recommend:
        if not optimizer.model_info:
            optimizer.analyze_model()
        results['recommendations'] = optimizer.get_optimization_recommendations(args.target)

    # Output
    if args.json:
        print(json.dumps(results, indent=2, default=str))
    else:
        optimizer.print_summary()

        if args.recommend and 'recommendations' in results:
            print("OPTIMIZATION RECOMMENDATIONS")
            print("-" * 70)
            for i, rec in enumerate(results['recommendations'], 1):
                print(f"\n{i}. {rec['step'].upper()}")
                print(f"   {rec['description']}")
                print(f"   Expected speedup: {rec['expected_speedup']}")
                if rec.get('command'):
                    print(f"   Command: {rec['command']}")
            print()

    # Save to file
    if args.output:
        with open(args.output, 'w') as f:
            json.dump(results, f, indent=2, default=str)
        logger.info(f"Results saved to {args.output}")


if __name__ == '__main__':
    main()
