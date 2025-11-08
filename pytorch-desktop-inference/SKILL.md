---
name: pytorch-desktop-inference
description: Optimize PyTorch v2.9.0 inference for desktop deployment with quantization and memory management. Use when implementing ML model inference, optimizing CUDA performance, managing GPU memory, applying torch.compile() JIT, configuring quantization, or benchmarking model performance for desktop applications.
---

# PyTorch for Desktop AI Applications

## Overview

PyTorch v2.9.0 provides powerful tools for deploying machine learning models on desktop systems with optimized inference performance. This skill covers model optimization, quantization techniques, CUDA acceleration, memory management, and comprehensive benchmarking to ensure your applications run efficiently on consumer-grade hardware.

## Core Capabilities

### 1. Inference Optimization with torch.compile()

PyTorch 2.x introduces `torch.compile()` for automatic JIT compilation and optimization:

```python
import torch
import torch._dynamo

# Enable torch.compile with eager mode backend (safest)
model_compiled = torch.compile(model, backend="eager")

# Production backend (CPU and CUDA)
model_compiled = torch.compile(model, backend="inductor")

# Inference mode - disables gradient computation
with torch.inference_mode():
    output = model_compiled(input_tensor)
```

**Key Benefits:**
- 1.5-3x speedup on supported hardware
- Automatic kernel fusion
- Memory optimization
- Works with TorchScript export

### 2. Model Quantization Strategies

#### Dynamic Quantization (Easiest)
Best for production when speed is prioritized over peak accuracy:

```python
quantized_model = torch.quantization.quantize_dynamic(
    model,
    {torch.nn.Linear, torch.nn.Conv2d},
    dtype=torch.qint8
)
```

#### Static Quantization (Better Accuracy)
Requires calibration data for optimal accuracy:

```python
model.qconfig = torch.quantization.get_default_qconfig('fbgemm')
torch.quantization.prepare(model, inplace=True)

# Calibration loop
for data in calibration_loader:
    model(data)

torch.quantization.convert(model, inplace=True)
```

#### Quantization-Aware Training (QAT)
Train with quantization in mind for best results:

```python
model.qconfig = torch.quantization.get_default_qat_qconfig('fbgemm')
torch.quantization.prepare_qat(model, inplace=True)

# Training loop
for epoch in range(num_epochs):
    for data, target in train_loader:
        output = model(data)
        loss = loss_fn(output, target)
        loss.backward()
        optimizer.step()

torch.quantization.convert(model, inplace=True)
```

### 3. CUDA Performance Optimization

#### GPU Memory Management

```python
import torch

# Clear GPU cache
torch.cuda.empty_cache()

# Monitor GPU memory
print(f"Allocated: {torch.cuda.memory_allocated() / 1e9:.2f} GB")
print(f"Reserved: {torch.cuda.memory_reserved() / 1e9:.2f} GB")

# Set memory fraction (prevent OOM)
torch.cuda.set_per_process_memory_fraction(0.8)
```

#### Pinned Memory for Faster CPU-GPU Transfer

```python
# Allocate pinned memory
data_loader = DataLoader(
    dataset,
    pin_memory=True,
    num_workers=4
)
```

#### CUDA Streams for Overlapping Operations

```python
stream1 = torch.cuda.Stream()
stream2 = torch.cuda.Stream()

with torch.cuda.stream(stream1):
    output1 = model1(input1)

with torch.cuda.stream(stream2):
    output2 = model2(input2)

torch.cuda.current_stream().wait_stream(stream1)
torch.cuda.current_stream().wait_stream(stream2)
```

### 4. Memory Management Best Practices

```python
import torch
import gc

# Disable automatic mixed precision if not needed
torch.cuda.is_available()

# Gradient checkpointing for memory efficiency
from torch.utils.checkpoint import checkpoint

def forward(model, x):
    return checkpoint(model, x, use_reentrant=False)

# Clear cache regularly
torch.cuda.empty_cache()
gc.collect()

# Use context managers
with torch.no_grad():
    with torch.cuda.device(0):
        output = model(input_data)
```

### 5. Model Loading and Device Management

```python
import torch

# Load model to appropriate device
device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
model = torch.load("model.pt", map_location=device)
model.to(device)
model.eval()

# Set proper data type
model = model.half()  # FP16
model = model.to(torch.bfloat16)  # BF16

# Distribute across GPUs (if available)
if torch.cuda.device_count() > 1:
    model = torch.nn.DataParallel(model)
```

### 6. Benchmarking and Profiling

```python
import torch
from torch.profiler import profile, record_function, ProfilerActivity

# Warmup
for _ in range(10):
    model(dummy_input)

# Profile inference
with profile(
    activities=[ProfilerActivity.CPU, ProfilerActivity.CUDA],
    record_shapes=True
) as prof:
    for _ in range(100):
        model(input_data)

print(prof.key_averages().table(sort_by="cuda_time_total"))

# Memory profiling
torch.cuda.reset_peak_memory_stats()
output = model(input_data)
peak_memory = torch.cuda.max_memory_allocated() / 1e9
print(f"Peak memory: {peak_memory:.2f} GB")
```

## Performance Optimization Workflow

```
1. Baseline Benchmarking
   ↓
2. Select Optimization Strategy (compile, quantization, or both)
   ↓
3. Apply Optimization
   ↓
4. Validate Accuracy
   ↓
5. Profile Memory & Latency
   ↓
6. Iterate or Deploy
```

## Practical Example: Complete Inference Pipeline

```python
import torch
import time

class OptimizedInference:
    def __init__(self, model_path, device="cuda"):
        self.device = torch.device(device)

        # Load model
        self.model = torch.load(model_path, map_location=self.device)
        self.model.eval()

        # Optimize with compile
        self.model = torch.compile(self.model, backend="inductor")

        # Quantize if available
        if device == "cpu":
            self.model = torch.quantization.quantize_dynamic(
                self.model,
                {torch.nn.Linear},
                dtype=torch.qint8
            )

    def infer(self, input_data, num_runs=100):
        input_tensor = torch.tensor(input_data).to(self.device)

        # Warmup
        with torch.inference_mode():
            for _ in range(10):
                _ = self.model(input_tensor)

        # Benchmark
        torch.cuda.synchronize() if self.device.type == "cuda" else None
        start = time.perf_counter()

        with torch.inference_mode():
            for _ in range(num_runs):
                output = self.model(input_tensor)

        torch.cuda.synchronize() if self.device.type == "cuda" else None
        elapsed = time.perf_counter() - start

        latency_ms = (elapsed / num_runs) * 1000
        throughput = num_runs / elapsed

        return {
            "output": output.cpu().numpy(),
            "latency_ms": latency_ms,
            "throughput": throughput
        }
```

## Bundled Resources

This skill includes comprehensive guides and tools for PyTorch optimization:

- **benchmark-pytorch-model.py** - Complete performance profiling and benchmarking script
- **pytorch-inference-optimization.md** - Detailed guide to torch.compile(), JIT, and TorchScript
- **pytorch-quantization.md** - Comprehensive quantization techniques and best practices
- **pytorch-cuda-optimization.md** - CUDA acceleration, memory, and stream management
- **pytorch-memory-management.md** - Memory profiling, gradient tracking, and cache clearing
- **pytorch-config-template.yaml** - Production-ready inference configuration template

## Requirements

- **Python:** 3.10 or higher
- **PyTorch:** 2.9.0 or higher
- **CUDA:** 11.8+ (optional, for GPU acceleration)
- **GPU VRAM:** Minimum 2GB for desktop inference, 4GB+ recommended
- **System RAM:** 8GB+ recommended

## Common Use Cases

1. **Real-time Inference** - Deploy trained models with sub-100ms latency
2. **AI-Powered Desktop Apps** - Integrate ML into native applications
3. **Model Optimization** - Reduce model size and memory footprint
4. **GPU Acceleration** - Leverage CUDA for faster inference on consumer hardware
5. **Performance Analysis** - Profile and benchmark model inference performance
6. **Production Deployment** - Export and optimize models for release
