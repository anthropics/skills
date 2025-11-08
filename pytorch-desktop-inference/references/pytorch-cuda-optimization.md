# PyTorch CUDA Optimization Guide

## CUDA Basics

### Checking CUDA Availability

```python
import torch

# Check if CUDA is available
print(f"CUDA Available: {torch.cuda.is_available()}")
print(f"CUDA Version: {torch.version.cuda}")
print(f"GPU Count: {torch.cuda.device_count()}")

# Get GPU name
print(f"GPU Name: {torch.cuda.get_device_name(0)}")

# Get GPU capability
print(f"CUDA Capability: {torch.cuda.get_device_capability(0)}")
```

### Setting Device

```python
# Method 1: Default device
device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
tensor = torch.randn(100, 100, device=device)

# Method 2: Specific device
device = torch.device("cuda:0")  # First GPU
model = model.to(device)

# Method 3: Within context
with torch.cuda.device(0):
    x = torch.randn(100, 100)  # Created on GPU 0
```

## GPU Memory Management

### Memory Allocation and Deallocation

```python
import torch

# Check memory before
print(f"Allocated: {torch.cuda.memory_allocated() / 1e9:.2f} GB")
print(f"Reserved: {torch.cuda.memory_reserved() / 1e9:.2f} GB")

# Allocate tensor
large_tensor = torch.randn(1000, 1000, 1000, device="cuda")

# Check memory after
print(f"Allocated: {torch.cuda.memory_allocated() / 1e9:.2f} GB")

# Delete and free
del large_tensor
torch.cuda.empty_cache()

# Verify freed
print(f"Allocated: {torch.cuda.memory_allocated() / 1e9:.2f} GB")
```

### Memory Profiling

```python
import torch

# Reset peak memory stats
torch.cuda.reset_peak_memory_stats()

# Run inference
output = model(input_data)

# Get peak memory
peak_memory = torch.cuda.max_memory_allocated() / 1e9
print(f"Peak Memory: {peak_memory:.2f} GB")

# Get current memory
current_memory = torch.cuda.memory_allocated() / 1e9
print(f"Current Memory: {current_memory:.2f} GB")
```

### Memory Fraction Control

```python
import torch

# Limit GPU memory usage to 80% of available
torch.cuda.set_per_process_memory_fraction(0.8)

# Useful for multi-process systems or shared GPU resources
```

## CUDA Streams

CUDA streams allow overlapping computation and data transfer.

### Basic Stream Usage

```python
import torch

# Create streams
stream1 = torch.cuda.Stream()
stream2 = torch.cuda.Stream()

# Operations on stream1
with torch.cuda.stream(stream1):
    output1 = model1(input1)

# Operations on stream2 (parallel)
with torch.cuda.stream(stream2):
    output2 = model2(input2)

# Synchronize before using results
torch.cuda.current_stream().wait_stream(stream1)
torch.cuda.current_stream().wait_stream(stream2)

result = output1 + output2
```

### Stream Synchronization

```python
# Synchronize specific stream
stream.synchronize()

# Synchronize all streams
torch.cuda.synchronize()

# Important before timing measurements
```

### Advanced Stream Pattern: Pipeline Parallelism

```python
import torch

class StreamPipeline:
    def __init__(self, models, device="cuda"):
        self.models = [m.to(device) for m in models]
        self.streams = [torch.cuda.Stream() for _ in models]
        self.device = device

    def forward(self, inputs):
        """Process through pipeline with stream overlapping."""
        outputs = []

        for i, (model, stream, x) in enumerate(
            zip(self.models, self.streams, inputs)
        ):
            with torch.cuda.stream(stream):
                output = model(x)
                outputs.append(output)

        # Wait for all streams
        torch.cuda.synchronize()
        return outputs
```

## Pinned Memory

Pinned (page-locked) memory enables faster CPU-GPU transfers.

### Using Pinned Memory

```python
import torch
from torch.utils.data import DataLoader, Dataset

class PinnedDataLoader(DataLoader):
    """DataLoader with pinned memory for faster transfer."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.pin_memory = True

# Standard approach
train_loader = DataLoader(
    dataset,
    batch_size=32,
    pin_memory=True,  # Enable pinned memory
    num_workers=4     # Prefetch while GPU processes
)
```

### Manual Pinned Memory Allocation

```python
import torch

# Allocate pinned memory
data = torch.randn(1000, 1000)
pinned_data = data.pin_memory()

# Transfer to GPU is faster
gpu_data = pinned_data.to("cuda")
```

## Asynchronous GPU Operations

### Non-Blocking Transfers

```python
import torch

# Create pinned tensor
data = torch.randn(1000, 1000).pin_memory()

# Non-blocking transfer (returns immediately)
gpu_data = data.to("cuda", non_blocking=True)

# Do CPU work while GPU processes
cpu_result = some_cpu_operation()

# Synchronize if needed
torch.cuda.synchronize()
```

### Asynchronous Copy Pattern

```python
import torch

class AsyncGPUDataLoader:
    def __init__(self, data_loader, device="cuda"):
        self.data_loader = data_loader
        self.device = device
        self.stream = torch.cuda.Stream()
        self.next_batch = None
        self.preload_next()

    def preload_next(self):
        try:
            batch = next(iter(self.data_loader))
            with torch.cuda.stream(self.stream):
                self.next_batch = [
                    b.to(self.device, non_blocking=True) for b in batch
                ]
        except StopIteration:
            self.next_batch = None

    def __iter__(self):
        return self

    def __next__(self):
        torch.cuda.current_stream().wait_stream(self.stream)
        batch = self.next_batch

        if batch is None:
            raise StopIteration

        self.preload_next()
        return batch
```

## Mixed Precision Training and Inference

### Automatic Mixed Precision (AMP)

```python
import torch
from torch.cuda.amp import autocast

# Inference with mixed precision
model.eval()
with autocast():  # Automatically uses FP16 where beneficial
    output = model(input_data)
```

### Manual Float16 Conversion

```python
import torch

# Convert model to FP16
model = model.half()  # Same as .to(torch.float16)

# Inference
input_fp16 = input_data.half()
output = model(input_fp16)

# Results will be FP16
```

### BFloat16 for Better Precision

```python
import torch

# Use BFloat16 for better numerical stability
model = model.to(torch.bfloat16)

with torch.autocast(device_type="cuda", dtype=torch.bfloat16):
    output = model(input_data)
```

## Multi-GPU Inference

### DataParallel (Simple)

```python
import torch

model = torch.load("model.pt")

# Enable multi-GPU
if torch.cuda.device_count() > 1:
    model = torch.nn.DataParallel(model)

model = model.to("cuda")

# Inference (auto-distributed)
output = model(input_data)
```

### DistributedDataParallel (Advanced)

```python
import torch
import torch.distributed as dist

# Initialize process group
dist.init_process_group(backend="nccl")

# Move model to device
device = torch.device(f"cuda:{torch.distributed.get_rank()}")
model = model.to(device)

# Wrap with DDP
model = torch.nn.parallel.DistributedDataParallel(model)

# Inference
output = model(input_data)
```

## Performance Profiling

### NVIDIA-SMI Monitoring

```bash
# Monitor GPU usage in real-time
nvidia-smi

# Watch with refresh
watch -n 1 nvidia-smi

# Log to file
nvidia-smi -lms 100 > gpu_log.csv
```

### PyTorch Profiler with CUDA

```python
import torch
from torch.profiler import profile, record_function, ProfilerActivity

model.eval()

with profile(
    activities=[ProfilerActivity.CPU, ProfilerActivity.CUDA],
    record_shapes=True,
    with_stack=True,
) as prof:
    with torch.no_grad():
        for _ in range(10):
            output = model(input_data)

# Print summary
print(prof.key_averages().table(sort_by="cuda_time_total", row_limit=10))

# Export to trace
prof.export_chrome_trace("trace.json")
```

### Memory Timeline

```python
import torch
from torch.profiler import profile, ProfilerActivity

with profile(
    activities=[ProfilerActivity.CUDA],
    record_shapes=True,
    profile_memory=True,
) as prof:
    output = model(input_data)

# View memory allocation timeline
print(prof.key_averages().table(sort_by="self_cpu_memory_usage"))
```

## Performance Optimization Checklist

### Before Optimization
```python
import torch
import time

# Warmup GPU
for _ in range(10):
    _ = model(dummy_input)

torch.cuda.synchronize()
start = time.perf_counter()

# Benchmark
for _ in range(100):
    _ = model(input_data)

torch.cuda.synchronize()
elapsed = time.perf_counter() - start
baseline_ms = (elapsed / 100) * 1000
print(f"Baseline: {baseline_ms:.2f} ms")
```

### CUDA-Specific Optimizations

1. **Enable CUDA for Linear Layers**
   ```python
   # Automatically uses cuBLAS (fastest)
   linear = torch.nn.Linear(1000, 1000).to("cuda")
   ```

2. **Use Appropriate Data Types**
   ```python
   # FP32 (default) - stability
   # FP16 - speed (needs careful scaling)
   # BF16 - best of both
   model = model.to(torch.bfloat16)
   ```

3. **Batch Size Optimization**
   ```python
   # Larger batches improve GPU utilization
   # But limited by memory - profile to find sweet spot
   for batch_size in [1, 4, 8, 16, 32]:
       output = model(torch.randn(batch_size, 3, 224, 224).cuda())
   ```

4. **CUDA Graph Optimization** (Advanced)
   ```python
   # Capture CUDA operations into graph for replay
   graph = torch.cuda.CUDAGraph()
   with torch.cuda.graph(graph):
       output = model(input_data)

   # Replay graph (much faster for repeated patterns)
   graph.replay()
   ```

## Common CUDA Issues and Solutions

### Out of Memory (OOM)

```python
# Solution 1: Clear cache
torch.cuda.empty_cache()

# Solution 2: Reduce batch size
batch_size = batch_size // 2

# Solution 3: Use gradient checkpointing
from torch.utils.checkpoint import checkpoint
output = checkpoint(model, input_data)

# Solution 4: Use mixed precision
with torch.autocast(device_type="cuda"):
    output = model(input_data)
```

### CUDA Synchronization Issues

```python
# Always synchronize before timing
torch.cuda.synchronize()
start = time.perf_counter()
output = model(input_data)
torch.cuda.synchronize()
elapsed = time.perf_counter() - start
```

### Device Not Available

```python
# Check device availability
device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
print(f"Using device: {device}")

# Specify fallback
try:
    model = model.to("cuda:0")
except:
    print("CUDA not available, using CPU")
    model = model.to("cpu")
```

## Best Practices Summary

1. **Always use `torch.cuda.synchronize()` before timing**
2. **Enable `pin_memory=True` in DataLoader**
3. **Use `torch.no_grad()` for inference**
4. **Clear cache periodically with `torch.cuda.empty_cache()`**
5. **Profile memory before and after optimizations**
6. **Use mixed precision for faster inference**
7. **Batch operations to maximize GPU utilization**
8. **Monitor GPU with `nvidia-smi`**
