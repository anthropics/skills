# PyTorch Memory Management Guide

## Memory Profiling Basics

### Tracking Memory Usage

```python
import torch

# Get allocated memory
allocated_gb = torch.cuda.memory_allocated() / 1e9
print(f"Allocated: {allocated_gb:.2f} GB")

# Get reserved memory (pre-allocated by caching allocator)
reserved_gb = torch.cuda.memory_reserved() / 1e9
print(f"Reserved: {reserved_gb:.2f} GB")

# Get peak memory during execution
torch.cuda.reset_peak_memory_stats()
output = model(input_data)
peak_gb = torch.cuda.max_memory_allocated() / 1e9
print(f"Peak: {peak_gb:.2f} GB")
```

### Memory Usage Helper

```python
import torch

class MemoryTracker:
    def __init__(self):
        self.start_memory = 0

    def reset(self):
        torch.cuda.reset_peak_memory_stats()
        torch.cuda.empty_cache()
        self.start_memory = torch.cuda.memory_allocated()

    def get_allocated(self):
        """Get currently allocated memory in GB."""
        current = torch.cuda.memory_allocated()
        return (current - self.start_memory) / 1e9

    def get_peak(self):
        """Get peak memory used in GB."""
        peak = torch.cuda.max_memory_allocated()
        return (peak - self.start_memory) / 1e9

    def print_stats(self, label=""):
        allocated = self.get_allocated()
        peak = self.get_peak()
        print(f"{label} - Allocated: {allocated:.2f} GB, Peak: {peak:.2f} GB")

# Usage
tracker = MemoryTracker()
tracker.reset()
output = model(input_data)
tracker.print_stats("Model inference")
```

## Gradient Tracking and torch.no_grad()

### Using torch.no_grad()

Disables gradient computation for inference:

```python
import torch

model.eval()

# Without no_grad (uses extra memory for gradient tracking)
output = model(input_data)  # ~2x memory for gradients

# With no_grad (inference only)
with torch.no_grad():
    output = model(input_data)  # ~1x memory (no gradients)
```

### Using torch.inference_mode()

Even more optimized than `torch.no_grad()`:

```python
import torch

model.eval()

# inference_mode is stricter - no views/operations allowed
with torch.inference_mode():
    output = model(input_data)  # Fastest, minimal memory overhead
```

### Memory Impact Comparison

```python
import torch

model = torch.nn.Linear(10000, 10000).cuda()
input_data = torch.randn(100, 10000).cuda()

torch.cuda.reset_peak_memory_stats()
output = model(input_data)
standard_peak = torch.cuda.max_memory_allocated() / 1e9

torch.cuda.reset_peak_memory_stats()
with torch.no_grad():
    output = model(input_data)
no_grad_peak = torch.cuda.max_memory_allocated() / 1e9

torch.cuda.reset_peak_memory_stats()
with torch.inference_mode():
    output = model(input_data)
inference_peak = torch.cuda.max_memory_allocated() / 1e9

print(f"Standard: {standard_peak:.2f} GB")
print(f"no_grad: {no_grad_peak:.2f} GB (saves {(standard_peak-no_grad_peak)/standard_peak*100:.1f}%)")
print(f"inference_mode: {inference_peak:.2f} GB (saves {(standard_peak-inference_peak)/standard_peak*100:.1f}%)")
```

## Cache Management

### Clearing CUDA Cache

```python
import torch

# Check cache before
print(f"Before: {torch.cuda.memory_allocated() / 1e9:.2f} GB")

# Clear unused memory
torch.cuda.empty_cache()

# Check cache after
print(f"After: {torch.cuda.memory_allocated() / 1e9:.2f} GB")
```

### Automatic Cache Clearing

```python
import torch
import gc

def inference_with_cache_management(model, data_loader):
    """Perform inference with automatic cache clearing."""

    model.eval()

    for batch_idx, (data, target) in enumerate(data_loader):
        with torch.no_grad():
            output = model(data.cuda())

        # Clear GPU cache periodically
        if batch_idx % 10 == 0:
            torch.cuda.empty_cache()

        # Clear CPU cache
        gc.collect()

    # Final cleanup
    torch.cuda.empty_cache()
    gc.collect()
```

### Cache Memory Control

```python
import torch

# Set maximum memory fraction for caching
torch.cuda.set_per_process_memory_fraction(0.9)

# Empty cache but keep one block
torch.cuda.empty_cache()

# Reset to defaults
torch.cuda.reset_peak_memory_stats()
```

## Gradient Checkpointing

Gradient checkpointing trades computation for memory during backward pass.

### Basic Gradient Checkpointing

```python
import torch
from torch.utils.checkpoint import checkpoint

class ModelWithCheckpoint(torch.nn.Module):
    def __init__(self):
        super().__init__()
        self.layer1 = torch.nn.Linear(1000, 1000)
        self.layer2 = torch.nn.Linear(1000, 1000)
        self.layer3 = torch.nn.Linear(1000, 1000)

    def forward(self, x):
        # Without checkpoint: saves all activations (~3x memory)
        # x = self.layer1(x)
        # x = self.layer2(x)
        # x = self.layer3(x)

        # With checkpoint: saves only layer inputs (~1x memory)
        x = checkpoint(self.layer1, x, use_reentrant=False)
        x = checkpoint(self.layer2, x, use_reentrant=False)
        x = checkpoint(self.layer3, x, use_reentrant=False)
        return x
```

### Checkpoint Configuration

```python
from torch.utils.checkpoint import checkpoint

# Modern reentrant=False (recommended)
output = checkpoint(model, x, use_reentrant=False)

# Legacy reentrant=True (less memory efficient)
output = checkpoint(model, x, use_reentrant=True)
```

### Memory Savings Example

```python
import torch
from torch.utils.checkpoint import checkpoint

model = torch.nn.Sequential(
    torch.nn.Linear(1000, 1000),
    torch.nn.ReLU(),
    torch.nn.Linear(1000, 1000),
    torch.nn.ReLU(),
    torch.nn.Linear(1000, 1000),
).cuda()

input_data = torch.randn(64, 1000, requires_grad=True).cuda()

# Forward without checkpoint
torch.cuda.reset_peak_memory_stats()
output = model(input_data)
memory_no_checkpoint = torch.cuda.max_memory_allocated() / 1e9

# Forward with checkpoint
torch.cuda.reset_peak_memory_stats()

def forward_with_checkpoint(x):
    x = checkpoint(model[0], x, use_reentrant=False)
    x = checkpoint(model[1], x, use_reentrant=False)
    x = checkpoint(model[2], x, use_reentrant=False)
    x = checkpoint(model[3], x, use_reentrant=False)
    x = checkpoint(model[4], x, use_reentrant=False)
    return x

output = forward_with_checkpoint(input_data)
memory_with_checkpoint = torch.cuda.max_memory_allocated() / 1e9

print(f"Without checkpoint: {memory_no_checkpoint:.2f} GB")
print(f"With checkpoint: {memory_with_checkpoint:.2f} GB")
print(f"Memory saved: {(1 - memory_with_checkpoint/memory_no_checkpoint)*100:.1f}%")
```

## Model-Specific Memory Optimization

### Batch Normalization in Inference

```python
import torch

model = torch.nn.Sequential(
    torch.nn.Linear(1000, 1000),
    torch.nn.BatchNorm1d(1000),
    torch.nn.ReLU(),
)

# Set to eval mode (uses running stats, not batch stats)
model.eval()

# This uses less memory than train mode
with torch.no_grad():
    output = model(input_data)
```

### Dropout in Inference

```python
import torch

model = torch.nn.Sequential(
    torch.nn.Linear(1000, 1000),
    torch.nn.Dropout(0.5),
    torch.nn.ReLU(),
)

# Set to eval mode (dropout disabled)
model.eval()

with torch.no_grad():
    output = model(input_data)
```

### Layer Normalization

```python
import torch

# LayerNorm typically more memory efficient than BatchNorm
model = torch.nn.Sequential(
    torch.nn.Linear(1000, 1000),
    torch.nn.LayerNorm(1000),
    torch.nn.ReLU(),
)

model.eval()

with torch.no_grad():
    output = model(input_data)
```

## Model Pruning for Memory

### Weight Pruning

```python
import torch
import torch.nn.utils.prune as prune

# Apply structured pruning
model = torch.nn.Linear(1000, 1000)
prune.ln_structured(model, name="weight", amount=0.3, n=2, dim=0)

# Make pruning permanent
prune.remove(model, "weight")

# Check sparsity
print(f"Sparse parameters: {torch.sum(model.weight == 0)}")
```

## Memory Efficient DataLoading

### Pinned Memory DataLoader

```python
from torch.utils.data import DataLoader, TensorDataset

dataset = TensorDataset(input_data, target_data)

# Pin memory for faster CPU-GPU transfer
data_loader = DataLoader(
    dataset,
    batch_size=32,
    pin_memory=True,  # Important
    num_workers=4
)
```

### Lazy Loading Strategy

```python
import torch
from torch.utils.data import Dataset, DataLoader

class LazyDataset(Dataset):
    """Dataset that loads data on-demand."""

    def __init__(self, data_files):
        self.data_files = data_files

    def __len__(self):
        return len(self.data_files)

    def __getitem__(self, idx):
        # Load only when accessed
        data = torch.load(self.data_files[idx])
        return data

# Use with DataLoader
dataset = LazyDataset(file_list)
loader = DataLoader(dataset, batch_size=8, num_workers=4)
```

## Memory Profiling Tools

### PyTorch Memory Profiler

```python
import torch
from torch.profiler import profile, ProfilerActivity

with profile(
    activities=[ProfilerActivity.CPU, ProfilerActivity.CUDA],
    profile_memory=True,
    record_shapes=True,
) as prof:
    output = model(input_data)

# Print memory-intensive operations
print(prof.key_averages().table(
    sort_by="self_cpu_memory_usage",
    row_limit=10
))
```

### Custom Memory Monitoring

```python
import torch
import time

class MemoryMonitor:
    def __init__(self, interval=1.0):
        self.interval = interval
        self.running = False

    def start(self):
        self.running = True
        self.peak_memory = 0
        while self.running:
            current = torch.cuda.memory_allocated() / 1e9
            self.peak_memory = max(self.peak_memory, current)
            time.sleep(self.interval)

    def stop(self):
        self.running = False
        return self.peak_memory

# Usage
import threading

monitor = MemoryMonitor()
thread = threading.Thread(target=monitor.start, daemon=True)
thread.start()

# Run model
output = model(input_data)

peak = monitor.stop()
print(f"Peak memory: {peak:.2f} GB")
```

## Best Practices Summary

1. **Always use `torch.inference_mode()` for inference** - maximum memory efficiency
2. **Use `torch.no_grad()` if gradients not needed** - prevents gradient tracking
3. **Clear cache periodically** - `torch.cuda.empty_cache()` in loops
4. **Use gradient checkpointing** - trades computation for memory during training
5. **Set model to `.eval()` mode** - disables dropout and batch norm optimizations
6. **Enable `pin_memory=True`** - in DataLoader for faster transfers
7. **Profile before and after** - always measure memory impact
8. **Use lower precision** - FP16/BF16 for 2x memory savings
9. **Monitor with nvidia-smi** - track GPU memory in real-time
10. **Batch operations together** - reduces memory allocation overhead
