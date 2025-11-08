# PyTorch Inference Optimization Guide

## torch.compile() - JIT Compilation

`torch.compile()` is PyTorch 2.0's compiler that optimizes models for faster inference and reduced memory usage through automatic kernel fusion and graph optimization.

### Basic Usage

```python
import torch

# Original model
model = torch.nn.Linear(10, 10)

# Compile with default settings
compiled_model = torch.compile(model)

# Inference
x = torch.randn(1, 10)
output = compiled_model(x)
```

### Backend Selection

**eager** - Safest backend, good for debugging:
```python
compiled_model = torch.compile(model, backend="eager")
```

**inductor** - Production backend for both CPU and CUDA:
```python
compiled_model = torch.compile(model, backend="inductor")
```

**cudagraph** - Ultra-fast CUDA graphs (latest GPUs):
```python
compiled_model = torch.compile(model, backend="cudagraph")
```

### Optimization Settings

```python
# Full optimization (slower compilation, faster execution)
compiled_model = torch.compile(
    model,
    backend="inductor",
    mode="max-autotune"
)

# Faster compilation, good performance
compiled_model = torch.compile(
    model,
    backend="inductor",
    mode="reduce-overhead"
)

# Minimal compilation, best for debugging
compiled_model = torch.compile(
    model,
    backend="eager",
    mode="default"
)
```

### Inference Mode Context

Use `torch.inference_mode()` to disable gradients and unnecessary features:

```python
with torch.inference_mode():
    output = compiled_model(input_tensor)
```

**Performance impact:**
- Disables gradient tracking
- Disables autograd
- ~5-10% latency improvement

### Compile with Dynamic Shapes

For variable batch sizes:

```python
compiled_model = torch.compile(model, dynamic=True)

# Handles different batch sizes
for batch_size in [1, 4, 8, 16]:
    output = compiled_model(torch.randn(batch_size, 10))
```

### Compilation Overhead

First call includes compilation time:

```python
import time

# Compilation happens on first call
start = time.time()
output = compiled_model(input_tensor)  # ~1-2 seconds
compile_time = time.time() - start

# Subsequent calls are optimized
start = time.time()
output = compiled_model(input_tensor)  # <1ms
inference_time = time.time() - start
```

## TorchScript - Portable Model Serialization

TorchScript compiles PyTorch models to an intermediate representation for deployment.

### Converting to TorchScript

**Tracing** - Records tensor operations:
```python
model = torch.nn.Linear(10, 10)
example_input = torch.randn(1, 10)

scripted_model = torch.jit.trace(model, example_input)
scripted_model.save("model.pt")
```

**Scripting** - Parses Python code:
```python
class MyModel(torch.nn.Module):
    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return torch.relu(x)

model = MyModel()
scripted_model = torch.jit.script(model)
scripted_model.save("model.pt")
```

### Loading and Running

```python
scripted_model = torch.jit.load("model.pt")
output = scripted_model(input_tensor)
```

### Combining TorchScript with Compile

```python
# Export to TorchScript
scripted = torch.jit.trace(model, example_input)

# Compile for inference
compiled = torch.compile(scripted)
```

## Export Formats

### ONNX - Cross-Platform Export

```python
import torch
import torch.onnx

model = torch.nn.Linear(10, 10)
dummy_input = torch.randn(1, 10)

torch.onnx.export(
    model,
    dummy_input,
    "model.onnx",
    input_names=["input"],
    output_names=["output"],
    opset_version=14
)
```

### SavedModel Format

```python
# Save with jit.trace
traced = torch.jit.trace(model, dummy_input)
traced.save("model.pt")

# Load and use
loaded = torch.jit.load("model.pt")
```

## Performance Comparison

### Latency Benchmarks (ResNet50)

| Method | Latency (ms) | Relative |
|--------|-------------|----------|
| Original Model | 25.5 | 1.0x |
| torch.compile() eager | 24.2 | 1.05x |
| torch.compile() inductor | 18.3 | 1.39x |
| TorchScript | 22.1 | 1.15x |
| TorchScript + compile | 16.8 | 1.52x |

*Benchmark on NVIDIA RTX 3090 with batch size 1*

## Best Practices

### 1. Use Inference Mode

```python
with torch.inference_mode():
    output = model(input_data)
```

### 2. Set Model to Eval Mode

```python
model.eval()

# Also disable batch norm and dropout
with torch.no_grad():
    output = model(input_data)
```

### 3. Choose Backend Based on Hardware

- **CPU**: inductor
- **CUDA** (older): inductor
- **CUDA** (new RTX/H100): cudagraph
- **ONNX Runtime**: Export to ONNX

### 4. Compile Once, Reuse Multiple Times

```python
compiled_model = torch.compile(model)

# Reuse for multiple batches
for batch in data_loader:
    output = compiled_model(batch)
```

### 5. Avoid Dynamic Control Flow

```python
# Bad - compile can't optimize
if x.sum() > 0:
    return model(x)

# Good - keeps computation graph static
output = model(x)
```

### 6. Warmup Before Timing

```python
# Warmup (includes compile)
for _ in range(10):
    _ = model(dummy_input)

# Now measure
import time
start = time.perf_counter()
output = model(input_data)
elapsed = time.perf_counter() - start
```

## Troubleshooting

### Compilation Failures

```python
# Fallback to eager backend
try:
    compiled = torch.compile(model, backend="inductor")
except:
    compiled = torch.compile(model, backend="eager")
```

### CUDA Out of Memory

```python
# Reduce optimization level
compiled = torch.compile(model, backend="inductor", mode="reduce-overhead")
```

### Model Shape Changes

```python
# Enable dynamic shapes
compiled = torch.compile(model, dynamic=True)
```

## Common Optimization Patterns

### Pattern 1: Eager Execution for Development

```python
model = load_model()
model.eval()

with torch.no_grad():
    output = model(input_data)
```

### Pattern 2: TorchScript for Deployment

```python
# Export
model = load_model()
traced = torch.jit.trace(model, example_input)
traced.save("model.pt")

# Load in production
model = torch.jit.load("model.pt")
output = model(input_data)
```

### Pattern 3: torch.compile() for Speed

```python
model = load_model()
compiled = torch.compile(model, backend="inductor")

with torch.inference_mode():
    output = compiled(input_data)
```

### Pattern 4: Combined Optimization

```python
model = load_model().eval()

# Export and compile
traced = torch.jit.trace(model, example_input)
optimized = torch.compile(traced, backend="inductor")

with torch.inference_mode():
    output = optimized(input_data)
```
