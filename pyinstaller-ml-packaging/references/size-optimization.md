# PyInstaller Bundle Size Optimization

## Overview

ML packages can be large (1-5GB+), making distribution challenging. This guide covers techniques to reduce bundle size while maintaining functionality.

## Bundle Size Analysis

### Typical Component Sizes
```
PyTorch (CPU)           ~800MB
PyTorch (GPU+CUDA)      ~1.2GB
PyTorch (GPU+CUDA+cuDNN) ~1.3GB
Transformers            ~400MB
Diffusers               ~600MB
Models                  ~500MB-2GB each
```

### Identify Large Components
```bash
# List files by size
du -sh ./dist/inference/* | sort -rh | head -20

# Find largest Python packages
find ./dist/inference -name "*.so" -o -name "*.pyd" | xargs du -sh | sort -rh | head -20

# Check individual package sizes
du -sh ./dist/inference/torch*
du -sh ./dist/inference/transformers*
du -sh ./dist/inference/diffusers*
```

## Optimization Techniques

### 1. Selective Module Inclusion

Only include needed framework components in `hiddenimports`:

```python
# Bad: Imports entire ecosystem
hiddenimports = [
    'torch',
    'transformers',
    'diffusers',
    'onnx',
    'tensorflow',  # if not using
    'keras',       # if not using
]

# Good: Only needed components
hiddenimports = [
    'torch',
    'torch.nn',
    'torch.cuda',
    'transformers.pipelines',
    'transformers.models.bert',  # specific model only
]
```

### 2. Strip Debug Symbols

Remove debugging information from binaries:

```python
# In spec file
exe = EXE(
    ...,
    strip=True,  # Remove debug symbols (~10-20% reduction)
)

coll = COLLECT(
    ...,
    strip=True,
)
```

### 3. UPX Compression

Compress executable binary:

```python
exe = EXE(
    ...,
    upx=True,  # Enable UPX compression (~20-40% reduction)
    upx_exclude=['vcruntime140.dll'],  # Exclude incompressible files
)
```

### 4. Exclude Unnecessary Packages

Skip packages not needed at runtime:

```python
# Use build() exclusions in spec
excludedimports = [
    'pytest',
    'unittest',
    'pydoc',
    'distutils',
    'setuptools',
]

a = Analysis(
    ...,
    excludedimports=excludedimports,
)
```

### 5. Model Format Conversion

Convert models to smaller formats:

#### PyTorch to ONNX
```python
import torch
import torch.onnx
import numpy as np

# Load PyTorch model
model = torch.load('model.pth')
model.eval()

# Export to ONNX
dummy_input = torch.randn(1, 3, 224, 224)
torch.onnx.export(
    model,
    dummy_input,
    'model.onnx',
    opset_version=12,
    input_names=['input'],
    output_names=['output'],
    dynamic_axes={'input': {0: 'batch_size'}}
)
```

ONNX benefits:
- 20-30% smaller than PyTorch format
- Framework-agnostic
- Inference optimization support

#### Model Quantization

Reduce precision for smaller models:

```python
import torch

# Load model
model = torch.load('model.pth')

# Quantize to INT8
model_int8 = torch.quantization.quantize_dynamic(
    model,
    {torch.nn.Linear},
    dtype=torch.qint8
)

torch.save(model_int8, 'model_int8.pth')
```

Quantization impact:
- 75% smaller (FP32 to INT8)
- 50% smaller (FP32 to FP16)
- Minor accuracy loss (~1-2%)

#### Model Pruning

Remove unused weights:

```python
import torch.nn.utils.prune as prune

# Prune 50% of weights
for module in model.modules():
    if isinstance(module, torch.nn.Linear):
        prune.l1_unstructured(module, name='weight', amount=0.5)

# Save pruned model
torch.save(model, 'model_pruned.pth')
```

Pruning impact:
- 30-50% smaller
- Can be combined with quantization
- Requires retraining for accuracy

### 6. Lazy Loading

Don't include all models in bundle:

```python
# inference.py - lazy load models at runtime
import os
from pathlib import Path

model_cache = {}

def load_model(model_name):
    if model_name not in model_cache:
        # Load from file or download
        model_path = f'/path/to/models/{model_name}'
        if not Path(model_path).exists():
            # Download from huggingface
            from huggingface_hub import hf_hub_download
            model_path = hf_hub_download('org/model', 'model.pth')
        model = torch.load(model_path)
        model_cache[model_name] = model
    return model_cache[model_name]
```

Benefits:
- Exclude large models from bundle
- Download at first use
- Supports multiple model versions

### 7. Exclude Test Data

Remove test files and examples:

```python
# patterns to exclude when building
excludedimports = [
    'test',
    'tests',
    'testing',
    'example',
    'examples',
    'pytest',
    'unittest',
]
```

Or use datas filter:

```python
# Exclude test directories
import os
datas = []
for root, dirs, files in os.walk('/path/to/packages'):
    # Skip test directories
    dirs[:] = [d for d in dirs if d not in ['test', 'tests', '__pycache__']]
    for file in files:
        if not file.endswith(('.pyc', '.pyo')):
            datas.append((os.path.join(root, file), 'packages'))
```

### 8. One-Folder vs One-File Distribution

#### One-Folder (Recommended)
- Smaller initial bundle
- Faster startup
- Easier updates
- File size: 1.2-1.8GB for full GPU ML

#### One-File
- Simpler distribution
- Slower startup (extraction overhead)
- Larger bundle size
- File size: 1.5-2.2GB for full GPU ML

```python
# One-folder (recommended)
coll = COLLECT(
    exe, a.binaries, a.zipfiles, a.datas,
    strip=False, upx=True,
    name='inference'
)

# One-file (if needed)
exe = EXE(
    pyz, a.scripts, a.binaries, a.zipfiles, a.datas,
    [],
    name='inference',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    upx_exclude=[],
    runtime_tmpdir=None,
    console=True
)
```

## Optimization Workflow

### Step 1: Measure Baseline
```bash
du -sh dist/inference/
du -sh dist/inference/*.so | sort -rh | head -10
```

### Step 2: Apply Selective Imports
- Identify unused modules
- Update `hiddenimports` in spec file
- Rebuild and measure

### Step 3: Strip & Compress
- Enable strip=True
- Enable upx=True
- Rebuild and measure

### Step 4: Quantize Models
- Convert model to INT8 or FP16
- Replace in datas
- Test accuracy
- Rebuild and measure

### Step 5: Validate Performance
- Test inference speed
- Verify accuracy if quantized
- Check memory usage

## Size Optimization Examples

### PyTorch CPU Optimization
```python
# Before: 850MB

hiddenimports = [
    'torch',
    'torch._C',
    'torch.nn',
    'torch.utils.cpp_extension',
]

strip = True
upx = True

# After: 520MB (38% reduction)
```

### Diffusers Optimization
```python
# Before: 2.8GB (with model)

# Quantize model
model_fp16 = model.to(torch.float16)
torch.save(model_fp16, 'model_fp16.pth')

# Exclude unused schedulers
hiddenimports = [
    'diffusers.pipelines.stable_diffusion',
    'diffusers.schedulers.scheduling_ddim',  # only DDIM
    # exclude: pndm, euler, dpm_solver, etc
]

# Results
strip = True
upx = True

# After: 1.5GB (46% reduction)
```

### Multi-Model Optimization
```python
# Before: 3.5GB

# Use ONNX format (30% smaller)
# Quantize all models to INT8 (75% smaller on weights)
# Lazy load secondary models
# Strip debug symbols

# After: 1.2GB (65% reduction)
```

## Performance Impact

| Optimization | Size Reduction | Performance Impact | Risk |
|--------------|----------------|-------------------|------|
| Strip symbols | 10-20% | None | Low |
| UPX compress | 20-40% | 1-5% slower startup | Low |
| Exclude modules | 5-20% | None if correct | Medium |
| Quantize model | 50-75% | 1-5% accuracy loss | Medium |
| ONNX conversion | 20-30% | ~5% slower inference | Medium |
| Model pruning | 30-50% | 1-10% accuracy loss | High |

## Distribution Size Target

```
Minimal ML (no GPU):     300-500MB
Standard GPU ML:        1.2-1.5GB
Full ML Stack:          1.8-2.5GB
With Multiple Models:   2.5-4.0GB
```

## Compression for Distribution

After optimization, further compress for distribution:

```bash
# Create distribution archive
tar czf inference-1.0-linux-x64.tar.gz dist/inference/
zip -r inference-1.0-windows-x64.zip dist/inference/

# Typical compression: 30-50% additional
```

## Monitoring Size During Development

```python
# track_size.py
import os
from pathlib import Path
import json

def get_bundle_stats(bundle_path):
    total_size = 0
    file_count = 0

    for path in Path(bundle_path).rglob('*'):
        if path.is_file():
            total_size += path.stat().st_size
            file_count += 1

    return {
        'total_mb': round(total_size / (1024*1024), 1),
        'file_count': file_count,
    }

# Compare builds
baseline = get_bundle_stats('dist-baseline/inference')
optimized = get_bundle_stats('dist-optimized/inference')

reduction = ((baseline['total_mb'] - optimized['total_mb']) / baseline['total_mb'] * 100)
print(f"Optimization: {reduction:.1f}% reduction")
```

## Best Practices

1. **Measure before and after** each optimization
2. **Test accuracy and performance** after quantization
3. **Use one-folder distribution** for smaller size
4. **Strip symbols in production** (keep dev builds with symbols)
5. **Lazy load large models** not needed immediately
6. **Monitor startup time** with compression enabled
7. **Document size targets** and optimization decisions
8. **Create automated size reports** for CI/CD
