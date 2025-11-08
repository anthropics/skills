# PyInstaller CUDA Library Bundling

## Overview

CUDA libraries are C++ binaries that PyInstaller cannot automatically detect. GPU-accelerated ML applications require explicit CUDA library inclusion in the spec file. This guide covers bundling strategies for different CUDA versions and platforms.

## CUDA Architecture Overview

CUDA consists of:
- **CUDA Toolkit**: Developer tools and libraries (installed separately)
- **CUDA Runtime**: Libraries needed to run CUDA-compiled code
- **cuDNN**: Optimized neural network library
- **NCCL**: Multi-GPU communication library

## Finding CUDA Libraries

### Linux - Find Installation
```bash
# Check CUDA installation
ls /usr/local/cuda/lib64/ | grep cuda

# Common library versions
ls /usr/local/cuda/lib64/libcudart.so*
ls /usr/local/cuda/lib64/libcublas.so*
ls /usr/local/cuda/lib64/libnvrtc.so*
```

### CUDA Versions to Library Mapping

| CUDA Version | libcudart Version | libcublas Version | libnvrtc Version |
|--------------|-------------------|-------------------|------------------|
| 11.8 | 11.8 | 11 | 11.8 |
| 12.0 | 12.0 | 12 | 12.0 |
| 12.1 | 12.1 | 12 | 12.1 |
| 12.4 | 12.4 | 12 | 12.4 |

### Check System CUDA Version
```bash
# Check installed CUDA version
nvcc --version

# Check driver version
nvidia-smi
```

## Core CUDA Runtime Libraries

### Minimal GPU Support
```python
binaries = [
    # Essential CUDA runtime
    ('/usr/local/cuda-12.4/lib64/libcudart.so.12', '.'),
    ('/usr/local/cuda-12.4/lib64/libcudart.so.12.0', '.'),
]
```

### Standard GPU Support (PyTorch)
```python
binaries = [
    # CUDA Runtime
    ('/usr/local/cuda-12.4/lib64/libcudart.so.12', '.'),

    # CUBLAS - matrix operations
    ('/usr/local/cuda-12.4/lib64/libcublas.so.12', '.'),
    ('/usr/local/cuda-12.4/lib64/libcublasLt.so.12', '.'),

    # NVRTC - runtime compilation
    ('/usr/local/cuda-12.4/lib64/libnvrtc.so.12.4', '.'),
    ('/usr/local/cuda-12.4/lib64/libnvrtc-builtins.so.12.4', '.'),

    # CuDNN (if installed)
    ('/usr/lib/x86_64-linux-gnu/libcudnn.so.8', '.'),
]
```

### Full GPU Support (Advanced)
```python
binaries = [
    # Runtime core
    ('/usr/local/cuda-12.4/lib64/libcudart.so.12', '.'),

    # Linear algebra
    ('/usr/local/cuda-12.4/lib64/libcublas.so.12', '.'),
    ('/usr/local/cuda-12.4/lib64/libcublasLt.so.12', '.'),

    # Optimization
    ('/usr/local/cuda-12.4/lib64/libcusolver.so.11', '.'),
    ('/usr/local/cuda-12.4/lib64/libcusparse.so.12', '.'),

    # Data transfer
    ('/usr/local/cuda-12.4/lib64/libcudnn.so.8', '.'),

    # Runtime compilation
    ('/usr/local/cuda-12.4/lib64/libnvrtc.so.12.4', '.'),
    ('/usr/local/cuda-12.4/lib64/libnvrtc-builtins.so.12.4', '.'),

    # FFT operations
    ('/usr/local/cuda-12.4/lib64/libcufft.so.11', '.'),

    # Random number generation
    ('/usr/local/cuda-12.4/lib64/libcurand.so.10', '.'),

    # Multi-GPU communication
    ('/usr/local/cuda-12.4/lib64/libnccl.so.2', '.'),
]
```

## Library Dependencies

Some CUDA libraries depend on others. Common dependency chains:

```
libcublas.so → libcudart.so
libcusolver.so → libcublas.so, libcudart.so
libcufft.so → libcudart.so
libcurand.so → libcudart.so
libnccl.so → libcudart.so
libcudnn.so → libcublas.so, libcudart.so
```

Always include base libraries:
- libcudart.so (always required)
- libcublas.so (nearly always required)

## PyTorch Specific CUDA Bundling

### PyTorch CPU-Only
```python
binaries = []  # No CUDA libraries needed
```

### PyTorch GPU - Minimal
```python
binaries = [
    ('/usr/local/cuda-12.4/lib64/libcudart.so.12', '.'),
    ('/usr/local/cuda-12.4/lib64/libcublas.so.12', '.'),
    ('/usr/local/cuda-12.4/lib64/libcublasLt.so.12', '.'),
]
```

### PyTorch GPU - Full
```python
import glob
import os

# Discover CUDA path
cuda_home = '/usr/local/cuda-12.4'
cuda_lib_path = f'{cuda_home}/lib64'

# Collect all CUDA libraries automatically
cuda_binaries = []
for lib_file in glob.glob(f'{cuda_lib_path}/lib*.so*'):
    lib_name = os.path.basename(lib_file)
    cuda_binaries.append((lib_file, '.'))

binaries = cuda_binaries
```

## Diffusers Specific CUDA Bundling

Diffusers uses transformers which uses PyTorch, so follow PyTorch CUDA bundling patterns:

```python
binaries = [
    # PyTorch CUDA support
    ('/usr/local/cuda-12.4/lib64/libcudart.so.12', '.'),
    ('/usr/local/cuda-12.4/lib64/libcublas.so.12', '.'),
    ('/usr/local/cuda-12.4/lib64/libcublasLt.so.12', '.'),

    # Optional: CuDNN for optimized operations
    ('/usr/lib/x86_64-linux-gnu/libcudnn.so.8', '.'),
]
```

## CuDNN Integration

CuDNN (CUDA Deep Neural Network library) provides optimized implementations.

### Find CuDNN Installation
```bash
# Typical Linux locations
ls /usr/lib/x86_64-linux-gnu/libcudnn*
ls /usr/local/cuda/lib64/libcudnn*

# CuDNN 8.x library
file /usr/lib/x86_64-linux-gnu/libcudnn.so.8
```

### Include CuDNN
```python
binaries = [
    # ... CUDA libraries ...
    ('/usr/lib/x86_64-linux-gnu/libcudnn.so.8', '.'),
    ('/usr/lib/x86_64-linux-gnu/libcudnn_adv_infer.so.8', '.'),
    ('/usr/lib/x86_64-linux-gnu/libcudnn_adv_train.so.8', '.'),
    ('/usr/lib/x86_64-linux-gnu/libcudnn_ops_infer.so.8', '.'),
    ('/usr/lib/x86_64-linux-gnu/libcudnn_ops_train.so.8', '.'),
]
```

## NCCL (Multi-GPU Communication)

Required for distributed training across multiple GPUs:

```python
binaries = [
    # ... other CUDA libraries ...
    ('/usr/local/cuda-12.4/lib64/libnccl.so.2', '.'),
]
```

## CUDA 12.4 Complete Bundle

```python
binaries = [
    # Runtime
    ('/usr/local/cuda-12.4/lib64/libcudart.so.12', '.'),
    ('/usr/local/cuda-12.4/lib64/libcudart.so.12.0', '.'),

    # Math libraries
    ('/usr/local/cuda-12.4/lib64/libcublas.so.12', '.'),
    ('/usr/local/cuda-12.4/lib64/libcublasLt.so.12', '.'),
    ('/usr/local/cuda-12.4/lib64/libcusolver.so.11', '.'),
    ('/usr/local/cuda-12.4/lib64/libcusparse.so.12', '.'),

    # Compiler/JIT
    ('/usr/local/cuda-12.4/lib64/libnvrtc.so.12.4', '.'),
    ('/usr/local/cuda-12.4/lib64/libnvrtc-builtins.so.12.4', '.'),

    # Other utilities
    ('/usr/local/cuda-12.4/lib64/libcufft.so.11', '.'),
    ('/usr/local/cuda-12.4/lib64/libcurand.so.10', '.'),
    ('/usr/local/cuda-12.4/lib64/libnccl.so.2', '.'),

    # CuDNN
    ('/usr/lib/x86_64-linux-gnu/libcudnn.so.8', '.'),
]
```

## CUDA 11.8 Bundle

```python
binaries = [
    ('/usr/local/cuda-11.8/lib64/libcudart.so.11.0', '.'),
    ('/usr/local/cuda-11.8/lib64/libcublas.so.11', '.'),
    ('/usr/local/cuda-11.8/lib64/libcublasLt.so.11', '.'),
    ('/usr/local/cuda-11.8/lib64/libcusolver.so.11', '.'),
    ('/usr/local/cuda-11.8/lib64/libcusparse.so.11', '.'),
    ('/usr/local/cuda-11.8/lib64/libnvrtc.so.11.8', '.'),
    ('/usr/local/cuda-11.8/lib64/libnvrtc-builtins.so.11.8', '.'),
    ('/usr/local/cuda-11.8/lib64/libcufft.so.10', '.'),
    ('/usr/local/cuda-11.8/lib64/libcurand.so.10', '.'),
    ('/usr/local/cuda-11.8/lib64/libnccl.so.2', '.'),
]
```

## Windows CUDA Bundling

### Find CUDA DLLs
```
C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v12.4\bin\
```

### Windows Binaries
```python
binaries = [
    ('C:\\Program Files\\NVIDIA GPU Computing Toolkit\\CUDA\\v12.4\\bin\\cudart64_12.dll', '.'),
    ('C:\\Program Files\\NVIDIA GPU Computing Toolkit\\CUDA\\v12.4\\bin\\cublas64_12.dll', '.'),
    ('C:\\Program Files\\NVIDIA GPU Computing Toolkit\\CUDA\\v12.4\\bin\\cublasLt64_12.dll', '.'),
    ('C:\\Program Files\\NVIDIA GPU Computing Toolkit\\CUDA\\v12.4\\bin\\nvrtc64_121_0.dll', '.'),
    ('C:\\Program Files\\NVIDIA GPU Computing Toolkit\\CUDA\\v12.4\\bin\\nvrtc-builtins64_121.dll', '.'),
]
```

## macOS CUDA Bundling

Apple Silicon (M1/M2/M3) uses Metal Performance Shaders - no CUDA support.

For Intel Macs (older):
```python
binaries = [
    ('/usr/local/cuda-12.4/lib/libcudart.dylib', '.'),
    ('/usr/local/cuda-12.4/lib/libcublas.dylib', '.'),
]
```

## Verification

### Test CUDA Availability in Package
```python
# test_cuda.py
import sys
import torch

if torch.cuda.is_available():
    print(f"CUDA available: {torch.cuda.get_device_name(0)}")
    print(f"CUDA version: {torch.version.cuda}")
else:
    print("CUDA not available!")
    sys.exit(1)
```

Run in packaged executable:
```bash
./inference/inference test_cuda.py
```

### Monitor Library Loading
```bash
# Linux: Check which libraries are loaded
ldd ./inference/inference | grep cuda

# strace to debug library issues
strace -e open,openat ./inference/inference 2>&1 | grep cuda
```

## Troubleshooting CUDA Issues

| Error | Cause | Solution |
|-------|-------|----------|
| libcudart.so.12: cannot open shared object | Library missing | Add to binaries, check path |
| CUDA_ERROR_NO_DEVICE | GPU driver not installed | Install NVIDIA driver |
| CUDA out of memory | Model too large | Reduce batch size or use quantization |
| Version mismatch | CUDA version incompatible | Rebuild with matching CUDA version |

## Size Impact

- Minimal CUDA (2 libraries): ~50MB
- Standard PyTorch GPU: ~150-200MB
- Full GPU support: ~300-400MB
- With CuDNN: +50-100MB

## Best Practices

1. **Match CUDA version** to build and runtime environment
2. **Include only necessary libraries** to minimize bundle size
3. **Test on target GPU hardware** before deployment
4. **Document CUDA version requirements** for users
5. **Use absolute paths** in spec file
6. **Create separate builds** for different CUDA versions if needed
7. **Monitor GPU memory** during execution in packaged binary
