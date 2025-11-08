# PyInstaller Spec File Configuration

## Overview

Spec files are Python scripts that configure PyInstaller's build process. They define how dependencies are discovered, bundled, and packaged into executables. For ML applications, proper spec configuration is critical for including all dependencies correctly.

## Spec File Structure

A typical spec file contains four main components:

```python
# 1. Analysis: Analyze Python imports and dependencies
a = Analysis([
    'inference.py',  # Entry point script
    # ... additional modules
],
    pathex=[],  # Additional import paths
    binaries=[],  # Non-Python binary dependencies
    datas=[],  # Non-binary data files
    hiddenimports=[],  # Modules that Analysis cannot detect
)

# 2. PYZ: Create Python bytecode archive
pyz = PYZ(a.pure, a.zipped_data, cipher=None)

# 3. EXE: Create executable
exe = EXE(
    pyz,
    a.scripts,
    a.binaries,
    a.zipfiles,
    a.datas,
    [],
    name='inference',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    upx_exclude=[],
    runtime_tmpdir=None,
    console=True,
    disable_windowed_traceback=False,
)

# 4. COLLECT: Create distribution package (one-folder)
coll = COLLECT(
    exe,
    a.binaries,
    a.zipfiles,
    a.datas,
    strip=False,
    upx=True,
    upx_exclude=[],
    name='inference'
)
```

## Analysis Configuration

### pathex
Additional directories to search for imports:
```python
pathex=[
    '/path/to/venv/lib/python3.11/site-packages',
    '/path/to/models',  # Custom model directory
]
```

### binaries
Non-Python dependencies like CUDA libraries:
```python
binaries=[
    ('/usr/local/cuda/lib64/libcudart.so.12', '.'),
    ('/usr/local/cuda/lib64/libnvrtc.so.12', '.'),
    ('/usr/lib/x86_64-linux-gnu/libcublas.so.12', '.'),
]
```

### datas
Data files and directories to include:
```python
datas=[
    ('/home/user/models/model.pth', 'models'),
    ('/home/user/config', 'config'),
    ('/home/user/weights', 'weights'),
]
```

Format: `(source_path, destination_folder_in_bundle)`

### hiddenimports
Modules that PyInstaller cannot detect automatically:
```python
hiddenimports=[
    'torch',
    'torch.utils.cpp_extension',
    'diffusers',
    'transformers',
]
```

## ML Framework Spec Patterns

### PyTorch Pattern
```python
binaries=[
    # CUDA runtime
    ('/usr/local/cuda/lib64/libcudart.so.12', '.'),
    ('/usr/local/cuda/lib64/libcublas.so.12', '.'),
    ('/usr/local/cuda/lib64/libnvrtc.so.12', '.'),
    ('/usr/local/cuda/lib64/libnvrtc-builtins.so.12', '.'),
    # cuDNN
    ('/usr/lib/x86_64-linux-gnu/libcudnn.so.8', '.'),
]

datas=[
    ('/path/to/model.pth', 'models'),
]

hiddenimports=[
    'torch',
    'torch._C',
    'torch.utils.cpp_extension',
    'torch.distributed',
]
```

### Diffusers Pattern
```python
datas=[
    ('/path/to/stable-diffusion-v1-5', 'models'),
    ('/path/to/controlnet-canny', 'models'),
]

hiddenimports=[
    'diffusers',
    'diffusers.models',
    'diffusers.pipelines',
    'diffusers.schedulers',
    'transformers',
    'transformers.models',
]
```

### Transformers Pattern
```python
datas=[
    ('/path/to/model', 'models'),
]

hiddenimports=[
    'transformers',
    'transformers.models.bert',
    'transformers.models.gpt2',
    'safetensors',
    'huggingface_hub',
]
```

## Optimization Settings

### UPX Compression
Enable UPX compression to reduce binary size:
```python
exe = EXE(
    # ...
    upx=True,
    upx_exclude=['vcruntime140.dll'],  # Windows example
)
```

UPX typically reduces binary size by 20-40%.

### Console vs Windowed
- `console=True`: Show command-line window (for ML backends)
- `console=False`: No console (for GUI applications)

### Strip Symbols
Reduce size by stripping debug symbols:
```python
strip=True,  # Remove debug symbols
```

Reduces binary size by 10-20%.

## Custom Hooks

PyInstaller uses hooks to handle framework-specific import patterns. Create custom hooks for special cases.

### Hook Location
- Custom hooks: `./<project>/_pyinstaller_hooks/`
- Name format: `hook-<package_name>.py`

### Hook Example (Diffusers)
```python
# hook-diffusers.py
from PyInstaller.utils.hooks import collect_submodules

hiddenimports = collect_submodules('diffusers')
```

### Hook for ML Models
```python
# hook-inference.py
datas = [
    ('/path/to/models', 'models'),
    ('/path/to/config.yaml', '.'),
]
```

## Runtime Hooks

Execute Python code during executable startup:

```python
# runtime_hooks=['rthook_cuda.py']
```

Example runtime hook for environment setup:
```python
# rthook_cuda.py
import os
import sys

# Set CUDA environment variables
os.environ['CUDA_VISIBLE_DEVICES'] = '0'
os.environ['TF_FORCE_GPU_MEMORY_GROWTH'] = 'true'
```

## Advanced Patterns

### Multi-Model Bundle
Include multiple models in one package:
```python
datas=[
    ('/path/to/detector', 'models/detector'),
    ('/path/to/segmenter', 'models/segmenter'),
    ('/path/to/classifier', 'models/classifier'),
]
```

### Conditional Imports
Handle optional dependencies:
```python
hiddenimports = []
try:
    import torch
    hiddenimports.append('torch')
except ImportError:
    pass

try:
    import tensorflow
    hiddenimports.extend([
        'tensorflow',
        'tensorflow.keras',
    ])
except ImportError:
    pass
```

### Dynamic Module Discovery
Collect submodules automatically:
```python
from PyInstaller.utils.hooks import collect_submodules

hiddenimports = [
    'torch',
    'diffusers',
] + collect_submodules('transformers')
```

## Spec File Best Practices

1. **Use absolute paths** for all external resources
2. **Test bundle on clean system** without development environment
3. **Document dependencies** in comments
4. **Version spec files** alongside dependency updates
5. **Include all submodules** for ML frameworks
6. **Test on target platform** (Windows, Linux, macOS)
7. **Monitor file sizes** to catch unexpected bloat
8. **Keep separate specs** for different configurations (CPU, GPU, etc.)

## Troubleshooting Spec Issues

### Module Not Found Error
- Add to `hiddenimports` list
- Check import name vs package name (e.g., `PIL` vs `pillow`)
- Verify package is installed in build environment

### Missing Data Files
- Check paths in `datas` parameter
- Ensure destination folder matches runtime expectations
- Use absolute paths only

### CUDA Not Working
- Verify libraries in `binaries` parameter
- Check CUDA version consistency
- Test runtime environment variables

### Bundle Too Large
- Check `datas` parameter for unnecessary files
- Use quantized models
- Enable UPX compression
- Strip debug symbols
