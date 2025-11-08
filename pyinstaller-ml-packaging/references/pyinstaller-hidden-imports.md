# PyInstaller Hidden Imports for ML Libraries

## Overview

Hidden imports are modules that PyInstaller's static analysis cannot detect automatically. They're commonly needed for ML frameworks that use dynamic imports, namespace packages, or lazy loading patterns.

## PyTorch

PyTorch uses C++ extensions and dynamic imports that require explicit hidden imports.

### Core PyTorch Imports
```python
hiddenimports = [
    'torch',
    'torch._C',
    'torch.utils.cpp_extension',
    'torch.utils.data',
    'torch.nn',
    'torch.optim',
    'torch.nn.functional',
]
```

### CUDA Support
```python
hiddenimports = [
    'torch.cuda',
    'torch.cuda.random',
    'torch.cuda.nccl',
    'torch.cuda.comm',
    'torch.cuda.comm.reduce',
]
```

### Distributed Training (if needed)
```python
hiddenimports = [
    'torch.distributed',
    'torch.distributed.algorithms',
    'torch.distributed.rpc',
]
```

### Complete PyTorch Hidden Imports
```python
PYTORCH_HIDDEN_IMPORTS = [
    'torch',
    'torch._C',
    'torch._functorch',
    'torch._inductor',
    'torch.utils.cpp_extension',
    'torch.utils.data',
    'torch.utils.checkpoint',
    'torch.nn',
    'torch.nn.functional',
    'torch.optim',
    'torch.optim.lr_scheduler',
    'torch.cuda',
    'torch.cuda.random',
    'torch.cuda.nccl',
    'torch.backends.cudnn',
    'torch.profiler',
    'torch.jit',
    'torch.onnx',
]
```

## Transformers (HuggingFace)

Transformers uses dynamic model loading and lazy imports.

### Base Transformers
```python
hiddenimports = [
    'transformers',
    'transformers.models',
    'transformers.utils',
    'transformers.tokenization_utils',
    'transformers.feature_extraction_utils',
    'transformers.processing_utils',
]
```

### Common Model Types
```python
hiddenimports = [
    'transformers.models.bert',
    'transformers.models.gpt2',
    'transformers.models.t5',
    'transformers.models.vision_transformer',
    'transformers.models.resnet',
]
```

### Supporting Libraries
```python
hiddenimports = [
    'huggingface_hub',
    'safetensors',
    'tokenizers',
]
```

### Complete Transformers Hidden Imports
```python
TRANSFORMERS_HIDDEN_IMPORTS = [
    'transformers',
    'transformers.models',
    'transformers.models.bert',
    'transformers.models.gpt2',
    'transformers.models.t5',
    'transformers.models.vision_transformer',
    'transformers.models.resnet',
    'transformers.models.efficientnet',
    'transformers.utils',
    'transformers.utils.generic',
    'transformers.tokenization_utils',
    'transformers.tokenization_utils_base',
    'transformers.feature_extraction_utils',
    'transformers.processing_utils',
    'transformers.image_processing_utils',
    'huggingface_hub',
    'huggingface_hub.file_download',
    'safetensors',
    'safetensors.torch',
    'tokenizers',
]
```

## Diffusers

Diffusers provides pipeline abstractions with multiple model types.

### Core Diffusers
```python
hiddenimports = [
    'diffusers',
    'diffusers.models',
    'diffusers.pipelines',
    'diffusers.schedulers',
    'diffusers.loaders',
]
```

### Model Components
```python
hiddenimports = [
    'diffusers.models.unet_2d_condition',
    'diffusers.models.vae',
    'diffusers.models.autoencoder_kl',
    'diffusers.models.autoencoder_tiny',
    'diffusers.models.cross_attention',
]
```

### Scheduler Types
```python
hiddenimports = [
    'diffusers.schedulers.scheduling_ddim',
    'diffusers.schedulers.scheduling_pndm',
    'diffusers.schedulers.scheduling_euler_ancestral_discrete',
    'diffusers.schedulers.scheduling_dpm_solver_multistep',
    'diffusers.schedulers.scheduling_lcm',
]
```

### Pipeline Types
```python
hiddenimports = [
    'diffusers.pipelines.stable_diffusion',
    'diffusers.pipelines.stable_diffusion_xl',
    'diffusers.pipelines.controlnet',
    'diffusers.pipelines.text_to_video',
]
```

### Complete Diffusers Hidden Imports
```python
DIFFUSERS_HIDDEN_IMPORTS = [
    'diffusers',
    'diffusers.models',
    'diffusers.models.unet_2d_condition',
    'diffusers.models.vae',
    'diffusers.models.autoencoder_kl',
    'diffusers.models.autoencoder_tiny',
    'diffusers.models.cross_attention',
    'diffusers.pipelines',
    'diffusers.pipelines.stable_diffusion',
    'diffusers.pipelines.stable_diffusion_xl',
    'diffusers.pipelines.controlnet',
    'diffusers.pipelines.text_to_video',
    'diffusers.pipelines.pipeline_utils',
    'diffusers.schedulers',
    'diffusers.schedulers.scheduling_ddim',
    'diffusers.schedulers.scheduling_pndm',
    'diffusers.schedulers.scheduling_euler_ancestral_discrete',
    'diffusers.schedulers.scheduling_dpm_solver_multistep',
    'diffusers.schedulers.scheduling_lcm',
    'diffusers.loaders',
    'diffusers.utils',
    'diffusers.utils.torch_utils',
    'diffusers.utils.pil_utils',
]
```

## ONNX (Open Neural Network Exchange)

ONNX for model optimization and cross-framework compatibility.

```python
hiddenimports = [
    'onnx',
    'onnx.onnx_pb',
    'onnxruntime',
    'onnxruntime.transformers',
    'onnxruntime.quantization',
]
```

## OpenVINO (Intel Optimization)

Intel's optimization toolkit for inference.

```python
hiddenimports = [
    'openvino',
    'openvino.runtime',
    'openvino.tools',
    'openvino.tools.mo',
]
```

## Common Supporting Libraries

### Image Processing
```python
hiddenimports = [
    'PIL',
    'PIL.Image',
    'PIL.ImageOps',
    'cv2',
    'skimage',
    'skimage.transform',
]
```

### Scientific Computing
```python
hiddenimports = [
    'numpy',
    'scipy',
    'scipy.signal',
    'scipy.special',
    'scipy.optimize',
]
```

### Data Handling
```python
hiddenimports = [
    'pandas',
    'h5py',
    'zarr',
]
```

### Serialization
```python
hiddenimports = [
    'yaml',
    'json',
    'pickle',
    'msgpack',
]
```

## Framework Detection Pattern

```python
# Automatic framework detection
hiddenimports = []

try:
    import torch
    hiddenimports.extend([
        'torch',
        'torch._C',
        'torch.utils.cpp_extension',
        'torch.cuda',
    ])
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

try:
    import transformers
    hiddenimports.extend([
        'transformers',
        'transformers.models',
        'huggingface_hub',
    ])
except ImportError:
    pass

try:
    import diffusers
    hiddenimports.extend([
        'diffusers',
        'diffusers.pipelines',
        'diffusers.models',
    ])
except ImportError:
    pass
```

## Dynamic Module Collection

Use PyInstaller's utility functions to collect submodules:

```python
from PyInstaller.utils.hooks import (
    collect_submodules,
    collect_data_files,
)

# Collect all transformers submodules
hiddenimports = collect_submodules('transformers')

# Collect all diffusers submodules
hiddenimports += collect_submodules('diffusers')

# Collect PyTorch submodules
hiddenimports += collect_submodules('torch')
```

## ML-Complete Hidden Imports Reference

Complete hidden imports for full ML stack:

```python
ML_STACK_HIDDEN_IMPORTS = [
    # PyTorch Core
    'torch',
    'torch._C',
    'torch.utils.cpp_extension',
    'torch.cuda',
    'torch.backends.cudnn',
    'torch.nn',
    'torch.optim',

    # Transformers
    'transformers',
    'transformers.models',
    'transformers.models.bert',
    'transformers.models.gpt2',
    'transformers.models.t5',
    'huggingface_hub',
    'safetensors',
    'tokenizers',

    # Diffusers
    'diffusers',
    'diffusers.models',
    'diffusers.pipelines',
    'diffusers.schedulers',

    # ONNX
    'onnxruntime',

    # Image Processing
    'PIL',
    'PIL.Image',
    'cv2',

    # Scientific
    'numpy',
    'scipy',

    # Other
    'yaml',
    'h5py',
]
```

## Testing Hidden Imports

Verify imports work after packaging:

```python
# test_imports.py
import sys
import importlib

modules_to_test = [
    'torch',
    'transformers',
    'diffusers',
    'PIL',
]

for module_name in modules_to_test:
    try:
        importlib.import_module(module_name)
        print(f"OK: {module_name}")
    except ImportError as e:
        print(f"FAILED: {module_name} - {e}")
        sys.exit(1)

print("All imports successful!")
```

Run in packaged executable:
```bash
./inference/inference test_imports.py
```
