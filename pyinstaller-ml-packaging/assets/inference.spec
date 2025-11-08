# -*- mode: python ; coding: utf-8 -*-
"""
PyInstaller Spec File for ML Backend Inference
Production template for packaging ML models with PyInstaller v6.16.0

Customize:
1. Set ENTRY_POINT to your main inference script
2. Update MODEL_PATH and CUDA paths for your environment
3. Adjust HIDDEN_IMPORTS for your specific frameworks
4. Test on target platform before distribution

Supported Frameworks:
- PyTorch (CPU/GPU with CUDA)
- Transformers (HuggingFace)
- Diffusers (Stable Diffusion)
- ONNX Runtime
"""

import os
import sys
from pathlib import Path

# ============================================================================
# Configuration - CUSTOMIZE FOR YOUR PROJECT
# ============================================================================

# Entry point script
ENTRY_POINT = 'inference.py'

# Model directory (relative or absolute path)
MODEL_PATH = 'models'

# CUDA installation path (update for your system)
CUDA_HOME = '/usr/local/cuda-12.4'  # Linux
# CUDA_HOME = 'C:\\Program Files\\NVIDIA GPU Computing Toolkit\\CUDA\\v12.4'  # Windows

# Enable GPU support
ENABLE_CUDA = True

# Enable CuDNN optimization
ENABLE_CUDNN = True

# Python version detection
PYTHON_VERSION = f"{sys.version_info.major}.{sys.version_info.minor}"

# ============================================================================
# Framework-Specific Hidden Imports
# ============================================================================

PYTORCH_IMPORTS = [
    'torch',
    'torch._C',
    'torch.utils.cpp_extension',
    'torch.utils.data',
    'torch.nn',
    'torch.nn.functional',
    'torch.optim',
]

PYTORCH_GPU_IMPORTS = [
    'torch.cuda',
    'torch.cuda.random',
    'torch.cuda.nccl',
    'torch.backends.cudnn',
]

TRANSFORMERS_IMPORTS = [
    'transformers',
    'transformers.models',
    'transformers.utils',
    'huggingface_hub',
    'safetensors',
    'safetensors.torch',
    'tokenizers',
]

DIFFUSERS_IMPORTS = [
    'diffusers',
    'diffusers.models',
    'diffusers.pipelines',
    'diffusers.schedulers',
    'diffusers.loaders',
]

ONNX_IMPORTS = [
    'onnxruntime',
]

COMMON_IMPORTS = [
    'numpy',
    'PIL',
    'PIL.Image',
    'cv2',
    'yaml',
    'json',
    'pickle',
]

# Combine all hidden imports
hidden_imports = PYTORCH_IMPORTS + COMMON_IMPORTS

# Add GPU imports if enabled
if ENABLE_CUDA:
    hidden_imports.extend(PYTORCH_GPU_IMPORTS)

# Uncomment for Transformers support
# hidden_imports.extend(TRANSFORMERS_IMPORTS)

# Uncomment for Diffusers support
# hidden_imports.extend(DIFFUSERS_IMPORTS)

# Uncomment for ONNX support
# hidden_imports.extend(ONNX_IMPORTS)

# ============================================================================
# CUDA Library Configuration
# ============================================================================

binaries = []

if ENABLE_CUDA:
    # PyTorch GPU - CUDA Runtime
    cuda_lib_path = f'{CUDA_HOME}/lib64'

    cuda_libraries = [
        'libcudart.so.12',           # CUDA Runtime
        'libcublas.so.12',           # Linear algebra
        'libcublasLt.so.12',         # Lightweight BLAS
        'libcusolver.so.11',         # Solver library
        'libcusparse.so.12',         # Sparse operations
        'libnvrtc.so.12.4',          # Runtime compilation
        'libnvrtc-builtins.so.12.4', # Builtins
        'libcufft.so.11',            # FFT operations
        'libcurand.so.10',           # Random generation
        'libnccl.so.2',              # Multi-GPU communication
    ]

    # Add detected CUDA libraries
    for lib_name in cuda_libraries:
        lib_path = os.path.join(cuda_lib_path, lib_name)
        if os.path.exists(lib_path):
            binaries.append((lib_path, '.'))

    # CuDNN integration (if installed)
    if ENABLE_CUDNN:
        cudnn_paths = [
            '/usr/lib/x86_64-linux-gnu/libcudnn.so.8',     # Linux default
            '/usr/local/cuda/lib64/libcudnn.so.8',         # CUDA directory
        ]
        for cudnn_path in cudnn_paths:
            if os.path.exists(cudnn_path):
                binaries.append((cudnn_path, '.'))
                break

# ============================================================================
# Data Files Configuration
# ============================================================================

datas = []

# Include model files
if os.path.isdir(MODEL_PATH):
    datas.append((MODEL_PATH, 'models'))

# Add config files if present
if os.path.isdir('config'):
    datas.append(('config', 'config'))

# Add weights if present
if os.path.isdir('weights'):
    datas.append(('weights', 'weights'))

# ============================================================================
# PyInstaller Analysis Block
# ============================================================================

a = Analysis(
    [ENTRY_POINT],
    pathex=[],
    binaries=binaries,
    datas=datas,
    hiddenimports=hidden_imports,
    hookspath=[],  # Custom hooks: ['./_pyinstaller_hooks']
    hooksconfig={},
    runtime_hooks=[],  # Custom runtime hooks: ['rthook_cuda.py']
    excludedimports=[
        'pytest',
        'unittest',
        'test',
        'tests',
        'distutils',
        'setuptools',
    ],
    win_no_prefer_redirects=False,
    win_private_assemblies=False,
    cipher=None,
    noarchive=False,
)

# ============================================================================
# Python Archive Block
# ============================================================================

pyz = PYZ(
    a.pure,
    a.zipped_data,
    cipher=None
)

# ============================================================================
# Executable Configuration
# ============================================================================

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
    strip=True,  # Remove debug symbols (10-20% size reduction)
    upx=True,  # Enable compression (20-40% size reduction)
    upx_exclude=[
        'vcruntime140.dll',  # Windows
        'libcudart.so.12',   # CUDA (incompressible)
    ],
    runtime_tmpdir=None,
    console=True,  # Show console (change to False for GUI)
    disable_windowed_traceback=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
    icon=None,  # Add icon: 'icon.ico' (Windows) or 'icon.icns' (macOS)
)

# ============================================================================
# Collection Block (One-Folder Distribution)
# ============================================================================

coll = COLLECT(
    exe,
    a.binaries,
    a.zipfiles,
    a.datas,
    strip=False,  # Keep false to preserve directory structure
    upx=True,
    upx_exclude=[],
    name='inference'
)

# ============================================================================
# Optional: One-File Distribution
# Use ONLY if you prefer single-file deployment
# COMMENTED OUT - Uncomment to use instead of COLLECT
# ============================================================================

# onefile = EXE(
#     pyz,
#     a.scripts,
#     a.binaries,
#     a.zipfiles,
#     a.datas,
#     [],
#     name='inference',
#     debug=False,
#     bootloader_ignore_signals=False,
#     strip=True,
#     upx=True,
#     upx_exclude=[],
#     runtime_tmpdir=None,
#     console=True,
# )
