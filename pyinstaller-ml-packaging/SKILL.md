---
name: pyinstaller-ml-packaging
description: Package Python ML backend as standalone sidecar executable with PyInstaller v6.16.0. Use when bundling PyTorch/Diffusers dependencies, creating one-folder distributions, including CUDA libraries, optimizing bundle size, or preparing ML backends for desktop deployment.
---

# PyInstaller ML Packaging & Distribution

## Overview

This skill provides a complete workflow for packaging machine learning Python backends into standalone executables using PyInstaller v6.16.0. It's designed for desktop applications that require PyTorch, Diffusers, transformers, and other ML libraries as separate processes or compiled binaries.

## Key Capabilities

### PyInstaller v6.16.0 Features
- **Enhanced Python 3.13 support** with improved module discovery
- **Better hidden import detection** for modern ML frameworks
- **Improved CUDA library handling** for GPU-accelerated binaries
- **Optimized one-folder distributions** for faster startup
- **Enhanced binary signing** support for macOS
- **Reduced bundle size** through better dependency analysis

### ML Framework Support
- **PyTorch**: Full CPU/GPU builds with CUDA runtime
- **Diffusers**: Stable Diffusion and image generation pipelines
- **Transformers**: HuggingFace transformer models
- **ONNX**: Model optimization and inference
- **OpenVINO**: Intel optimization toolkit

### Distribution Strategies

#### One-Folder Distribution (Recommended)
- Faster startup times
- Easier for updates and patches
- Better for resource-constrained environments
- Smaller initial load footprint

#### One-File Distribution
- Simpler distribution
- Single executable deployment
- Slower startup due to extraction
- Better for simple ML services

### CUDA/GPU Support
- Automatic CUDA library detection and bundling
- Support for multiple CUDA versions (11.8, 12.0, 12.1, 12.4)
- cuDNN integration for optimized inference
- GPU memory management in packaged environment

### Bundle Size Optimization
- Selective module inclusion (100-500MB reductions)
- Weight quantization for model files
- ONNX format conversion for lighter models
- Stripping debug symbols from binary dependencies

## Workflow

### 1. Preparation Phase
- Identify ML dependencies (PyTorch version, CUDA level)
- Create clean virtual environment
- Install specific framework versions
- Test model inference locally

### 2. Configuration Phase
- Generate or customize spec file
- Add hidden imports for framework components
- Configure CUDA library paths
- Set up entry points and hooks

### 3. Build Phase
- Run automated build script with validation
- Verify CUDA libraries are bundled correctly
- Test standalone executable
- Measure bundle size

### 4. Optimization Phase
- Remove unnecessary dependencies
- Optimize model weights
- Strip binaries
- Create distribution package

### 5. Validation Phase
- Test on clean system without Python
- Verify GPU access (if applicable)
- Benchmark performance vs. direct Python
- Test with actual inference workflows

## Quick Start

1. **Review** `pyinstaller-spec-files.md` for configuration options
2. **Customize** `inference.spec` for your ML models and dependencies
3. **Run** `build-ml-backend.py` with your spec file
4. **Optimize** using techniques in `size-optimization.md`
5. **Validate** the standalone executable with your inference code

## Common Scenarios

### Scenario 1: PyTorch with CUDA GPU Support
Use when packaging PyTorch models that require GPU acceleration:
- Set up CUDA library paths in spec file
- Include cuDNN if using optimized operations
- Test on target GPU hardware
- Reference: `pyinstaller-cuda-bundling.md`

### Scenario 2: Diffusers Stable Diffusion Backend
Use for image generation pipelines as sidecar process:
- Include all transformer model components
- Add hidden imports for diffusers pipeline classes
- Optimize model weights for size
- Reference: `pyinstaller-hidden-imports.md`

### Scenario 3: Multi-Model Inference Service
Use when bundling multiple model types (detection, segmentation, etc.):
- Create modular inference entry point
- Include all required dependencies
- Implement inter-process communication
- Reference: `build-ml-backend.py`, `inference.spec`

### Scenario 4: Resource-Constrained Deployment
Use for edge devices or limited storage environments:
- Apply all size optimization techniques
- Use quantized models (FP16, INT8)
- Enable one-folder distribution
- Reference: `size-optimization.md`

## Bundle Size Reference

| Framework | Base Size | With Models | Optimized |
|-----------|-----------|-------------|-----------|
| PyTorch CPU | 800MB | 2.5GB+ | 1.2GB |
| PyTorch GPU | 1.2GB | 3.2GB+ | 1.8GB |
| Diffusers | 600MB | 3GB+ (per model) | 1.5GB |
| Transformers | 400MB | 1.5GB+ | 700MB |

## Resources

### scripts/
- **build-ml-backend.py**: Automated build orchestration, validation, and optimization with comprehensive error checking

### references/
- **pyinstaller-spec-files.md**: Detailed spec file configuration, custom hooks, and advanced settings
- **pyinstaller-hidden-imports.md**: Complete hidden imports mapping for ML libraries (PyTorch, Diffusers, transformers, ONNX)
- **pyinstaller-cuda-bundling.md**: CUDA library inclusion strategies for different versions and architectures
- **size-optimization.md**: Bundle size reduction techniques, excluding modules, and weight quantization

### assets/
- **inference.spec**: Production-ready spec file template for ML backend packaging

## Best Practices

1. **Use Python 3.11-3.13** for optimal ML framework support and compatibility
2. **Test in virtual environments** before packaging to isolate dependencies
3. **Include all dependencies** in spec file to avoid runtime failures
4. **Version your builds** alongside framework updates for consistency
5. **Create separate builds** for different CUDA versions and platforms
6. **Monitor startup time** in packaged vs. direct execution
7. **Document GPU requirements** for end users and deployment targets

## Common Issues & Solutions

| Issue | Solution |
|-------|----------|
| CUDA libraries not found | Use `pyinstaller-cuda-bundling.md` to manually specify library paths |
| Model files missing at runtime | Ensure datas parameter includes all model directories in spec file |
| Bundle size exceeds limits | Refer to `size-optimization.md` for selective module inclusion |
| GPU not detected in binary | Verify CUDA toolkit installation and environment variables during build |
| Hidden import errors | Check `pyinstaller-hidden-imports.md` for comprehensive dependency list |

## Version Support

- **PyInstaller**: 6.16.0+
- **Python**: 3.11, 3.12, 3.13
- **PyTorch**: 2.0+ (CUDA 11.8, 12.0, 12.1, 12.4)
- **Transformers**: 4.30+
- **Diffusers**: 0.20+

## Integration Points

- **Desktop Frameworks**: Unity, Unreal Engine, Electron
- **Distribution**: GitHub Releases, cloud storage, custom installers
- **Monitoring**: Process logging, performance metrics, error telemetry
- **Updates**: Delta patching, version checking, rollback strategies
