---
name: litert
description: Google's on-device AI framework for deploying ML and GenAI models on edge devices (successor to TensorFlow Lite). Use when working with on-device inference, .tflite models, mobile ML deployment, GPU/NPU acceleration, LiteRT-LM for LLMs, model conversion from PyTorch/TensorFlow/JAX, or migrating from TensorFlow Lite. Triggers on Android/iOS/Web ML inference, CompiledModel API, hardware acceleration, edge AI deployment, or running models like Gemma on device.
license: MIT
metadata:
  author: munyaradzi makosa
  version: "1.0.0"
---

# LiteRT: On-Device AI Framework

## Overview

LiteRT (Lite Runtime) is Google's framework for deploying ML and generative AI on edge devices. It's the successor to TensorFlow Lite with advanced GPU/NPU acceleration delivering up to 100x faster inference than CPU.

## Platform Support

| Platform | CPU | GPU | NPU |
|----------|-----|-----|-----|
| Android | Yes | OpenCL, OpenGL | Qualcomm, MediaTek |
| iOS | Yes | Metal | ANE (coming) |
| macOS | Yes | Metal, WebGPU | ANE (coming) |
| Windows | Yes | WebGPU | Intel (coming) |
| Linux | Yes | WebGPU | - |
| Web | Yes | WebGPU | Coming |

## Quick Start

### Android (Kotlin)

```kotlin
// Add dependency: implementation 'com.google.ai.edge.litert:litert:2.1.0'

val model = CompiledModel.create(
    context.assets,
    "model.tflite",
    CompiledModel.Options(Accelerator.GPU)  // or NPU, CPU
)

val inputBuffers = model.createInputBuffers()
val outputBuffers = model.createOutputBuffers()

inputBuffers[0].writeFloat(inputData)
model.run(inputBuffers, outputBuffers)
val result = outputBuffers[0].readFloat()
```

### C++

```cpp
#include "litert/cc/litert_compiled_model.h"
#include "litert/cc/litert_environment.h"

LITERT_ASSIGN_OR_RETURN(auto env, Environment::Create({}));
LITERT_ASSIGN_OR_RETURN(auto compiled_model,
    CompiledModel::Create(env, "model.tflite", kLiteRtHwAcceleratorGpu));

LITERT_ASSIGN_OR_RETURN(auto inputs, compiled_model.CreateInputBuffers());
LITERT_ASSIGN_OR_RETURN(auto outputs, compiled_model.CreateOutputBuffers());
compiled_model.Run(inputs, outputs);
```

### Python

```python
from ai_edge_litert.interpreter import Interpreter

interpreter = Interpreter(model_path='model.tflite')
interpreter.allocate_tensors()
interpreter.set_tensor(input_index, input_data)
interpreter.invoke()
output = interpreter.get_tensor(output_index)
```

## APIs

### CompiledModel API (Recommended)
- Modern API for hardware acceleration
- Supports GPU, NPU, CPU
- Zero-copy buffer interop
- Async execution

### Interpreter API (Legacy)
- TensorFlow Lite compatible
- CPU-only in v2.x
- Use for backward compatibility

## Task Decision Tree

**Running inference on device?**
- Use CompiledModel API with appropriate accelerator
- See [gpu-acceleration.md](references/gpu-acceleration.md) or [npu-acceleration.md](references/npu-acceleration.md)

**Deploying LLMs (Gemma, Phi, Qwen)?**
- Use LiteRT-LM framework
- See [litert-lm.md](references/litert-lm.md)

**Converting models to .tflite?**
- PyTorch: Use `litert-torch` package
- TensorFlow: Use `tf.lite.TFLiteConverter`
- JAX: Use jax2tf bridge
- See [model-conversion.md](references/model-conversion.md)

**Migrating from TensorFlow Lite?**
- Package name changes only
- See [migration.md](references/migration.md)

## Performance Tips

1. **Choose the right accelerator**: NPU > GPU > CPU for most models
2. **Use zero-copy buffers**: Pass camera/GPU buffers directly
3. **Enable async execution**: Overlap CPU/GPU work
4. **Cache NPU compilation**: Use `CompilerCacheDir` environment option
5. **Quantize models**: INT8 reduces size 4x, improves speed

## Dependencies

### Android (Gradle)

```groovy
implementation 'com.google.ai.edge.litert:litert:2.1.0'
```

### Python

```bash
pip install ai-edge-litert           # Runtime
pip install litert-torch             # PyTorch conversion
pip install ai-edge-quantizer        # Quantization
```

## Resources

- **Official docs**: https://ai.google.dev/edge/litert
- **GitHub**: https://github.com/google-ai-edge/LiteRT
- **LiteRT-LM**: https://github.com/google-ai-edge/LiteRT-LM

## Reference Files

- [gpu-acceleration.md](references/gpu-acceleration.md) - GPU setup, zero-copy, async execution
- [npu-acceleration.md](references/npu-acceleration.md) - NPU setup, AOT/JIT compilation, vendor support
- [litert-lm.md](references/litert-lm.md) - LLM deployment with LiteRT-LM
- [model-conversion.md](references/model-conversion.md) - Converting PyTorch/TF/JAX to .tflite
- [migration.md](references/migration.md) - Migration from TensorFlow Lite
