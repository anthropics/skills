# GPU Acceleration with LiteRT

## Overview

LiteRT provides GPU acceleration across Android, iOS, macOS, Windows, Linux, and Web via ML Drift, delivering 1.4x faster performance than legacy TFLite GPU delegate.

## Supported Technologies

| Platform | GPU Backend |
|----------|-------------|
| Android | OpenCL, OpenGL |
| iOS/macOS | Metal |
| Windows/Linux | WebGPU |
| Web | WebGPU |

## Basic GPU Setup

### Kotlin (Android)

```kotlin
val model = CompiledModel.create(
    context.assets,
    "mymodel.tflite",
    CompiledModel.Options(Accelerator.GPU),
    env
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

// Create environment
LITERT_ASSIGN_OR_RETURN(auto env, Environment::Create({}));

// Load model with GPU acceleration
LITERT_ASSIGN_OR_RETURN(auto compiled_model,
    CompiledModel::Create(env, "mymodel.tflite", kLiteRtHwAcceleratorGpu));

// Create buffers
LITERT_ASSIGN_OR_RETURN(auto input_buffers, compiled_model.CreateInputBuffers());
LITERT_ASSIGN_OR_RETURN(auto output_buffers, compiled_model.CreateOutputBuffers());

// Run inference
compiled_model.Run(input_buffers, output_buffers);
```

## Zero-Copy Buffer Interop

Transfer GPU buffers directly without CPU copies for up to 2x performance in real-time applications.

### OpenGL Buffer (C++)

```cpp
// Wrap existing OpenGL buffer
LITERT_ASSIGN_OR_RETURN(auto gl_input_buffer,
    TensorBuffer::CreateFromGlBuffer(
        env,
        tensor_type,
        opengl_buffer.target,
        opengl_buffer.id,
        opengl_buffer.size_bytes,
        opengl_buffer.offset
    ));

// Use directly in inference
compiled_model.Run({gl_input_buffer}, output_buffers);
```

### AHardwareBuffer (Android NDK)

```cpp
// Wrap Android hardware buffer
LITERT_ASSIGN_OR_RETURN(auto ahwb_buffer,
    TensorBuffer::CreateFromAhwb(env, tensor_type, ahw_buffer, 0));
```

## Asynchronous Execution

Run GPU inference without blocking CPU for parallel workloads.

```cpp
// Create event for synchronization
LITERT_ASSIGN_OR_RETURN(auto input_event,
    Event::CreateManagedEvent(env, LiteRtEventTypeEglSyncFence));

// Attach event to input
inputs[0].SetEvent(std::move(input_event));

// Run async - CPU continues while GPU processes
compiled_model.RunAsync(inputs, outputs);

// Do other CPU work here...

// Wait for completion when needed
outputs[0].GetEvent().Wait();
```

## Dependencies

### Android (Gradle)

```groovy
implementation 'com.google.ai.edge.litert:litert:2.1.0'
// GPU acceleration is built-in, no additional dependency needed
```

### C++ (CMake)

Requires:
- LiteRT C API shared library
- GLES dependencies
- GPU accelerator prebuilts via `litert_gpu_accelerator_prebuilts()`

## Performance Tips

1. **Batch operations** - Combine multiple inferences when possible
2. **Reuse buffers** - Create input/output buffers once, reuse across calls
3. **Use zero-copy** - Pass GPU buffers directly from camera/rendering pipelines
4. **Async execution** - Overlap CPU preprocessing with GPU inference
5. **Warm-up** - Run one inference at startup to initialize GPU pipeline
