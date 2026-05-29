# NPU Acceleration with LiteRT

## Overview

NPUs deliver up to 100x faster inference than CPU and 10x faster than GPU with significantly lower power consumption. LiteRT provides unified NPU support across major vendors.

## Supported NPU Vendors

| Vendor | Status | Compilation |
|--------|--------|-------------|
| Qualcomm AI Engine Direct | Production | AOT + JIT |
| MediaTek NeuroPilot | Production | AOT + JIT |
| Google Tensor | Experimental | Contact Google |

## Compilation Strategies

### AOT (Ahead-of-Time)
- Best for large, complex models
- Reduces app initialization time
- Lower memory usage at startup
- Requires knowing target SoC at build time

### JIT (On-Device)
- Best for platform-agnostic distribution
- Higher first-run overhead
- No preparation needed
- Ideal for smaller models

## Basic NPU Setup

### Kotlin (Android)

```kotlin
// NPU with GPU fallback
val model = CompiledModel.create(
    context.assets,
    "model/mymodel.tflite",
    CompiledModel.Options(Accelerator.NPU, Accelerator.GPU)
)

val inputBuffers = model.createInputBuffers()
val outputBuffers = model.createOutputBuffers()

inputBuffers[0].writeFloat(inputData)
model.run(inputBuffers, outputBuffers)
val result = outputBuffers[0].readFloat()
```

### C++

```cpp
// Setup environment with NPU dispatch library
std::vector<Environment::Option> environment_options = {
    {Environment::OptionTag::DispatchLibraryDir, "/usr/lib64/npu_dispatch/"}
};
LITERT_ASSIGN_OR_RETURN(auto env,
    Environment::Create(absl::MakeConstSpan(environment_options)));

// Load model
LITERT_ASSIGN_OR_RETURN(auto model, Model::Load("mymodel_npu.tflite"));

// Create compiled model with NPU acceleration
LITERT_ASSIGN_OR_RETURN(auto compiled_model,
    CompiledModel::Create(env, model, kLiteRtHwAcceleratorNpu));

// Run inference
LITERT_ASSIGN_OR_RETURN(auto input_buffers, compiled_model.CreateInputBuffers());
LITERT_ASSIGN_OR_RETURN(auto output_buffers, compiled_model.CreateOutputBuffers());
compiled_model.Run(input_buffers, output_buffers);
```

## Zero-Copy with AHardwareBuffer

```cpp
// Direct NPU access from camera/video buffers
LITERT_ASSIGN_OR_RETURN(auto npu_input_buffer,
    TensorBuffer::CreateFromAhwb(env, tensor_type, ahw_buffer, 0));

compiled_model.Run({npu_input_buffer}, output_buffers);
```

## JIT Compilation Caching

Cache compilation artifacts to avoid recompilation on subsequent runs.

```cpp
std::vector<Environment::Option> options = {
    {Environment::OptionTag::DispatchLibraryDir, "/path/to/npu_dispatch/"},
    {Environment::OptionTag::CompilerCacheDir, "/path/to/cache/"}
};
LITERT_ASSIGN_OR_RETURN(auto env, Environment::Create(options));
```

Benefits:
- 37-97% reduction in initialization time
- Significant memory savings
- Cache invalidates when vendor version, build fingerprint, model, or options change

## Android Deployment

### Requirements
- Minimum API level 31+
- arm64-v8a architecture only

### Google Play Delivery Options

**On-demand delivery:**
```xml
<dist:module
    dist:title="@string/npu_model">
    <dist:delivery>
        <dist:on-demand/>
    </dist:delivery>
</dist:module>
```

**Install-time delivery:**
```xml
<dist:delivery>
    <dist:install-time/>
</dist:delivery>
```

## Accelerator Fallback

LiteRT automatically handles fallback when NPU is unavailable:

**Priority order:** NPU → GPU → CPU

Partial delegation is supported - unsupported operations run on fallback accelerators seamlessly.

## Performance Benchmarks (Snapdragon 8 Elite)

- NPU: Up to 100x faster than CPU
- NPU: ~10x faster than GPU
- 50+ models run in under 5ms
- Power usage: ~1/5 of CPU
