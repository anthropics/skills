# Migration from TensorFlow Lite to LiteRT

## Overview

LiteRT is the new name for TensorFlow Lite. Migration requires only package name updates - no logic changes needed. The `.tflite` file format remains unchanged.

## Android Migration

### Maven Dependencies

Replace TensorFlow Lite packages with LiteRT equivalents:

| Old Package | New Package |
|-------------|-------------|
| `org.tensorflow:tensorflow-lite` | `com.google.ai.edge.litert:litert` |
| `org.tensorflow:tensorflow-lite-gpu` | `com.google.ai.edge.litert:litert-gpu` |
| `org.tensorflow:tensorflow-lite-metadata` | `com.google.ai.edge.litert:litert-metadata` |
| `org.tensorflow:tensorflow-lite-support` | `com.google.ai.edge.litert:litert-support` |

### Gradle Update

```groovy
// Before
implementation 'org.tensorflow:tensorflow-lite:2.x.x'
implementation 'org.tensorflow:tensorflow-lite-gpu:2.x.x'

// After
implementation 'com.google.ai.edge.litert:litert:2.1.0'
```

### Important: GPU with Interpreter API

GPU acceleration with Interpreter API is only available in Maven V1 packages. For V2 packages, use CompiledModel API for GPU inference.

### Play Services

If using TensorFlow Lite via Google Play Services, no changes needed:

```groovy
// Continue using this - no changes required
implementation 'com.google.android.gms:play-services-tflite-java:x.x.x'
implementation 'com.google.android.gms:play-services-tflite-gpu:x.x.x'
```

## Python Migration

### Package Update

```bash
# Remove old package
pip uninstall tflite-runtime

# Install LiteRT
pip install ai-edge-litert
```

### Import Changes

```python
# Before
from tflite_runtime.interpreter import Interpreter

# After
from ai_edge_litert.interpreter import Interpreter
```

Usage remains identical:

```python
interpreter = Interpreter(model_path='model.tflite')
interpreter.allocate_tensors()
# ... rest of code unchanged
```

## iOS/macOS, C++, Swift, Objective-C

No migration needed. Continue using TensorFlow Lite packages - these SDKs have not been renamed.

## API Comparison

### Interpreter API (Legacy, Compatible)

Works identically in both TFLite and LiteRT:

```kotlin
// Android Kotlin
val interpreter = Interpreter(modelBuffer)
interpreter.run(input, output)
```

### CompiledModel API (New, Recommended)

LiteRT-exclusive API for hardware acceleration:

```kotlin
// Android Kotlin - New API
val model = CompiledModel.create(
    context.assets,
    "model.tflite",
    CompiledModel.Options(Accelerator.GPU)
)
val inputBuffers = model.createInputBuffers()
val outputBuffers = model.createOutputBuffers()
inputBuffers[0].writeFloat(inputData)
model.run(inputBuffers, outputBuffers)
```

## Version Requirements

### LiteRT 2.1.0 (Latest)
- Minimum Android SDK: 23 (Android 6)
- Minimum NDK: r26a
- APIs: CompiledModel + Interpreter

### LiteRT 1.4.1 (Legacy)
- Minimum Android SDK: 21 (Android 5)
- APIs: Interpreter only

## tf.lite Deprecation

The `tf.lite` module in TensorFlow is deprecated and will be removed from future TensorFlow packages. Migrate to LiteRT for continued updates:

```python
# Deprecated - will be removed
import tensorflow as tf
converter = tf.lite.TFLiteConverter.from_saved_model('model')

# Future-proof alternative
# Use ai-edge-litert package directly
```

## File Format

No changes to `.tflite` files:
- Same FlatBuffer format
- Same file extension
- Full backward compatibility
- Existing models work without modification
