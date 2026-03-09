# Model Conversion to LiteRT

## Overview

LiteRT accepts models in `.tflite` format (FlatBuffer). Convert from PyTorch, TensorFlow, or JAX.

## PyTorch Conversion

### Installation

```bash
pip install litert-torch-nightly torchvision
# Or stable: pip install litert-torch
```

### Basic Conversion

```python
import litert_torch
import torch
import torchvision

# Load PyTorch model
model = torchvision.models.resnet18(pretrained=True).eval()

# Create sample inputs (required for tracing)
sample_inputs = (torch.randn(1, 3, 224, 224),)

# Convert to LiteRT
edge_model = litert_torch.convert(model, sample_inputs)

# Validate outputs
pytorch_output = model(*sample_inputs)
edge_output = edge_model(*sample_inputs)
assert numpy.allclose(pytorch_output.detach().numpy(), edge_output, rtol=1e-3)

# Export to .tflite
edge_model.export('resnet18.tflite')
```

### Requirements

- PyTorch 2.1.0+ (model must be `torch.export` compliant)
- Model must be in eval mode: `model.eval()`

### Visualization

```bash
pip install ai-edge-model-explorer
```

```python
import model_explorer
model_explorer.visualize('resnet18.tflite')
```

## TensorFlow Conversion

### From SavedModel

```python
import tensorflow as tf

# Load SavedModel
converter = tf.lite.TFLiteConverter.from_saved_model('saved_model_dir')
tflite_model = converter.convert()

# Save
with open('model.tflite', 'wb') as f:
    f.write(tflite_model)
```

### From Keras Model

```python
import tensorflow as tf

# Convert Keras model directly
model = tf.keras.applications.MobileNetV2()
converter = tf.lite.TFLiteConverter.from_keras_model(model)
tflite_model = converter.convert()

with open('mobilenet.tflite', 'wb') as f:
    f.write(tflite_model)
```

## JAX Conversion

Use jax2tf bridge:

```python
import jax
import jax.numpy as jnp
from jax.experimental import jax2tf
import tensorflow as tf

# JAX function
def jax_fn(x):
    return jax.nn.relu(x @ weights + bias)

# Convert to TensorFlow
tf_fn = jax2tf.convert(jax_fn)

# Then use TFLite converter
concrete_func = tf.function(tf_fn).get_concrete_function(
    tf.TensorSpec([1, 784], tf.float32))
converter = tf.lite.TFLiteConverter.from_concrete_functions([concrete_func])
tflite_model = converter.convert()
```

## Quantization

Reduce model size and improve inference speed.

### Post-Training Dynamic Quantization

```python
converter = tf.lite.TFLiteConverter.from_saved_model('saved_model_dir')
converter.optimizations = [tf.lite.Optimize.DEFAULT]
tflite_model = converter.convert()
```

### Post-Training Integer Quantization (INT8)

```python
def representative_dataset():
    for _ in range(100):
        yield [np.random.rand(1, 224, 224, 3).astype(np.float32)]

converter = tf.lite.TFLiteConverter.from_saved_model('saved_model_dir')
converter.optimizations = [tf.lite.Optimize.DEFAULT]
converter.representative_dataset = representative_dataset
converter.target_spec.supported_ops = [tf.lite.OpsSet.TFLITE_BUILTINS_INT8]
converter.inference_input_type = tf.int8
converter.inference_output_type = tf.int8
tflite_model = converter.convert()
```

### Float16 Quantization

```python
converter = tf.lite.TFLiteConverter.from_saved_model('saved_model_dir')
converter.optimizations = [tf.lite.Optimize.DEFAULT]
converter.target_spec.supported_types = [tf.float16]
tflite_model = converter.convert()
```

## AI Edge Quantizer

Additional optimization tool:

```bash
pip install ai-edge-quantizer
```

```python
from ai_edge_quantizer import quantize

# Quantize existing tflite model
quantized_model = quantize('model.tflite', 'int8')
quantized_model.export('model_int8.tflite')
```

## LLM Conversion (LiteRT-LM)

For transformer models, use AI Edge Torch Generative API:

```python
import ai_edge_torch.generative as generative

# Convert transformer model
converted = generative.convert(
    model,
    tokenizer=tokenizer,
    quantization='int4'  # or 'int8', 'fp16'
)
converted.export('llm.litertlm')
```

## Supported Operations

LiteRT supports most common ML operations. Check compatibility:
- https://ai.google.dev/edge/litert/models/ops_compatibility

Unsupported ops can use:
1. Custom operators
2. Flex delegate (TensorFlow ops fallback)
3. Model modification to use supported ops
