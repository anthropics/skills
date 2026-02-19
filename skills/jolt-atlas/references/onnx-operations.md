# ONNX Operations & Model Format

This document covers the supported ONNX operations in jolt-atlas, the fixed-point representation, neural teleportation, and model format requirements.

## Supported Instructions

The following ONNX operations are supported in jolt-atlas. Each is implemented as a lookup-table-based instruction in the JOLT proving system, avoiding circuit representation entirely.

### Arithmetic Operations

| Operation | Description | Notes |
|---|---|---|
| `Add` | Element-wise addition | Supports broadcasting |
| `Sub` | Element-wise subtraction | Supports broadcasting |
| `Mul` | Element-wise multiplication | Fixed-point scaling applied |
| `MatMul` | Matrix multiplication | Core operation for linear layers |
| `Einsum` | Einstein summation | Generalized tensor contraction |
| `Pow` | Element-wise power | Integer exponents |
| `Sqrt` | Element-wise square root | Via lookup table |
| `Reciprocal` | Element-wise 1/x | Via lookup table |
| `Log` | Element-wise natural logarithm | Via lookup table |
| `Exp` | Element-wise exponential | Via lookup table |

### Activation Functions

| Operation | Description | Notes |
|---|---|---|
| `Relu` | Rectified linear unit: max(0, x) | Most common activation |
| `Sigmoid` | Logistic function: 1/(1+e^(-x)) | Via lookup table |
| `Erf` | Gaussian error function | Used in GELU implementation |
| `Gelu` | Gaussian Error Linear Unit | Via Erf lookup |
| `Tanh` | Hyperbolic tangent | Via lookup table |
| `Softmax` | Normalized exponential | Applied along specified axis |
| `Clip` | Clamp values to [min, max] range | Used for ReLU6, etc. |

### Normalization

| Operation | Description | Notes |
|---|---|---|
| `LayerNorm` | Layer normalization | Transformer standard |
| `BatchNorm` | Batch normalization | Folded via teleportation when possible |
| `ReduceMean` | Mean reduction along axes | Used in normalization implementations |

### Pooling & Convolution

| Operation | Description | Notes |
|---|---|---|
| `Conv` | N-dimensional convolution | 1D and 2D supported |
| `MaxPool` | Max pooling | Sliding window max |
| `AveragePool` | Average pooling | Sliding window mean |

### Shape & Tensor Manipulation

| Operation | Description | Notes |
|---|---|---|
| `Flatten` | Collapse dimensions | To 1D or specified axis |
| `Reshape` | Change tensor shape | Total elements must match |
| `Transpose` | Permute dimensions | Arbitrary axis ordering |
| `Concat` | Concatenate tensors along axis | All tensors must match on other dims |
| `Split` | Split tensor into chunks | Along specified axis |
| `Gather` | Index-based selection | Along specified axis |
| `Unsqueeze` | Insert dimension of size 1 | At specified axes |
| `Squeeze` | Remove dimensions of size 1 | At specified axes |
| `Expand` | Broadcast to larger shape | Following numpy rules |
| `Slice` | Extract sub-tensor | With start, end, step |
| `Pad` | Pad tensor with values | Constant padding |
| `Cast` | Type conversion | Between supported types |
| `Shape` | Return tensor shape | As 1D integer tensor |

### Structural / Utility

| Operation | Description | Notes |
|---|---|---|
| `Constant` | Embed constant value | Stored in graph |
| `ConstantOfShape` | Create tensor filled with value | Given shape and fill value |
| `Where` | Conditional selection | Element-wise ternary |
| `Dropout` | Identity at inference | No-op (training only) |

## Fixed-Point Representation

All tensor values in jolt-atlas are represented as `i32` integers. Floating-point model weights and activations are quantized during ONNX tracing using configurable scale factors.

### How it works

1. **Weight quantization:** When the ONNX model is loaded, floating-point weights are multiplied by a scale factor and rounded to integers.
2. **Input quantization:** User inputs must be provided as `Vec<i32>`. If your data is floating-point, multiply by the scale factor before passing.
3. **Intermediate values:** All intermediate computations maintain fixed-point representation. Multiplication results are rescaled to prevent overflow.
4. **Output dequantization:** The output tensor contains integer values. Divide by the appropriate scale factor to recover approximate floating-point values.

### Scale factors and RunArgs

The `RunArgs` configuration controls quantization behavior:

```rust
// Scale factor determines precision
// Higher scale = more precision but larger values = bigger trace
// Default scale is typically 2^12 = 4096

// Example: converting float input to fixed-point
let float_input: Vec<f32> = vec![0.5, -1.2, 3.7, 0.0];
let scale = 4096;
let fixed_input: Vec<i32> = float_input.iter()
    .map(|&x| (x * scale as f32).round() as i32)
    .collect();
```

### Overflow considerations

- `i32` range: -2,147,483,648 to 2,147,483,647
- With scale factor 4096 (2^12), the effective float range is roughly ±524,287
- Matrix multiplications accumulate sums, so large models with high scale factors risk overflow
- If you see incorrect outputs, try reducing the scale factor
- The `onnx-tracer` crate will panic on overflow in debug mode

## Neural Teleportation

Neural teleportation is a model transformation technique that folds batch normalization layers into adjacent linear (fully connected or convolutional) layers. This reduces the number of operations in the computational graph, leading to smaller and faster proofs.

### What it does

Given a sequence `Linear -> BatchNorm`, teleportation produces a single `Linear` layer with modified weights and biases that compute the same function:

```
Original:  y = BatchNorm(W*x + b)
           y = gamma * ((W*x + b) - mean) / sqrt(var + eps) + beta

Teleported: y = W'*x + b'
            where W' = gamma * W / sqrt(var + eps)
                  b' = gamma * (b - mean) / sqrt(var + eps) + beta
```

### When teleportation is applied

- Automatically during ONNX model loading when the tracer detects `Linear -> BatchNorm` or `Conv -> BatchNorm` patterns
- The original model file is not modified; teleportation happens in-memory
- Only applies when the batch norm has fixed statistics (inference mode)

### Impact on proofs

- Fewer operations in the DAG = fewer sumcheck rounds
- Reduced proof size
- Faster proving and verification times
- No change in model accuracy (mathematically equivalent transformation)

## ONNX Model Format Requirements

### Supported ONNX versions

jolt-atlas supports ONNX opset versions commonly exported by PyTorch (opset 11+) and ONNX Runtime. The tracer handles standard operator sets.

### Exporting from PyTorch

```python
import torch
import torch.onnx

model = YourModel()
model.eval()

dummy_input = torch.randn(1, input_features)

torch.onnx.export(
    model,
    dummy_input,
    "model.onnx",
    opset_version=13,
    input_names=["input"],
    output_names=["output"],
    dynamic_axes=None,  # Static shapes required
)
```

### Requirements

1. **Static shapes:** All tensor shapes must be known at export time. Dynamic axes are not supported.
2. **Single input:** The model should accept a single input tensor. Multi-input models require adapter wrappers.
3. **Supported operations only:** All operations in the graph must be in the supported instruction set above. Unsupported ops will cause a panic during tracing.
4. **No custom operators:** Only standard ONNX operators are supported.
5. **File naming:** Place the ONNX file as `network.onnx` inside a model directory (e.g., `onnx-tracer/models/my_model/network.onnx`).

### Model directory structure

```
onnx-tracer/models/
└── your_model/
    ├── network.onnx          # The ONNX model file
    └── (optional metadata)
```

## Known Limitations

The following ONNX operations are **not yet supported**:

- `LSTM`, `GRU`, `RNN` — Recurrent layers
- `ConvTranspose` — Transposed (deconvolution) layers
- `Resize`, `Upsample` — Spatial resizing operations
- `NonMaxSuppression` — Object detection post-processing
- `TopK` — K-largest element selection
- `ScatterND`, `ScatterElements` — Scatter operations
- `QuantizeLinear`, `DequantizeLinear` — ONNX-native quantization ops (jolt-atlas uses its own fixed-point scheme)
- Custom domain operators

If your model uses unsupported operations, you will need to either:
1. Replace them with supported equivalents in the PyTorch model before exporting
2. Use ONNX graph surgery tools (e.g., `onnx-graphsurgeon`) to rewrite the graph
3. Open a feature request on the jolt-atlas repository
