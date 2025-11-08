# GGUF Format Specification

## Overview

GGUF (GGJT-based Unified Format) is a single-file format for storing quantized neural network models developed by the llama.cpp project. It provides efficient storage, metadata support, and optimized tensor access patterns for inference.

## File Structure

### Header (256 bytes minimum)

```
[Magic Number] [Version] [Tensor Count] [Metadata Length]
[Metadata Block] [Tensor Data Block]
```

### Magic Number
- **Value**: 0x4747554606 (GGUF in ASCII + version)
- **Endianness**: Little-endian
- **Purpose**: File identification and format validation

### Version Number
- **Current**: 3
- **Compatibility**: Decoder should support older versions
- **Changes**: Track format evolution across versions

### Metadata Block

The metadata section stores model configuration and hyperparameters:

```
[Key-Value Count]
For each key-value pair:
  [Key Length] [Key String] [Value Type] [Value Data]
```

#### Common Metadata Keys

| Key | Type | Description |
|-----|------|-------------|
| `general.name` | string | Model name |
| `general.description` | string | Model description |
| `general.version` | string | Model version |
| `general.quantization` | string | Quantization level (Q4_K, etc.) |
| `model.architecture` | string | Model type (transformer, etc.) |
| `model.context_length` | uint32 | Context window size |
| `model.embedding_length` | uint32 | Embedding dimension |
| `model.feed_forward_length` | uint32 | FFN hidden dimension |
| `model.attention_head_count` | uint32 | Number of attention heads |
| `model.attention_head_count_kv` | uint32 | KV attention head count |
| `model.layer_count` | uint32 | Number of transformer layers |

### Tensor Data Block

Raw tensor data stored sequentially:

```
For each tensor:
  [Tensor Name Length] [Tensor Name]
  [Tensor Shape Count] [Tensor Shape Dimensions...]
  [Tensor Type] [Tensor Data...]
```

#### Tensor Types

| Type ID | Name | Bits | Description |
|---------|------|------|-------------|
| 0 | F32 | 32 | Float32 (full precision) |
| 1 | F16 | 16 | Float16 (half precision) |
| 2 | Q4_0 | 4 | 4-bit quantization (original) |
| 3 | Q4_1 | 4 | 4-bit quantization variant |
| 4 | Q4_K | 4 | 4-bit K-quantization (recommended) |
| 5 | Q5_K | 5 | 5-bit K-quantization |
| 6 | Q6_K | 6 | 6-bit K-quantization |
| 7 | Q8_K | 8 | 8-bit K-quantization |

## Quantization Implementation

### K-Quantization (K-Quant) Format

K-quants provide better quality than regular quantization by using importance-aware scaling:

```
Block Format:
[Scale Factors] [Quantized Values] [Residuals (optional)]
```

### Q4_K Structure

- **Block Size**: 32 weights per block
- **Data Layout**:
  - 2 bytes: scale factor (FP16)
  - 2 bytes: minimum value
  - 16 bytes: 4-bit quantized weights (128 values in 64 bytes -> 32 values in 16 bytes)

### Q5_K Structure

- **Block Size**: 32 weights per block
- **Data Layout**:
  - 3 bytes: scale factors
  - 32 bytes: 5-bit quantized weights

### Q6_K Structure

- **Block Size**: 64 weights per block
- **Data Layout**:
  - 3 bytes: scale factors
  - 48 bytes: 6-bit quantized weights

### Q8_K Structure

- **Block Size**: 32 weights per block
- **Data Layout**:
  - 2 bytes: scale factor
  - 32 bytes: 8-bit quantized weights

## Tensor Dimensions

Tensors are stored with explicit shape information:

```
Weight Tensor Example (Linear Layer):
  Shape: [output_dim, input_dim]
  Type: Q4_K
  Size: (output_dim * input_dim) * 4-bits
```

## Alignment and Padding

- **Tensor Alignment**: 32-byte boundaries for optimal memory access
- **Padding**: Zero-padding between sections for alignment
- **Rationale**: Enables SIMD optimizations and GPU memory efficiency

## Metadata Preservation

Critical metadata includes:

1. **Model Architecture**
   - Layer count and dimensions
   - Attention configuration
   - FFN settings

2. **Quantization Info**
   - Quantization level used
   - Key layer precision overrides
   - Mixed precision markers

3. **Model Provenance**
   - Original model source
   - Conversion tool version
   - Conversion timestamp

4. **Compatibility**
   - Supported inference backends
   - Minimum VRAM requirement
   - CPU/GPU variant markers

## Loading and Inference

### Memory Mapping

GGUF supports memory-mapped file access:

```
Benefits:
- Load only required tensors
- Reduce peak memory usage
- Enable OOM-safe inference
- Faster cold starts
```

### Tensor Access Pattern

```
1. Load metadata
2. Validate model architecture
3. Initialize GPU memory
4. Memory-map tensor data
5. Load layers on-demand
6. Perform inference
```

## Best Practices

### File Size Considerations

- **Original FP32**: ~4 bytes per parameter
- **Q4_K**: ~0.5 bytes per parameter (8x reduction)
- **Q8_K**: ~1 byte per parameter (4x reduction)

### Version Compatibility

- Always check GGUF version before loading
- Support version 3 minimum for modern models
- Handle version migrations gracefully

### Metadata Completeness

Include complete metadata for:
- Model compatibility checking
- Inference optimization
- User documentation
- License compliance

### Quantization Markers

Mark quantization level in metadata:

```json
{
  "general.quantization": "Q4_K",
  "general.quantized_from": "ggml-model.bin",
  "general.quantized_date": "2024-01-15",
  "quantization.key_layers": ["attention", "query", "key", "value"]
}
```

## Validation Checklist

- [ ] Magic number correct (0x4747554606)
- [ ] Version supported (>= 3)
- [ ] All metadata keys present
- [ ] Tensor count matches declaration
- [ ] All tensor shapes valid
- [ ] All tensor types supported
- [ ] No corrupted quantization blocks
- [ ] File size matches expected size

## Common Issues and Solutions

### Issue: "Invalid GGUF File"
- Check magic number
- Verify file not corrupted during transfer
- Try with different GGUF version

### Issue: "Memory Mapping Failed"
- Ensure sufficient disk cache
- Check file permissions
- Verify file integrity

### Issue: "Metadata Missing"
- Reconvert with newer tool
- Update model loader expectations
- Use fallback default values

## References

- llama.cpp GGUF Implementation: https://github.com/ggerganov/llama.cpp
- GGML Quantization Details: https://github.com/ggerganov/ggml
- Official Specification: Format v3 in llama.cpp source

## Appendix: File Format Example

```
Hex Dump of GGUF Header:
00: 47 47 55 46 06 00 00 00   GGUF....
08: 03 00 00 00               (version 3)
0C: 0A 00 00 00               (10 tensors)
10: 42 01 00 00               (metadata length)
14: [metadata block...]
[tensor data...]
```
