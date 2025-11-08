# GGUF Quantization Levels: Comprehensive Comparison

## Quick Reference Table

| Level | Bits | Size Reduction | VRAM (Base SD1.5) | Speed | Quality | Use Case | Artifacts |
|-------|------|----------------|------------------|-------|---------|----------|-----------|
| Q2_K | 2 | 90% | 0.5-1 GB | Fastest | Very Low | Mobile, CPU | Severe |
| Q3_K | 3 | 85% | 0.8-1.5 GB | Very Fast | Low | Legacy GPU | Visible |
| Q4_K | 4 | 75% | 1.2-2 GB | Fast | Good | Consumer (RTX 3060) | Minimal |
| Q5_K | 5 | 60% | 2-3 GB | Moderate | High | Enthusiast (RTX 4080) | Imperceptible |
| Q6_K | 6 | 50% | 2.5-3.5 GB | Slow | Very High | Professional (RTX 4090) | None |
| Q8_K | 8 | 25% | 3.5-4.5 GB | Very Slow | Lossless | Research | None |

## Detailed Level Specifications

### Q2_K: Extreme Compression (2-bit)

**Technical Details:**
- **Bit Depth**: 2 bits per weight
- **Block Size**: 32 weights per block
- **Bytes per Block**: 4-5 bytes
- **Compression Ratio**: ~12x (0.5 bytes per weight)

**Memory Requirements:**
- Model Memory: 0.5-1.0 GB
- VRAM for Inference: 1.5-2.0 GB
- Batch Size: 1 (single image)

**Performance:**
- Inference Speed: 20-25 img/sec (RTX 4080)
- Throughput: 15-20 img/sec with batch processing
- Startup Time: <0.5 seconds

**Quality Characteristics:**
- Color quantization artifacts (banding)
- Loss of fine details
- Visible degradation in gradients
- Acceptable for rough previews only
- Not recommended for delivery

**Recommended Hardware:**
- Mobile GPUs (max 4GB VRAM)
- Edge devices with CPU inference
- Extreme memory constraints
- Legacy GPUs (GTX 1050 Ti)

**Example Use Cases:**
- Quick preview generation on mobile
- Real-time preview on constrained devices
- Emergency inference when out of memory
- Proof-of-concept prototypes

**Tradeoffs:**
- Gain: 90% size reduction, maximum speed
- Loss: Severe quality degradation, visible artifacts
- Verdict: Use only when memory is critical

---

### Q3_K: Aggressive Compression (3-bit)

**Technical Details:**
- **Bit Depth**: 3 bits per weight
- **Block Size**: 32 weights per block
- **Bytes per Block**: 6-7 bytes
- **Compression Ratio**: ~8x (0.75 bytes per weight)

**Memory Requirements:**
- Model Memory: 0.8-1.5 GB
- VRAM for Inference: 2.0-2.5 GB
- Batch Size: 1-2

**Performance:**
- Inference Speed: 15-18 img/sec (RTX 4080)
- Throughput: 12-15 img/sec with batch processing
- Startup Time: <1 second

**Quality Characteristics:**
- Visible color artifacts in gradients
- Some detail loss in complex areas
- Acceptable for real-time preview
- Not suitable for final outputs
- Character faces show artifacts

**Recommended Hardware:**
- RTX 2060, GTX 1660
- Systems with 6-8 GB VRAM
- Legacy gaming GPUs
- Budget conscious setups

**Example Use Cases:**
- Real-time UI preview
- Batch preview generation
- Testing prompts before high-quality generation
- Memory-limited workstations

**Tradeoffs:**
- Gain: Excellent speed, 85% size reduction
- Loss: Noticeable quality loss, artifacts visible
- Verdict: Good for previews, not final results

---

### Q4_K: Balanced Compression (4-bit) - RECOMMENDED START

**Technical Details:**
- **Bit Depth**: 4 bits per weight
- **Block Size**: 32 weights per block
- **Bytes per Block**: 18-22 bytes
- **Compression Ratio**: ~4x (1 byte per weight)

**Memory Requirements:**
- Model Memory: 1.2-2.0 GB
- VRAM for Inference: 3.0-4.5 GB (with overhead)
- Batch Size: 1-4

**Performance:**
- Inference Speed: 10-12 img/sec (RTX 4080)
- Throughput: 8-10 img/sec with batch processing
- Startup Time: 1-2 seconds

**Quality Characteristics:**
- Imperceptible artifacts for most users
- Minimal detail loss in complex areas
- Colors accurate and well-rendered
- Suitable for final delivery
- Character faces render clearly
- Only experts notice quality difference

**Recommended Hardware:**
- RTX 3060 (12GB) - PRIMARY
- RTX 4060 (8GB)
- RTX 4070 (12GB)
- RTX 3070 (8GB)
- Most consumer GPUs 2021+

**Example Use Cases:**
- Professional production (most common)
- Commercial delivery
- Fine art generation
- Character design work
- Default choice for most users

**Tradeoffs:**
- Gain: Good quality, fast speed, 75% size reduction
- Loss: Minimal, imperceptible to most
- Verdict: Sweet spot for most users

**Tips:**
- Default recommendation for unknown use cases
- Excellent balance of quality and speed
- Works well with LoRA fine-tuning
- Sufficient for all practical applications

---

### Q5_K: High Quality (5-bit) - PROFESSIONAL CHOICE

**Technical Details:**
- **Bit Depth**: 5 bits per weight
- **Block Size**: 32 weights per block
- **Bytes per Block**: 24-28 bytes
- **Compression Ratio**: ~2.5x (1.6 bytes per weight)

**Memory Requirements:**
- Model Memory: 2.0-3.0 GB
- VRAM for Inference: 4.5-6.0 GB (with overhead)
- Batch Size: 1-4

**Performance:**
- Inference Speed: 8-10 img/sec (RTX 4080)
- Throughput: 6-8 img/sec with batch processing
- Startup Time: 1-2 seconds

**Quality Characteristics:**
- Near-lossless quality
- Imperceptible quality difference from FP32
- Excellent detail preservation
- Colors indistinguishable from original
- Suitable for professional work
- Expert inspection reveals no differences

**Recommended Hardware:**
- RTX 4080 (16GB) - PRIMARY
- RTX 3080 (10GB)
- RTX 3090 Ti (24GB)
- Professional workstations
- Content creator systems

**Example Use Cases:**
- Professional photography/art
- High-resolution output (2k+)
- Client deliverables
- Archive-quality generation
- Research and publications

**Tradeoffs:**
- Gain: Near-lossless quality, good speed
- Loss: 40% less compression than Q4_K, slower
- Verdict: Worth it for professional results

**Tips:**
- Recommended for quality-critical work
- Minimal speed penalty over Q4_K
- File size still very manageable
- Best value for professional use

---

### Q6_K: Very High Quality (6-bit)

**Technical Details:**
- **Bit Depth**: 6 bits per weight
- **Block Size**: 64 weights per block
- **Bytes per Block**: 48 bytes
- **Compression Ratio**: ~2x (2 bytes per weight)

**Memory Requirements:**
- Model Memory: 2.5-3.5 GB
- VRAM for Inference: 5.5-7.0 GB (with overhead)
- Batch Size: 1-2

**Performance:**
- Inference Speed: 6-8 img/sec (RTX 4080)
- Throughput: 5-6 img/sec with batch processing
- Startup Time: 2-3 seconds

**Quality Characteristics:**
- Virtually identical to original FP32
- No perceptible quality loss under inspection
- Excellent for archival purposes
- Suitable for critical applications
- Research-grade quality

**Recommended Hardware:**
- RTX 4090 (24GB) - PRIMARY
- RTX 3090 (24GB)
- Professional GPU clusters
- Workstations with unlimited VRAM

**Example Use Cases:**
- Research and development
- Academic publications
- Archival quality generation
- Critical artistic work
- When speed is not a constraint

**Tradeoffs:**
- Gain: Imperceptible quality loss vs original
- Loss: Only 2x compression, slowest practical level
- Verdict: Diminishing returns for most use cases

**Tips:**
- Usually unnecessary for diffusion models
- Q5_K is better choice unless VRAM unlimited
- File size becomes significant (2GB+)
- Mainly academic interest

---

### Q8_K: Near-Lossless (8-bit)

**Technical Details:**
- **Bit Depth**: 8 bits per weight
- **Block Size**: 32 weights per block
- **Bytes per Block**: 32 bytes
- **Compression Ratio**: ~1.33x (3 bytes per weight)

**Memory Requirements:**
- Model Memory: 3.5-4.5 GB
- VRAM for Inference: 6.5-8.0 GB (with overhead)
- Batch Size: 1-2

**Performance:**
- Inference Speed: 4-6 img/sec (RTX 4080)
- Throughput: 3-4 img/sec with batch processing
- Startup Time: 3-4 seconds

**Quality Characteristics:**
- Equivalent to FP32 original
- Absolutely no quality loss
- Perfect for comparison/validation
- Research reproducibility

**Recommended Hardware:**
- RTX 4090 (24GB+)
- High-end workstations only
- Data centers with unlimited VRAM

**Example Use Cases:**
- Quality/baseline comparison
- Scientific research validation
- Before/after analysis
- Very rare production use

**Tradeoffs:**
- Gain: Perfect fidelity to original
- Loss: Minimal compression, very slow, overkill
- Verdict: Rarely justified for diffusion

**Tips:**
- Use only for research/validation
- Q6_K provides 95% of benefit with better speed
- File sizes problematic (3.5-4.5 GB)
- Not recommended for production

---

## Quantization Selection Guide

### By Hardware

**RTX 3060 / RTX 4060 (8-12GB VRAM)**
- Recommended: Q4_K
- Alternative: Q3_K (if tight on VRAM)
- Max Quality: Q4_K

**RTX 4070 / RTX 3070 (12-16GB VRAM)**
- Recommended: Q4_K
- Alternative: Q5_K (with SDXL)
- Max Quality: Q5_K

**RTX 4080 / RTX 3080 (16GB VRAM)**
- Recommended: Q5_K
- Alternative: Q4_K (for speed)
- Max Quality: Q5_K

**RTX 3090 / RTX 4090 (24GB VRAM)**
- Recommended: Q5_K or Q6_K
- Alternative: Q8_K (for research)
- Max Quality: Q8_K or F32

### By Use Case

**Real-time Preview**
- Q3_K to Q4_K
- Priority: Speed > Quality

**Professional Production**
- Q4_K to Q5_K
- Priority: Quality = Speed

**High Resolution (2K+)**
- Q5_K to Q6_K
- Priority: Quality > Speed

**Research/Publishing**
- Q6_K to Q8_K
- Priority: Quality over all

**Mobile/Edge**
- Q2_K to Q3_K
- Priority: Size reduction

### By Model Type

**Stable Diffusion 1.5**
- Excellent: Q4_K
- Good: Q3_K
- Best: Q5_K

**SDXL (Larger)**
- Recommended: Q4_K (with LoRA) or Q5_K
- Alternative: Q3_K (extreme VRAM constraint)

**Specialized Models**
- Generally: Q4_K-Q5_K depending on size
- Test: Always benchmark for your specific model

## Quality Metrics

### Perceptual Quality

| Level | vs Original | Detectability | Artifacts |
|-------|-------------|----------------|-----------|
| Q2_K | -25% | Obvious | Severe |
| Q3_K | -10% | Noticeable | Visible |
| Q4_K | -2% | Expert only | Minimal |
| Q5_K | -0.5% | Imperceptible | None |
| Q6_K | -0.1% | Imperceptible | None |
| Q8_K | 0% | None | None |

### LPIPS Scores (Lower is Better)

Lower Perceptual Image Patch Similarity indicates better quality:

```
Q2_K: 0.15-0.25 (poor)
Q3_K: 0.05-0.10 (fair)
Q4_K: 0.01-0.03 (good)
Q5_K: 0.001-0.01 (excellent)
Q6_K: <0.001 (near-perfect)
Q8_K: ~0 (perfect)
```

## Conversion Considerations

### When Converting

1. **Start with Q4_K**
   - Default choice for unknown scenarios
   - Excellent balance point
   - Easy to verify quality

2. **Test Quality First**
   - Generate test images with identical seed
   - Compare visually before deployment
   - Check against original FP32 if available

3. **Monitor File Size**
   - Smaller ≠ automatically better
   - Q4_K usually sufficient
   - Larger models may need lower levels

### Common Mistakes

1. Using Q2_K or Q3_K for production
   - Results in visible artifacts
   - Hard to fix after delivery

2. Using Q8_K unnecessarily
   - Minimal quality benefit
   - Wastes storage and VRAM
   - Slower than needed

3. Not testing quantization
   - Always verify with sample generation
   - Quality varies by model architecture
   - Better to test than assume

## Summary

- **Recommended**: Start with Q4_K for consumer, Q5_K for professional
- **Balance Point**: Q4_K provides 95% of quality at 75% of original size
- **Speed**: Q3_K for real-time, Q4_K for batch
- **Quality**: Q5_K minimum for delivery, Q6_K+ only for research
- **Hardware**: Match quantization to VRAM availability
- **Always test**: Benchmark before production deployment
