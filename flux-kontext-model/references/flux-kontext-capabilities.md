# FLUX.1 Kontext Capabilities Reference

## In-Context Editing

FLUX.1 Kontext's primary strength is understanding and editing existing image content while preserving context and consistency.

### Editing Modes

#### Full Image Editing
- Regenerate entire image with context awareness
- Preserve composition and spatial relationships
- Suitable for style transfer and aesthetic refinement
- Use case: Changing lighting conditions on a miniature painting

#### Inpainting (Mask-based Editing)
- Edit specific regions using binary or soft masks
- Preserve untouched areas with perfect continuity
- Feather edges automatically for seamless blending
- Use case: Fixing painting details or replacing objects

#### Outpainting
- Extend images beyond original boundaries
- Maintain consistency with existing content
- Useful for cropping recovery
- Use case: Expanding miniature base composition

#### Style Transfer
- Apply artistic styles while preserving content
- Maintain spatial structure and object identity
- Work with multiple style reference images
- Use case: Converting between painting techniques (acrylic to oil)

### Context Preservation Features

1. **Spatial Awareness**
   - Understands relative positioning of objects
   - Preserves compositional balance
   - Maintains perspective consistency
   - Respects existing shadows and highlights

2. **Artistic Consistency**
   - Preserves painting technique characteristics
   - Maintains color harmony and palette
   - Keeps brushwork style consistent
   - Adapts to existing texture patterns

3. **Context Images**
   - Up to 8 reference images simultaneously
   - Adjustable influence weights per image
   - Separate style and content influences
   - Hierarchical context blending

### Quality Indicators

- **Consistency Score:** Measures deviation from context (0-100)
  - 90-100: Excellent consistency (recommended)
  - 75-89: Good consistency, minor artifacts acceptable
  - Below 75: Use stronger guidance or additional context images

- **Edge Continuity:** Seamless blending at edit boundaries
  - Automatic feathering in inpainting mode
  - No visible seams with proper masking
  - Gradient preservation across boundaries

## Multi-Image Control

FLUX.1 Kontext excels at processing multiple images to guide generation.

### Supported Configurations

#### Dual Reference (2 Images)
- One style reference + one content reference
- Typical use: Applying existing miniature style to new subject
- Balance with `context_weight: 0.7`

#### Quad Reference (4 Images)
- Multiple angles or iterations
- Consistency enforcement across variations
- Better detail preservation
- Recommended for product photography workflows

#### Extended Reference (6-8 Images)
- Comprehensive style documentation
- Complex multi-element subjects
- High consistency requirements
- Use for batch processing with galleries

### Control Mechanisms

#### Influence Weights
```
context_weight: 0.0-1.0
  0.0: Ignore all context (pure generation)
  0.3-0.5: Light context influence (creative)
  0.6-0.8: Strong context influence (consistent)
  0.9-1.0: Maximum context adherence (edit mode)
```

#### Blending Strategies
1. **Average Blending:** Equal influence from all references
2. **Weighted Blending:** Differential influence per image
3. **Sequential Blending:** Hierarchical context processing
4. **Masking-based:** Regional influence control

#### Multi-Image Consistency
- Enforces feature alignment across outputs
- Maintains color palette consistency
- Preserves lighting direction
- Synchronizes detail level

## Output Controls

### Aspect Ratio Preservation

FLUX.1 Kontext reliably maintains specified aspect ratios without artifacts:

**Standard Ratios:**
- **1:1 (Square):** 512x512, 768x768, 1024x1024
- **4:3 (Standard):** 768x576, 1024x768
- **16:9 (Widescreen):** 1024x576, 1360x768
- **3:2 (Photography):** 960x640, 1440x960

**Custom Ratios:**
- Any ratio supported with 64-pixel multiples
- Maximum resolution: 1536x1536 (full) or tiled
- Minimum resolution: 512x512 (acceptable quality)

### Resolution Control

| Resolution | Quality | Speed | Memory | Use Case |
|-----------|---------|-------|--------|----------|
| 512x512 | Good | Fast | 6GB | Previews, thumbnails |
| 768x768 | Excellent | Moderate | 12GB | Standard production |
| 1024x1024 | Excellent | Slow | 16GB+ | Premium quality |
| 1536x1536 | Maximum | Very Slow | Requires tiling | Poster/print |

### Guidance Scale Control

Guidance scale influences how strongly the model adheres to the prompt and context:

```
0.0-2.0: Minimum guidance (creative, unpredictable)
3.0-4.0: Light guidance (flexible)
5.0-7.0: Recommended range (balanced)
8.0-10.0: Strong guidance (literal adherence)
10.0+: Extreme guidance (potential artifacts)
```

**For FLUX.1 Kontext specifically:**
- Optimal range: 5.0-7.0
- With Lightning LoRA: reduce to 1.5-2.0
- For context editing: 6.0-7.5
- For creative variation: 3.5-5.0

### Seed Control

Deterministic generation for reproducibility:
- Set `seed` parameter for identical results
- Use `seed: -1` for random generation
- Batch processing with sequential seeds for variations

## Performance Characteristics

### Inference Speed Baselines (RTX 4090)

| Configuration | Steps | Time | Notes |
|--------------|-------|------|-------|
| Full Precision bfloat16 | 28 | ~45s | Maximum quality |
| Q5_K Quantization | 20 | ~25s | Quality/speed balance |
| Q4_K Quantization | 20 | ~18s | Recommended for production |
| Q3_K Quantization | 20 | ~12s | Memory-constrained |
| Q4_K + Lightning LoRA | 8 | ~8s | Real-time capable |

### Memory Requirements

| Format | Peak VRAM | Model Size | Quality Impact |
|--------|-----------|-----------|-----------------|
| bfloat16 | 24GB | 24GB | 100% reference |
| Q5_K | 10GB | 6.5GB | 99% of full |
| Q4_K | 8GB | 5.2GB | 97-98% of full |
| Q3_K | 6GB | 3.8GB | 95% of full |

### Batch Processing

- Optimal batch size: 2-4 images (RTX 4090)
- Memory scales linearly with batch size
- Sequential processing recommended for <8GB VRAM
- Context encoding can be cached across batch

## Integration Points

### With ComfyUI
- Native nodes for context editing
- Multi-image loading via image stacking
- LoRA loading in sampler configuration
- Batch processing pipeline ready

### With Diffusers
- `AutoPipelineForInpainting` for editing
- `DiffusionPipeline.from_pretrained()` for loading
- Scheduler integration (EulerDiscreteScheduler recommended)
- Memory-efficient inference modes

### With llama.cpp / GGUF
- Direct quantized model loading
- No GPU compilation required
- CPU inference feasible for batch processing
- Context caching across sequences

## Known Limitations

1. **Maximum images:** 8 simultaneous reference images
2. **Maximum resolution:** 1536x1536 before tiling required
3. **Context blur:** Very low context weights may lose details
4. **Prompt length:** Optimal at 75-150 tokens
5. **Aspect ratio extremes:** Below 0.5 or above 2.0 may degrade

## Optimization Tips

1. Use Q4_K quantization for production workflows (best speed/quality)
2. Combine with Lightning LoRA for real-time applications
3. Cache context encodings when batch editing
4. Use 768x768 as sweet spot for quality/performance
5. Leverage inpainting for precise edits over full regeneration
