# Concept Embeddings

Pre-trained textual inversion embeddings for controlling miniature painting prompts through sliders and UI components.

## Available Embeddings

### Weathering Embeddings

**Purpose**: Control weathering intensity from pristine to battle-worn

- `weathering_light.bin` - Light weathering (0-30% intensity)
- `weathering_moderate.bin` - Moderate weathering (40-60% intensity)
- `weathering_heavy.bin` - Heavy weathering (70-100% intensity)

**Usage in Prompts**:
```
<embedding:weathering_0> - pristine surface
<embedding:weathering_50> - moderately weathered
<embedding:weathering_100> - battle-worn
```

### Metallic Shine Embeddings

**Purpose**: Control reflectivity and shine from matte to mirror polish

- `metallic_matte.bin` - Matte finish (0-30% shine)
- `metallic_satin.bin` - Satin finish (40-60% shine)
- `metallic_gloss.bin` - Glossy finish (70-100% shine)

**Usage in Prompts**:
```
<embedding:metallic_matte> - no reflection
<embedding:metallic_satin> - subtle sheen
<embedding:metallic_gloss> - mirror polish
```

### Detail Level Embeddings

**Purpose**: Control complexity and detail density

- `detail_basic.bin` - Basic detail level
- `detail_moderate.bin` - Moderate detail
- `detail_high.bin` - Highly detailed
- `detail_hyper.bin` - Hyper-detailed

**Usage in Prompts**:
```
<embedding:detail_basic> - simple brushwork
<embedding:detail_hyper> - intricate fine details
```

### Rust & Corrosion Embeddings

**Purpose**: Control rust and corrosion appearance on metals

- `rust_light.bin` - Light surface rust
- `rust_moderate.bin` - Moderate oxidation
- `rust_heavy.bin` - Deep corrosion and pitting

**Usage in Prompts**:
```
<embedding:rust_light> - minor discoloration
<embedding:rust_heavy> - extensive corrosion
```

### Patina Embeddings

**Purpose**: Control aged patina on various metals

- `patina_copper.bin` - Green/blue copper patina
- `patina_silver.bin` - Tarnished silver patina
- `patina_bronze.bin` - Brown bronze patina
- `patina_aged.bin` - Universal aged patina

**Usage in Prompts**:
```
<embedding:patina_copper> - verdigris appearance
<embedding:patina_aged> - general aging
```

### Material Texture Embeddings

**Purpose**: Control specific material texture characteristics

- `texture_ceramic.bin` - Smooth glazed ceramic
- `texture_fabric.bin` - Woven cloth texture
- `texture_leather.bin` - Aged leather texture
- `texture_wood.bin` - Carved wood grain
- `texture_stone.bin` - Rough stone surface

**Usage in Prompts**:
```
<embedding:texture_leather> - tooled leather appearance
<embedding:texture_fabric> - woven textile pattern
```

### Lighting Style Embeddings

**Purpose**: Control lighting mood and style

- `light_dramatic.bin` - Dramatic high-contrast lighting
- `light_studio.bin` - Even studio lighting
- `light_rim.bin` - Rim/backlighting effect
- `light_ambient.bin` - Soft ambient light

**Usage in Prompts**:
```
<embedding:light_dramatic> - cinematic dramatic shadows
<embedding:light_rim> - edge-lit silhouette glow
```

## How to Use Embeddings

### In Python

```python
from prompt_generator import PromptGenerator

# Initialize generator
generator = PromptGenerator(
    embeddings_path="assets/concept-embeddings/"
)

# Use embedding in prompt
weathering_embedding = generator.embeddings["weathering"].interpolate(65)
prompt = f"{weathering_embedding} steel armor, detailed"
```

### Direct File Reference

Embeddings can be referenced directly in prompts using Stable Diffusion embedding syntax:

```
<embedding:weathering_65> armor with rust streaks
```

### Interpolation

For slider-based control, interpolate between light and heavy embeddings:

```python
intensity = 65  # 0-100 slider value
light_embedding = load_embedding("weathering_light.bin")
heavy_embedding = load_embedding("weathering_heavy.bin")

interpolated = lerp(light_embedding, heavy_embedding, intensity / 100.0)
```

## Training Your Own Embeddings

To train custom embeddings for specific concepts:

1. **Collect Training Data**: 50-100 images representing the concept
2. **Use Training Script**: See parent directory for training utilities
3. **Place Output**: Save in this directory with clear naming
4. **Document**: Add entry to README with usage examples

**Example Training Script**:
```python
from textual_inversion import train_embedding

train_embedding(
    concept_name="custom_weathering",
    data_path="training_data/weathering/",
    output_path="assets/concept-embeddings/custom_weathering.bin",
    epochs=150
)
```

## File Format

Embeddings are stored in PyTorch binary format (`.bin`) for compatibility:

- **Format**: PyTorch `.pt` or `.bin` (SafeTensors `.safetensors`)
- **Compression**: None (raw tensor)
- **Size**: 2-10MB per embedding
- **Vector Dimension**: 768 (for CLIP embeddings)

## Performance Notes

- **Load Time**: ~100ms per embedding
- **Interpolation Time**: ~5ms per blend
- **VRAM Required**: 2-5MB per embedding
- **Inference Impact**: ~30% faster than LoRA

## Compatibility

These embeddings are trained for and compatible with:

- **Stable Diffusion v1.4+**: Full support
- **Stable Diffusion XL**: Requires adapter conversion
- **ComfyUI**: Native support via embedding nodes
- **A1111 WebUI**: Drag-and-drop to embeddings folder
- **Diffusers library**: Load via `pipeline.load_textual_inversion()`

## Updating & Extending

Check periodically for improved embedding versions. New embeddings may be added for:

- Specific paint finish types
- Historical armor styles
- Fantasy aesthetic styles
- Material-specific effects
- Advanced lighting setups

## Support

For issues with embeddings:

1. Verify embedding file integrity
2. Check model compatibility
3. Try alternative interpolation methods
4. Review prompt context for conflicts
5. Retrain if quality is insufficient
