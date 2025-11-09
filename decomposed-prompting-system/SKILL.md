---
name: decomposed-prompting-system
description: Build UI-driven prompt generation system that hides complexity from users for miniature painting workflows. Use when implementing component breakdown UI (sliders, dropdowns, color pickers), creating prompt templates, upsampling simple inputs to token-dense prompts, implementing textual inversion for prompt sliders, or generating context-rich prompts from UI state.
---

# Decomposed Prompting System

## Overview

The Decomposed Prompting System enables non-technical users to control complex AI image generation through intuitive UI components. Convert simple UI interactions into highly detailed prompts optimized for miniature painting image generation. Hide prompt engineering complexity behind sliders, dropdowns, and color pickers while generating token-dense prompts that produce consistent, high-quality results.

## Core Concepts

### 1. UI Component Breakdown

Decompose complex prompts into manageable UI elements:

- **Sliders**: Numeric intensity controls (weathering 0-100%, metallic shine 0-100%)
- **Dropdowns**: Categorical selections (paint finish: matte/satin/gloss, era: medieval/sci-fi/modern)
- **Color Pickers**: Direct color specification for base coat, highlights, shadows
- **Toggle Groups**: Boolean modifiers (add shadows, add weathering, add highlights)
- **Text Inputs**: User-provided details (miniature name, special effects)

**Example Component Mapping:**
```
Weathering Slider (0-100%)
  0-20% → "pristine"
  20-50% → "lightly weathered"
  50-80% → "heavily weathered"
  80-100% → "battle-worn"
```

### 2. Prompt Template Engine Architecture

Structured template system with placeholder substitution:

- Base template structure with semantic sections
- Conditional sections based on UI state
- Modifier chains for intensity-based variations
- Context injection for domain-specific knowledge

**Template Structure Pattern:**
```
[base_description] [material_details] [paint_qualities]
[lighting] [atmosphere] + [conditional_modifiers]
```

### 3. Prompt Upsampling (Simple → Token-Dense)

Convert minimal user input into rich, detailed prompts:

```
Input:  "Weathered armor, metallic finish"
Output: "Intricately detailed weathered plate armor with oxidized patina,
         brushed steel finish, rust streaks, dramatic side lighting,
         cinematic quality, highly detailed, 8k resolution..."
```

**Upsampling Process:**
1. Parse UI state into semantic components
2. Expand each component using domain vocabulary
3. Add contextual modifiers and quality tokens
4. Inject lighting and atmospheric details
5. Apply weighting and emphasis markers

### 4. Textual Inversion Embeddings for Sliders

Use pre-trained embeddings to control concept intensity without fine-tuning:

- **Weathering Slider**: Maps 0-100% to embedding interpolation
- **Metallic Shine**: Controls surface reflection emphasis
- **Color Intensity**: Modulates color saturation in embeddings
- **Detail Level**: Scales complexity token weight

**Performance Advantage**: 30% faster than LoRA, lower memory footprint, real-time slider responsiveness.

### 5. Miniature Painting Vocabulary

Domain-specific terminology ensures quality outputs:

**Materials**: metallic, matte, satin, glazed, weathered, patinated, oxidized, brushed, polished
**Finishes**: glossy, matte, satin, lacquered, enameled, powder-coated
**Effects**: weathering, rust, patina, verdigris, chipping, scratches, dust, grime, moss
**Lighting**: dramatic, rim lighting, subsurface scattering, volumetric light, backlighting
**Quality**: hyper-detailed, photorealistic, cinematic, 8k, masterpiece, museum quality

### 6. UI State → Prompt Mapping Patterns

Consistent patterns for converting UI interactions to prompt modifications:

```python
# Slider mapping: intensity value to token and weight
slider_value (0-100%) → intensity_token + emphasis_weight

# Dropdown selection: categorical choice to token set
selected_option → primary_token + supporting_tokens

# Color picker: RGB to color tokens
RGB(r,g,b) → dominant_color_token + undertone + intensity

# Toggle group: active toggles combined
active_toggles → [modifier_1, modifier_2, ...] + AND logic
```

## Implementation Guide

### Step 1: Define UI Components

Create component definitions with mapping rules:

```python
components = {
    "weathering": {
        "type": "slider",
        "min": 0, "max": 100,
        "mappings": {
            (0, 20): "pristine",
            (20, 50): "lightly weathered",
            (50, 80): "heavily weathered",
            (80, 100): "battle-worn"
        },
        "embedding": "weathering_slider"
    },
    "material": {
        "type": "dropdown",
        "options": ["metal", "ceramic", "wood", "leather"],
        "tokens": {
            "metal": "polished steel, metallic sheen, reflective surface",
            "ceramic": "glazed ceramic, smooth glossy surface"
        }
    },
    "base_color": {
        "type": "color_picker",
        "token_template": "{color} base coat"
    }
}
```

### Step 2: Create Prompt Templates

Build templates with placeholders:

```
A beautifully painted {miniature_type}: {material_description},
{color_description}, {weathering_effects}, {finish_type},
{lighting_setup}, professional miniature painting, highly detailed
```

### Step 3: Implement Upsampling

Use `generate-prompt-from-ui.py` to convert UI state:

```python
from prompt_generator import PromptGenerator

generator = PromptGenerator(
    templates_path="assets/prompt-templates/",
    embeddings_path="assets/concept-embeddings/"
)

ui_state = {
    "weathering": 65,
    "material": "metal",
    "base_color": "#c0c0c0",
    "add_shadows": True
}

prompt = generator.generate(ui_state, template="armor")
```

### Step 4: Apply Textual Inversion

Reference embeddings for intensity control:

```python
weathering_embedding = interpolate_embedding(
    light_embedding,
    heavy_embedding,
    intensity=0.65
)

final_prompt = f"{weathering_embedding} {base_prompt}"
```

## Use Cases

### Armor Painting
- Material selector (steel, brass, copper, iron, gold)
- Weathering slider (pristine to battle-worn)
- Rust pattern dropdown (surface rust, deep corrosion, green patina)
- Metallic shine slider (0-100%)
- Lighting style selector (dramatic, studio, ambient)

### Fabric & Clothing
- Texture dropdown (silk, wool, linen, leather, fur)
- Color picker with undertone options
- Wear pattern slider (new, worn, tattered, decaying)
- Dye fade and stain toggles
- Stitch detail level

### Bases & Terrain
- Material selector (grass, stone, sand, water, wood, concrete)
- Weathering/aging slider
- Plant density toggle
- Lighting angle selector
- Dust/debris/moss effect slider

### Skin & Faces
- Skin tone picker with undertone
- Blemish/age slider
- Highlight intensity slider
- Emotion/expression dropdown
- Lighting mood selector (warm, cool, dramatic)

## Performance Considerations

- **Caching**: Cache generated prompts for identical UI states
- **Lazy Loading**: Load embeddings on-demand
- **Batch Processing**: Process multiple UI states for preview generation
- **Streaming**: Return prompt refinements incrementally

## Integration with Image Generation

Works with popular AI image generation backends:
- **Stable Diffusion** (native prompt support)
- **ComfyUI** (workflow integration)
- **Flux Kontext** (advanced control)
- **Custom models** (trained on miniature painting data)

Apply weighting syntax compatible with your backend:
```
(highly detailed miniature armor:1.3) (weathered metal:1.2) (dramatic lighting:1.1)
```

## File Organization

- `scripts/generate-prompt-from-ui.py` - Core prompt generation engine
- `references/prompt-engineering-patterns.md` - Token density and structure patterns
- `references/textual-inversion-embeddings.md` - Embedding interpolation techniques
- `references/prompt-template-system.md` - Template engine architecture details
- `references/miniature-painting-vocabulary.md` - Complete domain terminology
- `assets/prompt-templates/` - Pre-built templates for common miniatures
- `assets/concept-embeddings/` - Pre-trained embeddings for sliders

## Next Steps

1. Review `references/prompt-template-system.md` for architecture details
2. Study `scripts/generate-prompt-from-ui.py` for implementation patterns
3. Copy templates from `assets/prompt-templates/` as starting points
4. Configure UI components and slider mappings for your application
5. Test prompt generation with your chosen image model
6. Fine-tune embeddings for specialized use cases
