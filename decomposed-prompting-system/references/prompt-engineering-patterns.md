# Prompt Engineering Patterns

## Token Density & Context Structure

Effective AI image generation depends on prompt token optimization. This document covers patterns for creating high-quality, context-rich prompts from UI components.

## Core Principles

### 1. Token Density

**Definition**: The ratio of meaningful, weighted tokens to total tokens in a prompt.

**Target Density for Miniature Painting**: 70-85% meaningful tokens

**Example Low Density (Bad)**:
```
"A miniature of armor that is weathered and painted with steel color
and has some shine and might be a sword or shield with some detail"
```
- 34 tokens, only 12 meaningful = 35% density (TOO LOW)

**Example High Density (Good)**:
```
"Weathered steel plate armor, polished finish, metallic sheen,
dramatic lighting, hyper-detailed, masterpiece, 8k"
```
- 17 tokens, 15 meaningful = 88% density (GOOD)

### 2. Context Hierarchy

Structure prompts in priority order:

1. **PRIMARY** (Subject & Key Attributes)
   - What is being painted?
   - What material/finish?
   - What condition/wear?

2. **SECONDARY** (Details & Modifiers)
   - Specific effects (rust, patina, chipping)
   - Material qualities (reflectivity, texture)
   - Artistic style indicators

3. **TERTIARY** (Quality & Rendering)
   - Quality level (masterpiece, hyper-detailed)
   - Rendering style (photorealistic, cinematic)
   - Resolution (8k, 4k)

**Prompt Template Pattern**:
```
[PRIMARY: subject + key attributes]
[SECONDARY: details + modifiers]
[TERTIARY: quality + style]
```

### 3. Semantic Clustering

Group related concepts together in the prompt:

**GOOD** (Clustered by semantic meaning):
```
"weathered steel, rust streaks, oxidized patina,
polished metal highlights, brushed surface,
dramatic side lighting, volumetric shadows"
```

**BAD** (Scattered semantically):
```
"weathered, dramatic, steel, polished, rust,
shadows, oxidized, lighting, brushed, patina"
```

## Component-to-Token Mapping Patterns

### Pattern 1: Slider Values

**Intensity Mapping** (for weather, detail, shine):

```python
0-25%   → "light/subtle" token, weight 0.5
25-50%  → "moderate" token, weight 0.7
50-75%  → "heavy/pronounced" token, weight 1.0
75-100% → "extreme/maximal" token, weight 1.3-1.5
```

**Example - Weathering Slider**:
```
0% (Pristine)      → "pristine, mirror polish"
25% (Light)        → "lightly weathered, minor scratches"
50% (Moderate)     → "weathered patina, visible wear"
75% (Heavy)        → "heavily weathered, deep corrosion"
100% (Battle-Worn) → "battle-worn, severe damage"
```

### Pattern 2: Dropdown Selections

**One-to-Many Mapping** (category to multiple tokens):

```python
{
    "category": ["primary_token", "supporting_token", "tertiary_token"]
}
```

**Example - Material Dropdown**:
```python
{
    "metal": ["polished steel", "metallic sheen", "reflective surface"],
    "brass": ["burnished brass", "warm gold tone", "corrosion marks"],
    "leather": ["tooled leather", "aged patina", "subtle wear"]
}
```

**Expansion Rule**: Primary token is weighted highest, supporters add context.

### Pattern 3: Color Picker

**RGB to Semantic Color**:

```python
def rgb_to_color_tokens(r, g, b):
    """
    Convert RGB values to color tokens with undertones
    and intensity modifiers
    """
    brightness = (r + g + b) / 3
    dominant_hue = determine_hue(r, g, b)

    return {
        "base_color": color_name(dominant_hue),
        "undertone": undertone_modifier(r, g, b),
        "intensity": brightness_to_intensity(brightness)
    }
```

**Example - Silver Color (#c0c0c0)**:
```
RGB(192, 192, 192)
→ Base Color: "silver"
→ Undertone: "cool metallic"
→ Intensity: "bright, highly reflective"
→ Full Token: "bright silver with cool metallic tones"
```

### Pattern 4: Toggle Groups

**Boolean Modifiers** (active toggles combined with AND logic):

```python
active_toggles = ["add_shadows", "add_rust", "add_verdigris"]
→ "strategic shadows, rust streaks, green patina"
```

**Logical Combination Rule**:
```
IF toggle_1 AND toggle_2 AND toggle_3
THEN combine all corresponding modifiers
```

## Prompt Quality Hierarchy

### Tier 1: Minimal (Avoid)
- 5-8 tokens
- Single concept focus
- No quality indicators
- Example: "weathered armor"

### Tier 2: Basic (Accept)
- 12-15 tokens
- Multiple concepts
- Single quality token
- Example: "weathered steel armor, polished finish, detailed"

### Tier 3: Standard (Target)
- 18-25 tokens
- Multiple concept clusters
- Quality + style indicators
- Lighting mentioned
- Example: "weathered steel plate armor, polished finish, dramatic side lighting, highly detailed, professional miniature painting"

### Tier 4: Advanced (Ideal)
- 25-35 tokens
- Rich semantic clusters
- Multiple quality layers
- Specific effects
- Weighted emphasis
- Example: "(weathered steel armor:1.2) with oxidized patina, polished highlights, dramatic rim lighting, (subsurface scattering:1.1), hyper-detailed, photorealistic, 8k resolution, masterpiece"

## Upsampling Process

Transform simple UI input → token-dense prompt:

### Stage 1: Semantic Expansion
```
Input:     "Weathered metal"
Expanded:  "weathered steel", "oxidized surface", "patina"
```

### Stage 2: Attribute Addition
```
Materials → Finish: "weathered steel" → "weathered steel, matte finish"
```

### Stage 3: Effect Injection
```
Add effects based on UI toggles and sliders
"weathered steel, matte finish" → "weathered steel, matte finish, rust streaks"
```

### Stage 4: Quality Tokens
```
Add quality tier from detail_level slider
→ "highly detailed" or "hyper-detailed" or "professional grade"
```

### Stage 5: Weighting Application
```
Apply emphasis to key concepts
→ "(weathered steel:1.2) matte finish rust streaks"
```

## Specific Domains

### Miniature Painting Vocabulary Patterns

**Materials** cluster:
```
[material_name], [finish_type], [texture_descriptor]
"polished steel, gloss enamel, mirror-like surface"
```

**Effects** cluster:
```
[primary_effect], [secondary_effect], [accumulation]
"rust streaks, oxidized patina, dust accumulation"
```

**Lighting** cluster:
```
[light_type], [direction], [intensity], [quality]
"dramatic rim lighting, side-angled, strong contrast, cinematic"
```

**Quality** cluster:
```
[detail_level], [rendering_style], [resolution], [artisan_mark]
"hyper-detailed, photorealistic, 8k, masterpiece"
```

## Common Mistakes to Avoid

### 1. Redundancy
```
BAD:  "metallic metal steel shiny reflective"
GOOD: "polished steel, highly reflective"
```

### 2. Conflicting Modifiers
```
BAD:  "pristine weathered armor"
GOOD: "lightly weathered armor" (choose one intensity)
```

### 3. Vague Modifiers
```
BAD:  "nice colors" "cool effect" "pretty design"
GOOD: "vibrant undertones" "verdigris patina" "master-crafted details"
```

### 4. Missing Context
```
BAD:  "armor with rust"
GOOD: "weathered steel armor with surface rust streaks and oxidized patina"
```

### 5. Insufficient Weighting
```
BAD:  "detailed weathered armor highly weathered"
GOOD: "(heavily weathered:1.2) steel armor (rust streaks:1.1), detailed"
```

## Testing Prompt Quality

**Checklist for Evaluating Generated Prompts**:

- [ ] Density: 70%+ meaningful tokens
- [ ] Hierarchy: Primary concepts first
- [ ] Clustering: Semantic terms grouped
- [ ] Specificity: No vague terms ("nice", "cool", "good")
- [ ] Weight Balance: Key concepts emphasized appropriately
- [ ] Coherence: Concepts complement each other (no conflicts)
- [ ] Domain Accuracy: Uses miniature painting terminology
- [ ] Quality Indicators: Includes rendering quality tokens
- [ ] Completeness: Material, finish, lighting, quality all present
- [ ] Conciseness: No redundancy

## Template Structure Examples

### Armor Template
```
[Subject: miniature type + material]
[Condition: weathering level + effects]
[Finish: surface type + reflectivity]
[Lighting: light type + direction + intensity]
[Quality: detail + style + resolution]
```

### Fabric Template
```
[Subject: clothing type + material]
[Color: base + undertone + saturation]
[Wear: damage pattern + aging]
[Texture: fabric properties + woven structure]
[Quality: detail + lighting + style]
```

### Base/Terrain Template
```
[Subject: terrain type + composition]
[Vegetation: plant type + density]
[Weathering: age + erosion + accumulation]
[Features: rocks + water + structures]
[Quality: detail + lighting + style]
```

## Performance Implications

**Token Count Impact**:
- Too few (5-10 tokens): 50% quality reduction
- Minimal (12-15 tokens): 20% quality reduction
- Standard (18-25 tokens): Baseline quality
- Rich (25-35 tokens): 15% quality improvement
- Excessive (40+ tokens): Diminishing returns

**Recommendation**: Target 22-30 tokens for optimal quality/efficiency balance.

## Integration with Image Models

### Stable Diffusion
- Native support for weighted syntax: `(concept:weight)`
- Optimal weights: 0.8-1.3 range
- Test different weights for each concept

### ComfyUI
- Supports advanced weighting
- Can use embeddings directly
- Allows conditional logic in prompts

### Flux Kontext
- Advanced instruction following
- Less dependent on token weight
- Can handle more complex semantic structures
