# Prompt Templates Reference

Pre-built prompt templates for common miniature painting scenarios.

## Available Templates

### armor.txt
**Use For**: Armor pieces, plate mail, chest armor, shields, helmets

**Placeholders**:
- `{material_description}` - Material type (steel, brass, copper, etc.)
- `{base_color}` - Primary color (silver, gold, bronze, etc.)
- `{finish_type}` - Surface finish (matte, satin, gloss, lacquered)
- `{weathering_effects}` - Weathering description (pristine, weathered, battle-worn)
- `{lighting_style}` - Light type (dramatic, studio, ambient, rim)
- `{detail_level}` - Detail intensity (basic, moderate, highly detailed, hyper-detailed)

**Example Output**:
```
A beautifully painted suit of polished steel armor: silver, satin,
heavily weathered, dramatic side lighting, highly detailed, professional
miniature painting, masterpiece quality
```

### weapon.txt
**Use For**: Swords, axes, bows, spears, fantasy weapons

**Placeholders**:
- `{miniature_type}` - Weapon name/type
- `{material_description}` - Material and properties
- `{base_color}` - Color scheme
- `{weathering_effects}` - Age and condition
- `{finish_type}` - Surface quality
- `{lighting_style}` - Lighting setup
- `{detail_level}` - Detail amount

**Example Output**:
```
Intricately detailed painted fantasy sword: burnished steel, silver,
rust streaks and battle scars, gloss finish, dramatic backlighting,
highly detailed, fantasy weapon art, professional miniature painting
```

### character.txt
**Use For**: Character miniatures, NPCs, player characters, figures with faces

**Placeholders**:
- `{base_color}` - Skin tone and color
- `{material_description}` - Armor materials
- `{weathering_effects}` - Wear and age
- `{lighting_style}` - Face lighting
- `{finish_type}` - Surface quality
- `{detail_level}` - Portrait detail level

**Example Output**:
```
Fantasy character miniature: warm complexion, polished steel armor,
battle scars and weathering, dramatic rim lighting, satin finish,
highly detailed, professional miniature painting, masterpiece
```

### base.txt
**Use For**: Display bases, dioramas, terrain, scenic elements

**Placeholders**:
- `{material_description}` - Base material (earth, rock, grass, water)
- `{base_color}` - Color palette
- `{weathering_effects}` - Age and erosion
- `{lighting_style}` - Mood lighting
- `{finish_type}` - Surface treatment
- `{detail_level}` - Environmental detail

**Example Output**:
```
Miniature base terrain: weathered stone and moss, earthy tones,
aged with moss growth, dappled forest lighting, matte finish,
highly detailed, environmental storytelling, tabletop gaming quality
```

### fabric.txt
**Use For**: Clothing, cloaks, flags, fabric elements, robes

**Placeholders**:
- `{material_description}` - Fabric type (silk, wool, linen, leather)
- `{base_color}` - Fabric color
- `{texture_description}` - Weave and pattern
- `{wear_pattern}` - Condition and damage
- `{lighting_style}` - Fabric lighting
- `{finish_type}` - Surface quality
- `{detail_level}` - Stitch detail level

**Example Output**:
```
Detailed miniature clothing: silk fabric, deep purple, visible weaving
pattern, well-worn folds and creases, studio lighting, matte satin
finish, highly detailed, professional miniature painting, intricate
stitching detail
```

### generic.txt
**Use For**: Any miniature type when specific template doesn't apply

**Placeholders**:
- `{material_description}` - Primary materials
- `{base_color}` - Color scheme
- `{weathering_effects}` - Condition
- `{lighting_style}` - Light setup
- `{finish_type}` - Surface finish
- `{detail_level}` - Detail amount

**Example Output**:
```
Professionally painted miniature: polished brass, gold, light patina,
dramatic rim lighting, gloss finish, highly detailed, professional
miniature painting, masterpiece quality
```

## Placeholder Value Reference

### Material Descriptions
```
Metals:
"polished steel", "burnished brass", "bright copper", "oxidized iron",
"lustrous gold", "tarnished silver", "dark bronze"

Non-Metals:
"tooled leather", "glazed ceramic", "carved wood", "aged bone",
"woven fabric", "natural stone", "polished marble"
```

### Base Colors
```
"silver", "gold", "bronze", "copper", "crimson red", "deep blue",
"emerald green", "gunmetal gray", "ivory white", "jet black"
```

### Finish Types
```
"matte finish", "satin sheen", "gloss finish", "lacquered surface",
"enameled coating", "brushed metal", "polished surface"
```

### Weathering Effects
```
"pristine", "lightly weathered", "moderately weathered",
"heavily weathered", "battle-worn", "weathered and aged",
"oxidized patina", "rust streaks", "verdigris", "aged gracefully"
```

### Lighting Styles
```
"dramatic side lighting", "studio lighting", "ambient evening light",
"rim backlighting", "spotlight", "volumetric light rays",
"soft diffused light", "dramatic shadows"
```

### Detail Levels
```
"basic detail", "moderately detailed", "highly detailed",
"hyper-detailed", "intricate detail", "museum quality craftsmanship",
"professional grade detail"
```

## Quick Template Selection

| Miniature Type | Recommended Template |
|---|---|
| Plate armor | armor.txt |
| Helmet | armor.txt |
| Shield | armor.txt |
| Sword | weapon.txt |
| Axe | weapon.txt |
| Bow | weapon.txt |
| Character/NPC | character.txt |
| Player character | character.txt |
| Monster/Beast | character.txt |
| Display base | base.txt |
| Diorama scene | base.txt |
| Terrain | base.txt |
| Cloak/Cape | fabric.txt |
| Clothing | fabric.txt |
| Banner | fabric.txt |
| Unknown | generic.txt |

## Creating Custom Templates

To create a new template:

1. **Name clearly**: Use descriptive names (e.g., `dragon.txt`, `tabletop-rank.txt`)
2. **Use existing placeholders**: Reuse the standard ones when possible
3. **Maintain structure**: Follow the general pattern of existing templates
4. **Test thoroughly**: Generate samples with various input values
5. **Document**: Add entry to this README with use cases and placeholders

### Custom Template Example

```
A beautifully sculpted {creature_type}: {scale_detail},
{color_scheme}, {texture_description}, {wings_detail},
{lighting}, {detail_level}, fantasy creature art,
professional miniature painting, cinematic quality
```

## Template Composition

Templates can be composed from common sections:

**Subject Section**:
```
A beautifully painted {object_type}:
```

**Material Section**:
```
{material_description}, {material_properties}
```

**Color Section**:
```
{base_color}, {highlight_color}, {shadow_color}
```

**Condition Section**:
```
{weathering_effects}, {damage_marks}, {aging}
```

**Quality Section**:
```
{detail_level}, {artistic_style}, masterpiece quality
```

## Performance Notes

- **Template Rendering**: <1ms per template
- **Placeholder Substitution**: <1ms per variable
- **Total Impact**: Negligible (< 2-5ms total)
- **Caching**: Can cache rendered templates for identical inputs

## Integration

Templates integrate with the main PromptGenerator:

```python
from prompt_generator import PromptGenerator

generator = PromptGenerator()

# Auto-select template
prompt = generator.generate(ui_state)

# Explicit template selection
prompt = generator.generate(ui_state, template="armor")
```

See `scripts/generate-prompt-from-ui.py` for implementation details.

## Customization Guide

### Adjusting Template Structure

Modify template order for different emphasis:

**Default Order** (Best for most):
```
Subject → Material → Color → Condition → Finish → Lighting → Quality
```

**Quality-First** (When quality is paramount):
```
Quality → Subject → Material → Condition → Lighting
```

**Artistic-Focused** (For gallery pieces):
```
Subject → Artistic Style → Material → Color → Lighting → Quality
```

### Adding Domain-Specific Terms

Replace generic terms with domain vocabulary:

```
Before: "detailed armor"
After: "meticulously crafted steel plate armor with layered weathering"

Before: "nice color"
After: "burnished copper with verdigris highlights"
```

### Weighting for Emphasis

Add weighting syntax to emphasize concepts:

```
(highly detailed armor:1.2) (weathered steel:1.1) (dramatic lighting:1.0)
```

## Troubleshooting

### Template not rendering?
- Check all placeholders have values in context
- Verify placeholder names match exactly
- Use TemplateValidator to identify missing variables

### Generated prompt is vague?
- Add more specific material vocabulary
- Increase detail level descriptor
- Include material-specific effects
- Add lighting description

### Output is inconsistent?
- Ensure consistent material mappings
- Use controlled vocabulary
- Test all template + input combinations
