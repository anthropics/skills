# Prompt Template System Architecture

## Overview

The Prompt Template System provides a structured, composable architecture for generating prompts from UI state. Templates define the semantic structure and placeholder mapping while keeping actual prompt content modular and expandable.

## Core Architecture

### Three-Layer System

```
┌─────────────────────────────────────────┐
│  Layer 1: UI Components                 │
│  (Sliders, Dropdowns, Color Pickers)   │
└──────────────┬──────────────────────────┘
               │ UI State Dictionary
               ▼
┌─────────────────────────────────────────┐
│  Layer 2: Component Mappings            │
│  (Map components to tokens/embeddings)  │
└──────────────┬──────────────────────────┘
               │ Semantic Tokens
               ▼
┌─────────────────────────────────────────┐
│  Layer 3: Template Engine               │
│  (Fill templates with tokens)           │
└──────────────┬──────────────────────────┘
               │ Final Prompt String
               ▼
┌─────────────────────────────────────────┐
│  Image Generation Model                 │
└─────────────────────────────────────────┘
```

## Template Definition

### Basic Structure

```
A {miniature_type}: {material_description}, {color_description},
{weathering_effects}, {finish_type}, {lighting_setup},
professional miniature painting, {detail_level}, {artistic_style}
```

### Placeholder Categories

1. **Subject Placeholders**: What is being painted
   - `{miniature_type}`
   - `{character_role}`
   - `{object_type}`

2. **Material Placeholders**: Physical properties
   - `{material_description}`
   - `{material_texture}`
   - `{material_finish}`

3. **Color Placeholders**: Color information
   - `{base_color}`
   - `{color_highlights}`
   - `{color_shadows}`

4. **Condition Placeholders**: Wear and effects
   - `{weathering_effects}`
   - `{damage_marks}`
   - `{aging_signs}`

5. **Quality Placeholders**: Rendering quality
   - `{detail_level}`
   - `{artistic_style}`
   - `{rendering_quality}`

6. **Lighting Placeholders**: Light and atmosphere
   - `{lighting_setup}`
   - `{atmosphere}`
   - `{lighting_mood}`

7. **Modifier Placeholders**: Additional effects
   - `{additional_modifiers}`
   - `{special_effects}`
   - `{artistic_touches}`

## Template Types

### Type 1: Simple Substitution

**Use**: For static mappings where each component has one token

```python
template = (
    "A beautifully painted {miniature_type}: "
    "{material_description}, {base_color}, "
    "{weathering_effects}, professional miniature painting"
)
```

**Context Variables**:
```python
{
    "miniature_type": "suit of armor",
    "material_description": "polished steel",
    "base_color": "silver with highlights",
    "weathering_effects": "rust streaks"
}
```

### Type 2: Conditional Sections

**Use**: Include/exclude sections based on UI state

```python
template_with_conditions = """
A {miniature_type}: {material_description}, {base_color},
{weathering_effects}, {finish_type},
{% if add_lighting %}
with {lighting_style} lighting,
{% endif %}
{% if add_effects %}
featuring {special_effects},
{% endif %}
professional miniature painting, {detail_level}
"""
```

**Implementation** (Python with Jinja2):
```python
from jinja2 import Template

jinja_template = Template(template_with_conditions)

render_context = {
    "miniature_type": "armor",
    "material_description": "steel",
    "base_color": "silver",
    "weathering_effects": "weathered",
    "finish_type": "satin",
    "add_lighting": True,
    "lighting_style": "dramatic",
    "add_effects": True,
    "special_effects": "rust and patina",
    "detail_level": "highly detailed"
}

prompt = jinja_template.render(render_context)
```

### Type 3: Modifier Chains

**Use**: Build complex modifiers from multiple components

```python
class TemplateWithModifiers:
    def __init__(self, base_template: str,
                 modifier_separator: str = ", "):
        self.base_template = base_template
        self.modifier_separator = modifier_separator

    def fill(self, context: Dict[str, Any],
             modifiers: List[str]) -> str:
        """
        Fill template and append modifiers.

        Args:
            context: Template variables
            modifiers: List of modifier strings

        Returns:
            Filled template with appended modifiers
        """
        prompt = self.base_template.format(**context)

        if modifiers:
            prompt += self.modifier_separator + self.modifier_separator.join(modifiers)

        return prompt
```

### Type 4: Semantic Clustering

**Use**: Group related concepts for better prompt coherence

```python
class SemanticTemplate:
    """
    Template that organizes concepts into semantic clusters
    """

    def __init__(self):
        self.clusters = {
            "subject": [],      # What is being painted
            "material": [],     # Physical properties
            "condition": [],    # Wear, age, damage
            "appearance": [],   # Colors, finishes
            "environment": [],  # Lighting, atmosphere
            "quality": []       # Rendering quality
        }

    def fill(self, ui_state: Dict) -> str:
        """Generate prompt with semantic clustering"""

        self.clusters["subject"] = [ui_state.get("miniature_type", "miniature")]
        self.clusters["material"] = [ui_state.get("material_description", "")]
        self.clusters["condition"] = self._get_condition_tokens(ui_state)
        self.clusters["appearance"] = self._get_appearance_tokens(ui_state)
        self.clusters["environment"] = self._get_environment_tokens(ui_state)
        self.clusters["quality"] = self._get_quality_tokens(ui_state)

        # Build prompt respecting cluster order
        prompt_parts = []
        for cluster_name in ["subject", "material", "condition",
                            "appearance", "environment", "quality"]:
            tokens = [t for t in self.clusters[cluster_name] if t]
            if tokens:
                prompt_parts.append(", ".join(tokens))

        return ", ".join(prompt_parts)

    def _get_condition_tokens(self, state: Dict) -> List[str]:
        """Extract condition-related tokens"""
        tokens = []
        if state.get("weathering"):
            tokens.append(state["weathering"])
        if state.get("damage"):
            tokens.append(state["damage"])
        return tokens

    # Similar methods for other clusters...
```

## Template Inheritance & Composition

### Inheritance Pattern

```python
class BaseTemplate:
    """Base template with common sections"""

    INTRO = "A beautifully painted {miniature_type}: "
    OUTRO = "professional miniature painting, {detail_level}"

    def get_template(self) -> str:
        return self.INTRO + "[SUBCLASS CONTENT]" + self.OUTRO


class ArmorTemplate(BaseTemplate):
    """Specialized armor template"""

    ARMOR_SECTION = (
        "{material_description}, {finish_type}, "
        "{weathering_effects}, metallic {base_color}"
    )

    def get_template(self) -> str:
        return (self.INTRO + self.ARMOR_SECTION +
                ", {lighting_style}, " + self.OUTRO)


class FabricTemplate(BaseTemplate):
    """Specialized fabric/clothing template"""

    FABRIC_SECTION = (
        "{material_description}, {base_color}, "
        "{texture_description}, {wear_pattern}"
    )

    def get_template(self) -> str:
        return (self.INTRO + self.FABRIC_SECTION +
                ", {lighting_style}, " + self.OUTRO)
```

### Composition Pattern

```python
class ComposableTemplate:
    """Build templates by composing sections"""

    def __init__(self):
        self.sections = []

    def add_subject_section(self, template: str) -> 'ComposableTemplate':
        self.sections.append(template)
        return self

    def add_material_section(self, template: str) -> 'ComposableTemplate':
        self.sections.append(template)
        return self

    def add_condition_section(self, template: str) -> 'ComposableTemplate':
        self.sections.append(template)
        return self

    def add_quality_section(self, template: str) -> 'ComposableTemplate':
        self.sections.append(template)
        return self

    def build(self) -> str:
        return ", ".join(self.sections)


# Usage
template = (ComposableTemplate()
    .add_subject_section("A {miniature_type}")
    .add_material_section("{material_description}")
    .add_condition_section("{weathering_effects}")
    .add_quality_section("{detail_level}")
    .build())
```

## Template Variants

### Context-Specific Templates

```python
TEMPLATES = {
    # Fantasy miniatures
    "fantasy_armor": (
        "A magnificent suit of {material_description} armor, "
        "{base_color}, with {weathering_effects}, "
        "{finish_type}, dramatic {lighting_style}, "
        "{detail_level}, fantasy art, masterpiece"
    ),

    # Sci-Fi miniatures
    "scifi_armor": (
        "Advanced tactical armor: {material_description}, "
        "{base_color}, {weathering_effects}, "
        "{finish_type}, neon {lighting_style}, "
        "sci-fi aesthetic, {detail_level}"
    ),

    # Historical miniatures
    "historical_armor": (
        "Historically accurate {material_description} armor, "
        "{base_color}, period-appropriate {weathering_effects}, "
        "{finish_type}, museum lighting, {detail_level}"
    ),

    # Organic miniatures
    "character_skin": (
        "Detailed character portrait: {miniature_type}, "
        "{base_color} skin tones, {material_description}, "
        "{weathering_effects}, {lighting_style}, "
        "professional portrait, {detail_level}"
    ),

    # Terrain/Base
    "terrain": (
        "Miniature diorama base: {material_description}, "
        "{base_color} earth tones, {weathering_effects}, "
        "{vegetation}, {lighting_style}, {detail_level}"
    )
}
```

## Dynamic Template Selection

```python
class TemplateSelector:
    """Select appropriate template based on UI state"""

    def __init__(self, templates: Dict[str, str]):
        self.templates = templates

    def select(self, ui_state: Dict[str, Any]) -> str:
        """
        Select template based on miniature type and context.

        Args:
            ui_state: Current UI state

        Returns:
            Selected template string
        """

        miniature_type = ui_state.get("miniature_type", "generic").lower()

        # Exact match
        if miniature_type in self.templates:
            return self.templates[miniature_type]

        # Category match
        if "armor" in miniature_type:
            return self.templates.get("armor_template",
                                     self.templates["generic"])
        elif "weapon" in miniature_type:
            return self.templates.get("weapon_template",
                                     self.templates["generic"])
        elif "character" in miniature_type:
            return self.templates.get("character_template",
                                     self.templates["generic"])
        elif "base" in miniature_type or "terrain" in miniature_type:
            return self.templates.get("terrain_template",
                                     self.templates["generic"])

        # Default
        return self.templates["generic"]


# Usage
selector = TemplateSelector(TEMPLATES)
selected = selector.select({
    "miniature_type": "plate armor",
    "material": "steel"
})
```

## Variable Validation

```python
class TemplateValidator:
    """Validate template variables are present and valid"""

    @staticmethod
    def validate(template: str, context: Dict[str, Any]) -> Tuple[bool, List[str]]:
        """
        Check if all template placeholders have values.

        Returns:
            (is_valid, list_of_missing_variables)
        """

        import re

        # Find all placeholders
        placeholders = re.findall(r'\{(\w+)\}', template)

        missing = []
        for placeholder in placeholders:
            if placeholder not in context or context[placeholder] is None:
                missing.append(placeholder)

        return len(missing) == 0, missing


# Usage
is_valid, missing = TemplateValidator.validate(template, context)
if not is_valid:
    print(f"Missing variables: {missing}")
```

## Template Testing

```python
class TemplateTestCase:
    """Test template generation"""

    def test_armor_template(self):
        template = TEMPLATES["armor"]
        context = {
            "miniature_type": "plate armor",
            "material_description": "polished steel",
            "base_color": "silver",
            "weathering_effects": "rust streaks",
            "finish_type": "satin",
            "lighting_style": "dramatic",
            "detail_level": "highly detailed"
        }

        result = template.format(**context)

        assert "armor" in result.lower()
        assert "steel" in result.lower()
        assert "dramatic" in result.lower()
        assert result.count(",") >= 3  # Multiple sections


    def test_missing_variables(self):
        template = TEMPLATES["armor"]
        incomplete_context = {
            "miniature_type": "armor"
            # Missing other required variables
        }

        is_valid, missing = TemplateValidator.validate(
            template, incomplete_context
        )

        assert not is_valid
        assert len(missing) > 0
```

## Best Practices

### 1. Semantic Ordering
Place concepts in order of importance: subject > properties > conditions > quality

### 2. Consistent Placeholders
Use consistent naming: `{subject_attribute}` not `{attribute_subject}`

### 3. Flexibility
Make templates flexible enough to handle various component combinations

### 4. Clarity
Keep individual placeholders focused on single semantic concepts

### 5. Documentation
Document what each placeholder expects and valid values

### 6. Testing
Test templates with various component combinations

### 7. Composition
Build complex templates from simpler, reusable parts

## Integration with PromptGenerator

```python
class AdvancedPromptGenerator(PromptGenerator):
    """Extended generator with template system"""

    def __init__(self, templates_path: str = "assets/prompt-templates/",
                 embeddings_path: str = "assets/concept-embeddings/"):
        super().__init__(templates_path, embeddings_path)

        # Load template variants
        self.template_variants = self._load_template_variants()
        self.selector = TemplateSelector(self.template_variants)

    def generate(self, ui_state: Dict[str, Any],
                template: Optional[str] = None,
                include_weighting: bool = True) -> str:
        """
        Generate prompt with advanced template selection.

        Args:
            ui_state: UI component state
            template: Optional explicit template name
            include_weighting: Whether to apply emphasis weights

        Returns:
            Generated prompt string
        """

        # Auto-select template if not specified
        if template is None:
            template_str = self.selector.select(ui_state)
        else:
            template_str = self.template_variants.get(
                template,
                self.template_variants["generic"]
            )

        # Parse and validate
        is_valid, missing = TemplateValidator.validate(
            template_str, ui_state
        )

        if not is_valid:
            print(f"Warning: Missing template variables: {missing}")

        # Fill template
        context = self._build_context(ui_state)
        prompt = template_str.format(**context)

        # Apply weighting
        if include_weighting:
            prompt = self._apply_weighting(prompt, context)

        return prompt

    def _build_context(self, ui_state: Dict) -> Dict[str, str]:
        """Build context dictionary from UI state"""
        # This combines component parsing and token generation
        pass
```

## File Organization

Templates are stored in `assets/prompt-templates/`:

```
assets/prompt-templates/
├── armor.txt
├── weapon.txt
├── character.txt
├── base.txt
├── generic.txt
└── README.md (template reference)
```

Each file contains the template string, optionally with comments describing placeholders.
