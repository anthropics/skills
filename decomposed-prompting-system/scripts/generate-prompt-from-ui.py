"""
Decomposed Prompting System - UI State to Prompt Generator

Converts UI component state (sliders, dropdowns, color pickers) into
comprehensive, token-dense prompts optimized for AI image generation
of miniature painting subjects.

Usage:
    generator = PromptGenerator(
        templates_path="assets/prompt-templates/",
        embeddings_path="assets/concept-embeddings/"
    )

    ui_state = {
        "miniature_type": "armor",
        "weathering": 65,
        "material": "metal",
        "base_color": "#c0c0c0",
        "add_shadows": True,
        "lighting_style": "dramatic"
    }

    prompt = generator.generate(ui_state, template="armor")
"""

import json
import re
from typing import Dict, List, Tuple, Any, Optional
from pathlib import Path
from dataclasses import dataclass
from enum import Enum


class ComponentType(Enum):
    """Supported UI component types"""
    SLIDER = "slider"
    DROPDOWN = "dropdown"
    COLOR_PICKER = "color_picker"
    TOGGLE = "toggle"
    TEXT_INPUT = "text_input"


@dataclass
class SliderMapping:
    """Maps slider values to prompt tokens"""
    min_value: int
    max_value: int
    token: str
    intensity_weight: Optional[float] = None


class PromptGenerator:
    """Main prompt generation engine"""

    def __init__(self, templates_path: str = "assets/prompt-templates/",
                 embeddings_path: str = "assets/concept-embeddings/"):
        """
        Initialize the prompt generator.

        Args:
            templates_path: Path to prompt template files
            embeddings_path: Path to concept embeddings
        """
        self.templates_path = Path(templates_path)
        self.embeddings_path = Path(embeddings_path)
        self.component_mappings = self._load_component_mappings()
        self.vocabulary = self._load_vocabulary()
        self.templates = self._load_templates()

    def _load_component_mappings(self) -> Dict[str, Dict]:
        """Load component mapping definitions"""
        return {
            "weathering": {
                "type": ComponentType.SLIDER,
                "min": 0, "max": 100,
                "mappings": [
                    (0, 20, "pristine", 0.3),
                    (20, 50, "lightly weathered", 0.6),
                    (50, 80, "heavily weathered", 0.9),
                    (80, 100, "battle-worn", 1.2)
                ],
                "embedding": "weathering_slider"
            },
            "material": {
                "type": ComponentType.DROPDOWN,
                "options": {
                    "metal": "polished steel, metallic sheen, reflective surface",
                    "brass": "burnished brass, warm metallic tone, corrosion prone",
                    "copper": "bright copper, reddish metallic finish, oxidizable",
                    "iron": "dark iron, rough finish, rust prone",
                    "gold": "lustrous gold, warm glow, highly reflective",
                    "ceramic": "glazed ceramic, smooth glossy surface, brittle appearance",
                    "wood": "carved wood grain, matte finish, natural texture",
                    "leather": "tooled leather, subtle sheen, worn appearance"
                }
            },
            "base_color": {
                "type": ComponentType.COLOR_PICKER,
                "token_template": "{color} base coat with strategic highlights"
            },
            "lighting_style": {
                "type": ComponentType.DROPDOWN,
                "options": {
                    "dramatic": "dramatic side lighting, strong shadows, high contrast",
                    "studio": "even studio lighting, soft shadows, balanced illumination",
                    "ambient": "warm ambient light, soft diffused lighting, gentle shadows",
                    "rim": "rim lighting, backlighting, silhouette highlights, volumetric light",
                    "spotlight": "focused spotlight, dramatic contrast, cinematic lighting"
                }
            },
            "detail_level": {
                "type": ComponentType.SLIDER,
                "min": 0, "max": 100,
                "mappings": [
                    (0, 25, "basic detail", 0.5),
                    (25, 50, "moderate detail", 0.8),
                    (50, 75, "highly detailed", 1.0),
                    (75, 100, "hyper detailed", 1.3)
                ]
            },
            "finish_type": {
                "type": ComponentType.DROPDOWN,
                "options": {
                    "matte": "flat matte finish, non-reflective surface",
                    "satin": "satin finish, subtle sheen, mid-range reflectivity",
                    "gloss": "high gloss finish, mirror-like reflectivity",
                    "lacquered": "lacquered surface, protective glossy coating",
                    "enameled": "enameled coating, smooth hard surface"
                }
            }
        }

    def _load_vocabulary(self) -> Dict[str, List[str]]:
        """Load domain-specific vocabulary"""
        return {
            "quality_tokens": [
                "masterpiece", "museum quality", "hyper-detailed",
                "photorealistic", "professional grade", "cinematic",
                "8k resolution", "intricate craftsmanship"
            ],
            "effects_tokens": [
                "weathering", "rust streaks", "patina", "verdigris",
                "chipping paint", "dust accumulation", "grime",
                "battle damage", "age marks", "oxidation"
            ],
            "lighting_tokens": [
                "dramatic lighting", "rim lighting", "subsurface scattering",
                "volumetric light", "backlighting", "soft diffusion",
                "directional light", "cinematic light"
            ],
            "style_tokens": [
                "game-ready", "tabletop quality", "collector's piece",
                "fantasy inspired", "historically accurate", "sci-fi aesthetic"
            ]
        }

    def _load_templates(self) -> Dict[str, str]:
        """Load prompt templates"""
        return {
            "armor": (
                "A beautifully painted suit of {material_description} armor: "
                "{base_color}, {finish_description}, {weathering_effects}, "
                "{lighting_style}, {detail_level}, professional miniature painting, "
                "masterpiece, {additional_modifiers}"
            ),
            "weapon": (
                "Intricately detailed painted {miniature_type}: "
                "{material_description}, {base_color}, {weathering_effects}, "
                "{finish_description}, {lighting_style}, {detail_level}, "
                "fantasy weapon art, {additional_modifiers}"
            ),
            "character": (
                "Fantasy character miniature: {base_color}, "
                "{material_description} armor, detailed face, {weathering_effects}, "
                "{lighting_style}, {finish_description}, {detail_level}, "
                "professional miniature painting, {additional_modifiers}"
            ),
            "base": (
                "Miniature base terrain: {material_description}, "
                "{base_color}, {weathering_effects}, {lighting_style}, "
                "{finish_description}, {detail_level}, environmental storytelling, "
                "tabletop gaming, {additional_modifiers}"
            ),
            "generic": (
                "Professionally painted miniature: {material_description}, "
                "{base_color}, {weathering_effects}, {lighting_style}, "
                "{finish_description}, {detail_level}, {additional_modifiers}"
            )
        }

    def generate(self, ui_state: Dict[str, Any], template: str = "generic",
                 include_weighting: bool = True) -> str:
        """
        Generate a prompt from UI state.

        Args:
            ui_state: Dictionary of UI component states
            template: Template name to use
            include_weighting: Whether to include emphasis weights

        Returns:
            Generated prompt string
        """
        # Parse UI components
        components = self._parse_ui_state(ui_state)

        # Upsample to full tokens
        tokens = self._upsample_components(components)

        # Generate modifiers
        modifiers = self._generate_modifiers(ui_state)

        # Fill template
        prompt_template = self.templates.get(template, self.templates["generic"])

        prompt = prompt_template.format(
            material_description=tokens.get("material", "mysterious material"),
            base_color=tokens.get("base_color", "striking colors"),
            finish_description=tokens.get("finish", "standard finish"),
            weathering_effects=tokens.get("weathering", "well-preserved"),
            lighting_style=tokens.get("lighting", "balanced lighting"),
            detail_level=tokens.get("detail", "detailed"),
            additional_modifiers=", ".join(modifiers),
            miniature_type=ui_state.get("miniature_type", "miniature")
        )

        # Apply weighting if requested
        if include_weighting:
            prompt = self._apply_weighting(prompt, tokens)

        return prompt

    def _parse_ui_state(self, ui_state: Dict[str, Any]) -> Dict[str, Any]:
        """Parse and validate UI state"""
        parsed = {}

        for key, value in ui_state.items():
            if key not in self.component_mappings:
                parsed[key] = value
                continue

            mapping = self.component_mappings[key]
            component_type = mapping["type"]

            if component_type == ComponentType.SLIDER:
                parsed[key] = self._parse_slider(key, value, mapping)
            elif component_type == ComponentType.DROPDOWN:
                parsed[key] = value
            elif component_type == ComponentType.COLOR_PICKER:
                parsed[key] = self._parse_color(value)
            else:
                parsed[key] = value

        return parsed

    def _parse_slider(self, key: str, value: int,
                      mapping: Dict) -> Tuple[str, float]:
        """Map slider value to token and weight"""
        for min_val, max_val, token, weight in mapping["mappings"]:
            if min_val <= value <= max_val:
                return (token, weight or 1.0)
        return ("standard", 1.0)

    def _parse_color(self, color_hex: str) -> str:
        """Convert hex color to descriptive token"""
        color_map = {
            "#c0c0c0": "silver", "#808080": "gunmetal",
            "#ffd700": "gold", "#ff0000": "crimson",
            "#0000ff": "cobalt blue", "#00ff00": "emerald green",
            "#ff8800": "copper", "#800000": "maroon",
            "#ffff00": "golden yellow", "#ff00ff": "magenta"
        }
        return color_map.get(color_hex.lower(), "metallic")

    def _upsample_components(self, components: Dict) -> Dict[str, str]:
        """Expand components into full token descriptions"""
        tokens = {}

        # Material
        if "material" in components:
            tokens["material"] = self.component_mappings["material"]["options"].get(
                components["material"],
                "mysterious material"
            )

        # Base color
        if "base_color" in components:
            color_token = components["base_color"]
            tokens["base_color"] = (
                f"{color_token} base coat with strategic highlights and shadows"
            )

        # Finish
        if "finish_type" in components:
            tokens["finish"] = self.component_mappings["finish_type"]["options"].get(
                components["finish_type"],
                "standard finish"
            )

        # Weathering
        if "weathering" in components:
            token, weight = components["weathering"]
            tokens["weathering"] = token
            tokens["weathering_weight"] = weight

        # Lighting
        if "lighting_style" in components:
            tokens["lighting"] = self.component_mappings["lighting_style"]["options"].get(
                components["lighting_style"],
                "balanced lighting"
            )

        # Detail level
        if "detail_level" in components:
            token, weight = components["detail_level"]
            tokens["detail"] = token
            tokens["detail_weight"] = weight

        return tokens

    def _generate_modifiers(self, ui_state: Dict) -> List[str]:
        """Generate additional modifiers from UI state"""
        modifiers = []

        # Add quality tokens
        modifiers.extend(self.vocabulary["quality_tokens"][:2])

        # Add conditional modifiers
        if ui_state.get("add_shadows", False):
            modifiers.append("strategic shadows")

        if ui_state.get("add_effects", False):
            modifiers.extend(self.vocabulary["effects_tokens"][:2])

        if ui_state.get("artistic_style"):
            style = ui_state["artistic_style"]
            modifiers.append(f"{style} style")

        # Add from user input
        if ui_state.get("custom_modifiers"):
            modifiers.extend(ui_state["custom_modifiers"])

        return modifiers[:5]  # Limit to 5 modifiers

    def _apply_weighting(self, prompt: str, tokens: Dict) -> str:
        """Apply emphasis weighting to prompt"""
        weighted_prompt = prompt

        # Apply weights
        weights_to_apply = {
            "weathering_weight": "weathering",
            "detail_weight": "detail",
            "material_weight": "material"
        }

        for weight_key, token_key in weights_to_apply.items():
            if weight_key in tokens and token_key in tokens:
                weight = tokens[weight_key]
                token = tokens[token_key]

                # Apply weighting syntax (compatible with Stable Diffusion)
                if weight > 1.0:
                    weighted_token = f"({token}:{weight:.1f})"
                    weighted_prompt = weighted_prompt.replace(token, weighted_token)

        return weighted_prompt

    def generate_batch(self, ui_states: List[Dict], template: str = "generic") -> List[str]:
        """Generate multiple prompts at once"""
        return [self.generate(state, template) for state in ui_states]

    def interpolate_embedding(self, light_embedding: str,
                             heavy_embedding: str,
                             intensity: float) -> str:
        """
        Interpolate between two embeddings based on intensity.

        Used for slider-based concept control with textual inversion.
        """
        ratio = intensity / 100.0
        # In practice, this would load and interpolate actual embedding vectors
        # For now, return a weighted token string
        return f"<embedding:interpolated_{light_embedding}_{heavy_embedding}_{ratio:.2f}>"


# Example usage
if __name__ == "__main__":
    # Initialize generator
    generator = PromptGenerator()

    # Example 1: Weathered armor
    armor_state = {
        "miniature_type": "armor",
        "weathering": 65,
        "material": "metal",
        "base_color": "#c0c0c0",
        "finish_type": "satin",
        "lighting_style": "dramatic",
        "detail_level": 80,
        "add_shadows": True
    }

    armor_prompt = generator.generate(armor_state, template="armor")
    print("ARMOR PROMPT:")
    print(armor_prompt)
    print()

    # Example 2: Character miniature
    character_state = {
        "miniature_type": "Fantasy Paladin",
        "weathering": 30,
        "material": "brass",
        "base_color": "#ffd700",
        "finish_type": "gloss",
        "lighting_style": "rim",
        "detail_level": 90,
        "add_effects": True
    }

    character_prompt = generator.generate(character_state, template="character")
    print("CHARACTER PROMPT:")
    print(character_prompt)
    print()

    # Example 3: Batch generation
    ui_states = [
        {"weathering": 20, "material": "gold", "base_color": "#ffd700"},
        {"weathering": 50, "material": "copper", "base_color": "#ff8800"},
        {"weathering": 80, "material": "iron", "base_color": "#808080"}
    ]

    prompts = generator.generate_batch(ui_states)
    print("BATCH PROMPTS:")
    for i, prompt in enumerate(prompts, 1):
        print(f"{i}. {prompt}\n")
