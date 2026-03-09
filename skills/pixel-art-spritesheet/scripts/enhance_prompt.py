#!/usr/bin/env python3
"""
Prompt Enhancer for Pixel Art Sprite Sheets

Takes a rough user prompt and expands it into a detailed specification
suitable for AI image generation or manual creation.

Usage:
    python enhance_prompt.py "cat sprite"
    python enhance_prompt.py "walking knight" --style nes
    python enhance_prompt.py "dragon" --animation attack --size 48
"""

import argparse
import json
import re
import sys
from typing import Optional


# Style configurations
STYLES = {
    "gbc": {
        "name": "Pokemon GBC",
        "colors": 4,
        "cell_sizes": [32],
        "default_cell": 32,
        "feel": "cute, rounded, expressive",
        "palette": ["#FFFFFF", "#AAAAAA", "#555555", "#000000"]
    },
    "nes": {
        "name": "NES 8-bit",
        "colors": 4,
        "cell_sizes": [16, 24],
        "default_cell": 16,
        "feel": "iconic, bold silhouettes",
        "palette": ["#FFFFFF", "#AAAAAA", "#555555", "#000000"]
    },
    "snes": {
        "name": "SNES 16-bit",
        "colors": 8,
        "cell_sizes": [32, 48, 64],
        "default_cell": 32,
        "feel": "detailed, smooth, vibrant",
        "palette": ["#FFFFFF", "#C0C0C0", "#808080", "#404040",
                    "#FFD700", "#FFA500", "#FF4500", "#000000"]
    },
    "gameboy": {
        "name": "Game Boy DMG",
        "colors": 4,
        "cell_sizes": [16],
        "default_cell": 16,
        "feel": "nostalgic, green-tinted",
        "palette": ["#9BBC0F", "#8BAC0F", "#306230", "#0F380F"]
    }
}

# Animation templates
ANIMATIONS = {
    "idle": {
        "frames": 4,
        "poses": [
            "Neutral standing pose",
            "Slight squash (body compresses 1-2px)",
            "Return to neutral",
            "Slight stretch (body extends 1-2px)"
        ]
    },
    "walk": {
        "frames": 4,
        "poses": [
            "Right foot forward, contact position",
            "Passing position, feet together, body highest",
            "Left foot forward, contact position",
            "Passing position, feet together"
        ]
    },
    "run": {
        "frames": 6,
        "poses": [
            "Right foot contact, lean forward",
            "Push off, body rising",
            "Flight phase, both feet off ground",
            "Left foot contact, lean forward",
            "Push off, body rising",
            "Flight phase, both feet off ground"
        ]
    },
    "attack": {
        "frames": 4,
        "poses": [
            "Wind up, lean back, arm/weapon raised",
            "Strike motion, forward momentum",
            "Impact, full extension",
            "Recovery, returning to neutral"
        ]
    },
    "jump": {
        "frames": 4,
        "poses": [
            "Crouch anticipation, body compressed",
            "Launch, body extending upward",
            "Apex, arms/legs spread",
            "Descent, body tucking"
        ]
    },
    "bounce": {
        "frames": 4,
        "poses": [
            "Neutral position",
            "Squash down, wider and shorter",
            "Stretch up, taller and narrower",
            "Return to neutral"
        ]
    }
}

# Character archetypes for enhancement
ARCHETYPES = {
    "cat": {
        "shape": "compact body with large head, pointed ears, long tail",
        "features": "large expressive eyes, small nose, whiskers",
        "default_animation": "idle"
    },
    "dog": {
        "shape": "medium body, floppy or pointed ears, wagging tail",
        "features": "round eyes, black nose, tongue may be visible",
        "default_animation": "idle"
    },
    "slime": {
        "shape": "dome/teardrop blob, no limbs",
        "features": "two simple dot eyes, glossy highlight",
        "default_animation": "bounce"
    },
    "knight": {
        "shape": "humanoid, bulky armor, oversized helmet",
        "features": "T-shaped visor, sword, shield",
        "default_animation": "walk"
    },
    "dragon": {
        "shape": "reptilian body, wings, long tail, horns",
        "features": "fierce eyes, scales, possibly fire breath",
        "default_animation": "idle"
    },
    "robot": {
        "shape": "boxy or rounded mechanical body",
        "features": "screen face or LED eyes, antenna, joints",
        "default_animation": "idle"
    },
    "ghost": {
        "shape": "floating sheet/wisp form, wavy bottom edge",
        "features": "hollow eyes, open mouth, translucent feel",
        "default_animation": "bounce"
    },
    "bird": {
        "shape": "round body, small wings, thin legs",
        "features": "beak, round eyes, tail feathers",
        "default_animation": "idle"
    }
}


def detect_subject(prompt: str) -> tuple[str, dict]:
    """Detect the subject from the prompt and return archetype info."""
    prompt_lower = prompt.lower()

    for name, info in ARCHETYPES.items():
        if name in prompt_lower:
            return name, info

    # Default to generic creature
    return "creature", {
        "shape": "compact rounded body",
        "features": "simple eyes, minimal details",
        "default_animation": "idle"
    }


def detect_style(prompt: str) -> str:
    """Detect style hints from prompt."""
    prompt_lower = prompt.lower()

    if any(x in prompt_lower for x in ["nes", "8-bit", "8bit", "nintendo"]):
        return "nes"
    if any(x in prompt_lower for x in ["snes", "16-bit", "16bit", "super nintendo"]):
        return "snes"
    if any(x in prompt_lower for x in ["gameboy", "game boy", "dmg", "green"]):
        return "gameboy"
    if any(x in prompt_lower for x in ["gbc", "pokemon", "color"]):
        return "gbc"

    return "gbc"  # Default


def detect_animation(prompt: str, archetype: dict) -> str:
    """Detect animation type from prompt."""
    prompt_lower = prompt.lower()

    for anim_name in ANIMATIONS:
        if anim_name in prompt_lower:
            return anim_name

    # Check for related words
    if any(x in prompt_lower for x in ["walking", "move", "moving"]):
        return "walk"
    if any(x in prompt_lower for x in ["running", "sprint", "fast"]):
        return "run"
    if any(x in prompt_lower for x in ["attack", "fight", "swing", "hit"]):
        return "attack"
    if any(x in prompt_lower for x in ["jump", "leap", "hop"]):
        return "jump"

    return archetype.get("default_animation", "idle")


def detect_mood(prompt: str) -> str:
    """Detect mood/personality from prompt."""
    prompt_lower = prompt.lower()

    if any(x in prompt_lower for x in ["cute", "adorable", "kawaii", "sweet"]):
        return "cute and friendly"
    if any(x in prompt_lower for x in ["angry", "fierce", "scary", "evil"]):
        return "fierce and intimidating"
    if any(x in prompt_lower for x in ["sad", "melancholy", "lonely"]):
        return "melancholic"
    if any(x in prompt_lower for x in ["happy", "cheerful", "joyful"]):
        return "cheerful and energetic"
    if any(x in prompt_lower for x in ["cool", "badass", "epic"]):
        return "cool and confident"

    return "charming and appealing"


def enhance_prompt(
    user_prompt: str,
    style_override: Optional[str] = None,
    animation_override: Optional[str] = None,
    size_override: Optional[int] = None
) -> dict:
    """
    Transform a rough prompt into a detailed specification.

    Returns a dictionary with complete sprite sheet specification.
    """

    # Detect elements from prompt
    subject_name, archetype = detect_subject(user_prompt)
    style_key = style_override or detect_style(user_prompt)
    animation_key = animation_override or detect_animation(user_prompt, archetype)
    mood = detect_mood(user_prompt)

    style = STYLES[style_key]
    animation = ANIMATIONS[animation_key]

    cell_size = size_override or style["default_cell"]
    frames = animation["frames"]

    # Build specification
    spec = {
        "subject": {
            "name": subject_name,
            "description": f"{mood} {subject_name}",
            "shape": archetype["shape"],
            "features": archetype["features"]
        },
        "style": {
            "name": style["name"],
            "colors": style["colors"],
            "feel": style["feel"]
        },
        "canvas": {
            "width": cell_size * frames,
            "height": cell_size,
            "cell_width": cell_size,
            "cell_height": cell_size,
            "columns": frames,
            "rows": 1,
            "background": "#FF00FF"
        },
        "palette": style["palette"][:style["colors"]],
        "animation": {
            "name": animation_key,
            "frames": frames,
            "poses": animation["poses"]
        },
        "direction": "facing right"
    }

    return spec


def spec_to_text(spec: dict) -> str:
    """Convert specification dict to formatted text."""

    lines = [
        "SPRITE SHEET SPECIFICATION",
        "=" * 30,
        f"Subject: {spec['subject']['description']}",
        f"Style: {spec['style']['name']} ({spec['style']['colors']} colors)",
        f"Mood: {spec['style']['feel']}",
        "",
        "CANVAS SETUP",
        f"- Dimensions: {spec['canvas']['width']}x{spec['canvas']['height']} pixels",
        f"- Grid: {spec['canvas']['rows']} row × {spec['canvas']['columns']} columns",
        f"- Cell: {spec['canvas']['cell_width']}x{spec['canvas']['cell_height']} pixels per frame",
        f"- Background: {spec['canvas']['background']} (magenta, transparent)",
        "",
        "COLOR PALETTE"
    ]

    for i, color in enumerate(spec['palette'], 1):
        usage = ["outline/shadow", "shadow/dark", "main/body", "highlight"][min(i-1, 3)]
        lines.append(f"{i}. {color} - {usage}")

    lines.extend([
        "",
        "CHARACTER DESIGN",
        f"- Shape: {spec['subject']['shape']}",
        f"- Features: {spec['subject']['features']}",
        f"- Facing: {spec['direction']}",
        "",
        f"ANIMATION: {spec['animation']['name'].title()} ({spec['animation']['frames']} frames)"
    ])

    for i, pose in enumerate(spec['animation']['poses'], 1):
        lines.append(f"  F{i}: {pose}")

    return "\n".join(lines)


def spec_to_image_prompt(spec: dict) -> str:
    """Convert specification to an AI image generation prompt."""

    canvas = spec['canvas']
    style = spec['style']
    subject = spec['subject']
    animation = spec['animation']

    palette_str = ", ".join(spec['palette'])

    frames_desc = "\n".join(
        f"Frame {i+1}: {pose}"
        for i, pose in enumerate(animation['poses'])
    )

    prompt = f"""Create a pixel art sprite sheet, {canvas['width']}x{canvas['height']} pixels total.

STYLE: {style['name']} era pixel art, {style['colors']}-color palette only, clean pixels with no anti-aliasing, crisp edges, retro game aesthetic.

LAYOUT: {canvas['columns']} frames in a horizontal row, each frame {canvas['cell_width']}x{canvas['cell_height']} pixels, solid magenta #FF00FF background.

CHARACTER: A {subject['description']}. {subject['shape'].capitalize()}. {subject['features'].capitalize()}. {spec['direction'].capitalize()}.

PALETTE: Strictly use only these {style['colors']} colors: {palette_str}

ANIMATION FRAMES (left to right):
{frames_desc}

CRITICAL: No gradients, no anti-aliasing, no extra colors. Hard pixel edges only. Each frame clearly separated. Character centered in each cell with consistent size across all frames."""

    return prompt


def main():
    parser = argparse.ArgumentParser(
        description="Enhance pixel art prompts into detailed specifications"
    )
    parser.add_argument(
        "prompt",
        type=str,
        help="User's rough prompt (e.g., 'cat sprite', 'walking knight')"
    )
    parser.add_argument(
        "--style",
        choices=list(STYLES.keys()),
        help="Override detected style"
    )
    parser.add_argument(
        "--animation",
        choices=list(ANIMATIONS.keys()),
        help="Override detected animation"
    )
    parser.add_argument(
        "--size",
        type=int,
        choices=[16, 24, 32, 48, 64],
        help="Override cell size"
    )
    parser.add_argument(
        "--format",
        choices=["text", "json", "image-prompt"],
        default="text",
        help="Output format"
    )

    args = parser.parse_args()

    spec = enhance_prompt(
        args.prompt,
        style_override=args.style,
        animation_override=args.animation,
        size_override=args.size
    )

    if args.format == "json":
        print(json.dumps(spec, indent=2))
    elif args.format == "image-prompt":
        print(spec_to_image_prompt(spec))
    else:
        print(spec_to_text(spec))
        print("\n" + "=" * 30)
        print("IMAGE GENERATION PROMPT:")
        print("=" * 30 + "\n")
        print(spec_to_image_prompt(spec))


if __name__ == "__main__":
    main()
