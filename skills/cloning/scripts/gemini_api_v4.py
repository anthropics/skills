#!/usr/bin/env python3
"""
Gemini API Integration for Website Cloning (v4.0 Enhanced)

Enhanced version with:
- Confidence-scored design tokens
- Framework detection integration
- Layout analysis data
- Component semantic mapping
- Optimal Gemini 3 parameters (temperature 1.0, high thinking)

Usage:
    python3 gemini_api_v4.py --artifacts /path/to/artifacts/ \
                              --output /path/to/output/ \
                              --model pro

    # Or import as module:
    from gemini_api_v4 import send_to_gemini_v4
    result = send_to_gemini_v4(artifacts_path, output_path, model="pro")
"""

import argparse
import base64
import json
import os
import re
import sys
import time
from pathlib import Path
from typing import Optional

try:
    import requests
except ImportError:
    print("Installing requests...")
    import subprocess
    subprocess.check_call([sys.executable, "-m", "pip", "install", "requests", "-q"])
    import requests


# =============================================================================
# Configuration
# =============================================================================

def _load_dotenv() -> None:
    """Load .env file if python-dotenv is installed (optional)."""
    try:
        from dotenv import load_dotenv
        load_dotenv()
    except ImportError:
        pass


def get_api_key() -> str:
    """
    Get Gemini API key from environment variables.
    Checks (in order): GOOGLE_API_KEY → GEMINI_API_KEY
    """
    _load_dotenv()
    key = os.environ.get("GOOGLE_API_KEY") or os.environ.get("GEMINI_API_KEY")

    if not key:
        raise ValueError(
            "\n"
            "============================================================\n"
            "  GEMINI API KEY REQUIRED\n"
            "============================================================\n\n"
            "The cloning skill needs a Gemini API key.\n\n"
            "SETUP:\n"
            "  export GEMINI_API_KEY='your-key-here'\n\n"
            "Or add to ~/.zshrc for persistence:\n"
            "  echo 'export GEMINI_API_KEY=\"your-key\"' >> ~/.zshrc\n"
            "  source ~/.zshrc\n\n"
            "GET A KEY:\n"
            "  https://aistudio.google.com/apikey\n\n"
            "============================================================\n"
        )
    return key


# API Configuration
API_KEY = get_api_key()
API_BASE = "https://generativelanguage.googleapis.com/v1beta/models"

# Available models
MODELS = {
    "pro": "gemini-3.1-pro-preview",      # Best quality for complex sites
    "flash": "gemini-3-flash-preview"   # Faster, simpler sites only
}

# Request configuration
MAX_RETRIES = 3
RETRY_DELAY = 5
REQUEST_TIMEOUT = 600  # 10 minutes for complex sites


# =============================================================================
# v4.0 Enhanced Prompt Template
# =============================================================================

CLONE_PROMPT_TEMPLATE_V4 = """# CLONE REQUEST: {url}

You are cloning a website with 100% visual fidelity.
Generate complete, production-ready Next.js 14 + Tailwind CSS code.

## SITE ANALYSIS (Pre-computed)

### Frameworks Detected
- CSS: {css_framework}
- Animation: {animation_library}
- Icons: {icon_library}
- Components: {component_library}
- Build: {build_tool}

### UI Patterns Found
{ui_patterns}

## LAYOUT STRUCTURE

### Primary Layout: {primary_layout}

### Grid Usage
{grid_layouts}

### Flexbox Usage
{flexbox_layouts}

### Z-Index Layers
{z_index_layers}

### Responsive Breakpoints
{breakpoints}

## COMPONENT MAP

### ARIA Landmarks
{landmarks}

### Detected Components
{components}

### Section Structure
{sections}

## DESIGN SYSTEM (Confidence-Scored)

### Colors (HIGH CONFIDENCE - Brand Critical)
{high_confidence_colors}

### Colors (MEDIUM CONFIDENCE - Interactive)
{medium_confidence_colors}

### Typography
- Primary Font: {primary_font}
- Heading Font: {heading_font}
- Font Weights: {font_weights}
- Font Sizes: {font_sizes}

### Font Manifest (with URLs)
{font_manifest}

### Spacing Scale
{spacing_scale}

### Visual Effects
- Shadows: {shadows}
- Border Radius: {border_radius}
- Gradients: {gradients}

### CSS Variables
{css_variables}

## ANIMATIONS (Exact Values)

### Animation Library: {animation_lib_detail}

### Timing Constants
- Premium Easing: {premium_easing}
- Durations: {durations}
- Staggers: {staggers}

### ScrollTriggers / Scroll Animations
{scroll_triggers}

### @Keyframes Definitions
{keyframes}

### Hover Transitions
{hover_transitions}

## SVG / ICONS

### Icon Library: {detected_icons}
### Inline SVG Count: {inline_svg_count}

### Logo SVG
{logo_svg}

### Icon Examples
{icon_examples}

## FILES TO CREATE

Create these SEPARATE component files (do NOT combine):
- app/page.tsx (main page, imports components)
- app/layout.tsx (root layout with fonts)
- app/globals.css (global styles, @font-face, @keyframes)
{component_files}
- tailwind.config.ts (custom colors, fonts)
- package.json (dependencies including {animation_library} if used)

## ANIMATION IMPLEMENTATION

{animation_implementation}

## ORIGINAL HTML STRUCTURE

```html
{html_content}
```

## REQUIREMENTS

1. **Exact Visual Match**: Use the exact colors, fonts, spacing from the design system
2. **Correct Layout Method**: Use {primary_layout} for main layouts as detected
3. **Animation Library**: Use {animation_library} (NOT alternatives)
4. **Icon Reproduction**: Use the exact icon library detected ({icon_library})
5. **Responsive Design**: Implement breakpoints at {breakpoint_values}
6. **TypeScript**: All files .tsx with proper types
7. **Image Hotlinking**: Use original image URLs from HTML

## OUTPUT FORMAT

```filepath:/path/to/file.tsx
// content
```

Include ALL files listed above. Generate complete, runnable code.
"""


# =============================================================================
# Helper Functions
# =============================================================================

def load_image_as_base64(image_path: str) -> tuple:
    """Load an image file and convert to base64."""
    path = Path(image_path)

    mime_types = {
        ".png": "image/png",
        ".jpg": "image/jpeg",
        ".jpeg": "image/jpeg",
        ".gif": "image/gif",
        ".webp": "image/webp"
    }
    mime_type = mime_types.get(path.suffix.lower(), "image/png")

    with open(path, "rb") as f:
        data = base64.b64encode(f.read()).decode("utf-8")

    return data, mime_type


def load_video_as_base64(video_path: str) -> tuple:
    """Load a video file and convert to base64."""
    path = Path(video_path)

    mime_types = {
        ".mp4": "video/mp4",
        ".webm": "video/webm",
        ".mov": "video/quicktime"
    }
    mime_type = mime_types.get(path.suffix.lower(), "video/mp4")

    with open(path, "rb") as f:
        data = base64.b64encode(f.read()).decode("utf-8")

    return data, mime_type


def format_list(items: list, max_items: int = 10, prefix: str = "- ") -> str:
    """Format a list for prompt display."""
    if not items:
        return "None detected"
    limited = items[:max_items]
    formatted = "\n".join(f"{prefix}{item}" for item in limited)
    if len(items) > max_items:
        formatted += f"\n{prefix}... and {len(items) - max_items} more"
    return formatted


def format_dict(data: dict, indent: int = 2) -> str:
    """Format a dictionary as YAML-like string for readability."""
    if not data:
        return "None"
    lines = []
    for key, value in data.items():
        if isinstance(value, dict):
            lines.append(f"{key}:")
            for k, v in value.items():
                lines.append(f"  {k}: {v}")
        elif isinstance(value, list):
            lines.append(f"{key}: {', '.join(str(v) for v in value[:5])}")
        else:
            lines.append(f"{key}: {value}")
    return "\n".join(lines)


# =============================================================================
# v4.0 Prompt Builder
# =============================================================================

def build_prompt_v4(
    url: str,
    html_content: str,
    frameworks: dict,
    layout: dict,
    components: dict,
    design_tokens: dict,
    animations: dict,
    svgs: dict
) -> str:
    """
    Build the v4.0 enhanced prompt with all extraction data.

    Args:
        url: The original website URL
        html_content: Cleaned HTML
        frameworks: Output from detect_frameworks.js
        layout: Output from analyze_layout.js
        components: Output from analyze_components.js
        design_tokens: Output from extract_design_tokens_v4.js
        animations: Output from map_animations_v4.js
        svgs: Output from extract_svgs.js

    Returns:
        Complete formatted prompt string
    """

    # Framework summary
    fw_summary = frameworks.get("summary", {})
    css_framework = fw_summary.get("css", "custom")
    animation_library = fw_summary.get("animation", "css-only")
    icon_library = fw_summary.get("icons", "inline-svg")
    component_library = fw_summary.get("components", "custom")
    build_tool = fw_summary.get("build", "nextjs")

    # UI Patterns
    ui_patterns_list = fw_summary.get("uiPatternsList", [])
    ui_patterns = format_list(ui_patterns_list, prefix="- Has ")

    # Layout data
    layout_summary = layout.get("summary", {})
    primary_layout = layout_summary.get("primaryLayout", "flexbox")

    # Grid layouts
    grid_data = layout.get("layoutMethod", {}).get("grid", [])
    grid_layouts = "\n".join(
        f"- {g.get('selector')}: columns={g.get('gridTemplateColumns', 'auto')}, gap={g.get('gap', 'auto')}"
        for g in grid_data[:5]
    ) if grid_data else "No CSS Grid detected"

    # Flexbox layouts
    flex_data = layout.get("layoutMethod", {}).get("flexbox", [])
    flexbox_layouts = "\n".join(
        f"- {f.get('selector')}: direction={f.get('flexDirection')}, justify={f.get('justifyContent')}"
        for f in flex_data[:5]
    ) if flex_data else "No Flexbox containers detected"

    # Z-index layers
    stacking = layout.get("stackingContexts", [])
    z_index_layers = "\n".join(
        f"- {s.get('selector')}: z-index={s.get('zIndex')} ({s.get('reason', '')})"
        for s in stacking[:5]
    ) if stacking else "No custom z-index layers"

    # Breakpoints
    breakpoints_data = layout.get("breakpoints", [])
    breakpoints = format_list([f"{b.get('value')}px ({b.get('type')})" for b in breakpoints_data])
    breakpoint_values = ", ".join(str(b.get("value")) + "px" for b in breakpoints_data[:4])

    # Components data
    comp_summary = components.get("summary", {})
    landmarks = format_list([
        f"{l.get('tag')} ({l.get('role')})" for l in components.get("landmarks", [])[:5]
    ])

    comp_list = components.get("components", [])
    components_str = "\n".join(
        f"- {c.get('type')}: {c.get('count')} found ({c.get('sampleSelector', '')})"
        for c in comp_list[:10]
    ) if comp_list else "No component patterns detected"

    sections_list = components.get("sections", [])
    sections = "\n".join(
        f"- {s.get('estimatedPurpose', 'unknown')}: {s.get('heading', s.get('id', 'untitled'))}"
        for s in sections_list[:10]
    ) if sections_list else "No sections identified"

    # Design tokens
    dt_summary = design_tokens.get("summary", {})

    # Colors by confidence
    high_colors = design_tokens.get("colors", {}).get("high", [])
    high_confidence_colors = "\n".join(
        f"- {c.get('hex')}: {c.get('context')} (used {c.get('count', 1)}x)"
        for c in high_colors[:10]
    ) if high_colors else "No high-confidence colors"

    medium_colors = design_tokens.get("colors", {}).get("medium", [])
    medium_confidence_colors = "\n".join(
        f"- {c.get('hex')}: {c.get('context')}"
        for c in medium_colors[:10]
    ) if medium_colors else "No medium-confidence colors"

    # Typography
    typography = design_tokens.get("typography", {})
    primary_font = typography.get("primary", "system-ui")
    heading_font = typography.get("heading") or primary_font
    font_weights = ", ".join(str(w) for w in typography.get("fontWeights", []))
    font_sizes = ", ".join(typography.get("fontSizes", [])[:10])

    # Font manifest
    font_manifest = design_tokens.get("fontManifest", {})
    font_manifest_str = ""
    for family, data in list(font_manifest.items())[:5]:
        weights = ", ".join(data.get("weights", []))
        font_manifest_str += f"- {family}: weights [{weights}]\n"
        for weight, url in list(data.get("urls", {}).items())[:3]:
            font_manifest_str += f"  - {weight}: {url}\n"
    if not font_manifest_str:
        font_manifest_str = "No @font-face rules detected"

    # Spacing
    spacing = design_tokens.get("spacing", {})
    spacing_scale = ", ".join(spacing.get("scale", [])[:15])

    # Visual effects
    shadows = format_list(design_tokens.get("shadows", [])[:5])
    border_radius = ", ".join(design_tokens.get("borderRadius", [])[:8])
    gradients = format_list(design_tokens.get("gradients", [])[:3])

    # CSS Variables
    css_vars = design_tokens.get("customProperties", {})
    css_variables = format_dict(dict(list(css_vars.items())[:10]))

    # Animations
    anim_summary = animations.get("summary", {})
    animation_lib_detail = anim_summary.get("animationLibrary", "css-only")

    timing = design_tokens.get("timingConstants", {})
    premium_easing = timing.get("premiumEasing", "ease-out")
    durations = ", ".join(timing.get("durations", [])[:5])

    staggers = animations.get("timingConstants", {}).get("staggers", [])
    staggers_str = "\n".join(
        f"- {s.get('container')}: stagger={s.get('staggerValue')}"
        for s in staggers[:5]
    ) if staggers else "No stagger patterns detected"

    # ScrollTriggers
    scroll_triggers = animations.get("gsapConfig", {}).get("scrollTriggers", [])
    if scroll_triggers:
        scroll_triggers_str = "\n".join(
            f"- {st.get('trigger')}: start=\"{st.get('start')}\", scrub={st.get('scrub')}"
            for st in scroll_triggers[:8]
        )
    else:
        scroll_reveal = animations.get("scrollRevealElements", [])
        if scroll_reveal:
            scroll_triggers_str = "\n".join(
                f"- {sr.get('selector')}: animation={sr.get('animation', 'fade')}"
                for sr in scroll_reveal[:8]
            )
        else:
            scroll_triggers_str = "No scroll animations detected"

    # Keyframes
    keyframes_data = animations.get("cssAnimations", {}).get("keyframes", [])
    keyframes = "\n".join(
        f"@keyframes {kf.get('name')}: {len(kf.get('frames', []))} frames"
        for kf in keyframes_data[:5]
    ) if keyframes_data else "No @keyframes detected"

    # Hover transitions
    hover_data = animations.get("hoverTransitions", [])
    hover_transitions = "\n".join(
        f"- {h.get('selector')}: {h.get('transition', '')[:50]}"
        for h in hover_data[:10]
    ) if hover_data else "No hover transitions detected"

    # SVGs
    svg_summary = svgs.get("summary", {})
    detected_icons = svg_summary.get("iconLibrary", "inline-svg")
    inline_svg_count = svg_summary.get("iconSvgs", 0)

    logo_svg = svgs.get("logoSvg")
    logo_svg_str = f"Logo SVG found ({logo_svg.get('viewBox', 'no viewBox')})" if logo_svg else "No logo SVG detected"

    icon_examples = svgs.get("inlineSvgs", [])[:5]
    icon_examples_str = "\n".join(
        f"- {ic.get('selector')}: {ic.get('pathCount', 0)} paths, viewBox={ic.get('viewBox', 'none')}"
        for ic in icon_examples
    ) if icon_examples else "No icon examples"

    # Component files to create
    estimated_sections = comp_summary.get("estimatedSections", [])
    component_files = "\n".join(
        f"- components/{section.title().replace('/', '')}.tsx"
        for section in estimated_sections
    ) if estimated_sections else "- components/Header.tsx\n- components/Footer.tsx"

    # Animation implementation instructions
    if animation_library == "gsap":
        animation_implementation = """### GSAP Implementation Required

Use this pattern for scroll animations:
```tsx
"use client";
import { useLayoutEffect, useRef } from "react";
import gsap from "gsap";
import { ScrollTrigger } from "gsap/ScrollTrigger";

if (typeof window !== "undefined") {
  gsap.registerPlugin(ScrollTrigger);
}

export default function Component() {
  const ref = useRef(null);

  useLayoutEffect(() => {
    const ctx = gsap.context(() => {
      gsap.from(".animate-element", {
        y: 50,
        opacity: 0,
        duration: 0.6,
        stagger: 0.12,
        ease: "power2.out",
        scrollTrigger: {
          trigger: ref.current,
          start: "top 80%",
          toggleActions: "play none none none"
        }
      });
    });
    return () => ctx.revert();
  }, []);

  return <div ref={ref}>...</div>;
}
```

Add to package.json: "gsap": "^3.12.5"
"""
    elif animation_library == "framerMotion":
        animation_implementation = """### Framer Motion Implementation Required

Use motion components for animations:
```tsx
"use client";
import { motion } from "framer-motion";

export default function Component() {
  return (
    <motion.div
      initial={{ opacity: 0, y: 20 }}
      whileInView={{ opacity: 1, y: 0 }}
      viewport={{ once: true }}
      transition={{ duration: 0.5, ease: [0.215, 0.61, 0.355, 1] }}
    >
      ...
    </motion.div>
  );
}
```

Add to package.json: "framer-motion": "^10.16.0"
"""
    elif animation_library == "aos":
        animation_implementation = """### AOS (Animate On Scroll) Implementation

Use data-aos attributes:
```tsx
"use client";
import { useEffect } from "react";
import AOS from "aos";
import "aos/dist/aos.css";

export default function Component() {
  useEffect(() => {
    AOS.init({ once: true, duration: 800 });
  }, []);

  return <div data-aos="fade-up">...</div>;
}
```

Add to package.json: "aos": "^2.3.4"
"""
    else:
        animation_implementation = """### CSS Animations Only

Use Tailwind animation utilities and @keyframes in globals.css:
```css
@keyframes fadeInUp {
  from { opacity: 0; transform: translateY(20px); }
  to { opacity: 1; transform: translateY(0); }
}

.animate-fade-in-up {
  animation: fadeInUp 0.6s ease-out forwards;
}
```
"""

    return CLONE_PROMPT_TEMPLATE_V4.format(
        url=url,
        css_framework=css_framework,
        animation_library=animation_library,
        icon_library=icon_library,
        component_library=component_library,
        build_tool=build_tool,
        ui_patterns=ui_patterns,
        primary_layout=primary_layout,
        grid_layouts=grid_layouts,
        flexbox_layouts=flexbox_layouts,
        z_index_layers=z_index_layers,
        breakpoints=breakpoints,
        breakpoint_values=breakpoint_values or "375px, 768px, 1024px, 1440px",
        landmarks=landmarks,
        components=components_str,
        sections=sections,
        high_confidence_colors=high_confidence_colors,
        medium_confidence_colors=medium_confidence_colors,
        primary_font=primary_font,
        heading_font=heading_font,
        font_weights=font_weights or "400, 500, 600, 700",
        font_sizes=font_sizes or "14px, 16px, 18px, 24px, 32px, 48px",
        font_manifest=font_manifest_str,
        spacing_scale=spacing_scale or "4px, 8px, 16px, 24px, 32px, 48px, 64px",
        shadows=shadows,
        border_radius=border_radius or "0px, 4px, 8px",
        gradients=gradients,
        css_variables=css_variables,
        animation_lib_detail=animation_lib_detail,
        premium_easing=premium_easing,
        durations=durations or "0.3s, 0.5s, 0.8s",
        staggers=staggers_str,
        scroll_triggers=scroll_triggers_str,
        keyframes=keyframes,
        hover_transitions=hover_transitions,
        detected_icons=detected_icons,
        inline_svg_count=inline_svg_count,
        logo_svg=logo_svg_str,
        icon_examples=icon_examples_str,
        component_files=component_files,
        animation_implementation=animation_implementation,
        html_content=html_content[:100000]  # Limit HTML size if needed
    )


def parse_generated_code(response_text: str) -> dict:
    """Parse Gemini's response to extract file paths and contents."""
    files = {}

    # Pattern to match code blocks with filepath
    pattern = r"```(?:filepath:)?([^\n`]+)\n(.*?)```"
    matches = re.findall(pattern, response_text, re.DOTALL)

    for filepath, content in matches:
        filepath = filepath.strip()
        content = content.strip()

        # Skip pure language identifiers
        if "/" not in filepath and "." not in filepath:
            continue

        # Normalize path
        if not filepath.startswith("/") and not filepath.startswith("./"):
            filepath = f"./{filepath}"

        files[filepath] = content

    # Fallback inference if no filepath-prefixed blocks
    if not files:
        code_blocks = re.findall(r"```(\w+)?\n(.*?)```", response_text, re.DOTALL)

        for lang, content in code_blocks:
            if "package.json" in content or '"name":' in content:
                files["./package.json"] = content.strip()
            elif "export default function" in content and "layout" in content.lower():
                files["./app/layout.tsx"] = content.strip()
            elif "export default function" in content:
                files["./app/page.tsx"] = content.strip()
            elif "@tailwind" in content:
                files["./app/globals.css"] = content.strip()

    return files


# =============================================================================
# Main API Function
# =============================================================================

def send_to_gemini_v4(
    artifacts_path: str,
    url: str = "unknown",
    model: str = "pro",
    output_path: Optional[str] = None
) -> dict:
    """
    Send all v4 artifacts to Gemini and get generated code.

    Args:
        artifacts_path: Path to folder containing all extraction artifacts
        url: The original website URL
        model: "pro" or "flash"
        output_path: Optional path to save generated files

    Returns:
        Dictionary with success status, files, and raw response
    """
    artifacts = Path(artifacts_path)

    # Load all artifact files
    def load_json(filename):
        path = artifacts / filename
        if path.exists():
            return json.loads(path.read_text())
        return {}

    frameworks = load_json("frameworks.json")
    layout = load_json("layout.json")
    components = load_json("components.json")
    design_tokens = load_json("design-tokens.json")
    animations = load_json("animations.json")
    svgs = load_json("svgs.json")

    html_path = artifacts / "source.html"
    html_content = html_path.read_text() if html_path.exists() else ""

    # Build prompt
    prompt = build_prompt_v4(
        url=url,
        html_content=html_content,
        frameworks=frameworks,
        layout=layout,
        components=components,
        design_tokens=design_tokens,
        animations=animations,
        svgs=svgs
    )

    # Build parts array
    parts = [{"text": prompt}]

    # Add screenshots
    screenshots_dir = artifacts / "screenshots"
    if screenshots_dir.exists():
        for img_path in sorted(screenshots_dir.glob("*.png"))[:15]:  # Limit to 15 images
            try:
                base64_data, mime_type = load_image_as_base64(str(img_path))
                parts.append({
                    "inline_data": {
                        "mime_type": mime_type,
                        "data": base64_data
                    }
                })
            except Exception as e:
                print(f"Warning: Could not load {img_path}: {e}")

    # Add scroll video if exists
    video_path = artifacts / "scroll-recording.webm"
    if not video_path.exists():
        video_path = artifacts / "scroll-recording.mp4"
    if video_path.exists():
        try:
            base64_data, mime_type = load_video_as_base64(str(video_path))
            parts.append({
                "inline_data": {
                    "mime_type": mime_type,
                    "data": base64_data
                }
            })
            print(f"Added scroll video: {video_path.name}")
        except Exception as e:
            print(f"Warning: Could not load video: {e}")

    # Build request with optimal v4 parameters
    model_name = MODELS.get(model, MODELS["pro"])

    request_body = {
        "contents": {
            "parts": parts
        },
        "generationConfig": {
            "temperature": 1.0,  # Google's recommendation for Gemini 3
            "maxOutputTokens": 65536,
            "topP": 0.95
        }
    }

    # Make API request
    api_url = f"{API_BASE}/{model_name}:generateContent"

    for attempt in range(MAX_RETRIES):
        try:
            print(f"\nSending to Gemini ({model_name})...")
            print(f"  - Prompt: {len(prompt)} chars")
            print(f"  - Images: {len([p for p in parts if 'inline_data' in p])}")

            response = requests.post(
                f"{api_url}?key={API_KEY}",
                headers={"Content-Type": "application/json"},
                json=request_body,
                timeout=REQUEST_TIMEOUT
            )

            if response.status_code != 200:
                error_msg = response.text
                print(f"API Error (attempt {attempt + 1}): {response.status_code}")

                if response.status_code == 429:
                    time.sleep(RETRY_DELAY * (attempt + 1))
                    continue
                elif response.status_code >= 500:
                    time.sleep(RETRY_DELAY)
                    continue
                else:
                    return {
                        "success": False,
                        "error": f"API Error {response.status_code}: {error_msg[:500]}"
                    }

            result = response.json()
            candidates = result.get("candidates", [])

            if not candidates:
                return {
                    "success": False,
                    "error": "No candidates in response"
                }

            content = candidates[0].get("content", {})
            parts_response = content.get("parts", [])

            response_text = ""
            for part in parts_response:
                if "text" in part:
                    response_text += part["text"]

            if not response_text:
                return {
                    "success": False,
                    "error": "No text in response"
                }

            # Parse generated code
            files = parse_generated_code(response_text)

            # Save files if output path provided
            if output_path and files:
                output_dir = Path(output_path)
                output_dir.mkdir(parents=True, exist_ok=True)

                for filepath, content in files.items():
                    clean_path = filepath.lstrip("./")
                    full_path = output_dir / clean_path
                    full_path.parent.mkdir(parents=True, exist_ok=True)
                    full_path.write_text(content)
                    print(f"  Created: {full_path}")

            return {
                "success": True,
                "files": files,
                "raw_response": response_text,
                "model_used": model_name,
                "file_count": len(files)
            }

        except requests.exceptions.Timeout:
            print(f"Timeout (attempt {attempt + 1})")
            if attempt < MAX_RETRIES - 1:
                time.sleep(RETRY_DELAY)
                continue
            return {"success": False, "error": "Request timed out"}

        except Exception as e:
            print(f"Error (attempt {attempt + 1}): {e}")
            if attempt < MAX_RETRIES - 1:
                time.sleep(RETRY_DELAY)
                continue
            return {"success": False, "error": str(e)}

    return {"success": False, "error": "Max retries exceeded"}


# =============================================================================
# CLI Interface
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Generate website clone using Gemini API (v4.0 Enhanced)"
    )
    parser.add_argument(
        "--artifacts", "-a",
        required=True,
        help="Path to folder containing all extraction artifacts"
    )
    parser.add_argument(
        "--url", "-u",
        default="unknown",
        help="Original website URL"
    )
    parser.add_argument(
        "--output", "-o",
        required=True,
        help="Output folder for generated project"
    )
    parser.add_argument(
        "--model", "-m",
        choices=["pro", "flash"],
        default="pro",
        help="Gemini model to use (default: pro)"
    )

    args = parser.parse_args()

    result = send_to_gemini_v4(
        artifacts_path=args.artifacts,
        url=args.url,
        model=args.model,
        output_path=args.output
    )

    if result["success"]:
        print(f"\n{'='*50}")
        print(f"SUCCESS! Generated {result['file_count']} files")
        print(f"{'='*50}")
        print(f"\nFiles created in: {args.output}")
        print(f"\nNext steps:")
        print(f"  cd {args.output}")
        print(f"  npm install")
        print(f"  npm run dev")
    else:
        print(f"\nERROR: {result['error']}")
        sys.exit(1)


if __name__ == "__main__":
    main()
