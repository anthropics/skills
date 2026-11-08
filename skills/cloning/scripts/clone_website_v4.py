#!/usr/bin/env python3
"""
Website Cloning Orchestrator (v4.0)

This is the reference implementation for the enhanced cloning workflow.
In practice, Claude orchestrates this workflow directly using the claude-in-chrome
MCP tools, with this script serving as documentation and fallback.

v4.0 Enhancements:
- 7 new extraction layers for 98-100% fidelity
- Multi-viewport screenshots (mobile, tablet, desktop, wide)
- Confidence-scored design tokens
- Layout analysis (Grid/Flex/Z-index)
- Component semantic mapping
- SVG/icon extraction
- Deep animation configuration

The workflow:
1. PRE-ANALYSIS: Detect frameworks (Tailwind, GSAP, etc.)
2. CAPTURE: Multi-viewport screenshots at 2x DPI
3. DESIGN TOKENS: Confidence-scored color/font extraction
4. LAYOUT: Grid/Flexbox/Z-index analysis
5. COMPONENTS: ARIA landmarks, semantic structure
6. SVGS: Icon extraction and library detection
7. ANIMATIONS: Full ScrollTrigger/keyframe config
8. HTML: Clean source extraction
9. HOVER STATES: Exact CSS changes on hover
10. GEMINI: Send all data with v4 prompt template
11. OUTPUT: Generate Next.js 14 + Tailwind project

Usage (reference only - normally Claude does this interactively):
    python3 clone_website_v4.py https://example.com ./output-folder
"""

import argparse
import json
import os
import sys
from datetime import datetime
from pathlib import Path

# Import our other scripts
try:
    from gemini_api_v4 import send_to_gemini_v4
except ImportError:
    print("Warning: gemini_api_v4 not found. Using placeholder.")
    send_to_gemini_v4 = None


# =============================================================================
# Configuration
# =============================================================================

# Temp folder for artifacts
TEMP_BASE = Path("/tmp/claude/cloning")

# Screenshot settings
SCROLL_OVERLAP = 0.2  # 20% overlap between screenshots

# Viewports for multi-viewport capture
VIEWPORTS = [
    {'name': 'mobile', 'width': 375, 'height': 812},
    {'name': 'tablet', 'width': 768, 'height': 1024},
    {'name': 'desktop', 'width': 1440, 'height': 900},
    {'name': 'wide', 'width': 1920, 'height': 1080},
]


# =============================================================================
# JavaScript Extraction Scripts (v4.0)
# =============================================================================

def get_script_path(script_name: str) -> Path:
    """Get the path to a JavaScript extraction script."""
    scripts_dir = Path(__file__).parent
    return scripts_dir / script_name


def load_script(script_name: str) -> str:
    """Load a JavaScript extraction script."""
    script_path = get_script_path(script_name)
    if script_path.exists():
        return script_path.read_text()
    else:
        raise FileNotFoundError(f"Script not found: {script_path}")


# Script names for v4.0 extraction
V4_SCRIPTS = {
    'frameworks': 'detect_frameworks.js',
    'design_tokens': 'extract_design_tokens_v4.js',
    'layout': 'analyze_layout.js',
    'components': 'analyze_components.js',
    'svgs': 'extract_svgs.js',
    'animations': 'map_animations_v4.js',
    'hover_states': 'capture_hover_matrix.js',
}

# HTML extraction script
HTML_EXTRACTION_SCRIPT = """
(function extractHTML() {
    const html = document.documentElement.outerHTML;
    const parser = new DOMParser();
    const doc = parser.parseFromString(html, 'text/html');

    // Remove tracking/analytics scripts
    const scriptsToRemove = doc.querySelectorAll(
        'script[src*="analytics"], ' +
        'script[src*="gtag"], ' +
        'script[src*="tracking"], ' +
        'script[src*="pixel"], ' +
        'script[src*="hotjar"], ' +
        'script[src*="intercom"], ' +
        'script[src*="drift"], ' +
        'script[src*="hubspot"], ' +
        'noscript'
    );
    scriptsToRemove.forEach(s => s.remove());

    // Remove inline event handlers
    doc.querySelectorAll('*').forEach(el => {
        const attrs = el.attributes;
        for (let i = attrs.length - 1; i >= 0; i--) {
            const attr = attrs[i];
            if (attr.name.startsWith('on')) {
                el.removeAttribute(attr.name);
            }
        }
    });

    return doc.documentElement.outerHTML;
})();
"""


# =============================================================================
# Workflow Documentation
# =============================================================================

WORKFLOW_DOC = """
=====================================================================
WEBSITE CLONING WORKFLOW v4.0
=====================================================================

When the /cloningv2 skill is invoked, Claude performs these steps:

STEP 1: GATHER USER INPUT
-------------------------
Claude uses AskUserQuestion to ask:
a) URL (if not provided in the command)
b) Output location (where to save the cloned project)
c) Gemini model choice (pro or flash)

STEP 2: LOAD BROWSER TOOLS
--------------------------
MCPSearch to load:
- mcp__claude-in-chrome__tabs_context_mcp
- mcp__claude-in-chrome__navigate
- mcp__claude-in-chrome__computer
- mcp__claude-in-chrome__javascript_tool
- mcp__claude-in-chrome__resize_window

STEP 3: PRE-ANALYSIS (NEW in v4.0)
----------------------------------
Run detect_frameworks.js to identify:
- CSS framework (Tailwind, Bootstrap, Bulma, custom)
- Animation library (GSAP, Framer Motion, AOS, Lenis)
- Icon library (Heroicons, Lucide, Font Awesome)
- Component library (Radix, Headless UI, Chakra)

STEP 4: MULTI-VIEWPORT SCREENSHOTS (NEW in v4.0)
-----------------------------------------------
Capture at 4 viewports:
- Mobile (375x812)
- Tablet (768x1024)
- Desktop (1440x900)
- Wide (1920x1080)

Each at 2x DPI for Retina quality.

STEP 5: FULL-PAGE SCROLL CAPTURE
--------------------------------
At desktop viewport, scroll and capture with 20% overlap.
Stitch into single tall image for Gemini context.

STEP 6: DESIGN TOKEN EXTRACTION (Enhanced in v4.0)
--------------------------------------------------
Run extract_design_tokens_v4.js:
- Colors with HIGH/MEDIUM/LOW confidence
- Typography with font manifest (URLs)
- Spacing scale
- Premium easing functions

STEP 7: LAYOUT ANALYSIS (NEW in v4.0)
-------------------------------------
Run analyze_layout.js:
- Grid configurations (columns, gap)
- Flexbox configurations
- Z-index stacking contexts
- Responsive breakpoints

STEP 8: COMPONENT MAPPING (NEW in v4.0)
--------------------------------------
Run analyze_components.js:
- ARIA landmarks
- Component patterns (modal, dropdown, tabs, etc.)
- Section purposes (hero, features, pricing, etc.)

STEP 9: SVG/ICON EXTRACTION (NEW in v4.0)
-----------------------------------------
Run extract_svgs.js:
- Inline SVG capture
- Icon library detection
- Logo SVG isolation

STEP 10: ANIMATION MAPPING (Enhanced in v4.0)
---------------------------------------------
Run map_animations_v4.js:
- Full ScrollTrigger configuration
- @keyframes definitions
- Stagger patterns
- Easing functions

STEP 11: HOVER STATE CAPTURE
----------------------------
Run capture_hover_matrix.js:
- Exact CSS changes on hover
- Transition timing
- Confidence categorization

STEP 12: HTML EXTRACTION
------------------------
Clean HTML with tracking removed.

STEP 13: SEND TO GEMINI
-----------------------
Using gemini_api_v4.py with:
- v4 prompt template
- All extraction data
- Multi-viewport screenshots
- Scroll video (optional)

STEP 14: OUTPUT
---------------
Generate Next.js 14 + Tailwind project:
- app/page.tsx, layout.tsx, globals.css
- components/*.tsx
- tailwind.config.ts
- package.json

STEP 15: VERIFY (Optional)
--------------------------
Run npm run dev and take screenshot to compare.

=====================================================================
"""


# =============================================================================
# Helper Functions
# =============================================================================

def create_session_folder() -> Path:
    """Create a timestamped session folder for artifacts."""
    timestamp = datetime.now().strftime("%Y%m%d-%H%M%S")
    session_folder = TEMP_BASE / f"session-{timestamp}"
    session_folder.mkdir(parents=True, exist_ok=True)

    # Create subfolders
    (session_folder / "screenshots").mkdir(exist_ok=True)
    (session_folder / "extractions").mkdir(exist_ok=True)

    return session_folder


def save_artifact(session_folder: Path, filename: str, content: str) -> Path:
    """Save an artifact to the session folder."""
    filepath = session_folder / filename
    filepath.write_text(content)
    return filepath


def save_json_artifact(session_folder: Path, filename: str, data: dict) -> Path:
    """Save a JSON artifact to the session folder."""
    filepath = session_folder / filename
    filepath.write_text(json.dumps(data, indent=2))
    return filepath


def copy_artifacts_to_output(session_folder: Path, output_folder: Path) -> Path:
    """Copy cloning artifacts to the output folder for reference."""
    import shutil

    artifacts_folder = output_folder / "_cloning-artifacts"
    artifacts_folder.mkdir(parents=True, exist_ok=True)

    # Copy screenshots
    screenshots_dest = artifacts_folder / "screenshots"
    screenshots_dest.mkdir(exist_ok=True)

    screenshots_src = session_folder / "screenshots"
    if screenshots_src.exists():
        for img in screenshots_src.glob("*.png"):
            shutil.copy(img, screenshots_dest / img.name)

    # Copy extractions
    extractions_src = session_folder / "extractions"
    if extractions_src.exists():
        for f in extractions_src.glob("*.json"):
            shutil.copy(f, artifacts_folder / f.name)

    # Copy main artifacts
    for filename in ['design-tokens.json', 'source.html', 'frameworks.json',
                     'layout.json', 'components.json', 'svgs.json',
                     'animations.json', 'hover-states.json']:
        src = session_folder / filename
        if src.exists():
            shutil.copy(src, artifacts_folder / filename)

    return artifacts_folder


def print_workflow():
    """Print the workflow documentation."""
    print(WORKFLOW_DOC)


# =============================================================================
# Main Entry Point
# =============================================================================

def main():
    """
    CLI entry point (for reference/testing).

    In normal usage, Claude orchestrates this workflow directly
    using the instructions in SKILL.md.
    """
    parser = argparse.ArgumentParser(
        description="Clone a website's design (v4.0 reference implementation)"
    )
    parser.add_argument(
        "url",
        nargs='?',
        help="URL of the website to clone"
    )
    parser.add_argument(
        "output",
        nargs='?',
        help="Output folder for the generated project"
    )
    parser.add_argument(
        "--model", "-m",
        choices=["pro", "flash"],
        default="pro",
        help="Gemini model to use (default: pro)"
    )
    parser.add_argument(
        "--artifacts", "-a",
        help="Path to existing artifacts folder (skip capture step)"
    )
    parser.add_argument(
        "--workflow",
        action="store_true",
        help="Print the workflow documentation and exit"
    )
    parser.add_argument(
        "--list-scripts",
        action="store_true",
        help="List available extraction scripts"
    )

    args = parser.parse_args()

    if args.workflow:
        print_workflow()
        return

    if args.list_scripts:
        print("v4.0 Extraction Scripts")
        print("=" * 40)
        for name, filename in V4_SCRIPTS.items():
            script_path = get_script_path(filename)
            status = "✓" if script_path.exists() else "✗"
            print(f"  {status} {name}: {filename}")
        return

    if not args.url:
        print("Usage: python clone_website_v4.py <url> <output>")
        print()
        print("Options:")
        print("  --workflow       Print the full workflow documentation")
        print("  --list-scripts   List available extraction scripts")
        print("  --artifacts      Use pre-captured artifacts")
        print("  --model          Choose Gemini model (pro/flash)")
        return

    if not args.output:
        print("Error: Output folder is required")
        sys.exit(1)

    print("=" * 60)
    print("WEBSITE CLONING TOOL v4.0")
    print("=" * 60)
    print()
    print(f"URL: {args.url}")
    print(f"Output: {args.output}")
    print(f"Model: gemini-3.1-{args.model}-preview")
    print()

    if args.artifacts:
        # Use existing artifacts
        session_folder = Path(args.artifacts)
        print(f"Using existing artifacts from: {session_folder}")
    else:
        print("NOTE: This script is a reference implementation.")
        print("In normal usage, Claude captures data interactively")
        print("using the claude-in-chrome browser extension.")
        print()
        print("To use this script, provide pre-captured artifacts with --artifacts")
        print()
        print("Expected artifacts structure:")
        print("  <folder>/")
        print("    screenshots/")
        print("      viewport-mobile.png")
        print("      viewport-tablet.png")
        print("      viewport-desktop.png")
        print("      viewport-wide.png")
        print("      01-scroll-0.png, 02-scroll-500.png, ...")
        print("    extractions/")
        print("      frameworks.json")
        print("      design-tokens.json")
        print("      layout.json")
        print("      components.json")
        print("      svgs.json")
        print("      animations.json")
        print("      hover-states.json")
        print("    source.html")
        sys.exit(1)

    # Validate artifacts
    screenshots_folder = session_folder / "screenshots"
    screenshots = sorted(screenshots_folder.glob("*.png"))
    extractions_folder = session_folder / "extractions"

    if not screenshots:
        print(f"ERROR: No screenshots found in {screenshots_folder}")
        sys.exit(1)

    print(f"Found {len(screenshots)} screenshots")

    # Load extraction data
    extraction_data = {}
    for name, filename in V4_SCRIPTS.items():
        json_file = extractions_folder / f"{name}.json"
        if json_file.exists():
            extraction_data[name] = json.loads(json_file.read_text())
            print(f"Loaded {name} data")

    # Load HTML
    html_file = session_folder / "source.html"
    if html_file.exists():
        html_content = html_file.read_text()
        print(f"Loaded source.html ({len(html_content)} bytes)")
    else:
        print("Warning: source.html not found")
        html_content = ""

    # Send to Gemini
    if send_to_gemini_v4 is None:
        print()
        print("ERROR: gemini_api_v4 module not available")
        print("Cannot send to Gemini API")
        sys.exit(1)

    print()
    print("Sending to Gemini API...")
    print("This may take several minutes for complex sites.")
    print()

    result = send_to_gemini_v4(
        artifacts_path=str(session_folder),
        url=args.url,
        model=args.model,
        output_path=args.output
    )

    if result.get("success"):
        # Copy artifacts
        output_folder = Path(args.output)
        copy_artifacts_to_output(session_folder, output_folder)

        print()
        print("=" * 60)
        print("SUCCESS!")
        print("=" * 60)
        files = result.get("files", {})
        print()
        print(f"Generated {len(files)} files in: {args.output}")
        print()
        print("Files created:")
        for filepath in sorted(files.keys()):
            print(f"  {filepath}")
        print()
        print("Cloning artifacts saved to:")
        print(f"  {args.output}/_cloning-artifacts/")
        print()
        print("Next steps:")
        print(f"  cd {args.output}")
        print("  npm install")
        print("  npm run dev")
        print()
    else:
        print()
        print("=" * 60)
        print("ERROR")
        print("=" * 60)
        print()
        print(f"Failed: {result.get('error', 'Unknown error')}")
        print()
        raw_response = result.get("raw_response")
        if raw_response:
            print("Raw response (first 1000 chars):")
            print(raw_response[:1000])
        sys.exit(1)


if __name__ == "__main__":
    main()
