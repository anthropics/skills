#!/usr/bin/env python3
"""
2.5D Asset Inspector
Usage: python scripts/inspect-assets.py image1.png image2.jpg ...
   or: python scripts/inspect-assets.py path/to/folder/

Checks each image and reports:
- Format and mode
- Whether it has a real transparent background
- Background type if not transparent (dark, light, complex)
- Recommended depth level based on image characteristics
- Whether the background is likely a problem (product shot vs scene/artwork)

The AI reads this output and uses it to inform the user.
The script NEVER modifies images — inspect only.
"""

import argparse
import json
import sys
import os


def analyse_image(path):
    try:
        from PIL import Image
    except ImportError:
        print("Error: Pillow not installed. Install with: pip install Pillow")
        sys.exit(2)
    result = {
        "path": path,
        "filename": os.path.basename(path),
        "status": None,
        "format": None,
        "mode": None,
        "size": None,
        "bg_type": None,
        "bg_colour": None,
        "likely_needs_removal": None,
        "notes": [],
    }

    try:
        img = Image.open(path)
        result["format"] = img.format or os.path.splitext(path)[1].upper().strip(".")
        result["mode"] = img.mode
        result["size"] = img.size
        w, h = img.size

    except Exception as e:
        result["status"] = "ERROR"
        result["notes"].append(f"Could not open: {e}")
        return result

    # --- Alpha / transparency check ---
    if img.mode == "RGBA":
        extrema = img.getextrema()
        alpha_min = extrema[3][0]  # 0 = has real transparency, 255 = fully opaque
        if alpha_min == 0:
            result["status"] = "CLEAN"
            result["bg_type"] = "transparent"
            result["notes"].append("Real alpha channel with transparent pixels — clean cutout")
            result["likely_needs_removal"] = False
            return result
        else:
            result["notes"].append("RGBA mode but alpha is fully opaque — background was never removed")
            img = img.convert("RGB")  # treat as solid for analysis below

    if img.mode not in ("RGB", "L"):
        img = img.convert("RGB")

    # --- Sample corners and edges to detect background colour ---
    pixels = img.load()
    sample_points = [
        (0, 0), (w - 1, 0), (0, h - 1), (w - 1, h - 1),  # corners
        (w // 2, 0), (w // 2, h - 1),                       # top/bottom center
        (0, h // 2), (w - 1, h // 2),                       # left/right center
    ]

    samples = []
    for x, y in sample_points:
        try:
            px = pixels[x, y]
            if isinstance(px, int):
                px = (px, px, px)
            samples.append(px[:3])
        except Exception:
            pass

    if not samples:
        result["status"] = "UNKNOWN"
        result["notes"].append("Could not sample pixels")
        return result

    # --- Classify background ---
    avg_r = sum(s[0] for s in samples) / len(samples)
    avg_g = sum(s[1] for s in samples) / len(samples)
    avg_b = sum(s[2] for s in samples) / len(samples)
    avg_brightness = (avg_r + avg_g + avg_b) / 3

    # Check colour consistency (low variance = solid bg, high variance = scene/complex bg)
    max_r = max(s[0] for s in samples)
    max_g = max(s[1] for s in samples)
    max_b = max(s[2] for s in samples)
    min_r = min(s[0] for s in samples)
    min_g = min(s[1] for s in samples)
    min_b = min(s[2] for s in samples)
    variance = max(max_r - min_r, max_g - min_g, max_b - min_b)

    result["bg_colour"] = (int(avg_r), int(avg_g), int(avg_b))

    if variance > 80:
        result["status"] = "COMPLEX_BG"
        result["bg_type"] = "complex or scene"
        result["notes"].append(
            "Background varies significantly across edges — likely a scene, "
            "photograph, or artwork background rather than a solid colour"
        )
        result["likely_needs_removal"] = False  # complex bg = probably intentional content
        result["notes"].append(
            "JUDGMENT: Complex backgrounds usually mean this image IS the content "
            "(site screenshot, artwork, section bg). Background likely should be KEPT."
        )

    elif avg_brightness < 40:
        result["status"] = "DARK_BG"
        result["bg_type"] = "solid dark/black"
        result["notes"].append(
            f"Solid dark background detected — average edge brightness: {avg_brightness:.0f}/255"
        )
        result["likely_needs_removal"] = True
        result["notes"].append(
            "JUDGMENT: Dark studio backgrounds on product shots typically need removal. "
            "BUT if this is a screenshot, artwork, or intentionally dark composition, keep it."
        )

    elif avg_brightness > 210:
        result["status"] = "LIGHT_BG"
        result["bg_type"] = "solid white/light"
        result["notes"].append(
            f"Solid light background detected — average edge brightness: {avg_brightness:.0f}/255"
        )
        result["likely_needs_removal"] = True
        result["notes"].append(
            "JUDGMENT: White studio backgrounds on product shots typically need removal. "
            "BUT if this is a screenshot, UI mockup, or document, keep it."
        )

    else:
        result["status"] = "MIDTONE_BG"
        result["bg_type"] = "solid mid-tone colour"
        result["notes"].append(
            f"Solid mid-tone background detected — avg colour: RGB{result['bg_colour']}"
        )
        result["likely_needs_removal"] = None  # ambiguous — let AI judge
        result["notes"].append(
            "JUDGMENT: Ambiguous — could be a branded background (keep) or a "
            "studio colour backdrop (remove). AI must judge based on context."
        )

    # --- JPEG format warning ---
    if result["format"] in ("JPEG", "JPG"):
        result["notes"].append(
            "JPEG format — cannot store transparency. "
            "If bg removal is needed, user must provide a PNG version or approve CSS workaround."
        )

    # --- Size note ---
    if w > 2000 or h > 2000:
        result["notes"].append(
            f"Large image ({w}x{h}px) — resize before embedding. "
            "See references/asset-pipeline.md Step 3 for depth-appropriate targets."
        )

    return result


def print_report(results):
    print("\n" + "═" * 55)
    print("  2.5D Asset Inspector Report")
    print("═" * 55)

    for r in results:
        print(f"\n📁  {r['filename']}")
        print(f"    Format : {r['format']}  |  Mode: {r['mode']}  |  Size: {r['size']}")

        status_icons = {
            "CLEAN": "✅",
            "DARK_BG": "⚠️ ",
            "LIGHT_BG": "⚠️ ",
            "COMPLEX_BG": "🔵",
            "MIDTONE_BG": "❓",
            "UNKNOWN": "❓",
            "ERROR": "❌",
        }
        icon = status_icons.get(r["status"], "❓")
        print(f"    Status : {icon}  {r['status']}")

        if r["bg_type"]:
            print(f"    Bg type: {r['bg_type']}")

        if r["likely_needs_removal"] is True:
            print("    Removal: Likely needed (product/object shot)")
        elif r["likely_needs_removal"] is False:
            print("    Removal: Likely NOT needed (scene/artwork/content image)")
        else:
            print("    Removal: Ambiguous — AI must judge from context")

        for note in r["notes"]:
            print(f"    → {note}")

    print("\n" + "═" * 55)
    clean = sum(1 for r in results if r["status"] == "CLEAN")
    flagged = sum(1 for r in results if r["status"] in ("DARK_BG", "LIGHT_BG", "MIDTONE_BG"))
    complex_bg = sum(1 for r in results if r["status"] == "COMPLEX_BG")
    errors = sum(1 for r in results if r["status"] == "ERROR")

    print(f"  Clean: {clean}  |  Flagged: {flagged}  |  Complex/Scene: {complex_bg}  |  Errors: {errors}")
    print("═" * 55)
    print("\nNext step: Read JUDGMENT notes above and inform the user.")
    print("See references/asset-pipeline.md for the exact notification format.\n")


def collect_paths(args):
    paths = []
    for arg in args:
        if os.path.isdir(arg):
            for f in os.listdir(arg):
                if f.lower().endswith((".png", ".jpg", ".jpeg", ".webp", ".avif")):
                    paths.append(os.path.join(arg, f))
        elif os.path.isfile(arg):
            paths.append(arg)
        else:
            print(f"⚠️  Not found: {arg}")
    return paths


def main():
    parser = argparse.ArgumentParser(
        description="2.5D Asset Inspector — checks images for background type, "
        "transparency, and depth-level recommendations."
    )
    parser.add_argument(
        "paths",
        nargs="+",
        help="Image files or directories to inspect",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output results as JSON",
    )
    args = parser.parse_args()

    paths = collect_paths(args.paths)
    if not paths:
        print("No valid image files found.")
        sys.exit(1)

    results = [analyse_image(p) for p in paths]

    if args.json:
        print(json.dumps(results, indent=2, default=str))
    else:
        print_report(results)


if __name__ == "__main__":
    main()
