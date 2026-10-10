#!/usr/bin/env python3
"""
Screenshot Stitching Script (v4.0)

Combines multiple scroll screenshots into one tall full-page image.
This helps Gemini understand the complete page layout at once.

Usage:
    python stitch_screenshots.py <screenshot_folder> <output_path> [--overlap 0.2]

Example:
    python stitch_screenshots.py /tmp/screenshots/ /tmp/fullpage.png --overlap 0.2
"""

import argparse
import os
import sys

try:
    from PIL import Image
except ImportError:
    print("Error: Pillow is required. Install with: pip install Pillow")
    sys.exit(1)


def stitch_screenshots(
    screenshot_folder: str,
    output_path: str,
    overlap_percent: float = 0.2,
    max_height: int = 32000  # Prevent extremely tall images
) -> str:
    """
    Stitch multiple scroll screenshots into one tall image.

    Args:
        screenshot_folder: Folder containing numbered screenshots
        output_path: Where to save the stitched image
        overlap_percent: How much screenshots overlap (default 20%)
        max_height: Maximum output height in pixels

    Returns:
        Path to the stitched image
    """
    # Get all scroll screenshots (not hover/interaction ones)
    files = sorted([
        f for f in os.listdir(screenshot_folder)
        if f.endswith(('.png', '.jpg', '.jpeg')) and ('scroll' in f.lower() or f[0].isdigit())
    ])

    if not files:
        print(f"No scroll screenshots found in {screenshot_folder}")
        return None

    print(f"Found {len(files)} screenshots to stitch")

    # Load all images
    images = [Image.open(os.path.join(screenshot_folder, f)) for f in files]

    # Calculate total height accounting for overlap
    width = images[0].width
    viewport_height = images[0].height
    overlap = int(viewport_height * overlap_percent)

    total_height = viewport_height + (len(images) - 1) * (viewport_height - overlap)

    # Check if we're exceeding max height
    if total_height > max_height:
        print(f"Warning: Total height ({total_height}px) exceeds max ({max_height}px)")
        print("Limiting number of images to prevent memory issues")

        # Calculate how many images we can use
        max_images = 1 + (max_height - viewport_height) // (viewport_height - overlap)
        images = images[:max_images]
        total_height = viewport_height + (len(images) - 1) * (viewport_height - overlap)
        print(f"Using {len(images)} images, resulting in {total_height}px height")

    print(f"Creating stitched image: {width}x{total_height}px")

    # Create stitched image
    stitched = Image.new('RGB', (width, total_height))

    y = 0
    for i, img in enumerate(images):
        stitched.paste(img, (0, y))
        print(f"  Pasted screenshot {i+1}/{len(images)} at y={y}")
        y += viewport_height - overlap

    stitched.save(output_path, quality=95, optimize=True)
    print(f"Saved stitched image to: {output_path}")

    # Print size info
    file_size = os.path.getsize(output_path)
    print(f"File size: {file_size / 1024 / 1024:.2f} MB")

    return output_path


def stitch_viewports(
    screenshot_paths: list,
    output_path: str,
    layout: str = 'horizontal'
) -> str:
    """
    Stitch multiple viewport screenshots side by side.

    This is used for showing responsive design:
    [Mobile | Tablet | Desktop | Wide]

    Args:
        screenshot_paths: List of paths to viewport screenshots
        output_path: Where to save the composite image
        layout: 'horizontal' or 'vertical'

    Returns:
        Path to the composite image
    """
    if not screenshot_paths:
        print("No viewport screenshots provided")
        return None

    images = [Image.open(p) for p in screenshot_paths]

    if layout == 'horizontal':
        # Calculate dimensions
        total_width = sum(img.width for img in images)
        max_height = max(img.height for img in images)

        # Create composite
        composite = Image.new('RGB', (total_width, max_height), color='white')

        x = 0
        for img in images:
            # Center vertically
            y = (max_height - img.height) // 2
            composite.paste(img, (x, y))
            x += img.width

    else:  # vertical
        # Calculate dimensions
        max_width = max(img.width for img in images)
        total_height = sum(img.height for img in images)

        # Create composite
        composite = Image.new('RGB', (max_width, total_height), color='white')

        y = 0
        for img in images:
            # Center horizontally
            x = (max_width - img.width) // 2
            composite.paste(img, (x, y))
            y += img.height

    composite.save(output_path, quality=95, optimize=True)
    print(f"Saved viewport composite to: {output_path}")

    return output_path


def main():
    parser = argparse.ArgumentParser(
        description="Stitch scroll screenshots into a single full-page image"
    )
    parser.add_argument("screenshot_folder", help="Folder containing screenshots")
    parser.add_argument("output_path", help="Output path for stitched image")
    parser.add_argument(
        "--overlap",
        type=float,
        default=0.2,
        help="Overlap percentage between screenshots (default: 0.2)"
    )
    parser.add_argument(
        "--max-height",
        type=int,
        default=32000,
        help="Maximum output height in pixels (default: 32000)"
    )

    args = parser.parse_args()

    if not os.path.isdir(args.screenshot_folder):
        print(f"Error: {args.screenshot_folder} is not a directory")
        sys.exit(1)

    result = stitch_screenshots(
        args.screenshot_folder,
        args.output_path,
        args.overlap,
        args.max_height
    )
    if not result:
        sys.exit(1)


if __name__ == "__main__":
    main()
