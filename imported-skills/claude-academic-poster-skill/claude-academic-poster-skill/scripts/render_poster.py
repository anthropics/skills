#!/usr/bin/env python3
"""Render a poster PPTX to PDF and high-res inspection images.

Usage:
    # Full render with automatic region crops
    python render_poster.py poster.pptx

    # Custom inspection regions (as fraction of page)
    python render_poster.py poster.pptx --regions '{"left_top": [0, 0.25, 0.52, 0.55]}'

    # Higher DPI
    python render_poster.py poster.pptx --dpi 400

Outputs (in --outdir):
    poster.pdf              PDF export via LibreOffice
    full_render.png         Full poster at specified DPI
    overview.png            Scaled-down overview (1/3 size)
    region_*.png            Cropped inspection regions

Default regions split the content area into a 2x3 grid:
    header, left_top, right_top, left_bottom, right_bottom, footer
"""

import argparse
import json
import os
import subprocess
import sys


DEFAULT_REGIONS = {
    "header":       [0.0, 0.0,  1.0, 0.24],
    "left_top":     [0.0, 0.22, 0.52, 0.52],
    "right_top":    [0.48, 0.22, 1.0, 0.52],
    "left_bottom":  [0.0, 0.50, 0.52, 0.80],
    "right_bottom": [0.48, 0.50, 1.0, 0.80],
    "footer":       [0.0, 0.78, 1.0, 1.0],
}


def render(pptx_path, outdir, dpi, regions):
    import fitz
    from PIL import Image
    import io

    Image.MAX_IMAGE_PIXELS = 200_000_000  # poster renders are large

    os.makedirs(outdir, exist_ok=True)

    # Step 1: PPTX → PDF via LibreOffice
    pdf_path = os.path.join(outdir, "poster.pdf")
    result = subprocess.run(
        ["libreoffice", "--headless", "--convert-to", "pdf",
         pptx_path, "--outdir", outdir],
        capture_output=True, text=True, timeout=120,
    )
    # Rename to standard name
    base = os.path.splitext(os.path.basename(pptx_path))[0]
    src = os.path.join(outdir, f"{base}.pdf")
    if os.path.exists(src) and src != pdf_path:
        os.rename(src, pdf_path)

    if not os.path.exists(pdf_path):
        print(f"ERROR: LibreOffice conversion failed: {result.stderr}")
        sys.exit(1)

    print(f"PDF: {pdf_path}")

    # Step 2: PDF → high-res PNG via pymupdf
    doc = fitz.open(pdf_path)
    page = doc[0]
    scale = dpi / 72
    mat = fitz.Matrix(scale, scale)
    pix = page.get_pixmap(matrix=mat)
    img = Image.open(io.BytesIO(pix.tobytes("png")))
    w, h = img.size

    full_path = os.path.join(outdir, "full_render.png")
    img.save(full_path)
    print(f"Full render: {full_path} ({w}x{h})")

    # Overview (1/3 size)
    overview = img.resize((w // 3, h // 3))
    overview_path = os.path.join(outdir, "overview.png")
    overview.save(overview_path)
    print(f"Overview: {overview_path}")

    # Step 3: Crop inspection regions
    for name, (left, top, right, bottom) in regions.items():
        box = (int(w * left), int(h * top), int(w * right), int(h * bottom))
        crop = img.crop(box)
        crop_path = os.path.join(outdir, f"region_{name}.png")
        crop.save(crop_path)
        print(f"Region {name}: {crop_path} ({crop.size[0]}x{crop.size[1]})")

    # Also copy PDF to project root for convenience
    root_pdf = os.path.join(os.path.dirname(pptx_path),
                            os.path.splitext(os.path.basename(pptx_path))[0] + ".pdf")
    if os.path.abspath(root_pdf) != os.path.abspath(pdf_path):
        import shutil
        shutil.copy(pdf_path, root_pdf)
        print(f"PDF copy: {root_pdf}")

    print(f"\nDone. Inspect region_*.png images for overlaps and spacing issues.")


def main():
    parser = argparse.ArgumentParser(description="Render poster for visual inspection")
    parser.add_argument("pptx", help="Path to the poster .pptx file")
    parser.add_argument("--outdir", default="figures/render", help="Output directory")
    parser.add_argument("--dpi", type=int, default=350, help="Render DPI (default: 350)")
    parser.add_argument("--regions", type=str, default=None,
                        help="JSON dict of named regions {name: [left, top, right, bottom]}")
    args = parser.parse_args()

    regions = DEFAULT_REGIONS
    if args.regions:
        regions = json.loads(args.regions)

    render(args.pptx, args.outdir, args.dpi, regions)


if __name__ == "__main__":
    main()
