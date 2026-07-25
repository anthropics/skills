#!/usr/bin/env python3
"""Extract figures from a PDF paper by rendering pages at high DPI and cropping.

Usage:
    # Render all pages as high-res images (for manual crop planning)
    python extract_figures.py paper.pdf --render-pages --dpi 500

    # Crop a specific region from a page
    python extract_figures.py paper.pdf --crop 2 0.15 0.07 0.92 0.27 --name fig1_method

    # Crop multiple figures defined in a JSON spec
    python extract_figures.py paper.pdf --crop-spec figures.json

The crop spec JSON format:
[
    {"page": 2, "left": 0.15, "top": 0.07, "right": 0.92, "bottom": 0.27, "name": "fig1_method"},
    {"page": 4, "left": 0.12, "top": 0.05, "right": 0.90, "bottom": 0.35, "name": "fig2_arch"},
    ...
]
All coordinates are fractions of page width/height (0.0 to 1.0).

Outputs go to --outdir (default: figures/cropped/).
"""

import argparse
import json
import os
import sys


def render_page(doc, page_num, dpi=500):
    """Render a PDF page as a PIL Image at the given DPI."""
    import fitz
    from PIL import Image
    import io

    page = doc[page_num]
    scale = dpi / 72
    mat = fitz.Matrix(scale, scale)
    pix = page.get_pixmap(matrix=mat)
    return Image.open(io.BytesIO(pix.tobytes("png")))


def render_all_pages(pdf_path, outdir, dpi):
    """Render every page as a PNG for visual crop planning."""
    import fitz

    os.makedirs(outdir, exist_ok=True)
    doc = fitz.open(pdf_path)

    for i in range(len(doc)):
        img = render_page(doc, i, dpi)
        path = os.path.join(outdir, f"page_{i+1}.png")
        img.save(path)
        print(f"Page {i+1}: {img.size[0]}x{img.size[1]} -> {path}")

    print(f"\nRendered {len(doc)} pages at {dpi} DPI to {outdir}/")
    print("Use these images to determine crop coordinates (as fractions 0.0-1.0)")


def crop_figure(doc, page_num, left, top, right, bottom, name, outdir, dpi=500):
    """Crop a region from a PDF page and save it."""
    os.makedirs(outdir, exist_ok=True)

    img = render_page(doc, page_num - 1, dpi)  # 1-indexed page number
    w, h = img.size

    box = (int(w * left), int(h * top), int(w * right), int(h * bottom))
    cropped = img.crop(box)

    path = os.path.join(outdir, f"{name}.png")
    cropped.save(path)
    print(f"{name}: page {page_num}, crop ({left:.2f},{top:.2f})-({right:.2f},{bottom:.2f}) "
          f"-> {cropped.size[0]}x{cropped.size[1]} -> {path}")
    return path


def main():
    parser = argparse.ArgumentParser(description="Extract figures from PDF papers")
    parser.add_argument("pdf", help="Path to the PDF paper")
    parser.add_argument("--render-pages", action="store_true",
                        help="Render all pages as PNGs for crop planning")
    parser.add_argument("--crop", nargs=5, metavar=("PAGE", "LEFT", "TOP", "RIGHT", "BOTTOM"),
                        help="Crop a single region: page left top right bottom (fractions)")
    parser.add_argument("--name", default="figure",
                        help="Name for the cropped figure (with --crop)")
    parser.add_argument("--crop-spec", help="JSON file with multiple crop specifications")
    parser.add_argument("--dpi", type=int, default=500, help="Render DPI (default: 500)")
    parser.add_argument("--outdir", default="figures/cropped", help="Output directory")
    args = parser.parse_args()

    import fitz

    if args.render_pages:
        render_all_pages(args.pdf, os.path.join(os.path.dirname(args.outdir), "pages"), args.dpi)
        return

    doc = fitz.open(args.pdf)

    if args.crop:
        page, left, top, right, bottom = args.crop
        crop_figure(doc, int(page), float(left), float(top),
                    float(right), float(bottom), args.name, args.outdir, args.dpi)

    elif args.crop_spec:
        with open(args.crop_spec) as f:
            specs = json.load(f)
        for spec in specs:
            crop_figure(doc, spec["page"], spec["left"], spec["top"],
                        spec["right"], spec["bottom"], spec["name"],
                        args.outdir, args.dpi)
        print(f"\nExtracted {len(specs)} figures to {args.outdir}/")

    else:
        print("Specify --render-pages, --crop, or --crop-spec")
        sys.exit(1)


if __name__ == "__main__":
    main()
