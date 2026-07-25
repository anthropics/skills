#!/usr/bin/env python3
"""Extract and crop figure regions for materials HTML decks."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Tuple

try:
    import fitz  # PyMuPDF
    from PIL import Image
except ImportError as exc:
    raise SystemExit("PyMuPDF and Pillow are required for figure extraction.") from exc


def extract_page_image(doc: fitz.Document, page_num: int, zoom: float = 2.0) -> Image.Image:
    """Render a PDF page to a Pillow image at the requested zoom."""
    page = doc.load_page(page_num)
    mat = fitz.Matrix(zoom, zoom)
    pix = page.get_pixmap(matrix=mat)
    return Image.frombytes("RGB", [pix.width, pix.height], pix.samples)


def crop_and_save(
    img: Image.Image,
    bbox: Tuple[float, float, float, float],
    output: Path,
) -> Path:
    """Crop *img* using normalized *bbox* and save to *output*."""
    width, height = img.size
    left = int(bbox[0] * width)
    top = int(bbox[1] * height)
    right = int(bbox[2] * width)
    bottom = int(bbox[3] * height)

    # Clamp to image bounds to guard against slightly out-of-range coordinates.
    left = max(0, min(left, width))
    top = max(0, min(top, height))
    right = max(left, min(right, width))
    bottom = max(top, min(bottom, height))

    cropped = img.crop((left, top, right, bottom))
    output.parent.mkdir(parents=True, exist_ok=True)
    cropped.save(output)
    return output


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pdf", required=True, help="Input PDF path")
    parser.add_argument(
        "--selections",
        required=True,
        help="JSON list of {page, bbox, output}; page is 1-based, bbox is normalized [0,1]",
    )
    parser.add_argument(
        "--manifest",
        default="output/asset_manifest.md",
        help="Output manifest path (default: output/asset_manifest.md)",
    )
    args = parser.parse_args(argv)

    pdf_path = Path(args.pdf)
    manifest_path = Path(args.manifest)
    output_dir = manifest_path.parent

    doc = fitz.open(pdf_path)
    selections = json.loads(Path(args.selections).read_text(encoding="utf-8"))

    manifest_lines = ["# Figure Asset Manifest", ""]
    for item in selections:
        page_num = int(item["page"]) - 1
        bbox = tuple(float(x) for x in item["bbox"])
        rel_path = item["output"]
        out_path = output_dir / rel_path

        img = extract_page_image(doc, page_num)
        crop_and_save(img, bbox, out_path)
        manifest_lines.append(f"- `{rel_path}`: page {page_num + 1}, bbox {bbox}")

    output_dir.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text("\n".join(manifest_lines), encoding="utf-8")
    print(manifest_path)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:  # noqa: BLE001
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
