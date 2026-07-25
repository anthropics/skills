#!/usr/bin/env python3
"""Extract rendered PDF pages and cropped visual assets for WER-EA reading packages."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

try:
    from PIL import Image, ImageDraw
except ModuleNotFoundError as exc:  # pragma: no cover - dependency guard
    Image = None
    ImageDraw = None
    PIL_IMPORT_ERROR = exc
else:
    PIL_IMPORT_ERROR = None


@dataclass
class ExtractedAsset:
    asset_id: str
    kind: str
    paper_label: str
    source_page: int
    rendered_page_file: str
    asset_file: str
    crop_status: str
    crop_box: list[float]
    claim_supported: str
    claim_too_strong: str
    destination: str
    defects: str
    qa_status: str


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Render selected PDF pages, crop figure/table assets, and write a visual asset manifest.",
    )
    parser.add_argument("--pdf", required=True, help="Path to the source PDF. The file is read-only.")
    parser.add_argument("--package-dir", required=True, help="Paper package directory to receive assets/.")
    parser.add_argument("--spec", required=True, help="visual_asset_spec.json with page and crop specs.")
    parser.add_argument("--dpi", type=int, default=220, help="Rendering DPI. Default: 220.")
    parser.add_argument("--json", action="store_true", help="Print JSON report to stdout.")
    return parser.parse_args(argv)


def load_spec(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("visual asset spec must be a JSON object")
    assets = payload.get("assets")
    if not isinstance(assets, list) or not assets:
        raise ValueError("visual asset spec must contain a non-empty assets list")
    return payload


def require_runtime() -> Any:
    try:
        import fitz  # type: ignore
    except ModuleNotFoundError as exc:
        raise RuntimeError(
            "PyMuPDF is required for PDF page rendering. Install with: "
            "python -m pip install pymupdf>=1.24,<2"
        ) from exc
    if PIL_IMPORT_ERROR is not None:
        raise RuntimeError("Pillow is required for contact sheets. Install with: python -m pip install pillow>=10,<13")
    return fitz


def ensure_dirs(package_dir: Path) -> dict[str, Path]:
    assets_dir = package_dir / "assets"
    rendered_dir = assets_dir / "rendered_pages"
    figures_dir = assets_dir / "figures"
    tables_dir = assets_dir / "tables"
    for path in [assets_dir, rendered_dir, figures_dir, tables_dir]:
        path.mkdir(parents=True, exist_ok=True)
    clean_previous_generated_assets(assets_dir, [rendered_dir, figures_dir, tables_dir])
    return {
        "assets": assets_dir,
        "rendered_pages": rendered_dir,
        "figures": figures_dir,
        "tables": tables_dir,
    }


def clean_previous_generated_assets(assets_dir: Path, asset_dirs: list[Path]) -> None:
    for asset_dir in asset_dirs:
        for png_path in asset_dir.glob("*.png"):
            png_path.unlink()
    for generated_file in [
        assets_dir / "asset_manifest.md",
        assets_dir / "contact_sheet.png",
        assets_dir / "visual_asset_report.json",
    ]:
        if generated_file.exists():
            generated_file.unlink()


def render_page(doc: Any, page_number: int, dpi: int, output_path: Path) -> None:
    page = doc.load_page(page_number - 1)
    zoom = dpi / 72
    matrix = doc.__class__.__module__  # keep mypy quiet about dynamic fitz
    del matrix
    import fitz  # type: ignore

    pix = page.get_pixmap(matrix=fitz.Matrix(zoom, zoom), alpha=False)
    pix.save(str(output_path))


def normalize_crop_box(crop_box: list[Any], image_size: tuple[int, int]) -> tuple[int, int, int, int]:
    if len(crop_box) != 4:
        raise ValueError("crop_box must contain [left, top, right, bottom]")
    width, height = image_size
    values = [float(value) for value in crop_box]
    if all(0 <= value <= 1 for value in values):
        left, top, right, bottom = values
        box = (left * width, top * height, right * width, bottom * height)
    else:
        box = tuple(values)
    left, top, right, bottom = [int(round(value)) for value in box]
    left = max(0, min(left, width - 1))
    top = max(0, min(top, height - 1))
    right = max(left + 1, min(right, width))
    bottom = max(top + 1, min(bottom, height))
    return left, top, right, bottom


def crop_asset(rendered_page: Path, output_path: Path, crop_box: list[Any]) -> tuple[list[int], tuple[int, int]]:
    with Image.open(rendered_page) as image:  # type: ignore[union-attr]
        box = normalize_crop_box(crop_box, image.size)
        cropped = image.crop(box)
        cropped.save(output_path)
        return list(box), cropped.size


def make_contact_sheet(asset_paths: list[Path], output_path: Path) -> None:
    if not asset_paths:
        raise ValueError("no assets available for contact sheet")
    thumbs = []
    label_height = 28
    thumb_width = 360
    thumb_height = 260
    for path in asset_paths:
        with Image.open(path) as image:  # type: ignore[union-attr]
            thumb = image.copy()
            thumb.thumbnail((thumb_width, thumb_height - label_height))
            canvas = Image.new("RGB", (thumb_width, thumb_height), "white")
            x = (thumb_width - thumb.width) // 2
            y = 8
            canvas.paste(thumb.convert("RGB"), (x, y))
            draw = ImageDraw.Draw(canvas)  # type: ignore[union-attr]
            draw.text((8, thumb_height - label_height + 6), path.name[:48], fill="black")
            thumbs.append(canvas)
    columns = min(3, len(thumbs))
    rows = (len(thumbs) + columns - 1) // columns
    sheet = Image.new("RGB", (columns * thumb_width, rows * thumb_height), "white")
    for index, thumb in enumerate(thumbs):
        x = (index % columns) * thumb_width
        y = (index // columns) * thumb_height
        sheet.paste(thumb, (x, y))
    sheet.save(output_path)


def write_manifest(assets_dir: Path, paper_id: str, source_pdf_note: str, extracted: list[ExtractedAsset]) -> None:
    lines = [
        f"# Asset Manifest: {paper_id}",
        "",
        f"- Source PDF note: {source_pdf_note}",
        "- Visual check status: rendered pages and cropped assets generated from the read-only source PDF.",
        "- Contact sheet: `contact_sheet.png`",
        "",
        "| Asset ID | Kind | Paper label | Source page | Rendered page | Asset file | Crop status | Crop box | Claim supported | Claim too strong | Destination | Defects | QA status |",
        "|---|---|---|---:|---|---|---|---|---|---|---|---|---|",
    ]
    for item in extracted:
        lines.append(
            "| {asset_id} | {kind} | {paper_label} | {source_page} | {rendered_page_file} | "
            "{asset_file} | {crop_status} | {crop_box} | {claim_supported} | {claim_too_strong} | "
            "{destination} | {defects} | {qa_status} |".format(
                asset_id=item.asset_id,
                kind=item.kind,
                paper_label=item.paper_label,
                source_page=item.source_page,
                rendered_page_file=item.rendered_page_file,
                asset_file=item.asset_file,
                crop_status=item.crop_status,
                crop_box=json.dumps(item.crop_box),
                claim_supported=item.claim_supported,
                claim_too_strong=item.claim_too_strong,
                destination=item.destination,
                defects=item.defects,
                qa_status=item.qa_status,
            )
        )
    (assets_dir / "asset_manifest.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_assets_readme(assets_dir: Path, paper_id: str) -> None:
    text = f"""# Assets: {paper_id}

This folder contains rendered PDF pages and cropped visual assets for the WER-EA intensive-reading package.

## Layout

- `rendered_pages/`: source PDF pages rendered to PNG.
- `figures/`: cropped figure assets.
- `tables/`: cropped table assets.
- `contact_sheet.png`: quick visual QA sheet.
- `asset_manifest.md`: source page, crop status, claim boundary, and QA status.
- `visual_asset_report.json`: machine-readable extraction report.

Use these assets with `figure_table_cards.md`, `paper.md`, `review_handoff.md`, and `obsidian_note.md`. Do not treat a crop as mechanism proof unless the source evidence supports that claim.
"""
    (assets_dir / "README.md").write_text(text, encoding="utf-8")


def extract_assets(pdf_path: Path, package_dir: Path, spec_path: Path, dpi: int) -> dict[str, Any]:
    if not pdf_path.is_file():
        raise FileNotFoundError(f"source PDF not found: {pdf_path}")
    if not spec_path.is_file():
        raise FileNotFoundError(f"visual asset spec not found: {spec_path}")
    fitz = require_runtime()
    spec = load_spec(spec_path)
    dirs = ensure_dirs(package_dir)
    paper_id = str(spec.get("paper_id") or package_dir.name)
    source_pdf_note = str(spec.get("source_pdf_note") or "read-only source PDF")
    extracted: list[ExtractedAsset] = []
    crop_paths: list[Path] = []
    rendered_pages: dict[int, Path] = {}

    doc = fitz.open(str(pdf_path))
    try:
        for raw_asset in spec["assets"]:
            page_number = int(raw_asset["source_page"])
            if page_number < 1 or page_number > doc.page_count:
                raise ValueError(f"{raw_asset.get('asset_id')}: source_page {page_number} outside PDF page range")
            rendered_page = rendered_pages.get(page_number)
            if rendered_page is None:
                rendered_page = dirs["rendered_pages"] / f"page_{page_number:03d}.png"
                render_page(doc, page_number, dpi, rendered_page)
                rendered_pages[page_number] = rendered_page

            asset_id = str(raw_asset["asset_id"])
            kind = str(raw_asset.get("kind") or "figure")
            output_dir = dirs["tables"] if kind == "table" else dirs["figures"]
            output_path = output_dir / f"{asset_id.lower()}_{slugify(str(raw_asset.get('paper_label') or kind))}.png"
            crop_box, crop_size = crop_asset(rendered_page, output_path, raw_asset["crop_box"])
            crop_paths.append(output_path)
            qa_status = "pass" if crop_size[0] >= 200 and crop_size[1] >= 120 else "partial"
            defects = "none" if qa_status == "pass" else "crop is small; inspect manually"
            extracted.append(
                ExtractedAsset(
                    asset_id=asset_id,
                    kind=kind,
                    paper_label=str(raw_asset.get("paper_label") or ""),
                    source_page=page_number,
                    rendered_page_file=relative_for_manifest(rendered_page, dirs["assets"]),
                    asset_file=relative_for_manifest(output_path, dirs["assets"]),
                    crop_status="cropped",
                    crop_box=crop_box,
                    claim_supported=str(raw_asset.get("claim_supported") or ""),
                    claim_too_strong=str(raw_asset.get("claim_too_strong") or ""),
                    destination=str(raw_asset.get("destination") or ""),
                    defects=defects,
                    qa_status=qa_status,
                )
            )
    finally:
        doc.close()

    contact_sheet = dirs["assets"] / "contact_sheet.png"
    make_contact_sheet(crop_paths, contact_sheet)
    write_manifest(dirs["assets"], paper_id, source_pdf_note, extracted)
    write_assets_readme(dirs["assets"], paper_id)
    report = {
        "status": "pass",
        "paper_id": paper_id,
        "rendered_pages": [relative_for_manifest(path, dirs["assets"]) for path in rendered_pages.values()],
        "assets": [item.__dict__ for item in extracted],
        "contact_sheet": "contact_sheet.png",
        "asset_manifest": "asset_manifest.md",
    }
    (dirs["assets"] / "visual_asset_report.json").write_text(
        json.dumps(report, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    return report


def relative_for_manifest(path: Path, assets_dir: Path) -> str:
    return path.relative_to(assets_dir).as_posix()


def slugify(value: str) -> str:
    cleaned = []
    for char in value.lower():
        if char.isalnum():
            cleaned.append(char)
        elif char in {" ", "-", "_", "."}:
            cleaned.append("-")
    slug = "".join(cleaned).strip("-")
    while "--" in slug:
        slug = slug.replace("--", "-")
    return slug or "asset"


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        report = extract_assets(
            pdf_path=Path(args.pdf),
            package_dir=Path(args.package_dir),
            spec_path=Path(args.spec),
            dpi=args.dpi,
        )
    except Exception as exc:
        payload = {"status": "error", "error": str(exc)}
        if args.json:
            print(json.dumps(payload, ensure_ascii=False, indent=2))
        else:
            print(f"error: {exc}", file=sys.stderr)
        return 1
    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
