#!/usr/bin/env python3
"""Audit a materials figure package."""

# ============================================================================
# ARCHIVE REFERENCE SCRIPT
# ----------------------------------------------------------------------------
# This file is retained as an archival reference required by the
# `figure_hard_workflow` release checks. It is NOT part of the active
# automation pipeline. Do not rely on it for current figure auditing;
# see `static/core/figure-contract.md` and `static/core/contract.md` for
# the contract-driven validation used today.
# ============================================================================

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


REQUIRED_TEXT_FILES = [
    "figure_contract.md",
    "caption.md",
    "qa_report.md",
    "asset_manifest.md",
]

REQUIRED_EXPORTS = [
    "figure.svg",
    "figure.pdf",
    "figure.png",
    "figure.tiff",
]

SOURCE_ANCHOR_FILES = [
    "source_data.csv",
    "source_data.tsv",
    "source_map.json",
]

CONTRACT_TERMS = [
    "Core Conclusion",
    "Evidence Chain",
    "Archetype",
    "Backend",
    "Journal/Export Contract",
    "Statistics And Image Integrity",
    "WER-EA Boundary",
    "Reviewer Risk",
]

CAPTION_TERMS = [
    "What The Figure Supports",
    "What The Figure Does Not Prove",
    "Source Anchor",
    "Caption Boundary",
]

QA_TERMS = [
    "Backend Exclusivity",
    "Export Check",
    "Source-Data Check",
    "Statistics Check",
    "Image-Integrity Check",
    "Caption-Boundary Check",
    "QA Status",
]


def read_text(path: Path, issues: list[str]) -> str:
    if not path.is_file():
        issues.append(f"missing {path.name}")
        return ""
    text = path.read_text(encoding="utf-8", errors="replace")
    if "\ufffd" in text:
        issues.append(f"{path.name} contains replacement characters")
    return text


def audit_image(path: Path, issues: list[str]) -> None:
    if not path.is_file():
        issues.append(f"missing {path.name}")
        return
    try:
        from PIL import Image
    except ImportError:
        issues.append("Pillow is required to audit raster exports; install pillow")
        return
    try:
        with Image.open(path) as image:
            width, height = image.size
            if width < 100 or height < 100:
                issues.append(f"{path.name} dimensions too small: {width}x{height}")
    except Exception as exc:  # pragma: no cover - exact decoder errors vary
        issues.append(f"{path.name} cannot be opened: {exc}")


def audit_exports(package_dir: Path, issues: list[str]) -> None:
    svg = package_dir / "figure.svg"
    if not svg.is_file():
        issues.append("missing figure.svg")
    else:
        svg_text = svg.read_text(encoding="utf-8", errors="ignore")
        if "<svg" not in svg_text:
            issues.append("figure.svg does not contain <svg")

    pdf = package_dir / "figure.pdf"
    if not pdf.is_file():
        issues.append("missing figure.pdf")
    elif pdf.stat().st_size < 20:
        issues.append("figure.pdf is too small")

    audit_image(package_dir / "figure.png", issues)
    audit_image(package_dir / "figure.tiff", issues)


def collect_issues(package_dir: Path, *, source_only: bool = False) -> list[str]:
    issues: list[str] = []
    if not package_dir.is_dir():
        return [f"package directory not found: {package_dir}"]

    for relative in REQUIRED_TEXT_FILES:
        read_text(package_dir / relative, issues)

    contract = read_text(package_dir / "figure_contract.md", issues)
    caption = read_text(package_dir / "caption.md", issues)
    qa_report = read_text(package_dir / "qa_report.md", issues)
    manifest = read_text(package_dir / "asset_manifest.md", issues)

    for term in CONTRACT_TERMS:
        if term not in contract:
            issues.append(f"figure_contract.md missing {term}")
    for term in CAPTION_TERMS:
        if term not in caption:
            issues.append(f"caption.md missing {term}")
    for term in QA_TERMS:
        if term not in qa_report:
            issues.append(f"qa_report.md missing {term}")

    combined = "\n".join([contract, caption, qa_report, manifest]).lower()
    for term in ["backend", "source data", "reviewer", "boundary"]:
        if term not in combined:
            issues.append(f"package text missing {term!r}")

    if not (package_dir / "plot.py").is_file():
        issues.append("missing Python plotting script: plot.py")
    if not any((package_dir / data).is_file() for data in SOURCE_ANCHOR_FILES):
        issues.append("missing source data or source_map anchor file")

    if not source_only:
        audit_exports(package_dir, issues)
    return issues


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package-dir", required=True)
    parser.add_argument(
        "--source-only",
        action="store_true",
        help="Audit a reproducible repository example without requiring generated exports.",
    )
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    package_dir = Path(args.package_dir)
    issues = collect_issues(package_dir, source_only=args.source_only)
    status = "pass" if not issues else "incomplete"
    checked_files = len(REQUIRED_TEXT_FILES) + 2
    if not args.source_only:
        checked_files += len(REQUIRED_EXPORTS)
    report = {
        "status": status,
        "package_dir": str(package_dir),
        "mode": "source-only" if args.source_only else "production",
        "checked_files": checked_files,
        "issues": issues,
    }
    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    return 0 if status == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
