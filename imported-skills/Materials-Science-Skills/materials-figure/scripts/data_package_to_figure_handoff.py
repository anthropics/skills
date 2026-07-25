#!/usr/bin/env python3
"""Generate a figure package skeleton from a materials-data FAIR package.

This script closes the handoff gap between ``materials-data`` (which produces a
FAIR dataset package) and ``materials-figure`` (which needs a figure contract,
storyboard, source data, and plotting scaffold).

The output package contains the four files required by the
``figure_hard_workflow`` release checks (README.md, figure_storyboard.yaml,
caption_boundary.md, figure_qa_report.md) plus ``source_data.csv`` and
``plot.py`` templates.

Example
-------

.. code-block:: powershell

    python plugins/materials-skills/skills/materials-figure/scripts/data_package_to_figure_handoff.py `
        --dataset-dir ./ceramics_sintering_generic_fair_package `
        --output-dir ./figures `
        --claim "Sintering temperature and additive content jointly affect bulk density."
"""

from __future__ import annotations

import argparse
import csv
import re
import shutil
import sys
from pathlib import Path
from typing import Any

import yaml


FIGURE_CONTRACT = """# Figure Contract

## Core Conclusion

{claim}

## Evidence Chain

{figure_evidence_chain}

## Archetype

quantitative grid

## Backend

Python (matplotlib / seaborn) for all rendering and export.

## Journal/Export Contract

- Target width: single-column (8.5 cm) or double-column (17.5 cm).
- Editable text, source-data anchor, statistics summary, and image-integrity notes included.
- Export formats: SVG, PDF, PNG, TIFF.

## Statistics And Image Integrity

- Error bars represent mean +/- standard deviation of replicates.
- No image manipulation beyond uniform scaling and cropping.
- Data points and sample sizes reported in caption or panel labels.

## Reviewer Risk

- Correlation is not causation; design type ({design_type}) bounds causal claims.
- Extrapolation outside tested factor levels is not supported.
"""


CAPTION_BOUNDARY = """# Caption and Boundary

## What The Figure Supports

- Factor effects on measured response variables.
- Within the tested experimental design ({design_type}).

## What The Figure Does Not Prove

- Mechanism beyond statistical association.
- Generalization to factor levels or materials outside the design matrix.

## Source Anchor

- Source data: `source_data.csv` (raw experimental measurements).
- Linked FAIR package: `{dataset_dir}`.

## Caption Boundary

All claims are bounded by the factor ranges and response variables in the
linked experiment record.
"""


QA_REPORT = """# Figure QA Report

## Backend Exclusivity

- Python-only rendering planned; no AI-generated raster substitutes.

## Export Check

- SVG, PDF, PNG, TIFF exports planned.

## Source-Data Check

- Source data file present: `source_data.csv`.
- Columns match experiment record factors and response variables.

## Statistics Check

- Replicate aggregation and uncertainty to be computed from raw data.

## Image-Integrity Check

- No splicing, cloning, or selective omission planned.

## Caption-Boundary Check

- Caption distinguishes correlation from mechanism.

## QA Status

incomplete - awaiting measured response values and final rendering.
"""


PLOT_TEMPLATE = '''"""Plot figure for {title}.

Run this script after filling ``source_data.csv`` with measured response values.
"""

from __future__ import annotations

import matplotlib.pyplot as plt
import pandas as pd


def load_data() -> pd.DataFrame:
    return pd.read_csv("source_data.csv")


def main() -> None:
    df = load_data()
    # TODO: replace with domain-specific plotting logic.
    fig, ax = plt.subplots(figsize=(6, 4))
    ax.text(0.5, 0.5, "Plot scaffold for {title}", ha="center", va="center")
    fig.savefig("figure.pdf", bbox_inches="tight")
    fig.savefig("figure.png", dpi=300, bbox_inches="tight")
    print("figure.pdf and figure.png written")


if __name__ == "__main__":
    main()
'''


def _slug(value: str) -> str:
    cleaned = re.sub(r"[^a-zA-Z0-9]+", "_", value.lower()).strip("_")
    return cleaned[:70] or "figure_package"


def _read_csv_header(path: Path) -> list[str]:
    with path.open("r", encoding="utf-8-sig", newline="") as handle:
        reader = csv.reader(handle)
        return next(reader, [])


def _find_source_csv(dataset_dir: Path) -> Path | None:
    raw_dir = dataset_dir / "raw_data"
    candidates = list(raw_dir.glob("*.csv"))
    if not candidates:
        return None
    # Prefer experiment_data_template.csv if present.
    for candidate in candidates:
        if candidate.name == "experiment_data_template.csv":
            return candidate
    return candidates[0]


def _extract_metadata(dataset_dir: Path) -> dict[str, Any]:
    """Best-effort metadata extraction from metadata.md and linked record."""
    metadata: dict[str, Any] = {
        "title": dataset_dir.name.replace("_fair_package", "").replace("_", " "),
        "design_type": "custom",
        "material_family": "",
        "domain": "",
        "factors": [],
        "responses": [],
    }
    metadata_path = dataset_dir / "metadata.md"
    if metadata_path.exists():
        text = metadata_path.read_text(encoding="utf-8")
        for line in text.splitlines():
            if line.strip().startswith("- topic:"):
                metadata["title"] = line.split(":", 1)[1].strip() or metadata["title"]
            elif line.strip().startswith("- design_type:"):
                metadata["design_type"] = line.split(":", 1)[1].strip() or metadata["design_type"]
            elif line.strip().startswith("- material_domain:"):
                metadata["domain"] = line.split(":", 1)[1].strip()
            elif line.strip().startswith("- material_family:"):
                metadata["material_family"] = line.split(":", 1)[1].strip()

    link_path = dataset_dir / "experiment_record_link.yaml"
    if link_path.exists():
        try:
            link = yaml.safe_load(link_path.read_text(encoding="utf-8"))
            record_path = Path(link.get("source_record_path", ""))
            if record_path.exists():
                record = yaml.safe_load(record_path.read_text(encoding="utf-8"))
                metadata["title"] = record.get("title") or metadata["title"]
                metadata["design_type"] = record.get("design", {}).get("type") or metadata["design_type"]
                profile = record.get("direction_profile", {})
                metadata["material_family"] = profile.get("material_family") or metadata["material_family"]
                metadata["domain"] = profile.get("domain") or metadata["domain"]
                metadata["factors"] = [f.get("name", "") for f in record.get("factors", [])]
                metadata["responses"] = [r.get("name", "") for r in record.get("response_variables", [])]
        except Exception:
            pass

    return metadata


def _build_storyboard(
    factors: list[str], responses: list[str], title: str, design_type: str
) -> dict[str, Any]:
    panels: list[dict[str, Any]] = []
    for idx, response in enumerate(responses):
        panels.append(
            {
                "id": chr(ord("A") + idx),
                "role": "property-performance",
                "title": f"Effect on {response}",
                "claim": f"{response} varies with {', '.join(factors)} under {design_type} design.",
                "evidence": f"Measured {response} values from source_data.csv.",
                "source": "source_data.csv",
            }
        )
    return {
        "layout": f"{len(panels)}x1" if len(panels) <= 3 else "2x2",
        "title": title,
        "panels": panels,
    }


def _copy_source_data(src: Path | None, dest: Path) -> None:
    if src is not None and src.exists():
        shutil.copy2(src, dest)
        return
    # Create a minimal placeholder if no source CSV was found.
    dest.write_text("# source_data.csv placeholder - populate with measured values\n", encoding="utf-8")


def generate_figure_package(
    dataset_dir: Path,
    output_dir: Path,
    claim: str | None = None,
    archetype: str = "quantitative grid",
) -> Path:
    metadata = _extract_metadata(dataset_dir)
    title = metadata["title"]
    design_type = metadata["design_type"]
    material_family = metadata["material_family"]
    domain = metadata["domain"]

    source_csv = _find_source_csv(dataset_dir)
    header = _read_csv_header(source_csv) if source_csv else []

    # Prefer factor/response names from the linked experiment record.
    factors = [f for f in metadata.get("factors", []) if f]
    responses = [r for r in metadata.get("responses", []) if r]

    # Fallback: infer from CSV header. Standard FAIR CSV header is:
    # run_id, <factor_names...>, <response_names...>, replicate_count, notes
    if not factors or not responses:
        if "run_id" in header and "replicate_count" in header and "notes" in header:
            run_id_idx = header.index("run_id")
            replicate_idx = header.index("replicate_count")
            notes_idx = header.index("notes")
            middle = header[run_id_idx + 1 : min(replicate_idx, notes_idx)]
            # Heuristic: factors were added first, then responses.
            factors = middle if not factors else factors
            responses = middle if not responses else responses
        else:
            factors = header if not factors else factors
            responses = header if not responses else responses

    package_name = _slug(title) + "_figure_package"
    package_dir = output_dir / package_name
    package_dir.mkdir(parents=True, exist_ok=True)

    _copy_source_data(source_csv, package_dir / "source_data.csv")

    storyboard = _build_storyboard(factors, responses, title, design_type)
    (package_dir / "figure_storyboard.yaml").write_text(
        yaml.safe_dump(storyboard, sort_keys=False, allow_unicode=True),
        encoding="utf-8",
    )

    figure_claim = claim or f"{title} shows systematic dependence on experimental factors."
    evidence_lines = "\n".join(
        f"- Panel {p['id']}: {p['claim']} (source: {p['source']})" for p in storyboard["panels"]
    )
    (package_dir / "figure_contract.md").write_text(
        FIGURE_CONTRACT.format(
            claim=figure_claim,
            figure_evidence_chain=evidence_lines,
            design_type=design_type,
            archetype=archetype,
        ),
        encoding="utf-8",
    )

    (package_dir / "caption_boundary.md").write_text(
        CAPTION_BOUNDARY.format(
            design_type=design_type,
            dataset_dir=str(dataset_dir.resolve()),
        ),
        encoding="utf-8",
    )

    (package_dir / "figure_qa_report.md").write_text(QA_REPORT, encoding="utf-8")

    (package_dir / "plot.py").write_text(PLOT_TEMPLATE.format(title=title), encoding="utf-8")

    readme = f"""# {title} figure package

Generated from FAIR dataset package:

- material_family: {material_family or "[not set]"}
- domain: {domain or "[not set]"}
- design_type: {design_type}

## Contents

- `figure_storyboard.yaml` - narrative arc and panel roles
- `figure_contract.md` - claim, evidence chain, archetype, backend, export contract
- `caption_boundary.md` - supported claims and explicit boundaries
- `figure_qa_report.md` - QA checklist status
- `source_data.csv` - source data copied from the FAIR package
- `plot.py` - Python plotting scaffold

## Next steps

1. Fill measured response values in `source_data.csv`.
2. Implement domain-specific plotting logic in `plot.py`.
3. Run `python plot.py` to generate figure exports.
4. Audit the package with `materials-figure/scripts/audit_figure_package.py`.
"""
    (package_dir / "README.md").write_text(readme, encoding="utf-8")

    return package_dir


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dataset-dir", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--claim", default=None, help="One-sentence core conclusion for the figure")
    parser.add_argument("--archetype", default="quantitative grid", help="Figure archetype")
    args = parser.parse_args()

    if not args.dataset_dir.is_dir():
        print(f"Error: dataset directory not found: {args.dataset_dir}", file=sys.stderr)
        return 1

    args.output_dir.mkdir(parents=True, exist_ok=True)
    package_dir = generate_figure_package(
        dataset_dir=args.dataset_dir,
        output_dir=args.output_dir,
        claim=args.claim,
        archetype=args.archetype,
    )
    print(package_dir)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
