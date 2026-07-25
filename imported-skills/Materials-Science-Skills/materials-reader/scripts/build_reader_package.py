from __future__ import annotations

import argparse
import csv
import json
import sys
from datetime import datetime, timezone
from pathlib import Path


REQUIRED_FILES = [
    "source_map.json",
    "paper.md",
    "translation_notes.md",
    "source_anchor_checklist.md",
    "figure_table_cards.md",
    "mechanism_evidence_table.csv",
    "dosage_window_table.csv",
    "citation_handoff.csv",
    "figure_handoff.csv",
    "review_handoff.md",
    "obsidian_note.md",
    "qa_report.md",
    "assets/asset_manifest.md",
    "assets/visual_asset_report.json",
]

CSV_HEADERS = {
    "mechanism_evidence_table.csv": [
        "claim_id",
        "source_anchor",
        "source_location",
        "original_excerpt",
        "evidence_layer",
        "evidence_type",
        "mechanism_interpretation",
        "boundary_note",
        "certainty_tier",
        "confidence_label",
        "missing_evidence_flag",
    ],
    "dosage_window_table.csv": [
        "claim_id",
        "source_anchor",
        "material_system",
        "dosage_or_ratio",
        "performance_metric",
        "measured_value",
        "test_condition",
        "workability_or_stability",
        "boundary_note",
        "missing_evidence_flag",
    ],
    "citation_handoff.csv": [
        "claim_id",
        "source_anchor",
        "source_location",
        "original_excerpt",
        "evidence_layer",
        "evidence_type",
        "source_role",
        "source_quality",
        "certainty_tier",
        "citation_role",
        "reviewer_risk",
        "missing_evidence_flag",
        "handoff_target",
    ],
    "figure_handoff.csv": [
        "claim_id",
        "source_anchor",
        "source_location",
        "original_excerpt",
        "evidence_layer",
        "evidence_type",
        "figure_archetype",
        "asset_id",
        "caption_boundary",
        "reviewer_risk",
        "certainty_tier",
        "missing_evidence_flag",
        "handoff_target",
    ],
}


def escape_csv_cell(value: object) -> str:
    text = "" if value is None else str(value)
    if text.startswith(("=", "+", "-", "@")):
        return "'" + text
    return text


def _ensure_inside(base: Path, target: Path) -> Path:
    base_resolved = base.resolve()
    target_resolved = target.resolve()
    if target_resolved != base_resolved and base_resolved not in target_resolved.parents:
        raise ValueError(f"Refusing to write outside output directory: {target}")
    return target


def _write_text(output_dir: Path, relative_path: str, content: str) -> Path:
    target = _ensure_inside(output_dir, output_dir / relative_path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(content, encoding="utf-8", newline="\n")
    return target


def _write_json(output_dir: Path, relative_path: str, payload: dict[str, object]) -> Path:
    return _write_text(
        output_dir,
        relative_path,
        json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
    )


def _write_csv(output_dir: Path, relative_path: str, header: list[str]) -> Path:
    target = _ensure_inside(output_dir, output_dir / relative_path)
    target.parent.mkdir(parents=True, exist_ok=True)
    with target.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow([escape_csv_cell(cell) for cell in header])
    return target


def _markdown_files(title: str, source_type: str, doi_or_url: str) -> dict[str, str]:
    return {
        "paper.md": (
            f"# {title or 'Untitled Paper'}\n\n"
            "## Metadata\n\n"
            f"- Source type: {source_type}\n"
            f"- DOI or URL: {doi_or_url}\n\n"
            "## Source Summary\n\n- Empty scaffold.\n\n"
            "## Claim Evidence Boundary\n\n- Add source-grounded rows.\n\n"
            "## Figure/Table Notes\n\n- Add inspected figure and table notes.\n\n"
            "## Missing Evidence\n\n- Keep unsupported claims flagged.\n"
        ),
        "translation_notes.md": (
            "# Translation Notes\n\n"
            "## Translation Status\n\n- Not requested or not started.\n\n"
            "## Chinese Interpretation\n\n- Add bounded interpretation when needed.\n"
        ),
        "source_anchor_checklist.md": (
            "# Source Anchor Checklist\n\n"
            "## Claim Anchors\n\n- [ ] Every claim has a source anchor.\n\n"
            "## Citation Anchors\n\n- [ ] Every citation handoff row has a source anchor.\n\n"
            "## Figure Anchors\n\n- [ ] Every figure handoff row has a source anchor.\n\n"
            "## Review Anchors\n\n- [ ] Every review handoff claim has a source anchor.\n\n"
            "## Missing Evidence Flags\n\n- [ ] Missing evidence remains explicit.\n"
        ),
        "figure_table_cards.md": (
            "# Figure And Table Cards\n\n"
            "## Figure Cards\n\n- No figures inspected yet.\n\n"
            "## Table Cards\n\n- No tables inspected yet.\n\n"
            "## Visual Risk Boundaries\n\n- Do not treat visual examples as mechanism proof.\n"
        ),
        "review_handoff.md": (
            "# Review Handoff\n\n"
            "## Review Claim Roles\n\n- Add claim roles after reading.\n\n"
            "## Mechanism Boundaries\n\n- Separate measured evidence from inference.\n\n"
            "## Missing Evidence\n\n- Add gaps.\n\n"
            "## Reviewer Risk\n\n- Add risk notes.\n"
        ),
        "obsidian_note.md": (
            f"# {title or 'Untitled Paper'}\n\n"
            "## Source Anchors\n\n- Empty scaffold.\n\n"
            "## Evidence Chain\n\n- Empty scaffold.\n\n"
            "## Figure And Table Cards\n\n- Empty scaffold.\n\n"
            "## Citation Handoff\n\n- Empty scaffold.\n\n"
            "## Figure Handoff\n\n- Empty scaffold.\n\n"
            "## Review Handoff\n\n- Empty scaffold.\n\n"
            "## QA Flags\n\n- Empty scaffold.\n"
        ),
        "qa_report.md": (
            "# Reader Package QA Report\n\n"
            "## Source Coverage\n\n- Status: scaffold\n\n"
            "## Figure/Table Coverage\n\n- Status: scaffold\n\n"
            "## Citation Handoff\n\n- Status: scaffold\n\n"
            "## Figure Handoff\n\n- Status: scaffold\n\n"
            "## Missing Evidence\n\n- Status: scaffold\n\n"
            "## Overclaim Risk\n\n- Status: scaffold\n\n"
            "## Absolute Path Leakage\n\n- Status: scaffold\n\n"
            "## Final Status\n\n- Status: scaffold\n"
        ),
        "assets/asset_manifest.md": (
            "# Asset Manifest\n\n"
            "No extracted assets yet. Keep generated visual files inside `assets/`.\n"
        ),
    }


def build_reader_package(
    output_dir: Path,
    metadata: dict[str, str],
    *,
    force: bool = False,
) -> dict[str, object]:
    """Create a standard reader package and return a JSON-safe report."""
    output_dir = Path(output_dir)
    if output_dir.exists() and any(output_dir.iterdir()) and not force:
        raise FileExistsError(
            f"Output directory is not empty; pass --force to overwrite scaffold files: {output_dir}"
        )
    output_dir.mkdir(parents=True, exist_ok=True)

    source_type = metadata.get("source_type", "")
    title = metadata.get("paper_title") or metadata.get("title", "")
    doi_or_url = metadata.get("doi_or_url") or metadata.get("doi", "")
    generated_at = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    created_files: list[str] = []

    manifest = {
        "package_type": "materials-reader-package",
        "skill_version": "1.2.0",
        "source_type": source_type,
        "paper_title": title,
        "doi_or_url": doi_or_url,
        "generated_at": generated_at,
        "required_files": REQUIRED_FILES,
        "handoff_targets": ["materials-citation", "materials-figure"],
        "evidence_boundary": "No unsupported claim is promoted without a source anchor.",
    }
    created_files.append(
        str(_write_json(output_dir, "package_manifest.json", manifest).relative_to(output_dir))
    )

    source_map = {
        "schema_version": "1.0",
        "source_type": source_type,
        "paper_title": title,
        "doi_or_url": doi_or_url,
        "sources": [],
    }
    created_files.append(
        str(_write_json(output_dir, "source_map.json", source_map).relative_to(output_dir))
    )

    visual_report = {
        "schema_version": "1.0",
        "package_type": "materials-reader-visual-assets",
        "assets": [],
        "warnings": [],
        "qa_status": "scaffold",
    }
    created_files.append(
        str(
            _write_json(
                output_dir, "assets/visual_asset_report.json", visual_report
            ).relative_to(output_dir)
        )
    )

    for relative_path, header in CSV_HEADERS.items():
        created_files.append(
            str(_write_csv(output_dir, relative_path, header).relative_to(output_dir))
        )

    for relative_path, content in _markdown_files(title, source_type, doi_or_url).items():
        created_files.append(
            str(_write_text(output_dir, relative_path, content).relative_to(output_dir))
        )

    assets_dir = _ensure_inside(output_dir, output_dir / "assets")
    (assets_dir / "rendered_pages").mkdir(parents=True, exist_ok=True)

    return {
        "status": "pass",
        "output_dir": str(output_dir),
        "created_files": sorted(created_files),
        "warnings": [],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build a reader package scaffold.")
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--source-type", required=True)
    parser.add_argument("--title", required=True)
    parser.add_argument("--doi", default="")
    parser.add_argument("--force", action="store_true")
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)

    try:
        report = build_reader_package(
            Path(args.output_dir),
            {
                "source_type": args.source_type,
                "paper_title": args.title,
                "doi_or_url": args.doi,
            },
            force=args.force,
        )
    except Exception as exc:
        report = {"status": "fail", "errors": [str(exc)], "warnings": []}
        if args.as_json:
            print(json.dumps(report, ensure_ascii=False, indent=2))
        else:
            print(str(exc), file=sys.stderr)
        return 1

    if args.as_json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        print(f"Created reader package at {report['output_dir']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
