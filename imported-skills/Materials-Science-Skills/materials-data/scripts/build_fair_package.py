#!/usr/bin/env python3
"""Build a materials FAIR dataset package scaffold."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import Any

import yaml


try:
    import jsonschema
except ImportError:  # pragma: no cover
    jsonschema = None  # type: ignore[assignment]


SKILL_ROOT = Path(__file__).resolve().parents[1]
SCHEMA_PATH = SKILL_ROOT.parent / "_shared" / "core" / "experiment-record-schema.yaml"


_COMMON_CSV_COLUMNS = [
    "sample_id",
    "formulation_id",
    "binder_or_matrix",
    "modifier_or_additive",
    "dosage",
    "mixing_parameter_1",
    "mixing_parameter_2",
    "curing_condition",
    "test_standard",
    "temperature",
    "humidity",
    "replicate_count",
    "measured_property",
    "value",
    "unit",
    "raw_or_processed",
    "processing_note",
]


def csv_header_for_domain(domain: str) -> str:
    """Return a domain-adaptive CSV header line.

    Currently all domains share the same generic columns; the *domain*
    parameter is accepted so that domain-specific extensions can be added
    later without changing the call-site.
    """
    return ",".join(_COMMON_CSV_COLUMNS) + "\n"


def slug(value: str) -> str:
    cleaned = re.sub(r"[^a-zA-Z0-9]+", "_", value.lower()).strip("_")
    return cleaned[:70] or "materials_dataset"


def load_record(path: Path) -> dict[str, Any]:
    return yaml.safe_load(path.read_text(encoding="utf-8"))


def validate_record(record: dict[str, Any], schema_path: Path) -> None:
    """Validate record when jsonschema is available; otherwise warn and continue."""
    if jsonschema is None:
        print("warning: jsonschema not installed; skipping experiment-record schema validation", file=sys.stderr)
        return
    schema = yaml.safe_load(schema_path.read_text(encoding="utf-8"))
    jsonschema.validate(record, schema)


def csv_header_from_record(record: dict[str, Any]) -> str:
    factors = record.get("factors", [])
    responses = record.get("response_variables", [])
    cols = ["run_id"]
    cols.extend(f["name"] for f in factors)
    cols.extend(r["name"] for r in responses)
    cols.extend(["replicate_count", "notes"])
    return ",".join(cols) + "\n"


def metadata_from_record(record: dict[str, Any]) -> str:
    study_id = record.get("study_id", "[needs confirmation]")
    title = record.get("title", "[needs confirmation]")
    profile = record.get("direction_profile", {})
    domain = profile.get("domain", "[needs confirmation]")
    family = profile.get("material_family", "[needs confirmation]")
    design = record.get("design", {})
    design_type = design.get("type", "[needs confirmation]")
    run_count = len(design.get("runs", []))

    factors_block = "\n".join(
        f"- {f.get('name', '')}: levels={f.get('levels', [])}, unit={f.get('unit', '')}, type={f.get('type', '')}"
        for f in record.get("factors", [])
    ) or "- [needs confirmation]"

    responses_block = "\n".join(
        f"- {r.get('name', '')}: unit={r.get('unit', '')}, method={r.get('measurement_method', '')}, replicates={r.get('replicate_count', '')}"
        for r in record.get("response_variables", [])
    ) or "- [needs confirmation]"

    materials_block = "\n".join(
        f"- role={m.get('role', '')}, name={m.get('name', '')}, supplier={m.get('supplier') or '[needs supplier]'}, spec={m.get('specification') or '[needs specification]'}"
        for m in record.get("materials", [])
    ) or "- [needs confirmation]"

    processing_block = "\n".join(
        f"- step={p.get('step', '')}, equipment={p.get('equipment') or '[needs equipment]'}, parameters={p.get('parameters', {})}"
        for p in record.get("processing", [])
    ) or "- [needs confirmation]"

    char_block = "\n".join(
        f"- name={c.get('name', '')}, standard={c.get('standard') or '[needs standard]'}, instrument={c.get('instrument') or '[needs instrument]'}"
        for c in record.get("characterization", [])
    ) or "- [needs confirmation]"

    return f"""# Dataset Metadata

## Study Identity

- study_id: {study_id}
- topic: {title}
- material_domain: {domain}
- material_family: {family}
- target_journal: [needs confirmation]
- data_contact: [needs confirmation]
- repository_or_supplement_url: [needs confirmation]

## Experiment Design

- design_type: {design_type}
- run_count: {run_count}

### Factors

{factors_block}

### Response Variables

{responses_block}

## Materials

{materials_block}

## Processing

{processing_block}

## Characterization

{char_block}

## Data Locations

- raw_data_location: raw_data/
- processed_data_location: processed_data/
- figure_data_location: figures/
- processing_note: [needs confirmation]
- uncertainty_type: [SD/SE/CI/not applicable]

## Linked Record

- experiment_record: experiment_record_link.yaml
"""


def artifact_record(package_dir: Path, relative_path: str) -> dict[str, str]:
    path = package_dir / relative_path
    status = "ready" if path.exists() else "missing"
    return {"status": status, "path": relative_path}


def data_package_handoff(package_dir: Path) -> dict[str, Any]:
    return {
        "contract": "data-package",
        "contract_version": "1.0",
        "status": "ready",
        "producer": "materials-data",
        "package_dir": str(package_dir.resolve()),
        "artifacts": {
            "metadata": artifact_record(package_dir, "metadata.md"),
            "readme": artifact_record(package_dir, "README.md"),
            "data_availability_statement": artifact_record(
                package_dir,
                "data_availability_statement.md",
            ),
            "fair_audit": artifact_record(package_dir, "fair_audit.md"),
            "raw_data": artifact_record(package_dir, "raw_data"),
            "processed_data": artifact_record(package_dir, "processed_data"),
            "figures": artifact_record(package_dir, "figures"),
        },
    }


def build_package(
    topic: str,
    domain: str,
    journal: str,
    output_dir: Path,
    experiment_record: Path | None = None,
) -> Path:
    record: dict[str, Any] | None = None
    if experiment_record is not None:
        record = load_record(experiment_record)
        schema_path = SCHEMA_PATH if SCHEMA_PATH.exists() else Path("plugins/materials-skills/skills/_shared/core/experiment-record-schema.yaml")
        validate_record(record, schema_path)

    package_dir = output_dir / f"{slug(topic)}_{journal.lower()}_fair_package"
    raw_dir = package_dir / "raw_data"
    processed_dir = package_dir / "processed_data"
    figures_dir = package_dir / "figures"
    for directory in (raw_dir, processed_dir, figures_dir):
        directory.mkdir(parents=True, exist_ok=True)
        (directory / ".gitkeep").write_text("", encoding="utf-8")

    if record is not None:
        (raw_dir / "experiment_data_template.csv").write_text(csv_header_from_record(record), encoding="utf-8")
        (package_dir / "metadata.md").write_text(metadata_from_record(record), encoding="utf-8")
        (package_dir / "experiment_record_link.yaml").write_text(
            f"source_record_path: {experiment_record}\nrecord_version: {record.get('version', 'unknown')}\n",
            encoding="utf-8",
        )
    else:
        (raw_dir / "experiment_data_template.csv").write_text(csv_header_for_domain(domain), encoding="utf-8")
        (package_dir / "metadata.md").write_text(metadata(topic, domain, journal), encoding="utf-8")

    (package_dir / "README.md").write_text(readme(topic, journal), encoding="utf-8")
    (package_dir / "data_availability_statement.md").write_text(data_availability(journal), encoding="utf-8")
    (package_dir / "fair_audit.md").write_text(fair_audit(), encoding="utf-8")
    (package_dir / "data-package.yaml").write_text(
        yaml.safe_dump(data_package_handoff(package_dir), sort_keys=False, allow_unicode=False),
        encoding="utf-8",
    )
    return package_dir


def metadata(topic: str, domain: str, journal: str) -> str:
    return f"""# Dataset Metadata

## Study Identity

- topic: {topic}
- material_domain: {domain}
- target_journal: {journal}
- manuscript_section: [needs confirmation]
- data_contact: [needs confirmation]
- repository_or_supplement_url: [needs confirmation]

## Materials Science Fields

- sample_id: [stable sample identifier]
- formulation_id: [mix or formulation identifier]
- binder_or_matrix: [primary binder or matrix material]
- modifier_or_additive: [modifier, filler, or additive]
- dosage: [modifier dosage with unit]
- mixing_parameters: [key mixing/processing parameters]
- curing_condition: [curing or conditioning protocol]
- aging_condition: [thermal, UV, moisture, freeze-thaw, or none]
- test_standard: [applicable test standard]
- environmental_conditions: [temperature, humidity, aging]
- replicate_count: [number of replicates per condition]

## Processing

- raw_data_location: raw_data/
- processed_data_location: processed_data/
- figure_data_location: figures/
- processing_note: [needs confirmation]
- uncertainty_type: [SD/SE/CI/not applicable]
"""


def readme(topic: str, journal: str) -> str:
    return f"""# Dataset README

## Topic

{topic}

## Target Journal

{journal}

## Folder Structure

- `raw_data/`: original experimental records or instrument-export tables.
- `processed_data/`: cleaned, averaged, normalized, or figure-ready tables.
- `figures/`: figure files or figure-ready assets.
- `metadata.md`: sample, condition, unit, and processing metadata.
- `data_availability_statement.md`: manuscript-ready data availability language.
- `fair_audit.md`: FAIR checklist result.

## Reuse Notes

Check units, test_standard, replicate_count, temperature, humidity, curing_condition, and environmental_conditions before reusing this dataset.
"""


def data_availability(journal: str) -> str:
    return f"""# Data Availability Statement

For {journal} submission: Data supporting the findings of this study are provided in the accompanying dataset package, including raw experimental records, processed tables, figure-ready data, metadata, and processing notes.

If some raw files cannot be shared publicly, replace this with a request-only or mixed-availability statement and explain the access constraint.
"""


def fair_audit() -> str:
    return """# FAIR Audit

| FAIR item | Status | Evidence | Action |
|---|---|---|---|
| Findable | pass | metadata.md and README.md are present | Confirm repository URL if public |
| Accessible | pass | data_availability_statement.md is present | Confirm access constraints |
| Interoperable | pass | CSV template is present in raw_data | Add processed CSV after analysis |
| Reusable | pass | units, standards, replicates, and conditions are represented in metadata | Replace placeholders with confirmed values |
"""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--topic", required=True)
    parser.add_argument("--domain", default="generic")
    parser.add_argument("--journal", default="generic")
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--experiment-record", type=Path, default=None)
    args = parser.parse_args()

    package_dir = build_package(
        args.topic,
        args.domain,
        args.journal,
        Path(args.output_dir),
        args.experiment_record,
    )
    print(package_dir)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
