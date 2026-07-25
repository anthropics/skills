#!/usr/bin/env python3
"""Convert a materials-doe experiment plan CSV into an experiment-record.yaml.

This script closes the handoff gap between ``materials-doe`` (which produces
``experiment_plan.csv``) and ``materials-data`` (which consumes
``experiment-record.yaml``). The generated record validates against the shared
schema in ``_shared/core/experiment-record-schema.yaml``.

Example
-------

.. code-block:: powershell

    python plugins/materials-skills/skills/materials-doe/scripts/doe_plan_to_experiment_record.py `
        --plan-csv experiment_plan.csv `
        --output experiment-record.yaml `
        --study-id ceramics-sintering-001 `
        --title "Sintering temperature optimization" `
        --material-family ceramics `
        --domain ceramics `
        --design-type L9 `
        --factors '[{"name":"sintering_temperature","unit":"degC","type":"continuous","levels":[1400,1500,1600]},
                    {"name":"additive_content","unit":"wt%","type":"continuous","levels":[0,1,2]}]' `
        --responses '[{"name":"bulk_density","unit":"g/cm3","measurement_method":"Archimedes","replicate_count":3}]'
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from datetime import date
from pathlib import Path
from typing import Any

import yaml

try:
    import jsonschema
except ImportError:  # pragma: no cover
    jsonschema = None  # type: ignore[assignment]


DOE_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SCHEMA = DOE_ROOT.parent / "_shared" / "core" / "experiment-record-schema.yaml"
TAGUCHI_ARRAY_LABELS = {"L9", "L16", "L25"}


def _today() -> str:
    return date.today().isoformat()


def _infer_factor_columns(header: list[str]) -> list[str]:
    """Return CSV columns that look like factor_A, factor_B, ..."""
    return [h for h in header if h.lower().startswith("factor_")]


def _infer_response_columns(header: list[str]) -> list[str]:
    """Return CSV columns that look like response_1, response_2, ..."""
    return [h for h in header if h.lower().startswith("response_")]


def _load_plan(path: Path) -> tuple[list[str], list[dict[str, Any]]]:
    text = path.read_text(encoding="utf-8-sig")
    reader = csv.DictReader(text.splitlines())
    header = reader.fieldnames or []
    rows = list(reader)
    return header, rows


def _parse_json_or_fail(raw: str, label: str) -> list[dict[str, Any]]:
    try:
        value = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise SystemExit(f"Invalid JSON for {label}: {exc}")
    if not isinstance(value, list):
        raise SystemExit(f"{label} must be a JSON list of objects")
    return [dict(item) for item in value]


def _build_factors(
    header: list[str],
    rows: list[dict[str, Any]],
    factor_cols: list[str] | None,
    factor_specs: list[dict[str, Any]] | None,
) -> tuple[list[dict[str, Any]], list[str]]:
    """Return (factors list, ordered factor column names)."""
    if factor_cols is None:
        factor_cols = _infer_factor_columns(header)
    if not factor_cols:
        raise SystemExit("No factor columns found in CSV. Provide --factor-cols or headers like factor_A.")

    if factor_specs is not None:
        if len(factor_specs) != len(factor_cols):
            raise SystemExit(
                f"--factors length ({len(factor_specs)}) does not match factor columns ({len(factor_cols)})"
            )
        factors: list[dict[str, Any]] = []
        for spec, col in zip(factor_specs, factor_cols):
            levels = sorted({_cast_number(row[col]) for row in rows if row.get(col) not in (None, "")})
            factors.append(
                {
                    "name": spec.get("name", col),
                    "unit": spec.get("unit", ""),
                    "type": spec.get("type", "continuous"),
                    "levels": spec.get("levels", levels),
                }
            )
        return factors, factor_cols

    factors = []
    for col in factor_cols:
        levels = sorted({_cast_number(row[col]) for row in rows if row.get(col) not in (None, "")})
        factors.append({"name": col, "unit": "", "type": "continuous", "levels": levels})
    return factors, factor_cols


def _build_responses(
    header: list[str],
    response_cols: list[str] | None,
    response_specs: list[dict[str, Any]] | None,
) -> list[dict[str, Any]]:
    explicit_response_cols = response_cols is not None
    if response_cols is None:
        response_cols = _infer_response_columns(header)

    if response_specs is not None:
        if explicit_response_cols and len(response_specs) != len(response_cols):
            raise SystemExit(
                f"--responses length ({len(response_specs)}) does not match response columns ({len(response_cols)})"
            )
        return [
            {
                "name": spec.get("name", col),
                "unit": spec.get("unit", ""),
                "measurement_method": spec.get("measurement_method", ""),
                "replicate_count": spec.get("replicate_count", 3),
            }
            for spec, col in zip(response_specs, response_cols or [f"response_{i}" for i in range(len(response_specs))])
        ]

    if not response_cols:
        # No response columns yet; experiments have not been run.
        return []

    return [
        {"name": col, "unit": "", "measurement_method": "", "replicate_count": 3}
        for col in response_cols
    ]


def _cast_number(value: Any) -> Any:
    if value is None:
        return ""
    text = str(value).strip()
    if text == "":
        return ""
    try:
        if "." in text:
            return float(text)
        return int(text)
    except ValueError:
        return text


def _build_runs(
    rows: list[dict[str, Any]],
    factor_cols: list[str],
    response_cols: list[str],
) -> list[dict[str, Any]]:
    runs = []
    for idx, row in enumerate(rows, start=1):
        run_id = str(row.get("exp_id", row.get("run_id", f"R{idx}"))).strip() or f"R{idx}"
        factor_levels = {col: _cast_number(row[col]) for col in factor_cols if col in row}
        runs.append(
            {
                "run_id": run_id,
                "factor_levels": factor_levels,
                "randomization_order": int(row.get("randomization_order", idx) or idx),
                "block": _cast_number(row.get("block", 1) or 1),
                "notes": str(row.get("notes", "") or ""),
            }
        )
    return runs


def _build_design(design_type: str, runs: list[dict[str, Any]]) -> dict[str, Any]:
    label = (design_type or "custom").strip() or "custom"
    if label.upper() in TAGUCHI_ARRAY_LABELS:
        return {
            "type": "Taguchi",
            "notes": f"source_design_type: {label}",
            "runs": runs,
        }
    return {"type": label, "runs": runs}


def build_record(
    plan_csv: Path,
    study_id: str,
    title: str,
    material_family: str,
    domain: str,
    application: str,
    design_type: str,
    factor_specs: list[dict[str, Any]] | None,
    response_specs: list[dict[str, Any]] | None,
    factor_cols: list[str] | None,
    response_cols: list[str] | None,
    created_by: str,
    created_at: str,
) -> dict[str, Any]:
    header, rows = _load_plan(plan_csv)
    factors, ordered_factor_cols = _build_factors(header, rows, factor_cols, factor_specs)
    responses = _build_responses(header, response_cols, response_specs)
    runs = _build_runs(rows, ordered_factor_cols, response_cols or [])
    design = _build_design(design_type, runs)

    return {
        "version": "1.0.0",
        "record_type": "experiment-design",
        "study_id": study_id,
        "title": title,
        "created_by": created_by,
        "created_at": created_at,
        "direction_profile": {
            "material_family": material_family,
            "domain": domain,
            "application": application,
        },
        "objectives": [
            {
                "description": f"investigate effect of factors on {responses[0]['name']}" if responses else "investigate factor effects",
                "response_variable": responses[0]["name"] if responses else "",
                "optimization": "maximize",
            }
        ],
        "response_variables": responses,
        "factors": factors,
        "design": design,
        "materials": [],
        "processing": [],
        "characterization": [],
        "evidence_links": [],
        "terminology": [],
    }


def validate_record(record: dict[str, Any], schema_path: Path) -> None:
    if jsonschema is None:
        return
    schema = yaml.safe_load(schema_path.read_text(encoding="utf-8"))
    jsonschema.validate(record, schema)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan-csv", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--study-id", default="")
    parser.add_argument("--title", default="")
    parser.add_argument("--material-family", default="")
    parser.add_argument("--domain", default="")
    parser.add_argument("--application", default="")
    parser.add_argument("--design-type", default="custom")
    parser.add_argument("--factors", default=None, help="JSON list of factor metadata objects")
    parser.add_argument("--responses", default=None, help="JSON list of response metadata objects")
    parser.add_argument("--factor-cols", default=None, help="Comma-separated CSV column names for factors")
    parser.add_argument("--response-cols", default=None, help="Comma-separated CSV column names for responses")
    parser.add_argument("--created-by", default="materials-doe")
    parser.add_argument("--created-at", default=_today())
    parser.add_argument("--schema", type=Path, default=None)
    args = parser.parse_args()

    if not args.plan_csv.exists():
        print(f"Error: plan CSV not found: {args.plan_csv}", file=sys.stderr)
        return 1

    factor_specs = _parse_json_or_fail(args.factors, "--factors") if args.factors else None
    response_specs = _parse_json_or_fail(args.responses, "--responses") if args.responses else None
    factor_cols = [c.strip() for c in args.factor_cols.split(",")] if args.factor_cols else None
    response_cols = [c.strip() for c in args.response_cols.split(",")] if args.response_cols else None

    study_id = args.study_id or args.plan_csv.stem
    title = args.title or study_id

    record = build_record(
        plan_csv=args.plan_csv,
        study_id=study_id,
        title=title,
        material_family=args.material_family,
        domain=args.domain,
        application=args.application,
        design_type=args.design_type,
        factor_specs=factor_specs,
        response_specs=response_specs,
        factor_cols=factor_cols,
        response_cols=response_cols,
        created_by=args.created_by,
        created_at=args.created_at,
    )

    if args.schema is not None:
        validate_record(record, args.schema)
    else:
        if DEFAULT_SCHEMA.exists():
            validate_record(record, DEFAULT_SCHEMA)

    args.output.write_text(yaml.safe_dump(record, sort_keys=False, allow_unicode=True), encoding="utf-8")
    print(args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
