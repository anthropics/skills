#!/usr/bin/env python3
"""Validate an experiment-record.yaml against the experiment-record JSON Schema.

Dependencies:
  - pyyaml (required)
  - jsonschema (optional; when unavailable only semantic checks run)

Exit codes:
  0  record is valid
  1  record is invalid or a fatal error occurred
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional

# ---------------------------------------------------------------------------
# Dependency imports
# ---------------------------------------------------------------------------

try:
    import yaml
except ImportError:
    print("ERROR: pyyaml is required. Install it with: pip install pyyaml", file=sys.stderr)
    sys.exit(1)

try:
    import jsonschema
    HAS_JSONSCHEMA = True
except ImportError:
    HAS_JSONSCHEMA = False

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

_SEMVER_RE = re.compile(r"^\d+\.\d+\.\d+$")


def _load_yaml(path: Path) -> Any:
    """Load a YAML file and return the parsed Python object."""
    with open(path, "r", encoding="utf-8") as fh:
        return yaml.safe_load(fh)


def _default_schema_path() -> Path:
    """Return the default schema path (core/experiment-record-schema.yaml next to this script)."""
    return Path(__file__).resolve().parent / "core" / "experiment-record-schema.yaml"


# ---------------------------------------------------------------------------
# Schema validation
# ---------------------------------------------------------------------------

def validate_against_schema(record: Dict[str, Any], schema: Dict[str, Any]) -> List[str]:
    """Validate *record* against *schema* using jsonschema.

    Returns a list of human-readable error strings (empty when valid).
    """
    if not HAS_JSONSCHEMA:
        return ["[SKIP] jsonschema is not installed; schema validation skipped"]

    validator = jsonschema.Draft7Validator(schema)
    errors: List[str] = []
    for error in sorted(validator.iter_errors(record), key=lambda e: list(e.absolute_path)):
        path = ".".join(str(p) for p in error.absolute_path) or "<root>"
        errors.append(f"{path}: {error.message}")
    return errors


# ---------------------------------------------------------------------------
# Semantic (strict-mode) checks
# ---------------------------------------------------------------------------

def semantic_checks(record: Dict[str, Any]) -> List[str]:
    """Run extra semantic checks that go beyond what JSON Schema expresses.

    Returns a list of warning strings (empty when everything is fine).
    """
    warnings: List[str] = []

    # -- version must be semver -------------------------------------------
    version = record.get("version")
    if version is not None and not _SEMVER_RE.match(str(version)):
        warnings.append(
            f"version '{version}' does not match semver format (MAJOR.MINOR.PATCH)"
        )

    # -- factors: continuous / categorical must have levels ---------------
    factors = record.get("factors") or []
    factor_names: List[str] = []
    for idx, factor in enumerate(factors):
        fname = factor.get("name", f"<factor[{idx}]>")
        factor_names.append(fname)
        ftype = factor.get("type")
        if ftype in ("continuous", "categorical"):
            levels = factor.get("levels")
            if not levels:
                warnings.append(
                    f"factor '{fname}' (type={ftype}) must have a non-empty 'levels' array"
                )

    # -- response_variables: unit must be present and non-empty -----------
    responses = record.get("response_variables") or []
    for idx, rv in enumerate(responses):
        rvname = rv.get("name", f"<response_variable[{idx}]>")
        unit = rv.get("unit")
        if not unit:
            warnings.append(
                f"response_variable '{rvname}' must have a non-empty 'unit'"
            )

    # -- design.runs: factor_levels keys must match factor names ----------
    design = record.get("design") or {}
    runs = design.get("runs") or []
    if factor_names:
        factor_name_set = set(factor_names)
        for ridx, run in enumerate(runs):
            rid = run.get("run_id", f"<run[{ridx}]>")
            fl = run.get("factor_levels") or {}
            extra_keys = set(fl.keys()) - factor_name_set
            if extra_keys:
                warnings.append(
                    f"run '{rid}' has factor_levels keys not in factors: {sorted(extra_keys)}"
                )
            missing_keys = factor_name_set - set(fl.keys())
            if missing_keys:
                warnings.append(
                    f"run '{rid}' is missing factor_levels for: {sorted(missing_keys)}"
                )

    # -- evidence_links: claim must not be empty --------------------------
    evidence = record.get("evidence_links") or []
    for idx, ev in enumerate(evidence):
        claim = ev.get("claim", "")
        if isinstance(claim, str) and claim.strip() == "":
            warnings.append(
                f"evidence_links[{idx}].claim must not be an empty string"
            )

    return warnings


# ---------------------------------------------------------------------------
# Record summary
# ---------------------------------------------------------------------------

def build_summary(record: Dict[str, Any]) -> Dict[str, Any]:
    """Build a compact summary dict from the record."""
    design = record.get("design") or {}
    return {
        "study_id": record.get("study_id"),
        "record_type": record.get("record_type"),
        "factor_count": len(record.get("factors") or []),
        "response_count": len(record.get("response_variables") or []),
        "run_count": len((design.get("runs") or [])),
        "design_type": design.get("type"),
    }


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Validate an experiment-record.yaml against the experiment-record JSON Schema.",
    )
    parser.add_argument(
        "record_path",
        type=str,
        help="Path to the experiment-record.yaml file to validate.",
    )
    parser.add_argument(
        "--schema",
        type=str,
        default=None,
        help="Path to the JSON Schema YAML file. "
             "Defaults to core/experiment-record-schema.yaml next to this script.",
    )
    parser.add_argument(
        "--output",
        type=str,
        default=None,
        help="Path to write the JSON validation report. Defaults to stdout.",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        default=False,
        help="Enable extra semantic checks beyond JSON Schema validation.",
    )
    return parser


def main(argv: Optional[List[str]] = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)

    record_path = Path(args.record_path)
    if not record_path.is_file():
        print(f"ERROR: record file not found: {record_path}", file=sys.stderr)
        return 1

    # -- Load record -------------------------------------------------------
    try:
        record = _load_yaml(record_path)
    except Exception as exc:
        print(f"ERROR: failed to parse YAML: {exc}", file=sys.stderr)
        return 1

    if not isinstance(record, dict):
        print("ERROR: top-level YAML value is not a mapping", file=sys.stderr)
        return 1

    # -- Load schema -------------------------------------------------------
    schema_path = Path(args.schema) if args.schema else _default_schema_path()
    schema_errors: List[str] = []

    if schema_path.is_file():
        try:
            schema = _load_yaml(schema_path)
        except Exception as exc:
            print(f"ERROR: failed to parse schema YAML: {exc}", file=sys.stderr)
            return 1
    else:
        if HAS_JSONSCHEMA:
            print(
                f"WARNING: schema file not found at {schema_path}; "
                "schema validation will be skipped",
                file=sys.stderr,
            )
        schema = None

    # -- Schema validation -------------------------------------------------
    if schema is not None and HAS_JSONSCHEMA:
        schema_errors = validate_against_schema(record, schema)
    elif not HAS_JSONSCHEMA:
        schema_errors = [
            "[SKIP] jsonschema is not installed; schema validation skipped"
        ]

    # -- Semantic checks ---------------------------------------------------
    semantic_warnings: List[str] = []
    if args.strict:
        semantic_warnings = semantic_checks(record)

    # -- Build report ------------------------------------------------------
    is_valid = len(schema_errors) == 0 and len(semantic_warnings) == 0
    # If jsonschema was skipped and no semantic warnings, still treat as valid
    # only when schema validation was actually skipped (not failed).
    if not HAS_JSONSCHEMA and not semantic_warnings:
        is_valid = True
    # Filter out [SKIP] messages from error count for validity determination
    real_schema_errors = [e for e in schema_errors if not e.startswith("[SKIP]")]
    if real_schema_errors:
        is_valid = False

    report: Dict[str, Any] = {
        "valid": is_valid,
        "schema_errors": schema_errors,
        "semantic_warnings": semantic_warnings,
        "record_summary": build_summary(record),
    }

    # -- Output ------------------------------------------------------------
    report_json = json.dumps(report, indent=2, ensure_ascii=False)
    if args.output:
        out_path = Path(args.output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        with open(out_path, "w", encoding="utf-8") as fh:
            fh.write(report_json + "\n")
    else:
        print(report_json)

    return 0 if is_valid else 1


if __name__ == "__main__":
    sys.exit(main())
