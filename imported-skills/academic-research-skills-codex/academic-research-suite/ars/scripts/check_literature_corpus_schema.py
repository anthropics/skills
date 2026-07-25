#!/usr/bin/env python3
"""Validate literature_corpus_entry.schema.json and rejection_log.schema.json
self-consistency, and validate adapter example output against them.

Usage:
    python scripts/check_literature_corpus_schema.py
        Scans scripts/adapters/examples/**/expected_passport.yaml and
        **/expected_rejection_log.yaml. Validates each against its schema.
        Enforces citation_key uniqueness per passport.

    python scripts/check_literature_corpus_schema.py --passport PATH
        Validate one passport YAML only.

    python scripts/check_literature_corpus_schema.py --rejection-log PATH
        Validate one rejection log YAML only.

Exit codes:
    0 - all validations passed
    1 - one or more validations failed
    2 - invocation error (e.g., schema file missing)
"""
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path
from typing import Any

try:
    import yaml
    from jsonschema import Draft202012Validator
    from jsonschema.exceptions import ValidationError  # noqa: F401
except ImportError as e:
    print(
        f"Missing dependency: {e}. Install with: pip install pyyaml jsonschema",
        file=sys.stderr,
    )
    sys.exit(2)

# Dual-path import (mirrors arxiv_client.py): the v3.10 laundering guard
# (#329) lives in check_v3_10_policy and is wired here so it runs over REAL
# passport entries, not just fixtures.
try:
    from check_v3_10_policy import assert_venue_type_source_clean
except ImportError:
    from scripts.check_v3_10_policy import assert_venue_type_source_clean

REPO_ROOT = Path(__file__).resolve().parent.parent
ENTRY_SCHEMA_PATH = REPO_ROOT / "shared/contracts/passport/literature_corpus_entry.schema.json"
REJECTION_SCHEMA_PATH = REPO_ROOT / "shared/contracts/passport/rejection_log.schema.json"
TERMINAL_POLICIES_SCHEMA_PATH = REPO_ROOT / "shared/contracts/passport/terminal_policies.schema.json"
EXAMPLES_ROOT = REPO_ROOT / "scripts/adapters/examples"


def load_schema(path: Path) -> dict[str, Any]:
    if not path.exists():
        print(f"ERROR: schema missing at {path}", file=sys.stderr)
        sys.exit(2)
    with path.open("r", encoding="utf-8") as f:
        schema = json.load(f)
    try:
        Draft202012Validator.check_schema(schema)
    except Exception as e:
        print(
            f"ERROR: schema at {path} is not valid Draft 2020-12: {e}",
            file=sys.stderr,
        )
        sys.exit(2)
    return schema


def _build_validator(schema: dict[str, Any]) -> Draft202012Validator:
    """Construct a validator wired with FORMAT_CHECKER so format keywords
    (date-time on generated_at and obtained_at) are actually enforced.
    Without this, malformed timestamps validate silently — a hole codex
    flagged in the T3 review (plan §901/§922 referenced this script's
    validators)."""
    return Draft202012Validator(
        schema, format_checker=Draft202012Validator.FORMAT_CHECKER
    )


def _safe_load_yaml(path: Path) -> tuple[Any, str | None]:
    """Parse a YAML file. Returns (data, error_message). On success
    error_message is None; on parse failure data is None and the
    message names the file and the parser error. Does not raise."""
    try:
        with path.open("r", encoding="utf-8") as f:
            return yaml.safe_load(f), None
    except yaml.YAMLError as e:
        return None, f"{path}: malformed YAML: {e}"
    except OSError as e:
        return None, f"{path}: cannot read file: {e}"


def validate_passport(
    path: Path,
    entry_schema: dict[str, Any],
    terminal_policies_schema: dict[str, Any] | None = None,
) -> list[str]:
    errors: list[str] = []
    data, parse_err = _safe_load_yaml(path)
    if parse_err:
        errors.append(parse_err)
        return errors
    if data is None:
        errors.append(f"{path}: empty YAML file")
        return errors
    if not isinstance(data, dict):
        errors.append(
            f"{path}: passport YAML must be a mapping (got {type(data).__name__})"
        )
        return errors
    # v3.10 (spec §3 PR-B item 1, R2-P1): validate the passport-level
    # terminal_policies block BEFORE iterating entries. An absent block is the
    # all-advisory backward-compat default (Invariant 7) — nothing to check.
    # A present block must validate against terminal_policies.schema.json; a
    # non-mapping value (null / list / string) is an error, never silently
    # ignored (codex Q3).
    if terminal_policies_schema is not None and "terminal_policies" in data:
        tp = data["terminal_policies"]
        if not isinstance(tp, dict):
            errors.append(
                f"{path}: 'terminal_policies' must be a mapping "
                f"(got {type(tp).__name__})"
            )
        else:
            tp_validator = _build_validator(terminal_policies_schema)
            for err in tp_validator.iter_errors(tp):
                errors.append(
                    f"{path}: terminal_policies schema validation error: {err.message}"
                )
    if "literature_corpus" not in data:
        errors.append(
            f"{path}: missing required 'literature_corpus' key (a passport must declare it, even as an empty list)"
        )
        return errors
    corpus = data["literature_corpus"]
    if not isinstance(corpus, list):
        errors.append(f"{path}: 'literature_corpus' must be a list")
        return errors
    validator = _build_validator(entry_schema)
    citation_keys: dict[str, int] = {}
    for i, entry in enumerate(corpus):
        for err in validator.iter_errors(entry):
            errors.append(
                f"{path}: literature_corpus[{i}] schema validation error: {err.message}"
            )
        # v3.10 laundering guard (R2-P1, #329): the schema types venue_type_source
        # as a non-empty string but cannot express the lookup-index exclusion, so
        # the semantic check runs here over real entries. A trusted_source_declared
        # entry whose venue_type_source names a lookup index (OpenAlex / Crossref /
        # Semantic Scholar) is laundering a k=3-unmatched signal into declared trust.
        # Only run on string fields — a non-string venue_type_source / provenance is
        # already a schema-type error (reported above); the semantic guard must not
        # crash on it (.strip() on a non-str), so let the schema error stand alone.
        if isinstance(entry, dict):
            vts = entry.get("venue_type_source", "")
            vtp = entry.get("venue_type_provenance", "")
            if isinstance(vts, str) and isinstance(vtp, str):
                for problem in assert_venue_type_source_clean(vts, vtp):
                    errors.append(f"{path}: literature_corpus[{i}]: {problem}")
        key = entry.get("citation_key") if isinstance(entry, dict) else None
        if key:
            citation_keys[key] = citation_keys.get(key, 0) + 1
    for key, count in citation_keys.items():
        if count > 1:
            errors.append(
                f"{path}: duplicate citation_key '{key}' appears {count} times (must be unique)"
            )
    return errors


def validate_rejection_log(path: Path, log_schema: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    data, parse_err = _safe_load_yaml(path)
    if parse_err:
        errors.append(parse_err)
        return errors
    if data is None:
        errors.append(f"{path}: empty YAML file")
        return errors
    if not isinstance(data, dict):
        errors.append(
            f"{path}: rejection log YAML must be a mapping (got {type(data).__name__})"
        )
        return errors
    validator = _build_validator(log_schema)
    for err in validator.iter_errors(data):
        errors.append(f"{path}: schema validation error: {err.message}")
    return errors


def scan_examples(
    entry_schema: dict[str, Any],
    log_schema: dict[str, Any],
    terminal_policies_schema: dict[str, Any] | None = None,
) -> list[str]:
    errors: list[str] = []
    if not EXAMPLES_ROOT.exists():
        return errors
    for passport in EXAMPLES_ROOT.glob("*/expected_passport.yaml"):
        errors.extend(
            validate_passport(passport, entry_schema, terminal_policies_schema)
        )
    for log in EXAMPLES_ROOT.glob("*/expected_rejection_log.yaml"):
        errors.extend(validate_rejection_log(log, log_schema))
    return errors


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Validate literature_corpus passport + rejection log YAMLs."
    )
    ap.add_argument(
        "--passport", type=Path, help="Validate a single passport YAML."
    )
    ap.add_argument(
        "--rejection-log",
        type=Path,
        help="Validate a single rejection log YAML.",
    )
    args = ap.parse_args()

    entry_schema = load_schema(ENTRY_SCHEMA_PATH)
    log_schema = load_schema(REJECTION_SCHEMA_PATH)
    terminal_policies_schema = load_schema(TERMINAL_POLICIES_SCHEMA_PATH)

    errors: list[str] = []
    if args.passport:
        errors.extend(
            validate_passport(args.passport, entry_schema, terminal_policies_schema)
        )
    if args.rejection_log:
        errors.extend(validate_rejection_log(args.rejection_log, log_schema))

    if not args.passport and not args.rejection_log:
        errors.extend(scan_examples(entry_schema, log_schema, terminal_policies_schema))

    if errors:
        for e in errors:
            print(e, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
