#!/usr/bin/env python3
"""Validate an ARS sprint contract against sprint_contract.schema.json.

Usage: python scripts/check_sprint_contract.py path/to/contract.json [--ars-version vX.Y.Z]

Exit 0 on pass (warnings may still be printed to stderr).
Exit 1 on schema or structural validation failure, or file error.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

import jsonschema

SCHEMA_PATH = Path(__file__).resolve().parent.parent / "shared" / "sprint_contract.schema.json"


def load_schema() -> dict:
    return json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))


def validate(contract: dict) -> list[str]:
    """Return list of schema violation messages. Empty list means pass."""
    schema = load_schema()
    validator = jsonschema.Draft202012Validator(
        schema,
        format_checker=jsonschema.Draft202012Validator.FORMAT_CHECKER,
    )
    return [f"{list(e.absolute_path)}: {e.message}" for e in validator.iter_errors(contract)]


def check_structural_invariants(contract: dict) -> list[str]:
    """Uniqueness checks for dimension id, dimension name, and condition_id
    per spec §4.1 item 2. Empty list means pass; only meaningful if
    validate() already returned [].
    """
    errors: list[str] = []

    dims = contract.get("acceptance_dimensions", [])
    ids = [d.get("id") for d in dims if d.get("id") is not None]
    names = [d.get("name") for d in dims if d.get("name") is not None]
    for dup_id in sorted({x for x in ids if ids.count(x) > 1}):
        errors.append(
            f"duplicate acceptance_dimensions id '{dup_id}'; "
            "downstream aggregation assumes unique ids"
        )
    for dup_name in sorted({x for x in names if names.count(x) > 1}):
        errors.append(
            f"duplicate acceptance_dimensions name '{dup_name}'; "
            "downstream lint assumes unique names"
        )

    conds = contract.get("failure_conditions", [])
    cids = [c.get("condition_id") for c in conds if c.get("condition_id") is not None]
    for dup_cid in sorted({x for x in cids if cids.count(x) > 1}):
        errors.append(
            f"duplicate failure_conditions condition_id '{dup_cid}'; "
            "precedence resolution assumes unique condition_ids"
        )

    return errors


# v? accepts both 'v3.6.2' and '3.6.2' on --ars-version CLI input;
# baseline_version is schema-bound to require the v prefix.
_VERSION_RE = re.compile(r"^v?(\d+)\.(\d+)\.(\d+)$")

# Module-level alongside _VERSION_RE; reused by SC-10 (Task 12).
_DIM_REF_RE = re.compile(r"\bD\d+\b")


def _parse_version(v: str | None) -> tuple[int, int, int] | None:
    if not v:
        return None
    m = _VERSION_RE.match(v)
    if not m:
        return None
    return int(m.group(1)), int(m.group(2)), int(m.group(3))


def warn_suspicious(contract: dict, ars_current_version: str | None) -> list[str]:
    """Soft warnings per spec §4.3 (SC-1 baseline lag through SC-11
    panel_size sanity). Non-blocking; printed to stderr by main().
    """
    warnings: list[str] = []

    # SC-1 baseline lag: contract.baseline_version lags current ARS by > 2 minor
    bv = _parse_version(contract.get("baseline_version"))
    cv = _parse_version(ars_current_version)
    if bv and cv:
        bv_major, bv_minor, _ = bv
        cv_major, cv_minor, _ = cv
        if bv_major == cv_major and (cv_minor - bv_minor) > 2:
            warnings.append(
                f"SC-1 WARNING: contract baseline v{bv_major}.{bv_minor}.* lags "
                f"current ARS v{cv_major}.{cv_minor}.* by {cv_minor - bv_minor} minor; "
                "retirement candidate"
            )
        elif bv_major != cv_major:
            warnings.append(
                f"SC-1 WARNING: contract baseline major v{bv_major} differs from "
                f"current ARS v{cv_major}; retirement candidate"
            )

    # SC-2 single dimension
    dims = contract.get("acceptance_dimensions", [])
    if len(dims) == 1:
        warnings.append(
            "SC-2 WARNING: contract has only 1 acceptance dimension; "
            "consider whether this mode needs sprint contract at all"
        )

    # SC-3 no mandatory dimension. Empty dims handled by schema validation
    # (minItems: 1); SC-3 only fires when dims exist but lack mandatory.
    if dims and not any(d.get("priority") == "mandatory" for d in dims):
        warnings.append(
            f"SC-3 WARNING: 0 of {len(dims)} acceptance dimensions are mandatory; "
            "failure_conditions referencing 'mandatory' will be vacuous"
        )

    # SC-4 orphan dimension reference in failure_conditions[].expression.
    # Intentionally loose: does not parse expression semantics, just tokenises D\d+.
    dim_ids = {d.get("id") for d in dims if d.get("id") is not None}
    for fc in contract.get("failure_conditions", []):
        expr = fc.get("expression", "")
        for tok in _DIM_REF_RE.findall(expr):
            if tok not in dim_ids:
                warnings.append(
                    f"SC-4 WARNING: failure condition {fc.get('condition_id')} "
                    f"references {tok} which is not in acceptance_dimensions"
                )

    # SC-5 measurement_procedure.reviewer_must_output_before_paper missing required outputs.
    # Schema enforces minItems:2 but cannot constrain which specific strings are present;
    # SC-5 covers that semantic gap. Reviewer-only per v3.6.6 §7.1: writer / evaluator
    # contracts intentionally omit measurement_procedure (§3.3.1 reviewer-conditional),
    # so firing SC-5 on every clean generator template is noise. Hoist mp here too so SC-9
    # below can also detect the reviewer-mode field path.
    mode = contract.get("mode", "")
    mp = contract.get("measurement_procedure", {})
    if mode.startswith("reviewer_"):
        outputs = mp.get("reviewer_must_output_before_paper", [])
        required_outputs = {"contract_paraphrase", "scoring_plan"}
        missing = required_outputs - set(outputs)
        if missing:
            warnings.append(
                f"SC-5 WARNING: hard-gate protocol requires both 'contract_paraphrase' "
                f"and 'scoring_plan' in reviewer_must_output_before_paper; missing: {sorted(missing)}"
            )

    # SC-7 conflicting failure-condition actions at same severity.
    # Skip entries with missing severity — schema validation catches those upstream.
    by_sev: dict[int, list[tuple[str, str]]] = defaultdict(list)
    for fc in contract.get("failure_conditions", []):
        sev = fc.get("severity")
        if sev is not None:
            by_sev[sev].append((fc.get("condition_id"), fc.get("action")))
    for sev, pairs in by_sev.items():
        actions = {a for _, a in pairs}
        if len(pairs) > 1 and len(actions) > 1:
            ids = ", ".join(p[0] for p in pairs)
            warnings.append(
                f"SC-7 WARNING: {ids} share severity={sev} but map to different actions; "
                "precedence tie-breaking falls back to ordinal position"
            )

    # SC-9 impossible paraphrase_minimum_dimensions.
    # The paraphrase-count gate is mode-conditional per v3.6.6 §7.1: each mode reads its
    # own field. Reviewer reads mp.paraphrase_minimum_dimensions; writer reads
    # pre_commitment_artifacts.acceptance_criteria_paraphrase.minimum_dimensions;
    # evaluator reads disagreement_handling.paraphrase_minimum_dimensions. The lint
    # rule (paraphrase count must not exceed dimension count) is identical across
    # all three modes — only the source field changes.
    if mode.startswith("reviewer_"):
        pmd = mp.get("paraphrase_minimum_dimensions")
        pmd_source = "measurement_procedure.paraphrase_minimum_dimensions"
        phase_label = "Phase 1"
    elif mode == "writer_full":
        pmd = (contract.get("pre_commitment_artifacts", {})
               .get("acceptance_criteria_paraphrase", {})
               .get("minimum_dimensions"))
        pmd_source = "pre_commitment_artifacts.acceptance_criteria_paraphrase.minimum_dimensions"
        phase_label = "Phase 4a"
    elif mode == "evaluator_full":
        pmd = contract.get("disagreement_handling", {}).get("paraphrase_minimum_dimensions")
        pmd_source = "disagreement_handling.paraphrase_minimum_dimensions"
        phase_label = "Phase 6a"
    else:
        pmd = None
        pmd_source = None
        phase_label = None
    if isinstance(pmd, int) and pmd > len(dims):
        warnings.append(
            f"SC-9 WARNING: {pmd_source}={pmd} exceeds dimension "
            f"count {len(dims)}; {phase_label} lint will always fail"
        )

    # SC-10 unreferenced mandatory/high dimension.
    # Covered = directly referenced via Dn token in any expression, OR
    # any expression contains a priority-scope keyword matching this
    # dimension's priority (e.g., "any mandatory ...", "every mandatory ...",
    # "any high-priority ...", "two or more high-priority ..."). See
    # spec §5.5 recognised expression vocabulary patterns 1-3.
    referenced: set[str] = set()
    for fc in contract.get("failure_conditions", []):
        referenced.update(_DIM_REF_RE.findall(fc.get("expression", "")))
    priority_keywords = {"mandatory": "mandatory", "high": "high-priority"}
    for d in dims:
        did = d.get("id")
        prio = d.get("priority")
        if prio not in ("mandatory", "high"):
            continue
        if did in referenced:
            continue
        pkw = priority_keywords[prio]
        priority_covered = any(
            pkw in fc.get("expression", "").lower()
            for fc in contract.get("failure_conditions", [])
        )
        if priority_covered:
            continue
        warnings.append(
            f"SC-10 WARNING: {prio} dimension {did} has no "
            "failure_condition referencing it (directly or via its priority); "
            "its score cannot influence the editorial decision"
        )

    # SC-11 panel_size sanity. Reviewer-only per v3.6.6 §7.1: writer / evaluator
    # contracts intentionally omit panel_size (§3.3.5 reviewer-conditional). Each runs a
    # single agent so panel cardinality has no semantic anchor in those modes.
    if mode.startswith("reviewer_"):
        ps = contract.get("panel_size")
        if ps == 1:
            warnings.append(
                "SC-11 WARNING: panel_size=1 means no cross-reviewer aggregation; "
                "cross_reviewer_quantifier values collapse to pass-through"
            )
        expected_panel = {"reviewer_full": 5, "reviewer_methodology_focus": 2}
        if mode in expected_panel and ps != expected_panel[mode]:
            warnings.append(
                f"SC-11 WARNING: panel_size={ps} inconsistent with mode={mode}; "
                f"expected {expected_panel[mode]}"
            )

    return warnings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("contract", type=Path, help="Path to the sprint contract JSON")
    parser.add_argument("--ars-version", type=str, default=None,
                        help="Current ARS version (e.g. v3.6.2) for SC-1 baseline lag check")
    args = parser.parse_args()

    try:
        contract = json.loads(args.contract.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError) as exc:
        print(f"ERROR: failed to load {args.contract}: {exc}", file=sys.stderr)
        return 1

    errors = validate(contract)
    if errors:
        for e in errors:
            print(f"ERROR: {e}", file=sys.stderr)
        print(
            f"\n{len(errors)} schema violation(s). "
            "See shared/sprint_contract.schema.json for field definitions.",
            file=sys.stderr,
        )
        return 1

    struct_errors = check_structural_invariants(contract)
    if struct_errors:
        for e in struct_errors:
            print(f"ERROR: {e}", file=sys.stderr)
        print(
            f"\n{len(struct_errors)} structural invariant violation(s).",
            file=sys.stderr,
        )
        return 1

    for w in warn_suspicious(contract, args.ars_version):
        print(w, file=sys.stderr)

    print(f"OK: {args.contract} is a valid sprint_contract (Schema 13.1)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
