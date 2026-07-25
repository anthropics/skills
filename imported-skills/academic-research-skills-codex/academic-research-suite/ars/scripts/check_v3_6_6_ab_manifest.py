#!/usr/bin/env python3
"""Enforce the v3.6.6 A/B evidence fixture manifest contract per §6.2 schema +
§6.5 git-tracked invariants per design doc 2026-04-27-ars-v3.6.6-generator-evaluator-contract-design.md.

Three rule families per spec body §7.5:

1. Schema-shape checks: top-level fields exist with declared types;
   per-paper required fields present; paper-A vs paper-C asymmetric rules.

2. Path-existence checks (mode-conditional + populated-optional):
   - Required-paths-exist: every required-under-current-mode path declared in
     the manifest must exist git-tracked.
   - Declared-paths-exist: any populated optional path must also exist.
   - Reverse-scan: every git-tracked file under tests/fixtures/v3.6.6-ab/
     must be referenced from the manifest (no orphans).

3. Behaviour on malformed input: exit 1 with parse-error message
   identifying the file (mirrors check_sprint_contract.py convention).

Exit code: 0 on pass, 1 on any rule violation. CLI: `--root <path>` (default `.`).
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

import yaml

FIXTURE_DIR = "tests/fixtures/v3.6.6-ab"
MANIFEST_RELPATH = "manifest.yaml"
SEMVER_RE = re.compile(r"^\d+\.\d+\.\d+$")
LINT_MODES = {"spec_branch", "implementation_pr"}
PAPER_ROLES = {"paper-A", "paper-C"}
INPUT_ARTEFACT_FIELDS = {
    "paper_configuration_record",
    "paper_outline",
    "argument_blueprint",
    "annotated_bibliography",
    "style_profile",
    "knowledge_isolation_directive",
}
TREATMENT_SUBFIELDS = {
    "phase4a_output",
    "phase4b_output",
    "phase6a_output",
    "phase6b_output",
}


def _load_manifest(manifest_path: Path) -> dict | None:
    """Load YAML manifest. Return parsed dict, or None on parse failure
    (caller emits the parse error)."""
    try:
        with manifest_path.open("r", encoding="utf-8") as f:
            data = yaml.safe_load(f)
    except (FileNotFoundError, yaml.YAMLError) as exc:
        print(
            f"ERROR: failed to load manifest at {manifest_path}: {exc}",
            file=sys.stderr,
        )
        return None
    if not isinstance(data, dict):
        print(
            f"ERROR: manifest at {manifest_path} is not a top-level YAML mapping "
            f"(got {type(data).__name__})",
            file=sys.stderr,
        )
        return None
    return data


def _check_schema_shape(manifest: dict) -> list[str]:
    """Schema-shape checks per §6.2 + §7.5. Returns list of error messages."""
    errors: list[str] = []

    # Top-level required fields
    fixture_version = manifest.get("fixture_version")
    if not isinstance(fixture_version, str) or not SEMVER_RE.match(fixture_version):
        errors.append(
            f"fixture_version must match semver regex {SEMVER_RE.pattern}; "
            f"got {fixture_version!r}"
        )
    mode = manifest.get("manifest_lint_mode")
    if mode not in LINT_MODES:
        errors.append(
            f"manifest_lint_mode must be one of {sorted(LINT_MODES)}; got {mode!r}"
        )
    docs = manifest.get("documentation_paths")
    if not isinstance(docs, list) or len(docs) == 0:
        errors.append(
            "documentation_paths must be a non-empty array (must contain at least the spec-PR-shipped README.md)"
        )
    elif not all(isinstance(p, str) for p in docs):
        errors.append("documentation_paths entries must all be strings (relative paths)")
    papers = manifest.get("papers")
    if not isinstance(papers, list):
        errors.append("papers must be an array")
        return errors  # cannot continue per-paper checks
    if len(papers) != 7:
        errors.append(f"papers must contain exactly 7 entries; got {len(papers)}")

    # summary_output type check (mode-conditional requirement handled in path-existence)
    summary_output = manifest.get("summary_output")
    if summary_output is not None and not isinstance(summary_output, str):
        errors.append(
            f"summary_output (when present) must be a string relative path; got {type(summary_output).__name__}"
        )
    if mode == "implementation_pr" and summary_output is None:
        errors.append("summary_output is required under manifest_lint_mode=implementation_pr")

    # Per-paper checks
    paper_a_count = 0
    paper_c_count = 0
    paper_a_types: dict[str, int] = {}
    seen_paper_ids: set[str] = set()
    for i, p in enumerate(papers):
        if not isinstance(p, dict):
            errors.append(f"papers[{i}] must be an object")
            continue
        ctx = f"papers[{i}]"
        # paper_id
        pid = p.get("paper_id")
        if not isinstance(pid, str) or not pid:
            errors.append(f"{ctx}.paper_id must be a non-empty string slug")
        else:
            if pid in seen_paper_ids:
                errors.append(f"{ctx}.paper_id={pid!r} is not unique across papers[]")
            seen_paper_ids.add(pid)
            ctx = f"papers[{pid}]"
        # role
        role = p.get("role")
        if role not in PAPER_ROLES:
            errors.append(f"{ctx}.role must be one of {sorted(PAPER_ROLES)}; got {role!r}")
        elif role == "paper-A":
            paper_a_count += 1
        elif role == "paper-C":
            paper_c_count += 1
        # paper_type + topic_label required strings
        for field in ("paper_type", "topic_label"):
            val = p.get(field)
            if not isinstance(val, str) or not val:
                errors.append(f"{ctx}.{field} must be a non-empty string")
        if role == "paper-A":
            pt = p.get("paper_type")
            if isinstance(pt, str):
                paper_a_types[pt] = paper_a_types.get(pt, 0) + 1
        # input_artefacts
        ia = p.get("input_artefacts")
        if not isinstance(ia, dict) or not any(
            ia.get(f) for f in INPUT_ARTEFACT_FIELDS
        ):
            errors.append(
                f"{ctx}.input_artefacts must be an object with at least one populated sub-field "
                f"from {sorted(INPUT_ARTEFACT_FIELDS)}"
            )
        elif not all(
            isinstance(v, str) and v for k, v in ia.items() if k in INPUT_ARTEFACT_FIELDS
        ):
            errors.append(
                f"{ctx}.input_artefacts populated sub-fields must be non-empty string paths"
            )
        # baseline_output (object with two required sub-fields, both string paths)
        bo = p.get("baseline_output")
        if not isinstance(bo, dict):
            errors.append(f"{ctx}.baseline_output must be an object")
        else:
            for sub in ("writer_draft", "evaluator_review"):
                v = bo.get(sub)
                if not isinstance(v, str) or not v:
                    errors.append(
                        f"{ctx}.baseline_output.{sub} must be a non-empty string path"
                    )
        # treatment_output (object with four sub-fields when present)
        to = p.get("treatment_output")
        if to is not None:
            if not isinstance(to, dict):
                errors.append(f"{ctx}.treatment_output (when present) must be an object")
            else:
                for sub in TREATMENT_SUBFIELDS:
                    v = to.get(sub)
                    if v is not None and (not isinstance(v, str) or not v):
                        errors.append(
                            f"{ctx}.treatment_output.{sub} (when present) must be a non-empty string path"
                        )
                # implementation_pr mode: all four sub-fields required
                if mode == "implementation_pr":
                    for sub in TREATMENT_SUBFIELDS:
                        if to.get(sub) is None:
                            errors.append(
                                f"{ctx}.treatment_output.{sub} is required under manifest_lint_mode=implementation_pr"
                            )
        elif mode == "implementation_pr":
            errors.append(
                f"{ctx}.treatment_output (object with phase4a/4b/6a/6b sub-fields) is required under manifest_lint_mode=implementation_pr"
            )
        # role-conditional fields
        if role == "paper-A":
            judge_baseline = p.get("judge_output_baseline")
            if not isinstance(judge_baseline, str) or not judge_baseline:
                errors.append(
                    f"{ctx}.judge_output_baseline is required for paper-A entries (non-empty string path)"
                )
            judge_treatment = p.get("judge_output_treatment")
            if mode == "implementation_pr":
                if not isinstance(judge_treatment, str) or not judge_treatment:
                    errors.append(
                        f"{ctx}.judge_output_treatment is required for paper-A entries under manifest_lint_mode=implementation_pr"
                    )
            elif judge_treatment is not None and (
                not isinstance(judge_treatment, str) or not judge_treatment
            ):
                errors.append(
                    f"{ctx}.judge_output_treatment (when present) must be a non-empty string path"
                )
            metrics_output = p.get("metrics_output")
            if mode == "implementation_pr":
                if not isinstance(metrics_output, str) or not metrics_output:
                    errors.append(
                        f"{ctx}.metrics_output is required for paper-A entries under manifest_lint_mode=implementation_pr"
                    )
            elif metrics_output is not None and (
                not isinstance(metrics_output, str) or not metrics_output
            ):
                errors.append(
                    f"{ctx}.metrics_output (when present) must be a non-empty string path"
                )
        elif role == "paper-C":
            # paper-C must-not-have rules
            for forbidden in ("judge_output_baseline", "judge_output_treatment", "metrics_output"):
                if forbidden in p:
                    errors.append(
                        f"{ctx}.{forbidden} must NOT be present on paper-C entries (paper-C is categorical and exempt from codex H1/H3 judge + per-paper metrics)"
                    )
            # paper-C must-have rules
            kfm = p.get("known_failure_mode")
            if not isinstance(kfm, str) or not kfm:
                errors.append(f"{ctx}.known_failure_mode is required for paper-C entries (non-empty string)")
            fe = p.get("failure_evidence")
            if not isinstance(fe, str) or not fe:
                errors.append(f"{ctx}.failure_evidence is required for paper-C entries (non-empty string path)")

    # Aggregate role + paper-type counts
    if paper_a_count != 6:
        errors.append(f"len([p for p in papers if p.role == 'paper-A']) must == 6; got {paper_a_count}")
    if paper_c_count != 1:
        errors.append(f"len([p for p in papers if p.role == 'paper-C']) must == 1; got {paper_c_count}")
    if len(paper_a_types) != 3:
        errors.append(
            f"paper-A entries must span exactly 3 paper_type families; got {sorted(paper_a_types)}"
        )
    for pt, count in paper_a_types.items():
        if count != 2:
            errors.append(
                f"paper-A paper_type={pt!r} must appear exactly twice; got {count}"
            )

    return errors


def _collect_declared_paths(manifest: dict) -> set[str]:
    """All paths declared in the manifest. Used for both required + reverse-scan."""
    declared: set[str] = set()
    for p in manifest.get("documentation_paths", []) or []:
        if isinstance(p, str):
            declared.add(p)
    summary = manifest.get("summary_output")
    if isinstance(summary, str):
        declared.add(summary)
    for paper in manifest.get("papers", []) or []:
        if not isinstance(paper, dict):
            continue
        ia = paper.get("input_artefacts") or {}
        if isinstance(ia, dict):
            for k, v in ia.items():
                if k in INPUT_ARTEFACT_FIELDS and isinstance(v, str):
                    declared.add(v)
        bo = paper.get("baseline_output") or {}
        if isinstance(bo, dict):
            for sub in ("writer_draft", "evaluator_review"):
                v = bo.get(sub)
                if isinstance(v, str):
                    declared.add(v)
        to = paper.get("treatment_output") or {}
        if isinstance(to, dict):
            for sub in TREATMENT_SUBFIELDS:
                v = to.get(sub)
                if isinstance(v, str):
                    declared.add(v)
        for field in ("judge_output_baseline", "judge_output_treatment", "metrics_output", "failure_evidence"):
            v = paper.get(field)
            if isinstance(v, str):
                declared.add(v)
    return declared


def _check_path_existence(manifest: dict, fixture_root: Path) -> list[str]:
    """Path-existence checks: every declared path must exist git-tracked.
    Schema-shape already enforced mode-conditional required-vs-optional;
    here we just check declared-paths-exist (which subsumes required-paths-exist
    because all required paths are declared)."""
    errors: list[str] = []
    declared = _collect_declared_paths(manifest)
    for rel in sorted(declared):
        full = fixture_root / rel
        if not full.exists():
            errors.append(f"declared path does not exist git-tracked: {rel}")
    return errors


def _check_reverse_scan(manifest: dict, fixture_root: Path) -> list[str]:
    """Reverse-scan: every file under fixture_root (except manifest.yaml itself)
    must be referenced from the manifest. Orphans fail lint."""
    errors: list[str] = []
    declared = _collect_declared_paths(manifest)
    for path in sorted(fixture_root.rglob("*")):
        if not path.is_file():
            continue
        rel = str(path.relative_to(fixture_root))
        if rel == MANIFEST_RELPATH:
            continue
        if rel not in declared:
            errors.append(
                f"fixture-orphan: {rel} is git-tracked under {fixture_root} "
                f"but not referenced from manifest.yaml"
            )
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=Path("."),
        help="Repo root (default: cwd)",
    )
    args = parser.parse_args()

    fixture_root = args.root / FIXTURE_DIR
    manifest_path = fixture_root / MANIFEST_RELPATH

    manifest = _load_manifest(manifest_path)
    if manifest is None:
        return 1

    errors: list[str] = []
    errors.extend(_check_schema_shape(manifest))
    errors.extend(_check_path_existence(manifest, fixture_root))
    errors.extend(_check_reverse_scan(manifest, fixture_root))

    if errors:
        print("v3.6.6 A/B fixture manifest lint FAILED:", file=sys.stderr)
        for e in errors:
            print(f"  - {e}", file=sys.stderr)
        return 1

    print(f"OK: {manifest_path} passes v3.6.6 A/B fixture manifest lint")
    return 0


if __name__ == "__main__":
    sys.exit(main())
