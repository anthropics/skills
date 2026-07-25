#!/usr/bin/env python3
"""Validator for evals/gold/<task>/ gold subsets.

Enforces 9 invariants documented in
docs/design/2026-05-21-v3.10-184-extend-eval-harness-spec.md
implementation plan (Task 4 of #184 Phase 1a; I10 added in 2026-05-24 amendment).

Usage:
    python -m scripts.check_evals_gold_set <gold-set-dir>

Exit code 0 = clean, non-zero = invariants violated. Prints one line per
violation prefixed with the invariant tag (I1-I7, I9, I10; I8 retired).
"""
from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

import yaml
from jsonschema import Draft202012Validator

_HERE = Path(__file__).resolve().parent
if str(_HERE) not in sys.path:
    sys.path.insert(0, str(_HERE))
from citation_verification_summary import (  # noqa: E402
    reduce_lookup_verified as _reduce_lookup_verified,
)

LABEL_ENUM = {"true", "false", "unresolvable"}
KIND_ENUM = {"valid_doi", "valid_arxiv", "manual_exempt", "fabricated",
             "fabricated_title_only"}
RESOLVER_NAMES = ("crossref", "openalex", "semantic_scholar", "arxiv")
# status + queried_by enums (and their status↔queried_by coherence) are now
# enforced by _RESOLVER_OUTCOME_VALIDATOR against the shipped summary-schema $def,
# not local constants (#332 P2).

_CORPUS_ENTRY_SCHEMA_PATH = (
    Path(__file__).resolve().parent.parent
    / "shared" / "contracts" / "passport" / "literature_corpus_entry.schema.json"
)
_CORPUS_ENTRY_VALIDATOR = Draft202012Validator(
    json.loads(_CORPUS_ENTRY_SCHEMA_PATH.read_text(encoding="utf-8")),
    format_checker=Draft202012Validator.FORMAT_CHECKER,
)

# Validate each resolver_outcome against the SHIPPED summary-schema $def rather
# than a hand-rolled coherence check, so the gold validator can't drift from the
# contract it pins (the I9b single-source-of-truth philosophy, applied to shape).
# The $def carries the status↔queried_by allOf coherence (ran → {id,title};
# skipped/unreachable → null) plus the required-present rule that a flat enum
# check silently under-enforced (#332 P2).
_SUMMARY_SCHEMA_PATH = (
    Path(__file__).resolve().parent.parent
    / "shared" / "contracts" / "passport" / "citation_verification_summary.schema.json"
)
# Safe to validate the extracted $def in isolation because resolver_outcome is
# $ref-less today. If it ever gains a $ref into a sibling $def, build the validator
# from the full schema document (with a registry) instead of the slice.
_RESOLVER_OUTCOME_VALIDATOR = Draft202012Validator(
    json.loads(_SUMMARY_SCHEMA_PATH.read_text(encoding="utf-8"))["$defs"]["resolver_outcome"]
)


def _load_json_strict(path: Path) -> Any:
    """Load JSON; raise on duplicate keys (I4)."""
    def _no_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        seen: set[str] = set()
        for k, _ in pairs:
            if k in seen:
                raise ValueError(f"duplicate JSON key: {k!r}")
            seen.add(k)
        return dict(pairs)
    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_no_duplicates)


def validate(root: Path) -> list[str]:
    """Return a list of invariant-violation messages. Empty list = clean."""
    errors: list[str] = []
    root = Path(root)
    expected_path = root / "expected_outcomes.json"
    tuples_dir = root / "tuples"
    manifest_path = root / "manifest.yaml"

    if not tuples_dir.is_dir():
        errors.append(f"I1: tuples/ directory not found at {tuples_dir}")
        return errors

    # I1: tuple filename stems == expected_outcomes keys
    tuple_stems = {p.stem for p in tuples_dir.glob("*.json")}
    try:
        expected = _load_json_strict(expected_path)
    except ValueError as e:
        errors.append(f"I4: {e}")
        return errors
    expected_keys = set(expected.keys())
    missing = expected_keys - tuple_stems
    extra = tuple_stems - expected_keys
    if missing:
        errors.append(f"I1: tuples missing for expected_outcomes keys: {sorted(missing)}")
    if extra:
        errors.append(f"I1: extra tuple files without expected_outcomes entry: {sorted(extra)}")

    # Load all tuple files ONCE into tuples_by_id
    tuples_by_id: dict[str, dict] = {}
    for path in sorted(tuples_dir.glob("*.json")):
        try:
            tuples_by_id[path.stem] = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as e:
            errors.append(f"I2: {path.name} is not valid JSON: {e}")
            # malformed tuple gets a single I2 error; I3/I5/I6/I7/I10 skip it

    # I2: tuple_id == filename stem
    for stem, tup in tuples_by_id.items():
        tid = tup.get("tuple_id")
        if tid != stem:
            errors.append(f"I2: {stem}.json tuple_id={tid!r} != filename stem {stem!r}")

    # I3: kind distribution matches manifest tuple_distribution
    if not manifest_path.is_file():
        errors.append(f"I3: manifest.yaml not found at {manifest_path}")
        return errors
    try:
        manifest = yaml.safe_load(manifest_path.read_text(encoding="utf-8"))
    except yaml.YAMLError as e:
        errors.append(f"I3: manifest.yaml does not parse: {e}")
        return errors
    if not isinstance(manifest, dict):
        errors.append(f"I3: manifest.yaml root is not a mapping (got {type(manifest).__name__})")
        return errors
    tuple_dist = manifest.get("tuple_distribution")
    if not isinstance(tuple_dist, list):
        errors.append(
            f"I3: manifest.yaml missing or invalid 'tuple_distribution' "
            f"(got {type(tuple_dist).__name__})"
        )
        return errors
    declared: dict[str, int] = {}
    for entry in tuple_dist:
        if not isinstance(entry, dict) or "kind" not in entry or "n" not in entry:
            errors.append(f"I3: manifest.yaml tuple_distribution entry malformed: {entry!r}")
            return errors
        declared[entry["kind"]] = entry["n"]

    # I3 observed accumulator
    observed: dict[str, int] = {}
    for stem, tup in tuples_by_id.items():
        k = tup.get("kind")
        if k not in KIND_ENUM:
            errors.append(f"I3: {stem}.json has unknown kind {k!r}")
            continue
        observed[k] = observed.get(k, 0) + 1

    # I3 declared-vs-observed comparison (Change 2: add observed-but-not-declared loop)
    for k, declared_n in declared.items():
        obs_n = observed.get(k, 0)
        if obs_n != declared_n:
            errors.append(f"I3: kind {k!r} count {obs_n} != manifest declared {declared_n}")
    for k in observed.keys() - declared.keys():
        errors.append(f"I3: kind {k!r} observed in tuples but not declared in manifest tuple_distribution")

    # I5: expected_outcomes label matches manifest's kind->label mapping
    kind_to_label = {entry["kind"]: entry["expected_lookup_verified"] for entry in tuple_dist}
    tuple_id_to_kind = {stem: tup.get("kind") for stem, tup in tuples_by_id.items()}
    for tid, outcome in expected.items():
        label = outcome.get("lookup_verified")
        if label not in LABEL_ENUM:
            errors.append(f"I5: {tid} lookup_verified={label!r} not in {sorted(LABEL_ENUM)}")
            continue
        kind = tuple_id_to_kind.get(tid)
        if kind is None:
            continue  # I1 already reported missing tuple
        expected_label = kind_to_label.get(kind)
        if expected_label is not None and label != expected_label:
            errors.append(
                f"I5: {tid} lookup_verified={label!r} but manifest declares "
                f"kind {kind!r} -> {expected_label!r}"
            )

    # I6: arxiv_id placement consistency
    for stem, tup in tuples_by_id.items():
        kind = tup.get("kind")
        arxiv_id = tup.get("arxiv_id")
        doi = (tup.get("corpus_entry") or {}).get("doi")
        if kind == "valid_arxiv":
            if not arxiv_id:
                errors.append(f"I6: {stem}.json kind=valid_arxiv but arxiv_id is null/missing")
            if doi:
                errors.append(f"I6: {stem}.json kind=valid_arxiv but corpus_entry.doi={doi!r} present")
        elif kind == "valid_doi":
            if arxiv_id:
                errors.append(f"I6: {stem}.json kind=valid_doi but arxiv_id={arxiv_id!r} present")
            if not doi:
                errors.append(f"I6: {stem}.json kind=valid_doi but corpus_entry.doi missing/null")
        else:
            if arxiv_id:
                errors.append(f"I6: {stem}.json kind={kind!r} but arxiv_id={arxiv_id!r} present (must be null)")

    # I7: fabrication_intent <-> kind is a fabrication kind. Both `fabricated`
    # (ID-keyed → false) and `fabricated_title_only` (no identifier → unresolvable,
    # the C-V6(a) by-design FN fixture) are fabrications and MUST carry the marker.
    fabrication_kinds = {"fabricated", "fabricated_title_only"}
    for stem, tup in tuples_by_id.items():
        kind = tup.get("kind")
        marker = tup.get("fabrication_intent")
        if kind in fabrication_kinds and marker is not True:
            errors.append(f"I7: {stem}.json kind={kind!r} but fabrication_intent={marker!r} (must be true)")
        if kind not in fabrication_kinds and marker is True:
            errors.append(f"I7: {stem}.json kind={kind!r} but fabrication_intent=true (must be false)")

    # I9: resolver_outcomes has all four resolver keys with valid status enum
    # + valid queried_by enum (v3.11 #182 Delta 4 / C-V6(a)).
    # I9b: every gold label must be REPRODUCIBLE by the shipped reducer (the
    # single source of truth, C-V6(a) narrowed-false). Rather than hand-rolling
    # the false condition here (which would drift from the reducer if C-V6(a) is
    # ever amended), recompute each label via reduce_lookup_verified and assert
    # it matches — pinning the gold to the reducer, not a parallel copy of its
    # logic. Both share a single pass over expected.items().
    for tid, outcome in expected.items():
        ros = outcome.get("resolver_outcomes", {})
        for resolver in RESOLVER_NAMES:
            entry = ros.get(resolver)
            if entry is None:
                errors.append(f"I9: {tid} resolver_outcomes missing resolver {resolver!r}")
                continue
            # Validate the resolver_outcome against the shipped summary-schema
            # $def: status enum, queried_by enum, queried_by required-present, AND
            # the status↔queried_by coherence allOf (ran → {id,title};
            # skipped/unreachable → null). A flat enum check under-enforced the
            # last two (#332 P2).
            for verr in _RESOLVER_OUTCOME_VALIDATOR.iter_errors(entry):
                errors.append(
                    f"I9: {tid} resolver_outcomes.{resolver} violates "
                    f"citation_verification_summary $defs.resolver_outcome: "
                    f"{verr.message}"
                )

        recomputed = _reduce_lookup_verified(ros)
        declared = outcome.get("lookup_verified")
        if recomputed != declared:
            errors.append(
                f"I9b: {tid} lookup_verified={declared!r} but the shipped reducer "
                f"computes {recomputed!r} from its resolver_outcomes "
                f"(gold label must match the single-source-of-truth reducer; "
                f"C-V6(a) narrowed-false: false needs an ID-keyed unmatched)"
            )

    # I10: per-tuple corpus_entry validates against literature_corpus_entry.schema.json
    for stem, tup in tuples_by_id.items():
        corpus_entry = tup.get("corpus_entry")
        if corpus_entry is None:
            errors.append(f"I10: {stem}.json missing required field 'corpus_entry'")
            continue
        for ve in _CORPUS_ENTRY_VALIDATOR.iter_errors(corpus_entry):
            path = "$" + "".join(f"[{p!r}]" if isinstance(p, str) else f"[{p}]" for p in ve.absolute_path)
            errors.append(
                f"I10: {stem}.json corpus_entry{path}: {ve.message}"
            )

    return errors


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: python -m scripts.check_evals_gold_set <gold-set-dir>", file=sys.stderr)
        return 2
    root = Path(argv[1])
    errors = validate(root)
    if errors:
        for e in errors:
            print(e, file=sys.stderr)
        return 1
    print(f"OK: {root} passes all gold-set invariants")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
