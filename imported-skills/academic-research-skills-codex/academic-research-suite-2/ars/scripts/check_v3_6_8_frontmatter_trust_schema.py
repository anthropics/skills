#!/usr/bin/env python3
"""ARS v3.7.1 trust-chain frontmatter lint (spec § 3.1 firm rules).

Spec: docs/design/2026-04-30-ars-v3.6.8-trust-provenance-and-drift-transparency-spec.md
      § 3.1 D1 — Frontmatter trust-strength conflation
      § Step 1 — Frontmatter schema split

Validates the three firm rules across all literature_corpus[] entries in a
passport (or, with --fixture, against an arbitrary YAML / JSON file). Rules:

  Rule #1 (round-2 R2-007 amend):
      source_verified_against_original=true
      ⟹ source_acquired=true
        AND source_verification_method ∈ {codex_audit, manual_grep, vision_check}
      The literal 'none' verification method is enumerated for shape
      uniformity but is FORBIDDEN in conjunction with verified=true.

  Rule #2:
      source_acquired=false
      ⟹ description_last_audit is null or the literal string 'none'.
      (No original source means an audit cannot be substantive.)

  Rule #3 (round-1 codex F-005 amend):
      A literature_corpus[] entry MUST NOT carry a literal
      `human_read_source` or `human_read_at` field. These keys are derived
      at read-time from the §3.6 peer file `<session>_human_read_log.yaml`
      and are USER-OWNED. Adapters and consumer agents emitting these
      keys would mutate `literature_corpus[]` (which is
      `additionalProperties: false` and adapter-owned per
      `academic-pipeline/references/literature_corpus_consumers.md`).

Defense-in-depth: the same rules are encoded in the JSON Schema's `allOf`
branches (rules #1 and #2) and via `additionalProperties: false` (rule #3).
This lint produces friendlier error messages, cites spec sections, and
runs over passport corpora — a level above per-entry schema validation.

Exit codes: 0 on pass, 1 on any rule violation.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Iterable

try:
    import yaml
except ImportError as e:
    print(
        f"Missing dependency: {e}. Install with: pip install pyyaml",
        file=sys.stderr,
    )
    sys.exit(2)

REPO_ROOT = Path(__file__).resolve().parent.parent
EXAMPLES_ROOT = REPO_ROOT / "scripts" / "adapters" / "examples"

VALID_VERIFICATION_METHODS = {"codex_audit", "manual_grep", "vision_check", "none"}
TRUE_VERIFICATION_METHODS = {"codex_audit", "manual_grep", "vision_check"}

# Per spec §3.6 firm rule #1 + §3.1 firm rule #3: literal `human_read_*`
# fields are forbidden on entries; they live in the peer file derived at
# read-time. Both keys are caught here for symmetry (the peer file carries
# `marked_at`; downstream join produces `human_read_source` and
# `human_read_at` as derived fields).
FORBIDDEN_HUMAN_READ_KEYS = ("human_read_source", "human_read_at")


def _load_yaml_or_json(path: Path) -> Any:
    text = path.read_text(encoding="utf-8")
    try:
        if path.suffix.lower() == ".json":
            return json.loads(text)
        return yaml.safe_load(text)
    except (yaml.YAMLError, json.JSONDecodeError) as exc:
        raise SystemExit(f"[ARS-V3.7.1 LINT ERROR: cannot parse {path}: {exc}]")


def _iter_entries(payload: Any) -> Iterable[dict[str, Any]]:
    """Yield entries from common shapes:
    - {literature_corpus: [...entries...]}  (passport shape)
    - [...entries...]                         (bare entry list)
    - {... entry fields ...}                  (single entry)
    """
    if isinstance(payload, dict):
        if "literature_corpus" in payload and isinstance(payload["literature_corpus"], list):
            for entry in payload["literature_corpus"]:
                if isinstance(entry, dict):
                    yield entry
            return
        if "citation_key" in payload:  # bare single entry
            yield payload
            return
        # Otherwise: nothing to scan.
        return
    if isinstance(payload, list):
        for entry in payload:
            if isinstance(entry, dict):
                yield entry


def _entry_label(entry: dict[str, Any], idx: int) -> str:
    return entry.get("citation_key") or f"<entry index={idx}>"


def check_entry(entry: dict[str, Any], label: str) -> list[str]:
    """Return a list of human-readable rule-violation messages."""
    errors: list[str] = []

    # Rule #3: forbidden human_read_* keys.
    for key in FORBIDDEN_HUMAN_READ_KEYS:
        if key in entry:
            errors.append(
                f"  [{label}] Rule #3 violated: literal {key!r} field on "
                f"entry. Per spec §3.1 firm rule #3 + §3.6 firm rule #1, "
                f"{key!r} is DERIVED from the §3.6 peer file "
                f"`<session>_human_read_log.yaml` and MUST NOT appear on "
                f"literature_corpus[] entries. Remove the field."
            )

    # Rule #1: source_verified_against_original=true triggers preconditions.
    verified = entry.get("source_verified_against_original")
    if verified is True:
        acquired = entry.get("source_acquired")
        method = entry.get("source_verification_method")
        if acquired is not True:
            errors.append(
                f"  [{label}] Rule #1 violated: source_verified_against_original=true "
                f"REQUIRES source_acquired=true (got source_acquired={acquired!r}). "
                f"Spec §3.1 firm rule #1: cannot claim verification against an "
                f"original that is not on disk."
            )
        if method is None:
            errors.append(
                f"  [{label}] Rule #1 violated: source_verified_against_original=true "
                f"REQUIRES source_verification_method ∈ "
                f"{{codex_audit, manual_grep, vision_check}} (got missing field). "
                f"Spec §3.1 firm rule #1 round-2 R2-007 amend."
            )
        elif method not in TRUE_VERIFICATION_METHODS:
            errors.append(
                f"  [{label}] Rule #1 violated: source_verified_against_original=true "
                f"REQUIRES source_verification_method ∈ "
                f"{{codex_audit, manual_grep, vision_check}} (got {method!r}). "
                f"Spec §3.1 firm rule #1 round-2 R2-007 amend: 'none' is "
                f"enumerated for shape uniformity but is FORBIDDEN here."
            )

    # Rule #2: source_acquired=false ⇒ description_last_audit MUST be present
    # AND its value MUST be the literal string "none". Round-1 codex P2 closure
    # made the field strictly required (a missing field is NOT equivalent to
    # null). Round-6 codex P2 closure tightened the value to the literal
    # sentinel "none" only — null is rejected — because spec §3.1 firm rule #2
    # reads "REQUIRES description_last_audit: none" (literal sentinel), and the
    # spec's value vocabulary at §3.1 line 111 lists `<round_id> | none` with
    # no null alternative.
    if entry.get("source_acquired") is False:
        if "description_last_audit" not in entry:
            errors.append(
                f"  [{label}] Rule #2 violated: source_acquired=false REQUIRES "
                f"description_last_audit to be present (with value 'none'). "
                f"The field is missing. Spec §3.1 firm rule #2: no original "
                f"means audit cannot be substantive, so the entry MUST "
                f"explicitly carry description_last_audit: 'none'."
            )
        else:
            last_audit = entry["description_last_audit"]
            if last_audit != "none":
                errors.append(
                    f"  [{label}] Rule #2 violated: source_acquired=false REQUIRES "
                    f"description_last_audit: 'none' — the literal sentinel "
                    f"string (got {last_audit!r}). Spec §3.1 firm rule #2 + "
                    f"§3.1 yaml at line 111 (value vocabulary `<round_id> | "
                    f"none`) — null is NOT an accepted alternative for the "
                    f"rule-#2 case (round-6 codex P2 closure)."
                )

    # Optional sanity for verification_method enumeration (catches typos
    # the schema would also catch, but with friendlier message + spec cite).
    method = entry.get("source_verification_method")
    if method is not None and method not in VALID_VERIFICATION_METHODS:
        errors.append(
            f"  [{label}] Invalid source_verification_method: {method!r}. "
            f"Allowed: {sorted(VALID_VERIFICATION_METHODS)}."
        )

    return errors


def check_payload(payload: Any, source: str) -> list[str]:
    failures: list[str] = []
    for idx, entry in enumerate(_iter_entries(payload)):
        label = _entry_label(entry, idx)
        for err in check_entry(entry, label):
            failures.append(err)
    if failures:
        failures.insert(0, f"[ARS-V3.7.1 LINT ERROR: trust-chain rule violations in {source}]")
    return failures


def _scan_examples() -> int:
    """Scan all expected_passport.yaml fixtures under scripts/adapters/examples."""
    if not EXAMPLES_ROOT.exists():
        print(f"[ARS-V3.7.1 LINT ERROR: examples root missing at {EXAMPLES_ROOT}]")
        return 1
    failures: list[str] = []
    fixture_count = 0
    for path in sorted(EXAMPLES_ROOT.rglob("expected_passport.yaml")):
        fixture_count += 1
        payload = _load_yaml_or_json(path)
        rel = path.relative_to(REPO_ROOT)
        failures.extend(check_payload(payload, str(rel)))
    if fixture_count == 0:
        print("[ARS-V3.7.1 LINT WARN: no expected_passport.yaml fixtures found under "
              f"{EXAMPLES_ROOT.relative_to(REPO_ROOT)}]")
    if failures:
        print("\n".join(failures))
        return 1
    print(f"[v3.7.1 trust-schema lint] PASSED ({fixture_count} fixture(s) scanned)")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    parser.add_argument(
        "--fixture",
        type=Path,
        help="Scan a single passport YAML / JSON file instead of the examples dir.",
    )
    args = parser.parse_args(argv)
    if args.fixture is not None:
        if not args.fixture.exists():
            print(f"[ARS-V3.7.1 LINT ERROR: fixture not found: {args.fixture}]")
            return 1
        payload = _load_yaml_or_json(args.fixture)
        failures = check_payload(payload, str(args.fixture))
        if failures:
            print("\n".join(failures))
            return 1
        print(f"[v3.7.1 trust-schema lint] PASSED ({args.fixture})")
        return 0
    return _scan_examples()


if __name__ == "__main__":
    sys.exit(main())
