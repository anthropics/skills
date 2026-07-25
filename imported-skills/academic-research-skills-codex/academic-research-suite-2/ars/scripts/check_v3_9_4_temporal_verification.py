#!/usr/bin/env python3
"""v3.9.4 spec lint — temporal verification sidecar conformance.

Enforces 8 invariants from spec §7:
  1. timeline.yaml schema conformance against timeline.schema.json
  2. supersession chain has no cycles (Task 7)
  3. every date carries precision and provenance.method (implicit via schema)
  4. citation_provenance.yaml schema conformance
  5. temporal_audit_results.yaml schema conformance + finding_kind closed list + per-kind required-field map (via oneOf)
  6. M3 IRON RULE block present in report_compiler_agent.md and draft_writer_agent.md (Task 22 implements lint of this)
  7. M6 Citation Provenance Protocol section present in timeline_extraction_agent.md (Task 21+22 implements)
  8. bibliography_agent.md matches the accepted post-#257 baseline for this temporal lint's ownership guard

This Task 6 scaffold implements invariants 1, 4, 5 (schema conformance). Invariants 2, 6-8 are added in later tasks.

Usage:
  python scripts/check_v3_9_4_temporal_verification.py \\
    --timeline phase2_investigation/timeline.yaml \\
    --citation-provenance phase2_investigation/citation_provenance.yaml \\
    --temporal-audit phase4_composition/temporal_audit_results.yaml

Exit codes:
  0 — all checks pass
  1 — one or more checks failed
  2 — invocation error
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

import jsonschema
import yaml

REPO_ROOT = Path(__file__).resolve().parents[1]
SCHEMAS = REPO_ROOT / "shared/contracts/passport"

BIBLIOGRAPHY_AGENT_PATH = REPO_ROOT / "deep-research/agents/bibliography_agent.md"
BIBLIOGRAPHY_AGENT_SHA256 = "39370675561f74fae9a8595bdeb03939402d273a0734b6bcaa1230d5e9928616"  # #489 harness-retirement baseline (B4-F01); F2 ownership guard per spec §3.4 + §3.6. The B4-F01 apply rewrote ONLY the Phase Boundary enforcement-status sentence (stale "hook deferred to #134" claim → post-PR-#294 two-layer reality); NO M6 citation-provenance / M5 version-family / temporal logic added, so the ownership invariant the hash protects is intact. (Previous baseline 4d8bee06… was the #272 guidance-layer state.)


def _validate(yaml_path: Path, schema_path: Path) -> list[str]:
    if not yaml_path.exists():
        return [f"missing: {yaml_path}"]
    if not schema_path.exists():
        return [f"missing schema: {schema_path}"]
    try:
        data = yaml.safe_load(yaml_path.read_text())
        schema = json.loads(schema_path.read_text())
        jsonschema.validate(data, schema)
        return []
    except jsonschema.ValidationError as exc:
        return [f"{yaml_path.name}: {exc.message} at {list(exc.absolute_path)}"]
    except Exception as exc:
        return [f"{yaml_path.name}: {exc}"]


def _check_supersession_cycles(timeline_path: Path) -> list[str]:
    """Invariant 2: supersession chain has no cycles.

    Walks each source's `supersedes` chain. Records the visited set; if a citation_key
    is revisited within the same walk, a cycle exists. Emits one error per cycle origin.
    """
    if not timeline_path.exists():
        return []
    try:
        data = yaml.safe_load(timeline_path.read_text())
    except Exception:
        return []  # schema validation handles parse errors
    sources = {s["citation_key"]: s for s in data.get("sources", []) if "citation_key" in s}
    errors: list[str] = []
    for origin_key in sources:
        visited_set: set[str] = set()
        visited_path: list[str] = []
        cur = origin_key
        while cur is not None:
            if cur in visited_set:
                errors.append(
                    f"supersession cycle detected starting at {origin_key}: "
                    f"{' -> '.join(visited_path)} -> {cur}"
                )
                break
            visited_set.add(cur)
            visited_path.append(cur)
            entry = sources.get(cur)
            cur = entry.get("supersedes") if entry else None
    return errors


def _check_bibliography_agent_unchanged() -> list[str]:
    """Invariant 8: bibliography_agent.md must match the accepted baseline sha256.

    Per spec §3.4 + §3.6 F2 closure: M6 citation provenance and M5-stub version-family awareness
    are owned by timeline_extraction_agent, NOT bibliography_agent. This lint enforces the invariant
    that temporal/version-family logic does not drift into bibliography_agent.md. #257 legitimately
    adds lit-review distributional-skew advisory text; that text is now part of this guard's baseline.
    If a future v3.x release legitimately modifies bibliography_agent.md, update the sha256 constant in
    the same commit.
    """
    if not BIBLIOGRAPHY_AGENT_PATH.exists():
        return [f"missing: {BIBLIOGRAPHY_AGENT_PATH}"]
    actual = hashlib.sha256(BIBLIOGRAPHY_AGENT_PATH.read_bytes()).hexdigest()
    if actual != BIBLIOGRAPHY_AGENT_SHA256:
        return [
            f"bibliography_agent.md modified — v3.9.4 F2 invariant violated. "
            f"expected sha256 {BIBLIOGRAPHY_AGENT_SHA256}, got {actual}. "
            f"Per spec §3.4 + §3.6, M6 citation provenance and M5-stub version-family awareness "
            f"are owned by timeline_extraction_agent, NOT bibliography_agent. #257 distributional-skew "
            f"advisory text is allowed only as part of the recorded baseline."
        ]
    return []


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeline", type=Path, required=True)
    parser.add_argument("--citation-provenance", type=Path, required=True)
    parser.add_argument("--temporal-audit", type=Path, required=True)
    args = parser.parse_args(argv)

    errors: list[str] = []
    errors.extend(_validate(args.timeline, SCHEMAS / "timeline.schema.json"))
    errors.extend(_validate(args.citation_provenance, SCHEMAS / "citation_provenance.schema.json"))
    errors.extend(_validate(args.temporal_audit, SCHEMAS / "temporal_audit_results.schema.json"))
    errors.extend(_check_supersession_cycles(args.timeline))
    errors.extend(_check_bibliography_agent_unchanged())

    if errors:
        for e in errors:
            print(f"ERROR: {e}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
