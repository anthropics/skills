#!/usr/bin/env python3
"""#392 lint — citation-verification intake question stays wired and byte-equivalent.

Step 13 of the intake interview surfaces the `terminal_policies.citation_existence`
choice (mark only / strict). Two failure modes this lint pins:

1. **Orphaning** — the exact #327 P1 failure that hit Step 12: the no-handoff
   interview directive bounds the flow short of the step, so the most common
   full-mode entry never asks the question. The directive must affirmatively
   reach Step 13 (`then Step 13`), not merely contain the token somewhere.
2. **Byte-equivalence erosion** — the advisory path must write NOTHING to the
   passport (per-key absence == advisory, Invariant 7). The Step 13 block must
   retain the write-nothing rule; a future edit that makes the advisory answer
   write an explicit key silently breaks byte-equivalence with pre-#392 runs.

Invariants:
  I1: intake_agent.md has the `### Step 13: Citation Verification Level` heading.
  I2: the `### When No Handoff Materials Are Detected` block affirmatively
      reaches Step 13 (contains "then Step 13").
  I3: the PCR template carries a `**Citation Verification**` row.
  I4: the Step 13 block retains the advisory write-nothing rule (a "write
      nothing to the passport" phrase) AND the strict seeding target
      (`terminal_policies.citation_existence: strict`).

Exit codes: 0 = pass, 1 = invariant violated, 2 = parse failure (file/heading
moved) — fail loud, never skip silently.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

INTAKE_REL = Path("academic-paper/agents/intake_agent.md")
STEP13_HEADING = "### Step 13: Citation Verification Level"
NO_HANDOFF_HEADING = "### When No Handoff Materials Are Detected"
PCR_ROW_RE = re.compile(r"^\|\s*\*\*Citation Verification\*\*\s*\|", re.MULTILINE)
WRITE_NOTHING_RE = re.compile(r"write nothing to the passport", re.IGNORECASE)
STRICT_SEED_RE = re.compile(r"terminal_policies\.citation_existence:\s*strict")


def _section(text: str, heading: str) -> str:
    """Return the block from `heading` to the next heading of <= its level."""
    start = text.find(heading)
    if start < 0:
        raise RuntimeError(f"heading not found: {heading!r}")
    level = heading.split(" ")[0]  # e.g. '###'
    pattern = re.compile(rf"^#{{2,{len(level)}}}\s", re.MULTILINE)
    m = pattern.search(text, start + len(heading))
    return text[start : m.start()] if m else text[start:]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="repo root (tests point this at a fake tree)",
    )
    args = parser.parse_args(argv)

    try:
        text = (args.root / INTAKE_REL).read_text(encoding="utf-8")
    except OSError as exc:
        print(f"PARSE ERROR: {exc}", file=sys.stderr)
        return 2

    errors: list[str] = []

    # I1
    if STEP13_HEADING not in text:
        print(
            f"PARSE ERROR: heading not found: {STEP13_HEADING!r} "
            "(step removed or renamed — update this lint in the same change)",
            file=sys.stderr,
        )
        return 2

    # I2 — anti-orphan (mirror of check_domain_evidence_profile C8 / #327 P1)
    try:
        no_handoff = _section(text, NO_HANDOFF_HEADING)
    except RuntimeError as exc:
        print(f"PARSE ERROR: {exc}", file=sys.stderr)
        return 2
    if "then Step 13" not in no_handoff:
        errors.append(
            "I2: the no-handoff interview directive does not affirmatively reach "
            "Step 13 — the citation-verification question is orphaned from the "
            "most common full-mode entry (the #327 P1 failure mode). The "
            "directive must contain 'then Step 13'."
        )

    # I3
    if not PCR_ROW_RE.search(text):
        errors.append(
            "I3: PCR template has no '**Citation Verification**' row — the "
            "scholar's answer has no recorded home."
        )

    # I4 — byte-equivalence (advisory writes nothing; strict seeds the key)
    step13 = _section(text, STEP13_HEADING)
    if not WRITE_NOTHING_RE.search(step13):
        errors.append(
            "I4: Step 13 lost the advisory write-nothing rule — an explicit "
            "advisory key would break Invariant 7 byte-equivalence with "
            "pre-#392 runs."
        )
    if not STRICT_SEED_RE.search(step13):
        errors.append(
            "I4: Step 13 lost the strict seeding target "
            "(`terminal_policies.citation_existence: strict`)."
        )

    if errors:
        for e in errors:
            print(f"FAIL {e}", file=sys.stderr)
        return 1

    print("citation-verification intake (#392): all 4 invariants pass")
    return 0


if __name__ == "__main__":
    sys.exit(main())
