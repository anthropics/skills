#!/usr/bin/env python3
"""#108 policy_anchor_disclosure_protocol.md static lint.

Decision Doc reference:
  docs/design/2026-05-14-ai-disclosure-schema-decision.md §4.1 (item 6) +
  §4.3 invariants + §4.4 11 open concerns + §3 G10 7-row precedence table.

Implementation spec reference:
  docs/design/2026-05-14-ai-disclosure-impl-spec.md §3 (resolved-paths table).

This lint enforces presence-of-required-content invariants on the protocol
doc the LLM reads at runtime when in `disclosure` mode with
`--policy-anchor=<a>` selector.

Checks
------
1. All 8 §4.3 invariants are named verbatim (G1 / G2 / G3 / G10 / G4 / G5 /
   G7 / G8 / G9 — G3 and G10 combined into a single composite invariant).
2. All 11 §4.4 concerns have a resolution clause referenced by number
   (`concern #1` through `concern #11`).
3. The §3 G10 7-row precedence table is present with all 7 rows
   (numbered 1..7).
4. The auto-promotion forbiddance clause is present (G3/G10 invariant
   load-bearing constraint).
5. The 4 canonical anchor slugs are enumerated in the lookup mechanism
   section.
6. The Nature ↔ v3.2 venue dedup pointer
   (`shared/policy_data/nature_policy.md`) is referenced.

Exit codes
----------
  0 - all checks pass
  1 - one or more violations
  2 - invocation error

Usage
-----
  python scripts/check_policy_anchor_protocol.py academic-paper/references/policy_anchor_disclosure_protocol.md
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REQUIRED_INVARIANTS = (
    "G1 invariant",
    "G2 invariant",
    "G3 / G10 invariant",
    "G4 invariant",
    "G5 invariant",
    "G7 invariant",
    "G8 invariant",
    "G9 invariant",
)
REQUIRED_CONCERN_NUMBERS = tuple(range(1, 12))
REQUIRED_CONCERNS = tuple(f"concern #{i}" for i in REQUIRED_CONCERN_NUMBERS)
REQUIRED_ANCHOR_SLUGS = ("prisma-trAIce", "icmje", "nature", "ieee")
DEDUP_POINTER = "shared/policy_data/nature_policy.md"
# The auto-promotion clause is the load-bearing G3/G10 invariant; both
# tokens MUST be present so a partial deletion (heading word but not the
# prohibition sentence, or vice versa) cannot silently satisfy the lint.
AUTO_PROMOTION_REQUIRED_TOKENS = (
    "auto-promotion",
    "MUST NOT be rendered as though USED",
)

CONCERN_PATTERN = re.compile(r"concern\s+#(\d+)\b")
TABLE_ROW_PATTERN = re.compile(r"^\s*\|\s*(\d+)\s*\|", re.MULTILINE)
ANCHOR_INVENTORY_PATTERN = re.compile(
    r"^\*\*Anchor inventory\*\*:\s*`([^`]+)`", re.MULTILINE
)


def lint_text(text: str) -> list[str]:
    violations: list[str] = []

    for inv in REQUIRED_INVARIANTS:
        if inv not in text:
            violations.append(f"missing required invariant reference: {inv}")

    # Word-boundary match prevents `concern #1` from matching against
    # `concern #10` / `concern #11`.
    found_concern_numbers = {int(m.group(1)) for m in CONCERN_PATTERN.finditer(text)}
    for n in REQUIRED_CONCERN_NUMBERS:
        if n not in found_concern_numbers:
            violations.append(f"missing §4.4 concern #{n} resolution clause")

    # Match real markdown table rows (`| N |` at line start); a prose
    # `row 4` mention elsewhere in the doc does not satisfy the check.
    found_rows = {int(m.group(1)) for m in TABLE_ROW_PATTERN.finditer(text)}
    for row in range(1, 8):
        if row not in found_rows:
            violations.append(
                f"missing G10 7-row precedence row {row} (no `| {row} |` markdown row found)"
            )

    for token in AUTO_PROMOTION_REQUIRED_TOKENS:
        if token not in text:
            violations.append(
                "missing auto-promotion forbiddance clause "
                f"(G3/G10 UNCERTAIN-not-USED invariant); token missing: '{token}'"
            )

    inventory_line = ANCHOR_INVENTORY_PATTERN.search(text)
    if not inventory_line:
        violations.append("missing `**Anchor inventory**: ...` line in protocol doc")
    else:
        inventory_slugs = {
            s.strip() for s in inventory_line.group(1).split(",") if s.strip()
        }
        canonical = set(REQUIRED_ANCHOR_SLUGS)
        missing = canonical - inventory_slugs
        extra = inventory_slugs - canonical
        for slug in sorted(missing):
            violations.append(
                f"missing canonical anchor slug from inventory: {slug} "
                f"(found inventory: {sorted(inventory_slugs)})"
            )
        for slug in sorted(extra):
            violations.append(
                f"unexpected anchor slug in inventory: {slug} (closed enum is "
                f"{sorted(canonical)}; remove it from the inventory line or "
                "expand the canonical enum first)"
            )

    if DEDUP_POINTER not in text:
        violations.append(
            f"missing Nature ↔ v3.2 venue dedup pointer: {DEDUP_POINTER}"
        )

    return violations


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "path",
        nargs="?",
        default="academic-paper/references/policy_anchor_disclosure_protocol.md",
        help="path to policy_anchor_disclosure_protocol.md (default: %(default)s)",
    )
    args = parser.parse_args(argv)
    target = Path(args.path)
    if not target.exists():
        print(f"error: file not found: {target}", file=sys.stderr)
        return 2
    text = target.read_text(encoding="utf-8")
    violations = lint_text(text)
    if violations:
        for v in violations:
            print(f"{target}: {v}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
