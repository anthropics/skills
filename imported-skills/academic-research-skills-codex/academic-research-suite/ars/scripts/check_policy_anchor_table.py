#!/usr/bin/env python3
"""#108 policy_anchor_table.md static lint.

Decision Doc reference:
  docs/design/2026-05-14-ai-disclosure-schema-decision.md §4.1 (item 6a)
  + §4.3 invariants.

Implementation spec reference:
  docs/design/2026-05-14-ai-disclosure-impl-spec.md §2.1 (file map) + §4
  (TDD test discipline) + §4.4 (Nature ↔ v3.2 venue de-dup guard).

This lint enforces structural invariants on the anchor data table — the
source-of-truth reference the LLM-prose renderer (policy_anchor_disclosure_
protocol.md) reads at runtime to resolve `--policy-anchor=<a>` selectors.

Checks
------
1. Exactly four anchor sections present, slugs ∈ {prisma-trAIce, icmje,
   nature, ieee}.
2. Each anchor section carries a Snapshot ref line of the form
   "**Snapshot:** `<slug>:wayback=<id>` …".
3. Each anchor table has 16 rows numbered 1..16 in canonical order.
4. Each row's source_strength cell ∈
   {explicit-mandate, explicit-recommend, conditional-mandate, implicit,
    not-addressed, unknown}.
5. Each mandate / recommend / conditional cell carries a verbatim quote
   (double-quoted text not equal to a placeholder elision marker).
6. Helper hook `verify_nature_dedup_with_venue` exposed for the de-dup
   guard between the new anchor table and the v3.2
   venue_disclosure_policies.md Nature entry.

Exit codes
----------
  0 - all checks pass
  1 - one or more violations
  2 - invocation error

Usage
-----
  python scripts/check_policy_anchor_table.py academic-paper/references/policy_anchor_table.md
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

CANONICAL_ANCHOR_SLUGS = ("prisma-trAIce", "icmje", "nature", "ieee")
CANONICAL_FIELD_COUNT = 16
VALID_STRENGTHS = {
    "explicit-mandate",
    "explicit-recommend",
    "conditional-mandate",
    "implicit",
    "not-addressed",
    "unknown",
}
STRENGTHS_REQUIRING_QUOTE = {
    "explicit-mandate",
    "explicit-recommend",
    "conditional-mandate",
}
# Capture any non-empty trailing identifier so invalid anchor headings
# (underscore, space, punctuation) surface as "unknown anchor section"
# rather than being silently folded into the previous section.
ANCHOR_HEADING = re.compile(r"^##\s+Anchor:\s+(\S.*?)\s*$", re.MULTILINE)
NATURE_ANCHOR_SECTION = re.compile(
    r"^##\s+Anchor:\s+nature\s*$(.*?)(?=^##\s+Anchor:|\Z)",
    flags=re.MULTILINE | re.DOTALL,
)
NATURE_VENUE_SECTION = re.compile(
    r"^##\s+Venue:\s+Nature[^\n]*$(.*?)(?=^##\s+Venue:|\Z)",
    flags=re.MULTILINE | re.DOTALL,
)
SNAPSHOT_LINE = re.compile(
    r"\*\*Snapshot:\*\*\s+`([A-Za-z0-9-]+):wayback=([0-9]+)`"
)
ROW_LINE = re.compile(
    r"^\|\s*(\d+)\s*\|\s*([^|]+?)\s*\|\s*([A-Za-z-]+)\s*\|\s*(.+?)\s*\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|"
)
ELISION_MARKERS = {"(quote elided)", "(snapshot deleted)", "—"}

REPO_ROOT = Path(__file__).resolve().parent.parent
NATURE_POLICY_POINTER = "shared/policy_data/nature_policy.md"


def _split_anchor_sections(text: str) -> tuple[dict[str, str], list[str]]:
    """Split the doc into per-anchor sections keyed by slug. Returns
    (sections, duplicates) so the caller can flag duplicated headings —
    a plain dict overwrite would silently drop them."""
    sections: dict[str, str] = {}
    duplicates: list[str] = []
    seen: set[str] = set()
    matches = list(ANCHOR_HEADING.finditer(text))
    for idx, match in enumerate(matches):
        slug = match.group(1)
        start = match.end()
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(text)
        if slug in seen:
            duplicates.append(slug)
        seen.add(slug)
        sections[slug] = text[start:end]
    return sections, duplicates


def _parse_rows(section: str) -> list[tuple[int, str, str, str, str, str]]:
    """Return parsed (n, field_name, strength, quote_cell, locator, value_type)
    tuples from a single anchor's body."""
    rows: list[tuple[int, str, str, str, str, str]] = []
    for line in section.split("\n"):
        m = ROW_LINE.match(line)
        if not m:
            continue
        try:
            n = int(m.group(1))
        except ValueError:
            continue
        rows.append(
            (
                n,
                m.group(2).strip(),
                m.group(3).strip(),
                m.group(4).strip(),
                m.group(5).strip(),
                m.group(6).strip(),
            )
        )
    return rows


def _has_verbatim_quote(quote_cell: str) -> bool:
    """A verbatim quote cell starts with `\"` (or `(inference passage)` for
    implicit cells handled separately)."""
    stripped = quote_cell.strip()
    if stripped in ELISION_MARKERS:
        return False
    if not stripped:
        return False
    # Accept escaped double-quote (`\\"`) in addition to plain `"`
    return stripped.startswith('"') or stripped.startswith('\\"')


def lint_text(text: str) -> list[str]:
    """Run all structural checks; return violation messages list (empty=pass)."""
    violations: list[str] = []
    sections, duplicates = _split_anchor_sections(text)

    # Check 1: anchor slug coverage
    found_slugs = set(sections.keys())
    canonical = set(CANONICAL_ANCHOR_SLUGS)
    missing = canonical - found_slugs
    extra = found_slugs - canonical
    for slug in sorted(missing):
        violations.append(f"missing anchor section: {slug}")
    for slug in sorted(extra):
        violations.append(f"unknown anchor section: {slug}")
    for slug in duplicates:
        violations.append(
            f"duplicate anchor section: {slug} appears more than once "
            "(second occurrence silently overwrites the first)"
        )

    # Check 2 + 3 + 4 + 5: per-anchor structure
    for slug in CANONICAL_ANCHOR_SLUGS:
        body = sections.get(slug)
        if body is None:
            continue
        snapshot_match = SNAPSHOT_LINE.search(body)
        if not snapshot_match:
            violations.append(f"anchor {slug}: snapshot ref line missing or malformed")
        elif snapshot_match.group(1) != slug:
            violations.append(
                f"anchor {slug}: snapshot ref slug mismatch ({snapshot_match.group(1)})"
            )

        rows = _parse_rows(body)
        if len(rows) != CANONICAL_FIELD_COUNT:
            violations.append(
                f"anchor {slug}: expected {CANONICAL_FIELD_COUNT} field rows, got {len(rows)}"
            )
        seen_numbers: list[int] = []
        for n, field_name, strength, quote_cell, _locator, _vtype in rows:
            seen_numbers.append(n)
            if strength not in VALID_STRENGTHS:
                violations.append(
                    f"anchor {slug} row {n} ({field_name}): unknown source_strength '{strength}'"
                )
            if strength in STRENGTHS_REQUIRING_QUOTE and not _has_verbatim_quote(quote_cell):
                violations.append(
                    f"anchor {slug} row {n} ({field_name}): {strength} cell lacks verbatim quote"
                )
        expected_numbers = list(range(1, CANONICAL_FIELD_COUNT + 1))
        if seen_numbers != expected_numbers[: len(seen_numbers)]:
            violations.append(
                f"anchor {slug}: field rows not in canonical 1..16 order (saw {seen_numbers})"
            )

    return violations


def verify_nature_dedup_with_venue(
    anchor_table_path: Path,
    venue_policies_path: Path,
    *,
    anchor_text: str | None = None,
    venue_text: str | None = None,
    repo_root: Path | None = None,
) -> list[str]:
    """Confirm both Nature consumers cite shared/policy_data/nature_policy.md
    inside their Nature-specific section AND the canonical source file
    exists. The pointer must live inside the Nature section of each
    consumer — a citation list at the file bottom would otherwise satisfy
    a plain substring match without representing the dedup invariant."""
    violations: list[str] = []
    if not anchor_table_path.exists():
        return [f"anchor table file not found: {anchor_table_path}"]
    if not venue_policies_path.exists():
        return [f"venue policies file not found: {venue_policies_path}"]
    root = repo_root if repo_root is not None else REPO_ROOT
    canonical_source_path = root / NATURE_POLICY_POINTER
    if not canonical_source_path.exists():
        violations.append(
            f"canonical Nature policy source file missing: "
            f"{canonical_source_path}. Both consumers cite the path but the "
            "source file does not exist; either create it or remove the pointers."
        )
    if anchor_text is None:
        anchor_text = anchor_table_path.read_text(encoding="utf-8")
    if venue_text is None:
        venue_text = venue_policies_path.read_text(encoding="utf-8")
    nature_section = NATURE_ANCHOR_SECTION.search(anchor_text)
    if not nature_section:
        violations.append("anchor table missing `## Anchor: nature` section")
    elif NATURE_POLICY_POINTER not in nature_section.group(1):
        violations.append(
            f"anchor table Nature section missing dedup pointer to {NATURE_POLICY_POINTER}"
        )
    nature_venue_section = NATURE_VENUE_SECTION.search(venue_text)
    if not nature_venue_section:
        violations.append("venue policies missing `## Venue: Nature ...` section")
    elif NATURE_POLICY_POINTER not in nature_venue_section.group(1):
        violations.append(
            f"venue policies Nature section missing dedup pointer to "
            f"{NATURE_POLICY_POINTER}"
        )
    return violations


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "path",
        nargs="?",
        default="academic-paper/references/policy_anchor_table.md",
        help="path to policy_anchor_table.md (default: %(default)s)",
    )
    parser.add_argument(
        "--venue-policies",
        default="academic-paper/references/venue_disclosure_policies.md",
        help="path to venue_disclosure_policies.md for the Nature dedup guard",
    )
    args = parser.parse_args(argv)
    target = Path(args.path)
    venue_path = Path(args.venue_policies)
    if not target.exists():
        print(f"error: file not found: {target}", file=sys.stderr)
        return 2
    text = target.read_text(encoding="utf-8")
    violations = lint_text(text)
    # Derive repo root from the anchor table path so tests using temp
    # subtree mirrors also exercise the canonical-source existence check.
    derived_repo_root = target.resolve().parent.parent.parent
    dedup_violations = verify_nature_dedup_with_venue(
        target, venue_path, anchor_text=text, repo_root=derived_repo_root
    )
    violations.extend(dedup_violations)
    if violations:
        for v in violations:
            print(f"{target}: {v}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
