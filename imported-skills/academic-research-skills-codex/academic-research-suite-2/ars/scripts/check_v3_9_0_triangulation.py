#!/usr/bin/env python3
"""Cross-version contamination-suffix lint: finalizer suffix table contract +
formatter allowlist + refusal-list guard.

NOTE ON NAMING: this file is named for v3.9.0 (where the triangulation matrix
landed) but is the CANONICAL contamination-suffix oracle across versions. It now
also guards the v3.10/v3.11 Delta-1 arXiv four-index tokens (EXPECTED_DELTA1_ROWS).
The v3.9.0 name is historical; renaming would churn spec-consistency.yml + the CI
manifest + the test companion for no benefit.

Per spec v3.9.0 §3.8 rules 1-7, extended by #182 Delta 1:
  Rule 1 — matrix-row oracle: the 3 v3.9.0 markers present in the finalizer
           suffix-table rows; the 4 Delta-1 arXiv markers (incl. PREPRINT
           compositions) each pinned to their exact (k, k_max) table cell
  Rule 2 — preprint composition order: PREPRINT before triangulation token
  Rule 3 — v3.7.3 legacy compat: k=1 k_max=1 S2 row → CONTAMINATED-UNMATCHED (not COVERAGE-NOISE)
  Rule 4 — no *-BLOCK tokens in finalizer subsection (v3.10 policy-layer scope only)
  Rule 5 — formatter pass-through allowlist set-equality, 13 tokens (R-L3-2-E lint)
  Rule 6 — refusal-list-unchanged guard
  Rule 7 — CI integration (done in spec-consistency.yml)

Usage:
    python scripts/check_v3_9_0_triangulation.py
    python scripts/check_v3_9_0_triangulation.py --formatter-path PATH --orchestrator-path PATH
        (for test fixtures only)

Exit codes:
    0 — all checks pass
    1 — one or more checks failed
    2 — invocation error (e.g., file missing)
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_FORMATTER = REPO_ROOT / "academic-paper/agents/formatter_agent.md"
DEFAULT_ORCHESTRATOR = REPO_ROOT / "academic-pipeline/agents/pipeline_orchestrator_agent.md"

V3_9_0_SECTION_HEADER = "## Cite-Time Provenance Finalizer — v3.9.0 extension"

# Three new v3.9.0 markers that must appear in the finalizer suffix table.
EXPECTED_NEW_V3_9_0_SUFFIXES = {
    "CONTAMINATED-COVERAGE-NOISE",
    "CONTAMINATED-PARTIAL-UNMATCH",
    "CONTAMINATED-TRIANGULATION-UNMATCHED",
}

# The four v3.10/v3.11 Delta-1 markers are NOT declared as a bare set here — they
# are the keys of EXPECTED_DELTA1_ROWS below, which pins each to its exact (k, k_max)
# matrix cell. A separate presence-only set would be a parallel structure that could
# drift out of sync (and presence is strictly weaker than the cell assertion anyway),
# so the cell map is the single source of truth for the Delta-1 token set.

# Canonical 13-suffix allowlist (set-equality oracle, rule 5). This is the full
# contamination-suffix set across versions: 3 v3.7.3 legacy + 6 v3.9.0 + 4 Delta-1.
EXPECTED_ALLOWLIST_TOKENS = {
    # v3.7.3 legacy (3)
    "CONTAMINATED-PREPRINT",
    "CONTAMINATED-UNMATCHED",
    "CONTAMINATED-PREPRINT+UNMATCHED",
    # v3.9.0 new (6)
    "CONTAMINATED-COVERAGE-NOISE",
    "CONTAMINATED-PARTIAL-UNMATCH",
    "CONTAMINATED-TRIANGULATION-UNMATCHED",
    "CONTAMINATED-PREPRINT+COVERAGE-NOISE",
    "CONTAMINATED-PREPRINT+PARTIAL-UNMATCH",
    "CONTAMINATED-PREPRINT+TRIANGULATION-UNMATCHED",
    # v3.10/v3.11 Delta-1 arXiv four-index (4)
    "CONTAMINATED-ARXIV-UNMATCHED",
    "CONTAMINATED-QUADRANGULATION-UNMATCHED",
    "CONTAMINATED-PREPRINT+ARXIV-UNMATCHED",
    "CONTAMINATED-PREPRINT+QUADRANGULATION-UNMATCHED",
}


# ---------------------------------------------------------------------------
# Orchestrator helpers (rules 1-4)
# ---------------------------------------------------------------------------

def extract_v3_9_0_finalizer_subsection(orchestrator_text: str) -> str:
    """Return the v3.9.0 finalizer extension subsection (## header until next ## or EOF)."""
    lines = orchestrator_text.splitlines()
    in_section = False
    collected: list[str] = []
    for line in lines:
        if line.startswith(V3_9_0_SECTION_HEADER):
            in_section = True
            collected.append(line)
            continue
        if in_section:
            if line.startswith("## "):
                break
            collected.append(line)
    return "\n".join(collected)


# Matrix-row contract for the 4 Delta-1 tokens: each must appear in a suffix-table
# row carrying its exact (k, k_max) cell. The bullet prose + example markers below
# the table also mention these tokens, so a subsection-wide token scan would pass
# even if the operational row were deleted/mistokened. Rule 1 therefore asserts the
# matrix row, not mere subsection presence — the matrix table IS the contract.
# Column order in the suffix table: | base | preprint | k | k_max | present | suffix |
# so "| <k> | <k_max> |" locates the (k, k_max) cell exactly (same idiom as rule 3).
EXPECTED_DELTA1_ROWS = {
    "CONTAMINATED-ARXIV-UNMATCHED": "| 1 | 1 |",
    "CONTAMINATED-PREPRINT+ARXIV-UNMATCHED": "| 1 | 1 |",
    "CONTAMINATED-QUADRANGULATION-UNMATCHED": "| 4 | 4 |",
    "CONTAMINATED-PREPRINT+QUADRANGULATION-UNMATCHED": "| 4 | 4 |",
}


def check_marker_syntax(subsection_text: str) -> list[str]:
    """Rule 1 (matrix-row oracle): each v3.9.0 + Delta-1 marker must appear as a
    backtick-quoted suffix in a TABLE ROW, and each Delta-1 marker must sit in the
    row carrying its exact (k, k_max) cell.

    Scanning only `|`-delimited rows (not the explanatory bullets/examples below the
    table) is what makes this a contract oracle rather than a presence check: the
    matrix table IS the prompt contract, and deleting an operational row must fail
    even though the same token still appears in the surrounding prose.
    """
    table_rows = [ln for ln in subsection_text.splitlines() if "|" in ln]
    table_text = "\n".join(table_rows)
    row_tokens = set(re.findall(r"`(CONTAMINATED-[A-Z+\-]+)`", table_text))
    failures = []
    # v3.9.0 tokens span k_max RANGES across multiple rows (e.g. COVERAGE-NOISE is
    # k=1 k_max=1 AND k=1 k_max=2-4), so they get a presence-in-table-rows check, not
    # a single-cell assertion (same family-by-family treatment as rule 3's s2 rows).
    missing = EXPECTED_NEW_V3_9_0_SUFFIXES - row_tokens
    if missing:
        failures.append(
            f"rule 1 (marker syntax): missing v3.9.0 markers in finalizer "
            f"suffix-table rows: {sorted(missing)}"
        )
    # Delta-1 tokens are POINT cells, so the cell assertion is their sole check — it
    # is strictly stronger than presence (a token on the wrong tier, or absent
    # entirely, fails here), and EXPECTED_DELTA1_ROWS is their single source of truth.
    for token, cell in EXPECTED_DELTA1_ROWS.items():
        on_correct_row = any(
            f"`{token}`" in ln and cell in ln for ln in table_rows
        )
        if not on_correct_row:
            failures.append(
                f"rule 1 (matrix row): `{token}` is not on a suffix-table row "
                f"carrying its required {cell} (k, k_max) cell"
            )
    return failures


def check_preprint_composition_order(subsection_text: str) -> list[str]:
    """Rule 2: any CONTAMINATED-PREPRINT+X composition has PREPRINT before X (not X+PREPRINT)."""
    tokens = re.findall(r"`(CONTAMINATED-[A-Z+\-]+)`", subsection_text)
    failures = []
    for tok in tokens:
        # Strip CONTAMINATED- prefix, then check composition ordering.
        body = tok[len("CONTAMINATED-"):]
        if "PREPRINT" in body and "+" in body:
            parts = body.split("+")
            if parts[0] != "PREPRINT":
                failures.append(
                    f"rule 2 (preprint composition order): {tok} has non-leading PREPRINT"
                )
    return failures


def check_legacy_compat(subsection_text: str) -> list[str]:
    """Rule 3: k=1 k_max=1 + present_field=semantic_scholar_unmatched preserves
    v3.7.3 legacy CONTAMINATED-UNMATCHED suffix (NOT CONTAMINATED-COVERAGE-NOISE).

    Both the preprint=false and preprint=true legacy rows must be guarded:
    - preprint=false: suffix = CONTAMINATED-UNMATCHED, NOT CONTAMINATED-COVERAGE-NOISE
    - preprint=true: suffix = CONTAMINATED-PREPRINT+UNMATCHED, NOT
      CONTAMINATED-PREPRINT+COVERAGE-NOISE

    Additionally, both rows must be PRESENT. Deleting either row silently passes
    without this guard (absence-is-a-pass is a systematic false-negative per
    v3.9.0 spec §3.6 coverage-noise invariant).
    """
    failures = []
    seen_bare_legacy = False
    seen_preprint_legacy = False
    for line in subsection_text.splitlines():
        if "semantic_scholar_unmatched" not in line or "| 1 | 1 |" not in line:
            continue
        # Detect preprint variant: the table row has "| true |" in the preprint column.
        # Rows with "false / absent" or no explicit "true" are the bare (non-preprint) row.
        is_preprint = "| true |" in line
        if is_preprint:
            seen_preprint_legacy = True
            # Preprint legacy row must carry CONTAMINATED-PREPRINT+UNMATCHED.
            if "`CONTAMINATED-PREPRINT+UNMATCHED`" not in line:
                failures.append(
                    f"rule 3 (legacy compat — preprint variant): k=1 k_max=1 "
                    f"semantic_scholar_unmatched preprint=true row does NOT preserve "
                    f"`CONTAMINATED-PREPRINT+UNMATCHED` legacy suffix"
                )
            if "`CONTAMINATED-PREPRINT+COVERAGE-NOISE`" in line:
                failures.append(
                    f"rule 3 (legacy compat — preprint drift): preprint legacy row contains "
                    f"`CONTAMINATED-PREPRINT+COVERAGE-NOISE` (should be "
                    f"`CONTAMINATED-PREPRINT+UNMATCHED`)"
                )
        else:
            seen_bare_legacy = True
            # Bare (preprint=false / absent) legacy row must carry CONTAMINATED-UNMATCHED.
            if "`CONTAMINATED-UNMATCHED`" not in line:
                failures.append(
                    f"rule 3 (legacy compat — bare variant): k=1 k_max=1 "
                    f"semantic_scholar_unmatched preprint=false row does NOT preserve "
                    f"`CONTAMINATED-UNMATCHED` legacy suffix"
                )
            if "`CONTAMINATED-COVERAGE-NOISE`" in line:
                failures.append(
                    f"rule 3 (legacy compat — bare drift): bare legacy row contains "
                    f"`CONTAMINATED-COVERAGE-NOISE` (should be `CONTAMINATED-UNMATCHED`)"
                )
    if not seen_bare_legacy:
        failures.append(
            "rule 3 (legacy compat): bare k=1 k_max=1 semantic_scholar_unmatched legacy row is "
            "MISSING from the v3.9.0 finalizer subsection "
            "(CONTAMINATED-UNMATCHED legacy coverage required)"
        )
    if not seen_preprint_legacy:
        failures.append(
            "rule 3 (legacy compat): preprint k=1 k_max=1 semantic_scholar_unmatched legacy row is "
            "MISSING from the v3.9.0 finalizer subsection "
            "(CONTAMINATED-PREPRINT+UNMATCHED legacy coverage required)"
        )
    return failures


def check_no_high_block(subsection_text: str) -> list[str]:
    """Rule 4: no backtick-quoted *-BLOCK tokens in v3.9.0 subsection (those are v3.10 scope)."""
    block_tokens = re.findall(r"`([A-Z]+(?:-[A-Z]+)*-BLOCK)`", subsection_text)
    if block_tokens:
        return [
            f"rule 4 (no HIGH-BLOCK): backtick-quoted *-BLOCK token in v3.9.0 subsection: "
            f"{block_tokens}"
        ]
    return []


# ---------------------------------------------------------------------------
# Formatter helpers (rules 5-6)
# ---------------------------------------------------------------------------

def extract_allowlist_tokens(formatter_text: str) -> set[str]:
    """Parse the pass-through allowlist sentence (anchored at 'DO NOT trigger refusal').

    Strategy: locate the sentence containing 'DO NOT trigger refusal' (the canonical
    anchor phrase from v3.7.3 + v3.9.0 specs). Walk backward to find the opening '(' of
    the enclosing parenthetical, then forward to ')'. Extract backtick-quoted
    CONTAMINATED-* tokens from that parenthetical only.

    This avoids substring collisions because tokens are parsed from backtick-delimited
    code spans, not from arbitrary text. CONTAMINATED-PREPRINT and
    CONTAMINATED-PREPRINT+UNMATCHED are extracted as distinct tokens.
    """
    anchor = "DO NOT trigger refusal"
    idx = formatter_text.find(anchor)
    if idx < 0:
        return set()
    paren_start = formatter_text.rfind("(", 0, idx)
    paren_end = formatter_text.find(")", paren_start) if paren_start >= 0 else -1
    if paren_start < 0 or paren_end < 0:
        return set()
    parenthetical = formatter_text[paren_start:paren_end]
    pattern = re.compile(r"`(CONTAMINATED-[A-Z+\-]+)`")
    return set(pattern.findall(parenthetical))


def extract_refusal_rule_tokens(formatter_text: str) -> set[str]:
    """Parse the formatter refusal rules block (numbered list before the allowlist).

    Find numbered list lines (^N. ...) that appear BEFORE the allowlist anchor.
    Extract any backtick-quoted CONTAMINATED-* token in those rule bodies — there
    must be none, per R-L3-2-E.
    """
    anchor_idx = formatter_text.find("DO NOT trigger refusal")
    if anchor_idx < 0:
        return set()
    pre = formatter_text[:anchor_idx]
    rule_pattern = re.compile(r"^\d+\.\s.*$", re.MULTILINE)
    rule_lines = rule_pattern.findall(pre)
    if not rule_lines:
        return set()
    # Scan the last 15 numbered list lines (safely covers rules 1-10).
    contam_pattern = re.compile(r"`(CONTAMINATED-[A-Z+\-]+)`")
    found = set()
    for line in rule_lines[-15:]:
        found |= set(contam_pattern.findall(line))
    return found


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(description="v3.9.0 triangulation spec lint")
    parser.add_argument(
        "--formatter-path",
        default=str(DEFAULT_FORMATTER),
        help="Path to formatter_agent.md (for test fixtures)",
    )
    parser.add_argument(
        "--orchestrator-path",
        default=str(DEFAULT_ORCHESTRATOR),
        help="Path to pipeline_orchestrator_agent.md (for test fixtures)",
    )
    args = parser.parse_args()

    formatter_path = Path(args.formatter_path)
    orchestrator_path = Path(args.orchestrator_path)

    if not formatter_path.exists():
        print(f"ERROR: formatter not found: {formatter_path}", file=sys.stderr)
        return 2
    if not orchestrator_path.exists():
        print(f"ERROR: orchestrator not found: {orchestrator_path}", file=sys.stderr)
        return 2

    formatter_text = formatter_path.read_text(encoding="utf-8")
    orchestrator_text = orchestrator_path.read_text(encoding="utf-8")
    subsection = extract_v3_9_0_finalizer_subsection(orchestrator_text)

    failures: list[str] = []

    # Rules 1-4: finalizer/orchestrator side
    failures += check_marker_syntax(subsection)
    failures += check_preprint_composition_order(subsection)
    failures += check_legacy_compat(subsection)
    failures += check_no_high_block(subsection)

    # Rules 5-6: formatter side
    allowlist = extract_allowlist_tokens(formatter_text)
    missing = EXPECTED_ALLOWLIST_TOKENS - allowlist
    extra = allowlist - EXPECTED_ALLOWLIST_TOKENS
    if missing:
        failures.append(f"rule 5 (allowlist missing tokens): {sorted(missing)}")
    if extra:
        failures.append(f"rule 5 (allowlist extra tokens): {sorted(extra)}")

    in_refusal = extract_refusal_rule_tokens(formatter_text)
    if in_refusal:
        failures.append(
            f"rule 6 (R-L3-2-E violation — CONTAMINATED-* in refusal rules): {sorted(in_refusal)}"
        )

    if failures:
        print("v3.9.0 triangulation lint FAILED:", file=sys.stderr)
        for f in failures:
            print(f"  - {f}", file=sys.stderr)
        return 1

    print("v3.9.0 triangulation lint OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
