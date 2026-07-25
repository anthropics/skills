"""ARS v3.8 §3.6 + §5 — annotation literal sync lint.

The 8-row finalizer matrix in `scripts/claim_audit_finalizer.py` emits five
HIGH-WARN annotation classes that the formatter's terminal hard gate
(`academic-paper/agents/formatter_agent.md`) MUST refuse on. The annotation
literals appear in two places:

1. `scripts/claim_audit_finalizer.py` as `ANNOTATION_HIGH_WARN_*` constants
   (the finalizer write side — `apply_finalizer` returns these on
   gate_refuse=True rows).
2. `academic-paper/agents/formatter_agent.md` REFUSE rules 6-10 (the
   formatter read side — terminal hard gate scans the draft for these
   literals before emitting LaTeX/DOCX/PDF).

A literal drift between the two sides silently breaks the gate: if the
finalizer is renamed from `[HIGH-WARN-CLAIM-NOT-SUPPORTED]` to
`[HIGH-WARN-CLAIM-UNSUPPORTED]` and the formatter rule 6 is not updated,
the formatter will pass output that the orchestrator marked HIGH-WARN.

This lint extracts the five `ANNOTATION_HIGH_WARN_*` constant values from
the finalizer module and asserts each one's bracket prefix appears in the
formatter agent prompt's REFUSE list. The check uses bracket-prefix
matching (NOT byte-equivalence on the full annotation) because the
NEGATIVE-CONSTRAINT-VIOLATION + CONSTRAINT-VIOLATION-UNCITED literals
carry a runtime `({violated_constraint_id})` interpolation that the
formatter prose cannot duplicate verbatim — the prefix up to but not
including the interpolation hole is the contract.

Spec: docs/design/2026-05-15-issue-103-claim-alignment-audit-spec.md §5.

Lint exit codes:
  0 = pass (all five HIGH-WARN annotation prefixes present in formatter).
  1 = at least one annotation prefix missing from formatter REFUSE list.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
FINALIZER_MODULE = REPO_ROOT / "scripts" / "claim_audit_finalizer.py"
FORMATTER_AGENT = REPO_ROOT / "academic-paper" / "agents" / "formatter_agent.md"

_HEADING_AFTER_REFUSE = re.compile(r"(?m)^#{1,2}[ \t]+")


def _extract_refuse_block(formatter_text: str) -> str | None:
    """Return the REFUSE-rules block text, or None if the marker is absent.

    The block opens at the literal marker
    `**REFUSE to emit final output**` (line bold in `formatter_agent.md`)
    and ends at the next H2 or H1 heading. Numbered rules 1-10 live inside
    this block — restricting the lint search here prevents the false PASS
    where a HIGH-WARN literal appears in background prose / cross-reference
    but is removed from the gate rules.
    """
    marker = "**REFUSE to emit final output**"
    start = formatter_text.find(marker)
    if start == -1:
        return None
    nm = _HEADING_AFTER_REFUSE.search(formatter_text, start + len(marker))
    end = nm.start() if nm else len(formatter_text)
    return formatter_text[start:end]


def _annotation_match_token(annotation_literal: str) -> str:
    """Return the search token the formatter REFUSE block must contain.

    Annotation literals follow three shapes:
      - Closed plain:        `[HIGH-WARN-CLAIM-NOT-SUPPORTED]`
      - Interpolated suffix: `[HIGH-WARN-NEGATIVE-CONSTRAINT-VIOLATION ({violated_constraint_id})]`
      - Em-dash suffix:      `[HIGH-WARN-CLAIM-AUDIT-ANCHORLESS — v3.7.3 R-L3-1-A VIOLATION REACHED AUDIT]`

    Closed plain literals MUST match byte-equivalently including the
    closing bracket. Step 8 codex R2 P2-1 closure: cutting at `]` left
    just the prefix without the bracket, so a renamed formatter rule
    such as `[HIGH-WARN-FABRICATED-REFERENCE-RENAMED]` would still
    contain `[HIGH-WARN-FABRICATED-REFERENCE` and false-pass the lint
    while the terminal gate actually scans for the wrong literal.

    Interpolated and em-dash literals match the formatter prose's
    prefix form (which abbreviates the variable suffix). The search
    token cuts at the first ` (`, ` —`, or `{` — whichever appears
    first — and the formatter prose must contain that prefix exactly.

    Decision: closed literals exact, interpolated/em-dash prefix.
    """
    # Detect interpolated/em-dash shapes first — these need prefix match.
    # Use the earliest-occurring terminator (min idx across the three
    # candidate cuts), not the list-order first hit — `{` and ` (` can
    # both appear in the same literal and the earlier of the two is
    # the semantic prefix boundary.
    earliest = len(annotation_literal)
    for terminator in ("{", " (", " —"):
        idx = annotation_literal.find(terminator)
        if idx != -1 and idx < earliest:
            earliest = idx
    if earliest < len(annotation_literal):
        return annotation_literal[:earliest].rstrip()
    # Closed plain literal — return the whole thing so the search hit
    # requires byte-equivalent presence including the `]`.
    return annotation_literal


# Backwards-compat alias for tests written against the prior name.
_annotation_prefix = _annotation_match_token


def _extract_finalizer_high_warn_constants(source: str) -> dict[str, str]:
    """Parse the finalizer module source for `ANNOTATION_HIGH_WARN_*` constants.

    Imports `scripts.claim_audit_finalizer` and reads each
    `ANNOTATION_HIGH_WARN_*` attribute via `dir()` + `getattr()`. Reading the
    runtime module (instead of AST-walking the source) ensures the lint
    sees the exact string Python sees at import time, including any future
    derived/templated values.

    Filters to `ANNOTATION_HIGH_WARN_*` names only. The five canonical
    HIGH-WARN classes are:
      - ANNOTATION_HIGH_WARN_CLAIM_NOT_SUPPORTED
      - ANNOTATION_HIGH_WARN_NEGATIVE_CONSTRAINT_VIOLATION
      - ANNOTATION_HIGH_WARN_FABRICATED_REFERENCE
      - ANNOTATION_HIGH_WARN_ANCHORLESS
      - ANNOTATION_HIGH_WARN_CONSTRAINT_VIOLATION_UNCITED
    """
    ns: dict[str, object] = {}
    # The module's import of `INV14_FAULT_CLASS_TAGS` from
    # `_claim_audit_constants` is part of module init. Use the module
    # import path so the load succeeds end-to-end.
    sys.path.insert(0, str(REPO_ROOT))
    try:
        from scripts import claim_audit_finalizer  # noqa: F401  (import for side effect: load constants)

        for name in dir(claim_audit_finalizer):
            if name.startswith("ANNOTATION_HIGH_WARN_"):
                ns[name] = getattr(claim_audit_finalizer, name)
    finally:
        sys.path.remove(str(REPO_ROOT))
    return {name: value for name, value in ns.items() if isinstance(value, str)}


def main() -> int:
    if not FINALIZER_MODULE.exists():
        print(f"[v3.8 annotation-sync] FAIL: missing {FINALIZER_MODULE}")
        return 1
    if not FORMATTER_AGENT.exists():
        print(f"[v3.8 annotation-sync] FAIL: missing {FORMATTER_AGENT}")
        return 1

    constants = _extract_finalizer_high_warn_constants(FINALIZER_MODULE.read_text())
    if len(constants) != 5:
        print(
            f"[v3.8 annotation-sync] FAIL: expected exactly 5 ANNOTATION_HIGH_WARN_* "
            f"constants in claim_audit_finalizer.py; found {len(constants)}: "
            f"{sorted(constants)}"
        )
        return 1

    formatter_text = FORMATTER_AGENT.read_text()
    # Restrict the search to the REFUSE-list block so the lint actually
    # proves the formatter's terminal hard gate refuses on each annotation
    # — a literal that appears only in background prose or a cross-reference
    # would not be enforced by the gate. Step 8 codex R1 P3 closure.
    #
    # The REFUSE block opens at `**REFUSE to emit final output**` and ends
    # at the next H2 (`## `) or H1 (`# `) heading; numbered rules 1-10 live
    # inside that block. If the marker is missing the lint fails closed.
    refuse_block = _extract_refuse_block(formatter_text)
    if refuse_block is None:
        print(
            f"[v3.8 annotation-sync] FAIL: REFUSE-list marker "
            f"'**REFUSE to emit final output**' not found in {FORMATTER_AGENT.name}; "
            f"cannot scope the sync check to the gate rules."
        )
        return 1

    missing: list[tuple[str, str]] = []
    for name, literal in sorted(constants.items()):
        token = _annotation_match_token(literal)
        # Closed literals end in `]` and require exact byte-equivalent
        # substring match (Step 8 codex R2 P2-1 closure).
        # Interpolated/em-dash tokens (e.g. `[HIGH-WARN-NEGATIVE-
        # CONSTRAINT-VIOLATION`) require a BOUNDARY character following
        # the token in the formatter prose — otherwise a rename that
        # appends text (`[HIGH-WARN-NEGATIVE-CONSTRAINT-VIOLATION-RENAMED`)
        # would still substring-match the original prefix and false-pass
        # the lint. Step 8 codex R3 P2 closure: require the token to be
        # followed by ` ` (space-paren contract per canonical form) or
        # `]` (no-variable closing bracket) — both are valid boundaries
        # in the formatter REFUSE prose.
        if token.endswith("]"):
            present = token in refuse_block
        else:
            # Boundary characters that legitimately follow the token in
            # formatter prose: ` ` (the canonical ` ({var})]` continuation),
            # `]` (no-variable closing bracket), `` ` `` (markdown inline
            # code close — rules 7/9/10 wrap the token in backticks). Any
            # OTHER following character (a letter, digit, or hyphen)
            # indicates a rename attack — e.g. `…VIOLATION-RENAMED]`
            # should NOT satisfy `…VIOLATION` because the boundary is a
            # hyphen-letter run that extends the identifier.
            present = any(
                f"{token}{boundary}" in refuse_block
                for boundary in (" ", "]", "`")
            )
        if not present:
            missing.append((name, token))

    if missing:
        print(
            f"[v3.8 annotation-sync] FAIL: {len(missing)} HIGH-WARN annotation "
            f"literal(s) missing from formatter REFUSE list (spec §5 + §1 "
            f"deliverable 5):"
        )
        for name, prefix in missing:
            print(f"  - {name}: prefix {prefix!r} not found in {FORMATTER_AGENT.name}")
        return 1

    print(
        f"[v3.8 annotation-sync] PASS: all {len(constants)} HIGH-WARN annotation "
        f"prefixes present in formatter_agent.md REFUSE list"
    )
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
