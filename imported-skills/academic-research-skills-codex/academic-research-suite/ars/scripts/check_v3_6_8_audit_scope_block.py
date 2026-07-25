#!/usr/bin/env python3
"""ARS v3.7.1 Step 2 — D2 audit Scope Report block lint.

Spec: docs/design/2026-04-30-ars-v3.6.8-trust-provenance-and-drift-transparency-spec.md
      §3.2 (D2 — Audit scope coverage non-disclosure)
      §4 Step 2 — Audit report Scope Report block (lines 412-425)

Enforces, on the codex audit prompt template:

  R1. A Section 0 Scope Report header appears strictly BEFORE the first
      Section 1 heading (spec line 146: "must appear before any pass/fail
      summary"). The header is the literal "## Codex Audit Round N — Scope
      Report" (spec line 134).
  R2. The Scope Report block carries the four mandatory content fields
      (spec lines 136-140):
        - Total entries audited
        - Entries with retrieved original source
        - Entries description-only (no retrieved source)
        - Audit scope warning
  R3. The aggregate-status section carries the three required splits
      (spec lines 147-150):
        - verified-against-source: PASS | FAIL
        - description-internally-consistent: PASS | FAIL
        - unaudited-due-to-missing-source: <count>
  R4. The combined-aggregate "PASSED" verb is forbidden in audit summary
      contexts (spec line 152). We forbid the literal pattern
      "Audit summary ... PASSED" (case-insensitive on the surrounding
      tokens) anywhere in the template.
  R5. Additive-prepend invariant per Q5 amend (spec §3.2 line 131,
      §3.7 line 346): the Section 1 heading must appear with exact bytes
      "## Section 1 — Round metadata" so prepending Section 0 has not
      altered the existing v3.6.7 audit template's byte-equivalent
      Sections 1-7 zone.

Attack-surface design notes (informed by issue #77 lessons):
  - Heading-anchored matching uses begin-of-line regex `^## ` to skip
    headings that appear inside fenced code blocks. The Scope Report
    block in the canonical template DOES contain a fenced sub-block with
    its own "## Codex Audit Round N — Scope Report" heading; our header
    detector must recognize that as the canonical Scope Report marker
    even though it lives inside a fence. We resolve this by allowing the
    Scope Report header to be inside the first fenced block of Section 0
    OR at top-level — but require that AT LEAST ONE such header anchor
    exists strictly before the Section 1 boundary, and that exactly one
    Section-0 anchor exists at top level (the H2 outside any fence).
  - Multiple Section-0 H2 anchors at top level → reject (mirror of #77
    P1-1 duplicate-marker bypass).

Exit codes: 0 on PASS, 1 on FAIL.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_TARGET = REPO_ROOT / "shared" / "templates" / "codex_audit_multifile_template.md"

# The canonical Section-0 H2 anchor at the top level of the template.
SECTION_0_H2 = "## Section 0"
# The Scope Report header literal, placed inside the fenced markdown block
# of Section 0 per spec line 134.
SCOPE_REPORT_HEADER = "## Codex Audit Round N — Scope Report"
# The byte-equivalent Section 1 heading per Q5 invariant.
SECTION_1_HEADING_EXACT = "## Section 1 — Round metadata"

# Required Scope Report content fields (spec lines 136-142).
# Codex round-9 P2a: spec line 142 requires the Affected-refcodes
# disclosure too — without it, an audit can hide which entries were
# unaudited even if the count is published.
REQUIRED_FIELDS: list[str] = [
    "**Total entries audited:**",
    "**Entries with retrieved original source:**",
    "**Entries description-only (no retrieved source):**",
    "**Audit scope warning:**",
    "**Affected refcodes (description-only):**",
]

# Required aggregate-status splits (spec lines 147-150).
REQUIRED_SPLITS: list[str] = [
    "verified-against-source",
    "description-internally-consistent",
    "unaudited-due-to-missing-source",
]

# Line-equality regex for the canonical Scope Report header. End-of-line
# anchored so a suffixed form like "## Codex Audit Round N — Scope Report
# (draft)" cannot satisfy R1 by prefix match (codex round-12 P2,
# symmetric to round-8 P2 on Section 1). Optional trailing whitespace
# before the line break is tolerated (invisible in rendered Markdown);
# anything else after the canonical bytes — including a space + suffix —
# fails. \Z covers EOF cases.
_SCOPE_REPORT_HEADER_LINE_RE = re.compile(
    rf"^{re.escape(SCOPE_REPORT_HEADER)}[ \t]*(?:\n|\Z)",
    re.MULTILINE,
)

# Forbidden combined-aggregate "PASSED" verb in audit summary contexts.
# Spec line 152: "The combined-aggregate 'PASSED' verb is forbidden in
# audit summary." Codex round-4 forced fence-content scan; round-5 P2-5
# broadened the verdict-key set (verdict / status / result / final /
# overall) so the lint catches `Overall status: PASSED` etc., not only
# `verdict: PASSED`. PASSED is matched case-insensitive on the surrounding
# tokens but the verb itself stays caps-only — that IS the forbidden
# verb form. The 80-char window after `audit summary` keeps the spec
# self-explanation prose (`...forbidden in the audit summary.`) clear
# of any PASSED token within reach.
# A verdict-shaped key word: any of the canonical verdict tokens, optionally
# preceded by one or two short qualifier words (e.g. "Final verdict",
# "Audit status", "Overall final result"). Codex round-6 P2-9 broadened
# this so multi-word keys like `Final verdict: PASSED` are also caught.
# Each qualifier is restricted to alphabetic characters of length 1-15
# so the regex does not gobble unrelated text on the same line.
_VERDICT_TOKEN = r"(?:verdict|status|result|final|outcome|overall|summary)"
_VERDICT_KEY = rf"(?:[A-Za-z]{{1,15}}\s+){{0,2}}{_VERDICT_TOKEN}"
# Heading-style summary token used for multi-line lookahead detection
# (codex round-7 P2). Catches `## Audit Summary`, `## Final Verdict`,
# `## Overall Outcome`, etc. — H2 headings whose title carries any
# verdict-key token (bare PASSED on the next lines is the violation).
_SUMMARY_HEADING = rf"^##\s+(?:[A-Za-z][\w-]*\s+){{0,3}}{_VERDICT_TOKEN}\b[^\n]*"

FORBIDDEN_AGGREGATE_PATTERNS: list[re.Pattern[str]] = [
    # Same-line: "audit summary ... PASSED" within 80 chars (legacy R4).
    re.compile(r"audit\s+summary[^\n]{0,80}\bPASSED\b", re.IGNORECASE),
    # Same-line: `<key>: PASSED` (legacy + multi-word key).
    re.compile(rf"^\s*{_VERDICT_KEY}\s*:\s*PASSED\b", re.IGNORECASE | re.MULTILINE),
    # Multi-line (codex round-7 P2): `## Summary heading` followed within
    # ~5 lines (≤400 chars across newlines) by a `PASSED` token. Catches
    # `## Audit Summary\n\nThis audit PASSED.` and `## Audit Summary\n\nPASSED`.
    # DOTALL lets `.` cross newlines; the 400-char window stays tight enough
    # that a much later unrelated PASSED in a separate section does not pair
    # with the heading.
    re.compile(
        rf"{_SUMMARY_HEADING}.{{0,400}}?\bPASSED\b",
        re.IGNORECASE | re.MULTILINE | re.DOTALL,
    ),
]

# Bare-verdict line patterns used to detect a pass/fail summary preceding
# Section 0 (spec line 146 firm rule). Wider than R4 because here we want
# to catch BOTH PASS and FAIL — anything resembling a verdict line counts
# as a pass/fail summary, regardless of the verb.
BARE_VERDICT_BEFORE_SECTION_0_PATTERNS: list[re.Pattern[str]] = [
    # Heading-style pass/fail summary
    re.compile(r"^##\s+[A-Za-z][^\n]{0,80}\b(Summary|Verdict)\b", re.MULTILINE),
    # Existing first-aggregate-split line (kept from earlier rounds)
    re.compile(r"^\s*verified-against-source\s*:\s*(PASS|FAIL)\b", re.MULTILINE),
    # Bare `<key>: PASS|FAIL` line, no heading framing
    re.compile(rf"^\s*{_VERDICT_KEY}\s*:\s*(PASS|FAIL|PASSED|FAILED)\b", re.IGNORECASE | re.MULTILINE),
]


def _strip_fenced_blocks(text: str) -> str:
    """Replace fenced code blocks with same-length whitespace so headings
    inside fences don't count as top-level H2 anchors.

    Length preservation keeps any line/column reporting consistent with
    the original file. We support the standard ``` and ~~~ fences.
    """

    def _replace(match: re.Match[str]) -> str:
        content = match.group(0)
        # Replace non-newline characters with spaces so newlines and
        # column positions are preserved, but content is neutralized.
        return "".join(" " if ch != "\n" else "\n" for ch in content)

    pattern = re.compile(
        r"^([ \t]*)(```|~~~)[^\n]*\n.*?^\1\2[ \t]*$",
        re.DOTALL | re.MULTILINE,
    )
    return pattern.sub(_replace, text)


def _find_section_1_position(text_no_fences: str) -> int:
    """Return the byte offset of the exact top-level Section 1 heading, or -1 if absent.

    Codex round-3 P2-3: a decoy heading inside a fenced code block (e.g. in
    a worked example) was previously accepted as the anchor. The check now
    runs against the fence-stripped text and requires line-start anchoring
    so a fenced occurrence of the exact heading bytes cannot satisfy R5.

    Codex round-8 P2: byte-equivalence must hold for the WHOLE heading line.
    A `find()` match treats the canonical bytes as a prefix and accepts
    `## Section 1 — Round metadata (renamed)` as if it were the canonical
    heading. Match a full line whose only content is the canonical heading,
    optionally followed by trailing whitespace before the line break.
    """
    line_re = re.compile(
        rf"^{re.escape(SECTION_1_HEADING_EXACT)}[ \t]*(?:\n|\Z)",
        re.MULTILINE,
    )
    match = line_re.search(text_no_fences)
    return match.start() if match else -1


def _format_target_for_report(target: Path) -> str:
    """Format target path for lint report.

    Codex round-2 P2-2: when --target is a relative repo path or points
    outside REPO_ROOT, `target.relative_to(REPO_ROOT)` raises ValueError.
    Resolve to absolute first, then attempt relativization, falling back
    to the raw path if the resolved path is not under REPO_ROOT.
    """
    try:
        resolved = target.resolve()
    except (OSError, RuntimeError):
        return str(target)
    try:
        return str(resolved.relative_to(REPO_ROOT))
    except ValueError:
        return str(resolved)


def _section_0_block(text_full: str, text_no_fences: str) -> str:
    """Slice the Section 0 block from the H2 anchor up to (but not including)
    the next H2 boundary at top level. Returns "" if the anchor is missing.

    Codex round-2 P2-1: required-field and aggregate-status-split checks
    must scope to Section 0 only, not whole-file. Otherwise a marker that
    appears in a later appendix or documentation block can falsely satisfy
    the check while Section 0 itself is incomplete.

    Boundary detection runs on the fence-stripped string so a fenced sub-
    block inside Section 0 (e.g. the canonical Scope Report header) does
    not terminate the slice. The returned slice is taken from the original
    text so contents are byte-equivalent to the source.
    """
    import re as _re
    section_0_match = _re.search(
        r"^## Section 0\b", text_no_fences, _re.MULTILINE
    )
    if section_0_match is None:
        return ""
    start = section_0_match.start()
    next_h2 = _re.search(r"^## ", text_no_fences[start + 1 :], _re.MULTILINE)
    end = (start + 1 + next_h2.start()) if next_h2 else len(text_full)
    return text_full[start:end]


def check(target: Path) -> tuple[int, list[str]]:
    """Run all rules. Return (exit_code, report_lines)."""
    if not target.exists():
        return 1, [f"FAIL: target file does not exist: {target}"]

    text = text_full = target.read_text(encoding="utf-8")
    text_no_fences = _strip_fenced_blocks(text)
    section_0_only = _section_0_block(text_full, text_no_fences)

    report: list[str] = [f"[v3.7.1 audit-scope-block] target: {_format_target_for_report(target)}"]
    failed: bool = False

    # ---- R5: Section 1 byte-equivalence sentinel ----
    # Codex round-3 P2-3: search the fence-stripped string so a decoy heading
    # inside a fenced code block (e.g. worked example) cannot satisfy R5.
    section_1_pos = _find_section_1_position(text_no_fences)
    if section_1_pos == -1:
        failed = True
        report.append(
            "  FAIL [R5]: Section 1 heading exact bytes "
            f"{SECTION_1_HEADING_EXACT!r} missing or shifted; "
            "Q5 additive-prepend invariant broken (spec §3.2 line 131)."
        )

    # ---- R1: Section 0 H2 anchor present, before Section 1 ----
    section_0_anchors = [
        m.start()
        for m in re.finditer(r"^## Section 0\b", text_no_fences, re.MULTILINE)
    ]
    if not section_0_anchors:
        failed = True
        report.append(
            "  FAIL [R1]: Section 0 Scope Report header missing "
            f"(expected H2 anchor starting with {SECTION_0_H2!r} at top level)."
        )
    elif len(section_0_anchors) > 1:
        failed = True
        report.append(
            f"  FAIL [R1]: multiple Section 0 H2 anchors found at top level "
            f"(positions={section_0_anchors}); duplicate-marker hardening rejects "
            f"more than one (compare issue #77 P1-1)."
        )
    elif section_1_pos != -1 and section_0_anchors[0] >= section_1_pos:
        failed = True
        report.append(
            f"  FAIL [R1]: Section 0 anchor (offset {section_0_anchors[0]}) "
            f"appears at or after Section 1 heading (offset {section_1_pos}); "
            f"spec line 146 firm rule: Scope Report must appear BEFORE any "
            f"pass/fail summary."
        )

    # ---- R1 continued: Scope Report header literal must appear inside Section 0 ----
    # Codex round-3 P2-4: scope to section_0_only so a preamble decoy
    # (e.g. an "Appendix" or "historical reference" carrying the exact
    # header) cannot falsely satisfy R1 when the real Section 0 block
    # is missing the canonical header.
    # Codex round-6 P2-8: anchor to a real heading line. A prose mention
    # of the header literal (`The required header is "## Codex Audit Round
    # N — Scope Report"`) inside Section 0 must NOT satisfy the contract.
    # Codex round-12 P2: require line equality (not prefix) so a suffixed
    # form like `... — Scope Report (draft)` cannot satisfy R1. Uses the
    # module-level _SCOPE_REPORT_HEADER_LINE_RE shared with the ordering
    # boundary derivation below.
    if _SCOPE_REPORT_HEADER_LINE_RE.search(section_0_only) is None:
        failed = True
        report.append(
            f"  FAIL [R1]: Scope Report header line {SCOPE_REPORT_HEADER!r} "
            "missing from Section 0 (spec line 134; must appear as a real "
            "heading line, not a prose mention)."
        )

    # ---- R6 firm-rule check: no pass/fail summary ahead of Scope Report ----
    # Spec line 146 ordering rule: the Scope Report content must appear
    # before any pass/fail summary surface.
    # Codex round-5 P2-6 broadened detection to bare-verdict lines.
    # Codex round-9 P2b: anchor on the canonical Scope Report header.
    # Codex round-10 P2: search includes fenced content (canonical header
    # lives in fence by spec design).
    # Codex round-11 P2: derive boundary from the Section-0-validated
    # header, not first whole-file occurrence. A preamble decoy line
    # carrying the canonical header text would otherwise short-circuit
    # the boundary too early, letting verdict lines between the decoy
    # and the real Scope Report content escape the prefix scan.
    ordering_boundary: int | None = None
    section_0_start = section_0_anchors[0] if section_0_anchors else None
    if section_0_start is not None:
        scope_header_in_section_0 = _SCOPE_REPORT_HEADER_LINE_RE.search(section_0_only)
        if scope_header_in_section_0 is not None:
            ordering_boundary = section_0_start + scope_header_in_section_0.start()
    if ordering_boundary is None and section_1_pos != -1:
        ordering_boundary = section_1_pos
    if ordering_boundary is None and section_0_start is not None:
        ordering_boundary = section_0_start
    if ordering_boundary is not None:
        prefix = text_full[:ordering_boundary]
        for pattern in BARE_VERDICT_BEFORE_SECTION_0_PATTERNS:
            match = pattern.search(prefix)
            if match is not None:
                failed = True
                anchor = match.group(0).strip()
                report.append(
                    f"  FAIL [R1]: pass/fail summary detected ahead of Scope Report content "
                    f"(anchor: {anchor!r}); spec line 146 requires Scope Report "
                    f"to appear BEFORE any pass/fail summary."
                )
                break  # one fail diagnostic per check is enough

    # ---- R2: required content fields ----
    # Codex round-2 P2-1: scope to Section 0 only. A marker in an appendix
    # or documentation block must NOT satisfy the contract — the audit
    # prompt that gets sent to codex contains Section 0, not the appendix.
    for field in REQUIRED_FIELDS:
        if field not in section_0_only:
            failed = True
            report.append(
                f"  FAIL [R2]: required Scope Report field missing from Section 0: "
                f"{field!r} (spec lines 136-140)."
            )

    # ---- R3: aggregate-status three-way split ----
    # Codex round-2 P2-1: same scoping fix as R2.
    for split in REQUIRED_SPLITS:
        if split not in section_0_only:
            failed = True
            report.append(
                f"  FAIL [R3]: required aggregate-status split missing from Section 0: "
                f"{split!r} (spec lines 147-150)."
            )

    # ---- R4: forbidden combined-aggregate 'PASSED' verb (cap rule) ----
    # Codex rounds 4-7 + 13 enumerated the forbidden surface lexically
    # (verdict-key + same-line, multi-word keys, multi-line summary headings,
    # bare verdict lines). Each round surfaced another shape codex could
    # construct, signalling that pattern enumeration is unbounded.
    #
    # Round-13 architectural inflection (per
    # `feedback_architectural_inflection_after_repeated_p1.md`): replace
    # the enumeration with a cap rule. ANY unquoted `PASSED` token on the
    # post-Section-0 surface violates the spec line 152 contract. Quoted
    # forms (`"PASSED"`, `'PASSED'`, backtick `` `PASSED` ``) remain
    # permitted because the canonical spec template uses them in self-
    # explanation prose ("the combined-aggregate 'PASSED' verb is forbidden").
    #
    # Surface = template text after the Section 0 H2 anchor (or whole
    # text if Section 0 anchor missing — already failed by R1). The
    # legacy FORBIDDEN_AGGREGATE_PATTERNS still run as supplementary
    # diagnostics on the pre-Section-0 surface (the upstream parts where
    # an audit summary heading would be a structural violation).
    cap_rule_surface_start = (
        section_0_anchors[0] if section_0_anchors else 0
    )
    cap_rule_surface = text_full[cap_rule_surface_start:]
    bare_passed_re = re.compile(r"\bPASSED\b")
    for match in bare_passed_re.finditer(cap_rule_surface):
        # Determine if this PASSED is quoted (allowed) or bare (forbidden).
        start, end = match.start(), match.end()
        # Look at the immediate surrounding character on each side. Quoted
        # if both neighbours are matching quote characters or if either
        # side is a backtick (Markdown inline code).
        left = cap_rule_surface[start - 1] if start > 0 else ""
        right = cap_rule_surface[end] if end < len(cap_rule_surface) else ""
        is_quoted = (
            (left == '"' and right == '"')
            or (left == "'" and right == "'")
            or (left == "`" and right == "`")
            or (left == "“" and right == "”")
        )
        if is_quoted:
            continue
        failed = True
        # Build a small context excerpt for the diagnostic.
        ctx_start = max(0, start - 30)
        ctx_end = min(len(cap_rule_surface), end + 30)
        excerpt = cap_rule_surface[ctx_start:ctx_end].replace("\n", " ")
        report.append(
            f"  FAIL [R4]: unquoted PASSED token on post-Section-0 surface "
            f"(spec line 152 cap rule). Context: …{excerpt}… "
            "Use quoted form (\"PASSED\", `PASSED`) for self-explanation only."
        )
        break  # one diagnostic is enough; user fixes then re-runs

    # Supplementary diagnostics: run the legacy patterns on the FULL text
    # so any structural violations they specifically detect (audit-summary
    # heading + verdict combinations) still surface even when the cap
    # rule already fired. Skip if already failed to avoid noise.
    if not failed:
        for pattern in FORBIDDEN_AGGREGATE_PATTERNS:
            match = pattern.search(text_full)
            if match is not None:
                failed = True
                report.append(
                    f"  FAIL [R4]: forbidden combined-aggregate 'PASSED' verb in "
                    f"audit summary context: {match.group(0)!r} "
                    "(spec line 152: combined-aggregate 'PASSED' is forbidden)."
                )

    if failed:
        report.append("[v3.7.1 audit-scope-block] FAILED")
        return 1, report
    report.append("[v3.7.1 audit-scope-block] PASS")
    return 0, report


def main() -> int:
    parser = argparse.ArgumentParser(
        description="ARS v3.7.1 Step 2 — D2 audit Scope Report block lint."
    )
    parser.add_argument(
        "--target",
        type=Path,
        default=DEFAULT_TARGET,
        help="Audit prompt template path (default: shared/templates/codex_audit_multifile_template.md).",
    )
    args = parser.parse_args()

    exit_code, report = check(args.target)
    print("\n".join(report))
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
