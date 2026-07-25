#!/usr/bin/env python3
"""Static lint for #215 field-norm severity coverage across the three reviewer surfaces.

Issue: #215 (field-norm severity calibration, Kim et al. 2026 arXiv:2605.20668v1 W1/§F.3.4).

Enforces that the three #215 changes are present AND scoped to their own block, so a
bare keyword appearing elsewhere in a file cannot make the lint pass while the actual
load-bearing instruction is missing (falsifiability discipline, per
feedback_lint_passes_but_prompt_silent.md — same pattern as check_v3_9_2_phase_boundary).

Three surfaces:

1. domain_reviewer_agent.md — a `### Step 5: Field-Norm Severity Discipline (#215)` block
   that contains the hard rule (MUST ground the norm in an external source, MUST NOT
   assert from model knowledge), the broadened evidence definition (not just a literature
   citation), and the `[FIELD-NORM UNVERIFIED]` down-rate label.

2. devils_advocate_reviewer_agent.md — a 9th challenge dimension
   `### 9. Field-Norm Severity Calibration (#215)` AND the two required CRITICAL/MAJOR
   fields `field_norm_boundary` + `evidence_crossing_rationale`.

3. calibration_mode_protocol.md — a `### Phase 3.5: Severity-miscalibration measurement (#215)`
   block carrying the low/med/high risk classification and the anti-circularity grounding
   discipline (classify grounding, NOT norm-correctness — do not repeat the W1 failure).

Exit 0 = clean, 1 = any failure.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent


def _read(rel: str) -> str:
    return (REPO_ROOT / rel).read_text(encoding="utf-8")


def _block(text: str, header_re: str) -> str | None:
    """Return the markdown block from a header matching header_re up to the next header of
    the same-or-higher level (## or ###), or end of file. None if the header is absent.

    Scopes keyword checks to the block so a keyword elsewhere in the file does not count.
    A ``##``/``###`` line INSIDE a ``` fenced code block is NOT a real header (e.g. an
    Output Format section embeds a sample report whose code fence contains ``## ...`` lines);
    treating it as one would truncate the block early and drop content below it.
    """
    m = re.search(header_re, text, re.M)
    if not m:
        return None
    start = m.start()
    rest = text[m.end():]
    in_fence = False
    offset = 0
    for line in rest.splitlines(keepends=True):
        if line.lstrip().startswith("```"):
            in_fence = not in_fence
        elif not in_fence and re.match(r"\#{2,3} ", line):
            # A real header line (column 0, outside any fence) ends the block.
            return text[start : m.end() + offset]
        offset += len(line)
    return text[start:]


def check() -> list[str]:
    errors: list[str] = []

    # --- Surface 1: domain_reviewer_agent.md Step 5 ---
    dr = _read("academic-paper-reviewer/agents/domain_reviewer_agent.md")
    step5 = _block(dr, r"^### Step 5: Field-Norm Severity Discipline \(#215\)")
    if step5 is None:
        errors.append("domain_reviewer_agent.md: missing '### Step 5: Field-Norm Severity Discipline (#215)' block")
    else:
        # The down-rate prohibition AND the load-bearing positive MUST-ground clause must
        # both survive. The positive clause binds the modal to the grounding requirement
        # ("MUST** ground the norm in an external"), so weakening MUST→SHOULD is caught — a
        # bare "ground the norm" substring would still pass under SHOULD (codex re-review P1).
        for clause in ("MUST NOT", "[FIELD-NORM UNVERIFIED]", "MUST** ground the norm in an external"):
            if clause not in step5:
                errors.append(f"domain_reviewer_agent.md Step 5: missing required clause {clause!r}")
        # codex P1: evidence is NOT limited to a literature citation.
        if "not limited to a literature citation" not in step5:
            errors.append(
                "domain_reviewer_agent.md Step 5: missing the broadened-evidence rule "
                "('not limited to a literature citation')"
            )

    # --- Surface 2: devils_advocate_reviewer_agent.md dimension 9 + CRITICAL fields ---
    da = _read("academic-paper-reviewer/agents/devils_advocate_reviewer_agent.md")
    dim9 = _block(da, r"^### 9\. Field-Norm Severity Calibration \(#215\)")
    if dim9 is None:
        errors.append("devils_advocate_reviewer_agent.md: missing '### 9. Field-Norm Severity Calibration (#215)' dimension")
    # The two required fields must land in the OUTPUT FORMAT block — that is what makes the
    # rule reach the actual review output. A file-wide check would pass on the prose mention
    # in the gating section even if the output-format columns were deleted (codex P1).
    output_fmt = _block(da, r"^## Output Format")
    if output_fmt is None:
        errors.append("devils_advocate_reviewer_agent.md: missing '## Output Format' block")
    else:
        # The CRITICAL/MAJOR tables carry the fields as human-readable column HEADERS
        # (Title Case), which is what actually reaches the review output. The snake_case
        # names live only in the gating prose. Scope to EACH severity subsection separately:
        # if only one table loses its columns, a whole-block check still finds the names in
        # the other table and false-passes (codex re-review P1). These #### headers sit inside
        # the ```markdown sample, so slice between #### markers rather than using _block.
        for severity in ("CRITICAL", "MAJOR"):
            sub = re.search(rf"^#### {severity}\n(.*?)(?=^#### |\Z)", output_fmt, re.M | re.S)
            if sub is None:
                errors.append(f"devils_advocate_reviewer_agent.md Output Format: missing '#### {severity}' table")
                continue
            for column in ("Field-Norm Boundary", "Evidence-Crossing Rationale"):
                if column not in sub.group(1):
                    errors.append(
                        f"devils_advocate_reviewer_agent.md Output Format {severity} table: "
                        f"missing required column {column!r}"
                    )
    # The snake_case field NAMES + their grounding definition live in the CRITICAL-finding
    # gating block; check them there (scoped) so a definition deleted from that block is
    # caught independently of the output-format columns.
    crit_block = _block(da, r"^### What Constitutes a CRITICAL Finding")
    if crit_block is None:
        errors.append("devils_advocate_reviewer_agent.md: missing '### What Constitutes a CRITICAL Finding' block")
    else:
        for field in ("field_norm_boundary", "evidence_crossing_rationale"):
            if field not in crit_block:
                errors.append(
                    f"devils_advocate_reviewer_agent.md CRITICAL-finding block: missing field "
                    f"definition {field!r}"
                )
        if "[FIELD-NORM UNVERIFIED]" not in crit_block:
            errors.append(
                "devils_advocate_reviewer_agent.md CRITICAL-finding block: missing "
                "'[FIELD-NORM UNVERIFIED]' down-rate label"
            )

    # --- Surface 3: calibration_mode_protocol.md Phase 3.5 ---
    cal = _read("academic-paper-reviewer/references/calibration_mode_protocol.md")
    phase35 = _block(cal, r"^### Phase 3\.5: Severity-miscalibration measurement \(#215\)")
    if phase35 is None:
        errors.append("calibration_mode_protocol.md: missing '### Phase 3.5: Severity-miscalibration measurement (#215)' block")
    else:
        # Require the actual risk-level DEFINITIONS, not bare words. The intro line already
        # contains "low / med / high", so a substring check passes even if all three
        # definition bullets are deleted (codex P2). Each level is defined as **`level`** — …
        for level in ("low", "med", "high"):
            if f"**`{level}`**" not in phase35:
                errors.append(
                    f"calibration_mode_protocol.md Phase 3.5: missing the {level!r} risk-level definition"
                )
        # codex P1: classify GROUNDING, not norm-correctness — do not repeat the failure.
        if "MUST NOT" not in phase35 or "evals/gold/field_norm_severity" not in phase35:
            errors.append(
                "calibration_mode_protocol.md Phase 3.5: missing the anti-circularity grounding "
                "discipline (MUST NOT guess norm-correctness; anchor to evals/gold/field_norm_severity)"
            )

    return errors


def main() -> int:
    errors = check()
    if errors:
        for e in errors:
            print(f"ERROR: {e}", file=sys.stderr)
        return 1
    print("215_field_norm: all three reviewer surfaces carry their scoped #215 blocks")
    return 0


if __name__ == "__main__":
    sys.exit(main())
