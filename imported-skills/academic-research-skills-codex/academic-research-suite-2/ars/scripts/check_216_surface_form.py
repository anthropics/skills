#!/usr/bin/env python3
"""Static lint for the #216 Surface-Form Parity self-check on the Devil's Advocate surface.

Issue: #216 (reviewer-type / surface-form asymmetry, Kim et al. 2026 arXiv:2605.20668v1 §F.3.6).

Enforces that the parity gate is present AND that every load-bearing clause survives, scoped to
its own marker block, so a bare keyword elsewhere in the file cannot make the lint pass while the
actual instruction is gone (falsifiability discipline — same pattern as check_215_field_norm.py).

The DA agent must carry, INSIDE the `SURFACE-FORM-PARITY-BLOCK` marker comments:

  * extract the checkable substance before judging,
  * judge the claim against the paper, not the polish,
  * do NOT down-rate informal/vague wording UNLESS ambiguity changes truth conditions,
  * do NOT credit technical specificity without checking the paper,
  * run the opposite-style counterfactual and revise / mark ambiguous on a flip,
  * authorship is NOT a judgment input.

The block must be a REAL block (markers present, outside a fenced code sample), and the
verdict-time framing + the §F.3.6 attribution + the epistemic-status disclaimer must survive in
the surrounding section so the gate cannot decay into a bare checklist with no provenance.

Exit 0 = clean, 1 = any failure.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
DA_AGENT = "academic-paper-reviewer/agents/devils_advocate_reviewer_agent.md"
SYNTH_AGENT = "academic-paper-reviewer/agents/editorial_synthesizer_agent.md"

BEGIN_MARKER = "SURFACE-FORM-PARITY-BLOCK:BEGIN"
END_MARKER = "SURFACE-FORM-PARITY-BLOCK:END"

# The two verdict-time surfaces that adjudicate the correctness/weight of a reviewer concern.
# Both must carry a scoped Surface-Form Parity block (codex P2 round 6: the editorial synthesizer
# arbitrates sub-claims and explicitly down-ranks "too vague" criticisms — exactly where §F.3.6
# fires — so DA alone is not the only surface). Each surface declares its own section header and
# its own load-bearing clauses (the DA judges a verdict on a claim; the synthesizer weights a
# sub-claim in arbitration), but both share the marker block + epistemic discipline.
SURFACES = {
    DA_AGENT: {
        "section_header_re": r"^## Surface-Form Parity Self-Check \(#216\)",
        "section_label": "## Surface-Form Parity Self-Check (#216)",
        "clauses": {
            "extract-substance": "Extract the checkable substance first",
            "judge-vs-paper-not-polish": "Judge the claim against the paper, not against the polish",
            "no-down-rate-informal": "Do not down-rate informal or vague wording",
            "unless-truth-conditions": "unless* the ambiguity actually changes the truth conditions or makes the claim unevaluable",
            "no-credit-specificity": "Do not credit technical specificity",
            "still-requires-checking": "still requires checking against the paper before you accept it",
            "opposite-style-counterfactual": "Run the opposite-style counterfactual",
            "would-my-verdict-change": "would my verdict change if this same substantive claim were rewritten in the opposite style",
            "revise-or-mark-ambiguous": "revise the verdict, or mark the claim ambiguous",
            "authorship-not-input": "Authorship (human vs AI origin of a concern) is deliberately **not** a judgment input",
        },
    },
    SYNTH_AGENT: {
        "section_header_re": r"^### Step 1c — Surface-Form Parity Check \(#216\)",
        "section_label": "### Step 1c — Surface-Form Parity Check (#216)",
        "clauses": {
            "judge-substance-not-polish": "Judge the sub-claim's substance against the paper, not against its polish",
            "no-down-rate-informal": "Do not down-rate informal or vague wording",
            "unless-unevaluable": "unless* the ambiguity actually makes the sub-claim unevaluable",
            "no-credit-specificity": "Do not credit technical specificity",
            "needs-paper-evidence": "still needs paper evidence before it gains weight",
            "opposite-style-counterfactual": "Run the opposite-style counterfactual",
            "would-weight-change": "would this sub-claim's weight change if the same substance were rewritten in the opposite style",
            "reweight-or-unevaluable": "re-weight on substance, or mark the sub-claim unevaluable",
            "authorship-not-input": "Authorship (whether a sub-claim originated from a human or an AI reviewer) is **not** a weighting input",
        },
    },
}


def _read(rel: str) -> str:
    return (REPO_ROOT / rel).read_text(encoding="utf-8")


def _section(text: str, header_re: str) -> str | None:
    """Return the markdown section from a header matching header_re up to the next heading of the
    SAME-OR-HIGHER level (fence-aware: a heading inside a ``` fence does not end the section).
    None if header absent.

    The stop level is derived from the matched header's own ``#`` depth (codex P2 round 7): a
    ``###`` section like Step 1c must end at the next ``###``/``##``/``#``, not only at ``##`` —
    otherwise the marker block could be relocated into a later ``###`` subsection and still be
    counted as inside this section.
    """
    header_pat = re.compile(header_re, re.M)
    # Find the header, but ignore any match that sits inside an open ``` fence (codex P2 round 8):
    # a whole section wrapped in a code fence is only a sample, not a live instruction, so a
    # file-wide regex match there must not be treated as a real section header.
    in_fence = False
    pos = 0
    start = None
    header_end = None
    for line in text.splitlines(keepends=True):
        if line.lstrip().startswith("```"):
            in_fence = not in_fence
        elif not in_fence and header_pat.match(line):
            start = pos
            header_end = pos + len(line)
            break
        pos += len(line)
    if start is None or header_end is None:
        return None
    # depth of the matched header (number of leading '#').
    header_line = text[start:].splitlines()[0]
    depth = len(header_line) - len(header_line.lstrip("#"))
    if depth < 1:
        depth = 2  # defensive: header_re always targets a real heading
    # a heading ends the section if its depth <= this section's depth.
    stop_re = re.compile(r"^\#{1," + str(depth) + r"} ")
    rest = text[header_end:]
    in_fence = False
    offset = 0
    for line in rest.splitlines(keepends=True):
        if line.lstrip().startswith("```"):
            in_fence = not in_fence
        elif not in_fence and stop_re.match(line):
            return text[start : header_end + offset]
        offset += len(line)
    return text[start:]


def _marker_block(text: str) -> str | None:
    """Return the text strictly BETWEEN the BEGIN and END markers, only if both markers sit
    OUTSIDE any fenced code block (a marker buried in a ``` sample is not a live instruction).
    None if a marker is missing or fenced."""
    # Find marker positions and verify each is outside a code fence.
    in_fence = False
    begin_pos = end_pos = None
    pos = 0
    for line in text.splitlines(keepends=True):
        if line.lstrip().startswith("```"):
            in_fence = not in_fence
        else:
            if BEGIN_MARKER in line and not in_fence and begin_pos is None:
                begin_pos = pos + len(line)
            elif END_MARKER in line and not in_fence and end_pos is None and begin_pos is not None:
                end_pos = pos
        pos += len(line)
    if begin_pos is None or end_pos is None or end_pos <= begin_pos:
        return None
    return text[begin_pos:end_pos]


def _strip_fenced(text: str) -> str:
    """Drop any ``` fenced spans, keeping only LIVE (unfenced) lines. Used so a load-bearing
    clause wrapped in a code fence inside the marker block is not counted as present (codex P2
    round 12): a fenced clause is only a sample, not a live instruction."""
    out = []
    in_fence = False
    for line in text.splitlines(keepends=True):
        if line.lstrip().startswith("```"):
            in_fence = not in_fence
            continue
        if not in_fence:
            out.append(line)
    return "".join(out)


def _check_surface(rel: str, spec: dict) -> list[str]:
    """Check one verdict-time surface carries its scoped Surface-Form Parity block."""
    errors: list[str] = []
    text = _read(rel)
    label = spec["section_label"]

    section = _section(text, spec["section_header_re"])
    if section is None:
        errors.append(f"{rel}: missing '{label}' section")
        return errors

    # Both surfaces must carry the §F.3.6 attribution; the prior is named on at least one
    # surface (the DA section states it in full), but each section must attribute the paper.
    if "§F.3.6" not in section:
        errors.append(f"{rel} #216 section: missing the §F.3.6 paper attribution")
    if "specificity correlates with correctness" not in section:
        errors.append(
            f"{rel} #216 section: missing the named root-cause prior "
            f"('specificity correlates with correctness')"
        )

    # Extract the marker block from WITHIN the parity section, not the whole file (codex P2): a
    # block moved out of the section while the header/framing/disclaimer remain would still be
    # found by a file-wide lookup, false-passing even though the section no longer holds the gate.
    block = _marker_block(section)
    if block is None:
        errors.append(
            f"{rel}: missing a live '{BEGIN_MARKER}'..'{END_MARKER}' marker block "
            f"INSIDE the '{label}' section (markers absent, out of section, out of order, "
            f"or buried inside a code fence)"
        )
        return errors

    # Each load-bearing clause is asserted by a stable substring that binds the modal to the
    # action, so a weakening (e.g. dropping the MUST/NOT or the UNLESS guard) is caught — a bare
    # keyword like "ambiguous" or "paper" elsewhere cannot satisfy these (codex P1.1). Check the
    # LIVE (unfenced) block text only (codex P2 round 12): a clause wrapped in a ``` fence inside
    # the block is just a sample, not a live instruction.
    live_block = _strip_fenced(block)
    for name, needle in spec["clauses"].items():
        if needle not in live_block:
            errors.append(f"{rel} #216 parity block: missing load-bearing clause [{name}]")

    # The epistemic-status disclaimer must survive in the section (prompt-surface honesty: no
    # runtime-free-of-bias claim, directional counts are not a target). Mirrors #215.
    if "Epistemic status" not in section:
        errors.append(f"{rel} #216 section: missing the epistemic-status disclaimer")
    if "not a calibration target" not in section:
        errors.append(
            f"{rel} #216 section: missing the 'directional counts are not a calibration target' "
            f"disclaimer (prevents the §F.3.6 29/10 numbers reading as a threshold)"
        )

    return errors


def check() -> list[str]:
    errors: list[str] = []
    for rel, spec in SURFACES.items():
        errors.extend(_check_surface(rel, spec))
    # The DA section additionally must carry the verdict-time framing (distinct from #215's
    # severity gate). The synthesizer section is inherently arbitration-time, framed in the header.
    da_section = _section(_read(DA_AGENT), SURFACES[DA_AGENT]["section_header_re"])
    if da_section is not None and "verdict-assignment time" not in da_section and "verdict time" not in da_section:
        errors.append(
            f"{DA_AGENT} #216 section: missing the 'verdict' time-of-application framing "
            f"(the parity gate runs at verdict time, distinct from #215's severity gate)"
        )
    return errors


def main() -> int:
    errors = check()
    if errors:
        for e in errors:
            print(f"ERROR: {e}", file=sys.stderr)
        return 1
    print("216_surface_form: DA + editorial synthesizer carry the scoped Surface-Form Parity block")
    return 0


if __name__ == "__main__":
    sys.exit(main())
