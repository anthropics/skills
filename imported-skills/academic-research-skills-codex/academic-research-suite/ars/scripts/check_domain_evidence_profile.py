#!/usr/bin/env python3
"""Lint domain evidence profile documentation surface (#259).

Seven documentation-surface checks C1-C7. Honest about reach: verifies presence/
shape of required text, NOT runtime semantics (those rely on worked examples +
plan-stage review per the spec Test strategy). Exit 0 pass / 1 fail.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import Callable

# Path.cwd() (not __file__) so fixture tests can subprocess.run(cwd=fixture_repo).
REPO_ROOT = Path.cwd()
INTAKE = REPO_ROOT / "academic-paper" / "agents" / "intake_agent.md"
PROFILES = REPO_ROOT / "academic-paper" / "references" / "domain_evidence_profiles.md"
CONSUMER = REPO_ROOT / "academic-paper" / "agents" / "literature_strategist_agent.md"
SQH = REPO_ROOT / "deep-research" / "references" / "source_quality_hierarchy.md"

SHIP_ENUM = ("general_social_science", "cs_ml", "humanities_interpretive", "unknown_user_defined")
RESERVED = ("clinical", "wet_lab", "materials_physics", "legal_case_based", "education")

INTAKE_STEP12_HEADING = "### Step 12: Domain Evidence Profile"
CONSUMER_RESOLUTION_HEADING = "### Domain Evidence Profile Resolution"
INTAKE_NO_HANDOFF_HEADING = "### When No Handoff Materials Are Detected"
DECISION_TREE_HEADING = "### Literature Screening Decision Tree"


def _read(p: Path) -> str:
    return p.read_text(encoding="utf-8") if p.exists() else ""


def _heading_range(text: str, heading: str) -> str | None:
    """Byte range from `heading` to the next same-or-higher-level ATX heading
    (or EOF), IGNORING `#`-prefixed lines inside fenced code blocks.

    Determines the heading level by counting leading '#'. The block this guards
    contains fenced pseudocode whose comment lines start with `# ` at column 0;
    a naive `^#{1,level} ` scan would treat that comment as the next heading and
    truncate the range at the first pseudocode comment (so C3 would miss the
    universal-gate keywords / forbidden-carrier tokens that follow). We track
    fence state line-by-line and only accept a heading match OUTSIDE a fence.
    Scans only this range so C7 does not false-fail on historical-contrast prose
    elsewhere in the file.
    """
    idx = text.find(heading)
    if idx == -1:
        return None
    level = len(heading) - len(heading.lstrip("#"))
    rest = text[idx + len(heading):]
    lines = rest.splitlines(keepends=True)
    offset = 0
    in_fence = False
    heading_re = re.compile(rf"^#{{1,{level}}} ")
    for ln in lines:
        stripped = ln.lstrip()
        if stripped.startswith("```") or stripped.startswith("~~~"):
            in_fence = not in_fence
            offset += len(ln)
            continue
        if not in_fence and heading_re.match(ln):
            return text[idx: idx + len(heading) + offset]
        offset += len(ln)
    return text[idx: idx + len(heading) + len(rest)]


def _strip_fences(text: str) -> str:
    """Return `text` with all fenced code blocks (``` or ~~~) removed.

    Used by checks that must anchor a requirement in PROSE, not in a pseudocode
    identifier. e.g. C3's universal-gate keywords (relevance/methodology/
    predatory) must appear in the prose sentence, not merely inside the
    `UNIVERSAL_GATES = [relevance_to_RQ, ...]` pseudocode line — otherwise
    deleting the prose while leaving the code would falsely pass.
    """
    out, in_fence = [], False
    for ln in text.splitlines(keepends=True):
        s = ln.lstrip()
        if s.startswith("```") or s.startswith("~~~"):
            in_fence = not in_fence
            continue
        if not in_fence:
            out.append(ln)
    return "".join(out)


def check_c1() -> list[str]:
    """intake_agent: enum + reserved + PCR row + coherence + reserved-fallback +
    display form + Step 12 heading + carve-out + override tag (both halves)."""
    f: list[str] = []
    t = _read(INTAKE)
    if not t:
        return ["C1: intake_agent.md not found"]
    if INTAKE_STEP12_HEADING not in t:
        f.append(f"C1: missing exact heading '{INTAKE_STEP12_HEADING}'")
    for v in SHIP_ENUM:
        if v not in t:
            f.append(f"C1: intake missing enum value '{v}'")
    for v in RESERVED:
        if v not in t:
            f.append(f"C1: intake missing reserved value '{v}'")
    if "Domain Evidence Profile" not in t or "| **Domain Evidence Profile** |" not in t:
        f.append("C1: intake missing PCR 'Domain Evidence Profile' row")
    if "(requested:" not in t:
        f.append("C1: intake missing reserved-fallback display form '(requested: <reserved>)'")
    if "[PROFILE-OVERRIDE-NO-RESCREEN]" not in t:
        f.append("C1: intake missing [PROFILE-OVERRIDE-NO-RESCREEN] advisory")
    # Both halves of the override condition: already-run AND was-skipped.
    if not (re.search(r"already run", t) and re.search(r"was (explicitly )?skipped|skipped entirely", t)):
        f.append("C1: override condition missing 'already run OR was skipped' (both halves required)")
    if "Phase-1-fully-skipped carve-out" not in t and "skips literature screening" not in t:
        f.append("C1: intake missing Phase-1-fully-skipped carve-out")
    return f


def check_c2() -> list[str]:
    """profiles doc: exists, gaps column wording, reserved list, and a
    CLOSED-SET 4-profile table (exactly the 4 SHIP_ENUM rows — no 5th effective
    profile, no reserved value smuggled in as an effective row)."""
    f: list[str] = []
    t = _read(PROFILES)
    if not t:
        return ["C2: domain_evidence_profiles.md not found"]
    if "## Domain Evidence Profiles" not in t:
        f.append("C2: missing '## Domain Evidence Profiles' section")
    if "Critical gaps to surface" not in t:
        f.append("C2: gaps column must be 'Critical gaps to surface', not 'disqualifying'")
    if "disqualifying" in t.lower():
        f.append("C2: forbidden word 'disqualifying' present (profile is advisory)")
    for v in RESERVED:
        if v not in t:
            f.append(f"C2: profiles doc missing reserved value '{v}'")
    if "not in enum" not in t:
        f.append("C2: profiles doc missing 'not in enum' reserved note")

    # Closed-set table enforcement (hardening from review rounds). Parse the
    # `## Domain Evidence Profiles` section's table and check EVERY data row's
    # first cell — not just the ones that happen to be backticked tokens. The
    # earlier "only record backticked first cells" version had a false-pass: a
    # 5th effective row written WITHOUT backticks (`| clinical | ... |`) was
    # silently skipped, leaving got == SHIP_ENUM. Now every pipe data row counts,
    # and a first cell that is not exactly one of the four backticked SHIP_ENUM
    # values FAILS. The set must equal exactly the 4 SHIP_ENUM values, with no
    # duplicates.
    sec = _heading_range(t, "## Domain Evidence Profiles")
    if sec is None:
        f.append("C2: '## Domain Evidence Profiles' section not found for table parse")
        return f
    valid_first = {f"`{v}`" for v in SHIP_ENUM}
    row_tokens: list[str] = []
    for line in sec.splitlines():
        ln = line.strip()
        if not ln.startswith("|"):
            continue
        cells = [c.strip() for c in ln.strip("|").split("|")]
        first = cells[0] if cells else ""
        # Skip the header row and the |---|---| separator row.
        if first in ("Profile", "") or set(first) <= set("-: "):
            continue
        # Every remaining data row's first cell MUST be a backticked SHIP_ENUM.
        if first not in valid_first:
            f.append(
                f"C2: profile table data row has an invalid first cell {first!r} "
                f"(must be exactly one of {sorted(valid_first)} — no 5th effective "
                f"profile, no un-backticked or reserved value smuggled in)"
            )
            continue
        row_tokens.append(first.strip("`"))
    got = set(row_tokens)
    want = set(SHIP_ENUM)
    if got != want:
        f.append(
            f"C2: profile table is not the closed 4-row SHIP_ENUM set "
            f"(extra={sorted(got - want)}, missing={sorted(want - got)})"
        )
    if len(row_tokens) != len(set(row_tokens)):
        f.append(f"C2: profile table has duplicate profile rows: {row_tokens}")
    return f


def check_c3() -> list[str]:
    """consumer: resolution block, PCR-row resolve, 3 fallback cases, 3 consumer
    tags, universal-gate carve-out language; source_verification NOT a consumer."""
    f: list[str] = []
    t = _read(CONSUMER)
    if not t:
        return ["C3: literature_strategist_agent.md not found"]
    block = _heading_range(t, CONSUMER_RESOLUTION_HEADING)
    if block is None:
        return [f"C3: missing exact heading '{CONSUMER_RESOLUTION_HEADING}'"]
    # Backtick-strip before substring match: the prose writes the field name
    # backticked (`PCR \`Domain Evidence Profile\` row`), so the contiguous
    # substring "Domain Evidence Profile row" only exists after stripping.
    block_nb = block.replace("`", "")
    if "PCR" not in block_nb or "Domain Evidence Profile row" not in block_nb:
        f.append("C3: resolution block must resolve from the PCR 'Domain Evidence Profile row'")
    for tag in ("[NO-PROFILE-NEUTRAL]", "[PROFILE-UNRESOLVED]", "[PROFILE-DISCIPLINE-MISMATCH]"):
        if tag not in block:
            f.append(f"C3: resolution block missing consumer tag '{tag}'")
    # graceful-fallback cases
    for kw in ("absent", "unknown_user_defined", "not in the 4 enum"):
        if kw not in block:
            f.append(f"C3: resolution block missing fallback keyword '{kw}'")
    # Universal-gate carve-out language must be in PROSE, not only the pseudocode.
    # Strip fenced code first: otherwise the `UNIVERSAL_GATES = [relevance_to_RQ,
    # methodology_not_fatally_flawed, not_predatory_or_fabricated]` identifiers
    # would satisfy the check even if the prose sentence naming the three gates
    # were deleted — which would silently weaken the documented INVARIANT 5
    # contract. (hardening from a review round.)
    block_prose = _strip_fences(block)
    for kw in ("relevance", "methodology", "predatory"):
        if kw not in block_prose:
            f.append(f"C3: resolution PROSE (outside code fences) missing universal-gate keyword '{kw}'")
    # source_verification must NOT be given a profile step in this consumer file
    if "source_verification_agent is NOT" not in t.replace("`", ""):
        f.append("C3: consumer must state source_verification_agent is NOT a profile consumer")
    return f


def check_c4() -> list[str]:
    """profiles doc: advisory-only statement + #246 forward-ref."""
    f: list[str] = []
    t = _read(PROFILES)
    if "Advisory only" not in t:
        f.append("C4: profiles doc missing advisory-only statement")
    if "#246" not in t:
        f.append("C4: profiles doc missing #246 forward-reference note")
    return f


def check_c5() -> list[str]:
    """profiles doc: legacy guidance present, non-normative label, Medicine/Health
    + Education verbatim, Policy fold reference.

    Asserts the *content* of each legacy row, not the bare label — "Education"
    and "Policy" also appear in the reserved list / fold notes, so a bare-token
    check would false-pass even if the legacy row itself were deleted. Each
    assertion below binds a label to a distinctive phrase from its verbatim
    carry-forward, so deleting the row actually fails the check.
    """
    f: list[str] = []
    t = _read(PROFILES)
    if "non-normative" not in t.lower():
        f.append("C5: legacy carry-forward must be labeled non-normative")
    # Medicine/Health legacy row — distinctive phrase from the verbatim text.
    if "Medicine/Health" not in t or "evidence-based-medicine" not in t.lower():
        f.append("C5: missing preserved Medicine/Health legacy row (verbatim 'evidence-based-medicine' text)")
    # Education legacy row — distinctive phrase, NOT the bare reserved token.
    if "quasi-experimental" not in t.lower():
        f.append("C5: missing preserved Education legacy row (verbatim 'quasi-experimental' text)")
    # Policy fold — must bind "Policy" to the fold ON THE SAME LINE. The phrase
    # "folded into general_social_science" appears for BOTH Social Science and
    # Policy, so checking the bare phrase would still pass if only the Policy row
    # were deleted (Social Science's identical phrase survives). Require a single
    # line containing both "Policy" and the fold target. (hardening from a review round.)
    policy_fold = re.compile(
        r"Policy.*folded into\s*`?general_social_science`?", re.IGNORECASE
    )
    if not any(policy_fold.search(line) for line in t.splitlines()):
        f.append("C5: missing Policy→general_social_science fold (a single line binding 'Policy' to 'folded into general_social_science')")
    return f


def check_c6() -> list[str]:
    """R-5 leak guard: source_quality_hierarchy.md NOT modified by #259.

    INVARIANT 9 requires the deep-research file to stay substance-identical. A
    no-leaked-heading + heading-present check is too weak — editing the 6 table
    rows would pass. So we pin the `## Field-Specific Adjustments` block by
    SHA-256 against a baseline captured at plan time (the block is read-only for
    #259). If a legitimate, unrelated change to that block ever lands, the
    implementer updates EXPECTED_FSA_SHA256 in the same commit — making any edit
    a conscious, reviewed act rather than a silent #259 leak. The digest below is
    pinned to the current repo state; since #259 does not touch this file, a clean
    implementation matches it as-is (no implementer action needed unless the
    deep-research table legitimately changes for an unrelated reason).
    """
    import hashlib
    f: list[str] = []
    t = _read(SQH)
    if not t:
        return ["C6: source_quality_hierarchy.md not found"]
    if "## Domain Evidence Profiles" in t:
        f.append("C6: '## Domain Evidence Profiles' leaked into source_quality_hierarchy.md (R-5 violation)")
    block = _heading_range(t, "## Field-Specific Adjustments")
    if block is None:
        f.append("C6: source_quality_hierarchy.md '## Field-Specific Adjustments' block missing (was it edited?)")
        return f
    # Normalize trailing whitespace per line so a stray editor newline does not
    # false-fail, but any substantive row/cell change does.
    norm = "\n".join(ln.rstrip() for ln in block.strip().splitlines())
    digest = hashlib.sha256(norm.encode("utf-8")).hexdigest()
    # Pinned digest of the normalized Field-Specific Adjustments block as it
    # stands at plan time (#259 does NOT touch this file — INVARIANT 9 — so this
    # value is stable for a clean implementation). If a future, unrelated change
    # to deep-research's table is ever intentional, the implementer recomputes
    # and updates this constant IN THE SAME COMMIT — making the edit a conscious,
    # reviewed act rather than a silent #259 leak. Recompute with the same
    # _heading_range + per-line rstrip normalization used above.
    EXPECTED_FSA_SHA256 = "f7b38d39c5252c2d1ec931e563f32e40fce86a65d39fde5c590aa484b9686906"
    if digest != EXPECTED_FSA_SHA256:
        f.append(
            f"C6: Field-Specific Adjustments block changed (R-5 violation): "
            f"got {digest}, expected {EXPECTED_FSA_SHA256}. #259 must not edit "
            f"deep-research; if this change is intentional and unrelated, update "
            f"the pin in the same commit."
        )
    return f


def check_c7() -> list[str]:
    """Carrier-regression guard: within the Step 12 / Resolution heading ranges,
    the profile must NOT be carried by Schema 13 / selections[] / Material Passport.

    Per-OCCURRENCE negation filter (not per-line): the spec-compliant prose
    deliberately writes "NOT the Material Passport", "no selections[] ledger",
    "not a Schema number" to assert the carrier choice. A bare token scan would
    false-fail on that. But a per-LINE "any negation word anywhere" filter has a
    false-NEGATIVE hole: a real regression line like
    "Store on the Material Passport, do not use the PCR" contains both the
    affirmative carrier AND a (distant) negation, so a line-level filter would
    wrongly let it through. We instead require the negation to be CLOSE BEFORE the
    forbidden token (within ~30 chars, i.e. negating THAT carrier). An occurrence
    with no immediately-preceding negation trips the guard. So "NOT the Material
    Passport" passes (negation hugs the token) while "Store on the Material
    Passport, do not use the PCR" still fails (the negation is after, negating the
    PCR, not the carrier). Mutation fixture (g) inserts an affirmative line and
    must fail; the negation prose stays clean. Scoped to heading ranges so
    historical-contrast prose elsewhere in the file never reaches here.
    """
    f: list[str] = []
    forbidden = ("Schema 13", "selections[]", "Material Passport")
    # Negation immediately before the carrier token (<=30 chars). The window must
    # tolerate Markdown punctuation that legitimately sits between the negation
    # word and the (often backticked) carrier — e.g. "no `selections[]` ledger"
    # has a backtick between "no" and the token. Include backtick / asterisk /
    # parens so clean Markdown prose is not false-failed.
    #
    # "not only" / "not just" are AFFIRMATIVE, not negating: "Store not only on
    # the Material Passport but also in the PCR" affirms the carrier. The
    # negative lookahead `(?!\s+only|\s+just)` after the negation word rejects
    # those, so such a line is NOT exempted and still trips the guard. (hardening
    # from a review round.)
    neg_before = re.compile(
        r"\b(?:not(?!\s+only|\s+just)|no|never|n't)\b[\s\w,'\-`*()]{0,30}$",
        re.IGNORECASE,
    )
    for path, heading in ((INTAKE, INTAKE_STEP12_HEADING), (CONSUMER, CONSUMER_RESOLUTION_HEADING)):
        t = _read(path)
        block = _heading_range(t, heading)
        if block is None:
            f.append(f"C7: required heading '{heading}' not found in {path.name}")
            continue
        for line in block.splitlines():
            for token in forbidden:
                for m in re.finditer(re.escape(token), line):
                    pre = line[:m.start()]
                    if neg_before.search(pre):
                        continue  # this occurrence is explicitly negated -> allowed
                    f.append(
                        f"C7: affirmative forbidden-carrier '{token}' inside "
                        f"'{heading}' block ({path.name}): {line.strip()[:80]!r}"
                    )
    return f


def check_c8() -> list[str]:
    """Control-flow guard (#327 P1): the no-handoff interview directive's upper
    bound MUST cover Step 12 (Domain Evidence Profile producer).

    Unlike C1-C7 (documentation-surface presence), this check inspects a
    control-flow BOUND. The original directive
    `Execute the original Phase 0 full interview flow (Step 1-11).` bounded the
    most common full-mode entry (a fresh paper with no deep-research handoff) at
    Step 11, orphaning the Step-12 profile producer: an agent following it stops
    at Step 11, never writes the PCR `Domain Evidence Profile` row, and the
    consumer silently takes the `[NO-PROFILE-NEUTRAL]` fallback — the feature
    never activates on that path.

    Scope: only the `### When No Handoff Materials Are Detected` block, via the
    fence-aware `_heading_range` helper (so a `Step 1-11` mention in unrelated
    prose — e.g. plan-mode's "instead of the full 11" — never trips it). The
    requirement is that the block reaches Step 12; a directive that stops at
    Step 11 will not mention Step 12 and so fails.
    """
    f: list[str] = []
    t = _read(INTAKE)
    if not t:
        return ["C8: intake_agent.md not found"]
    block = _heading_range(t, INTAKE_NO_HANDOFF_HEADING)
    if block is None:
        return [f"C8: missing exact heading '{INTAKE_NO_HANDOFF_HEADING}'"]
    # Require a POSITIVE execution directive, not bare `Step 12` token presence:
    # a directive like "Execute (Step 1-11). Do not run Step 12 in this flow."
    # contains the token yet still orphans the producer. `then Step 12` is the
    # affirmative form the fix uses ("Step 1-11, then Step 12 per its own gating").
    if "then Step 12" not in block:
        f.append(
            "C8: no-handoff flow directive does not positively execute Step 12 — "
            "the Domain Evidence Profile producer (Step 12) is orphaned from the "
            "most common full-mode entry. The directive must affirmatively reach "
            "Step 12 (e.g. 'Step 1-11, then Step 12 per its own gating'), not "
            "merely mention the token."
        )
    return f


def check_c9() -> list[str]:
    """Reserved-fallback parse guard (#327 P2#2): the consumer must route a
    reserved-fallback row to its OWN advisory, not the malformed signal.

    Intake stores a reserved request as the display form
    `unknown_user_defined (requested: <reserved>)`. The original consumer had no
    parse step for that form, so it fell into case (c) (value not in the 4 enum)
    and emitted `[PROFILE-UNRESOLVED]` — the malformed/hallucinated signal — for a
    valid, acknowledged reserved request.

    C9 pins, within the resolution block, BOTH:
      (1) the distinct `[PROFILE-RESERVED-FALLBACK]` advisory tag exists, and
      (2) the block actually parses the `(requested: …)` parenthetical
          (otherwise the tag is unreachable and the row still routes to (c)).

    Division of labour with C3: C3 guards the three *original* consumer tags
    (NO-PROFILE-NEUTRAL / PROFILE-UNRESOLVED / PROFILE-DISCIPLINE-MISMATCH) and
    is deliberately NOT extended here, so each tag's mutation fixture isolates one
    check. C9 owns the fourth (reserved-fallback) tag + its parse semantics.
    """
    f: list[str] = []
    t = _read(CONSUMER)
    if not t:
        return ["C9: literature_strategist_agent.md not found"]
    block = _heading_range(t, CONSUMER_RESOLUTION_HEADING)
    if block is None:
        return [f"C9: missing exact heading '{CONSUMER_RESOLUTION_HEADING}'"]
    if "[PROFILE-RESERVED-FALLBACK]" not in block:
        f.append(
            "C9: resolution block missing the reserved-fallback advisory tag "
            "'[PROFILE-RESERVED-FALLBACK]' — a valid reserved request "
            "(`unknown_user_defined (requested: <reserved>)`) would collapse back "
            "into the [PROFILE-UNRESOLVED] malformed signal."
        )
    # Require BOTH the display form AND an explicit parse INSTRUCTION, not just
    # the suffix token: a block can carry `(requested: …)` only as a display
    # example while losing the "parse the parenthetical" instruction, leaving
    # reserved fallbacks to route back to the (c) malformed case. (Hardening from
    # codex review.) `parse`/`parsing` covers the instruction wording.
    if "(requested:" not in block:
        f.append(
            "C9: resolution block lacks the `(requested: …)` display form — the "
            "reserved-fallback path is unreachable, so the row routes to the (c) "
            "malformed case."
        )
    elif "parse" not in block.lower():
        f.append(
            "C9: resolution block shows the `(requested: …)` form but gives no "
            "parse INSTRUCTION (no 'parse'/'parsing' of the effective token + "
            "parenthetical) — without it the agent falls back to exact-string "
            "equality and the reserved fallback still routes to the (c) malformed "
            "case."
        )
    return f


def check_c10() -> list[str]:
    """Profile-aware currency gate (#327 P2#3): the screening decision tree's
    time-range (currency) node MUST consult the profile, and the "peer-review node
    only" fossil wording MUST be gone.

    `currency_window` is in PROFILE_LOOSENABLE and four prose passages say the
    year-range relaxes for humanities_interpretive canonical texts. But the
    time-range NODE in the decision tree had no profile branch, so a canonical
    humanities source admitted at the peer-review node was re-excluded at the
    time-range node (cited <= 100) — an INVARIANT 5 monotonic-admit violation. The
    prose under the tree also said the profile admits "at the peer-review node
    only", which encoded the bug and contradicted the four other passages.

    Scope: the `### Literature Screening Decision Tree` heading range (tree +
    its trailing prose), via `_heading_range`. Pins BOTH:
      (1) the currency node consults the profile (`currency rule` admit branch),
      (2) the `peer-review node only` fossil wording is absent.
    """
    f: list[str] = []
    t = _read(CONSUMER)
    if not t:
        return ["C10: literature_strategist_agent.md not found"]
    block = _heading_range(t, DECISION_TREE_HEADING)
    if block is None:
        return [f"C10: missing exact heading '{DECISION_TREE_HEADING}'"]
    # Pin the currency-node admit branch on its load-bearing semantic phrase, not
    # on a label. "recency is not a quality signal" lives ONLY inside the
    # humanities currency-node admit branch in this block; it disappears if the
    # branch is deleted and survives a label reword (e.g. "currency rule" ->
    # "recency rule"). Keying on a label would let a benign reword silently defeat
    # the guard while a broken edit that kept the label passed.
    if "recency is not a quality signal" not in block:
        f.append(
            "C10: decision-tree time-range node is not profile-aware — missing the "
            "humanities currency-node admit branch (its 'recency is not a quality "
            "signal' rationale). A canonical humanities source admitted at the "
            "peer-review node is re-excluded here (INVARIANT 5 violation)."
        )
    if "peer-review node only" in block:
        f.append(
            "C10: fossil wording 'peer-review node only' present — it encodes the "
            "#327 P2#3 bug (profile can't touch the currency node) and contradicts "
            "the four prose passages that relax currency for humanities. Name the "
            "PROFILE_LOOSENABLE nodes the profile actually admits at instead."
        )
    return f


CHECKS: list[tuple[str, Callable[[], list[str]]]] = [
    ("C1", check_c1), ("C2", check_c2), ("C3", check_c3), ("C4", check_c4),
    ("C5", check_c5), ("C6", check_c6), ("C7", check_c7), ("C8", check_c8),
    ("C9", check_c9), ("C10", check_c10),
]


def main() -> int:
    all_failures: list[str] = []
    for name, fn in CHECKS:
        try:
            all_failures.extend(fn())
        except Exception as exc:
            all_failures.append(f"{name}: check raised {type(exc).__name__}: {exc}")
    if all_failures:
        print("Domain evidence profile lint FAILED:", file=sys.stderr)
        for x in all_failures:
            print(f"  - {x}", file=sys.stderr)
        return 1
    print("Domain evidence profile lint OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
