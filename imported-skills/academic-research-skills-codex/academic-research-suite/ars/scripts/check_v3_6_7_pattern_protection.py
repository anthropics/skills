#!/usr/bin/env python3
"""Static audit for ARS v3.6.7 downstream-agent pattern protection.

Spec: docs/design/2026-04-29-ars-v3.6.7-downstream-agent-pattern-protection-spec.md

Greps the v3.6.7 reference files, audit template, and downstream agent prompts
for the keywords and obligation phrases that make each pattern-protection
clause detectable. Static only — does not validate runtime behaviour.
Behavioural validation belongs to spec §9 step 8 (live pipeline evaluation
case) and is out of scope here.

Falsifiability discipline (per feedback_lint_passes_but_prompt_silent.md):
- Agent-prompt checks scope grep to the `PATTERN PROTECTION (v3.6.7)` block
  via `block_marker`. A keyword that lands outside the block in unrelated
  prose does not count toward passing.
- Obligation-bearing patterns (forbidden / required / only-if) are enforced
  via `must_contain_regex` so the prohibition is grep-detectable as a
  contiguous fragment, not as two unrelated nouns elsewhere in the file.

Exit codes: 0 on pass, 1 on any failure.
"""

from __future__ import annotations

import os
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

REF_DIR = REPO_ROOT / "shared" / "references"
TPL_DIR = REPO_ROOT / "shared" / "templates"
AGENT_DIR = REPO_ROOT / "deep-research" / "agents"

SYNTHESIS_AGENT = AGENT_DIR / "synthesis_agent.md"
ARCHITECT_AGENT = AGENT_DIR / "research_architect_agent.md"
COMPILER_AGENT = AGENT_DIR / "report_compiler_agent.md"

# Markdown heading pattern that closes a `block_marker` scope. A check's scope
# starts at the marker and ends at the next H1/H2/H3 heading or EOF.
_HEADING_RE = re.compile(r"^#{1,3} ", re.MULTILINE)

# Negation / weakening patterns that, if present in the sentence containing
# an obligation match, indicate the obligation is being denied or weakened
# rather than asserted. R2-004 flagged "does not enumerate fully" / "not non-
# negotiable"; R3-002 expanded the list with should not / fails to / instead
# of / rarely / sometimes / is unable to. The patterns split into two groups:
#
# - _GENERAL_NEGATION_PATTERNS: DO NOT-style imperative prohibitions and
#   weakening modals. These reject most obligations BUT they would also
#   reject a legitimate prohibition like C3's "DO NOT simulate". For
#   prohibition-style obligations, callers pass `allow_prohibition=True` to
#   skip this group.
# - _ALWAYS_NEGATION_PATTERNS: weakening verbs and adverbs that never
#   constitute a valid prohibition signal (rarely / sometimes / fails to /
#   etc.). These apply regardless of `allow_prohibition`.
_GENERAL_NEGATION_PATTERNS = [
    # Subject + auxiliary negation that directly weakens an obligation.
    # These are the verb-negation forms most commonly used to undo a rule
    # ("X does not Y", "X must not Y"). They are excluded by default but
    # exempted for prohibition-style obligations like C3 via
    # `allow_prohibition`.
    re.compile(r"\bdoes not\b", re.IGNORECASE),
    re.compile(r"\bdo not\b", re.IGNORECASE),
    re.compile(r"\bDO NOT\b"),  # case-sensitive imperative form
    re.compile(r"\bdoesn'?t\b", re.IGNORECASE),
    re.compile(r"\bdon'?t\b", re.IGNORECASE),
    re.compile(r"\bshould not\b", re.IGNORECASE),
    re.compile(r"\bshouldn'?t\b", re.IGNORECASE),
    re.compile(r"\bmust not\b", re.IGNORECASE),
    re.compile(r"\bmustn'?t\b", re.IGNORECASE),
    # Adjective-targeted negations: explicit "not <obligation-adjective>"
    # forms that directly negate the contract vocabulary.
    re.compile(r"\bnot\s+(?:non[- ]negotiable|enumerate|required|mandatory|forbidden|verbatim|reserved)\b", re.IGNORECASE),
    re.compile(r"\bneed not\b", re.IGNORECASE),
    re.compile(r"\bno\s+buffer\b", re.IGNORECASE),
    re.compile(r"\bno\s+enumeration\b", re.IGNORECASE),
    # NOTE: `cannot` and `can't` are intentionally NOT in this list. They
    # are routinely used in benign conditional phrasing ("if X cannot fit,
    # the compiler reports..."), where `cannot` describes a trigger
    # condition rather than weakening an obligation. The other negation
    # patterns are tight enough to catch genuine weakening even without
    # `cannot`.
]
# Modal weakeners (`may`, `should`, `can`) downgrade mandatory obligations
# to advisory. They are scoped to a verb list so the bare token does not
# match unrelated prose ("you may want to see references/...", "this can
# be useful"). The verb list covers imperatives the v3.6.7 agent prompts
# actually use.
_MODAL_WEAKENED_VERBS = (
    r"(?:invite|enumerate|preserve|drop|skip|substitute|paraphrase"
    r"|wrap|include|default|defaults?|run|use|declare|pass(?:\s+through)?"
    r"|claim|cite|fall\s+back|be\s+quoted|be\s+permitted|use\s+chapter)"
)

_ALWAYS_NEGATION_PATTERNS = [
    re.compile(r"\bisn'?t\b", re.IGNORECASE),
    re.compile(r"\baren'?t\b", re.IGNORECASE),
    # `optional` only counts as a weakener when it directly modifies an
    # obligation noun. The bare token can appear in unrelated context
    # ("optional `approved_synonyms` field"), so we narrow this rule to
    # `optional <obligation-noun>` forms.
    re.compile(r"\boptional\s+(?:buffer|enumeration|preservation|inclusion|verbatim|hedge|hedges|enforcement|requirement|reservation)\b", re.IGNORECASE),
    # B2 R4-001: "X is recommended" / "are recommended" downgrades a
    # mandatory obligation to advisory. The narrowed verb list ensures
    # this only flags weakening of actual contract verbs / nouns.
    re.compile(
        r"\b(?:is|are)\s+recommended\b",
        re.IGNORECASE,
    ),
    # B2 R4-002 helper: "are allowed" / "is allowed" turns a forbidden
    # operation into an exception. Covers C2's mutated "deictic phrases
    # are allowed when shorter" and B5's "Over-setting ... are allowed"
    # when those structures slip past the per-rule regex.
    re.compile(r"\b(?:is|are)\s+allowed\b", re.IGNORECASE),
    # Modal/advisory weakener coverage for the obligation verb list.
    # B2 R4-001 added `may`; R5-001 added `should` / `can` /
    # `is/are permitted`; R6-001 added the future/conditional modals
    # (`will`, `would`, `ought to`) and the advisory adverb framings
    # (`ideally`, `preferably`, `We recommend that`).
    re.compile(rf"\bmay\s+(?:not\s+)?{_MODAL_WEAKENED_VERBS}\b", re.IGNORECASE),
    re.compile(rf"\bshould\s+(?:not\s+)?{_MODAL_WEAKENED_VERBS}\b", re.IGNORECASE),
    re.compile(rf"\bcan\s+(?:not\s+)?{_MODAL_WEAKENED_VERBS}\b", re.IGNORECASE),
    # B2 R6-001: future-tense `will` / `will not` directly contradicts a
    # mandatory obligation when paired with the obligation verb.
    re.compile(rf"\bwill\s+(?:not\s+)?{_MODAL_WEAKENED_VERBS}\b", re.IGNORECASE),
    # B2 R6-001: conditional `would` framings turn an imperative into a
    # hypothetical ("Compression would preserve" instead of "must preserve").
    re.compile(rf"\bwould\s+(?:not\s+)?{_MODAL_WEAKENED_VERBS}\b", re.IGNORECASE),
    # B2 R6-001: `ought to` is a modal-equivalent advisory.
    re.compile(rf"\bought\s+to\s+(?:not\s+)?{_MODAL_WEAKENED_VERBS}\b", re.IGNORECASE),
    # B2 R6-001: advisory adverb framings. "Ideally include X" or
    # "Preferably enumerate fully" downgrades the obligation. The verb
    # boundary is required so bare adverbs in unrelated context don't
    # trigger.
    re.compile(rf"\bideally\s+{_MODAL_WEAKENED_VERBS}\b", re.IGNORECASE),
    re.compile(rf"\bpreferably\s+{_MODAL_WEAKENED_VERBS}\b", re.IGNORECASE),
    # B2 R6-001: "We recommend that ..." reframing makes the obligation
    # advisory. Anchor on the recommend-that structure to avoid false
    # positives on legitimate references that just contain "recommend".
    re.compile(r"\bWe\s+recommend\s+that\b", re.IGNORECASE),
    # B2 R5-001: "is/are permitted" turns a forbidden operation into an
    # exception ("over-setting is permitted when concise"). Mirrors the
    # `is/are allowed` pattern.
    re.compile(r"\b(?:is|are)\s+permitted\b", re.IGNORECASE),
    re.compile(r"\bfails? to\b", re.IGNORECASE),
    re.compile(r"\binstead of\b", re.IGNORECASE),
    # `rarely` / `sometimes` / `occasionally` similarly need to be near
    # an obligation verb to count as weakeners.
    re.compile(r"\brarely\s+(?:enumerate|enforce|invoke|reserve|preserve|verify)", re.IGNORECASE),
    re.compile(r"\bsometimes\s+(?:enumerate|enforce|invoke|reserve|preserve|verify)", re.IGNORECASE),
    re.compile(r"\boccasionally\s+(?:enumerate|enforce|invoke|reserve|preserve|verify)", re.IGNORECASE),
    re.compile(r"\bis unable to\b", re.IGNORECASE),
    re.compile(r"\bare unable to\b", re.IGNORECASE),
    re.compile(r"\bonly when convenient\b", re.IGNORECASE),
    re.compile(r"\bif (?:space|time) (?:allows|permits)\b", re.IGNORECASE),
    # Feasibility qualifiers (R6-001). "when possible" / "where possible"
    # /etc. tail-attached to an obligation phrase silently downgrades it
    # from mandatory to best-effort.
    re.compile(r"\bwhen\s+possible\b", re.IGNORECASE),
    re.compile(r"\bwhere\s+possible\b", re.IGNORECASE),
    re.compile(r"\bwherever\s+feasible\b", re.IGNORECASE),
    re.compile(r"\bif\s+practical\b", re.IGNORECASE),
    re.compile(r"\bif\s+feasible\b", re.IGNORECASE),
    re.compile(r"\bbest[- ]effort\b", re.IGNORECASE),
    # Exception qualifiers (B2 R3-003). "except" / "unless" / "save when"
    # carve out a hole in an otherwise-mandatory rule. Mutation evidence:
    # "No subsetting except when concise" silently weakens B5. These are
    # treated as always-rejecting because no legitimate v3.6.7 contract
    # rule carries an opt-out clause; if a future spec rule needs a
    # genuine exception (e.g. "X is forbidden, except in mode Y"), the
    # check for that rule should structure the obligation regex to
    # demand both halves explicitly rather than relying on free prose.
    re.compile(r"\bexcept\s+(?:when|if|in|for|as|where)\b", re.IGNORECASE),
    re.compile(r"\bunless\b", re.IGNORECASE),
    re.compile(r"\bsave\s+when\b", re.IGNORECASE),
]


# Imperative/auxiliary verb-negation tokens that, when allow_prohibition is
# set, MAY appear in the matched obligation span but must still be rejected
# anywhere else in the bullet window. This is the "span-restricted exemption"
# (B2 R3-001): the obligation's own prohibition vocabulary ("DO NOT simulate",
# "must not claim audit-passed state", "does not paraphrase") rides verbatim
# in the matched span; a *second* prohibition elsewhere in the same bullet
# (e.g. trailing "this must not be enforced") still indicates weakening.
_PROHIBITION_VERB_PATTERN_TEXTS = {
    r"\bDO NOT\b",
    r"\bdo not\b",
    r"\bdoes not\b",
    r"\bdoesn'?t\b",
    r"\bdon'?t\b",
    r"\bmust not\b",
    r"\bmustn'?t\b",
}


def _match_excludes_negation(
    text_window: str,
    allow_prohibition: bool = False,
    matched_span: tuple[int, int] | None = None,
) -> bool:
    """Return True if the bullet window around an obligation match does NOT
    contain any negation that would weaken it.

    `allow_prohibition=True` exempts the literal prohibition tokens
    (DO NOT / do not / does not / must not / etc.) **only when they fall
    inside the matched obligation span**. A trailing "this must not be
    enforced" outside the matched span still rejects (B2 R3-001).

    The `_ALWAYS_NEGATION_PATTERNS` (rarely, sometimes, fails to, optional,
    except, unless, etc.) apply regardless because no legitimate obligation
    framing should rely on those.

    `matched_span` is `(start, end)` relative to `text_window`. When None
    or `allow_prohibition=False`, prohibition tokens anywhere in the
    window count as weakeners.
    """
    if any(p.search(text_window) for p in _ALWAYS_NEGATION_PATTERNS):
        return False
    for p in _GENERAL_NEGATION_PATTERNS:
        is_prohibition_pattern = p.pattern in _PROHIBITION_VERB_PATTERN_TEXTS
        for hit in p.finditer(text_window):
            if (
                allow_prohibition
                and is_prohibition_pattern
                and matched_span is not None
                and hit.start() >= matched_span[0]
                and hit.end() <= matched_span[1]
            ):
                # Prohibition token sits inside the matched obligation
                # span — it is the obligation's own vocabulary, not a
                # weakener. Skip this hit.
                continue
            return False
    return True


@dataclass
class Check:
    pattern_id: str
    description: str
    target: Path
    must_contain: list[str] = field(default_factory=list)
    must_contain_regex: list[tuple[str, str] | tuple[str, str, bool]] = field(default_factory=list)
    """Each entry is `(label, pattern)` or `(label, pattern, allow_prohibition)`.
    `allow_prohibition` is per-regex (not per-Check) so a check can mix
    prohibition-style obligations (REF-3 verbatim preservation, C3 anti-
    fake-audit guard, C3 audit-passed metadata) with assertion-style
    obligations (C1 protected hedges non-negotiable) without the
    prohibition exemption leaking across regexes (B2 codex R2-001)."""
    block_marker: str | None = None
    """If set, scope all keyword/regex checks to the text between the marker
    and the next H1/H2/H3 heading. Use for agent-prompt checks where the
    PATTERN PROTECTION clause must be inside its own block, not scattered
    elsewhere in the file."""

    def _scoped_text(self, full_text: str) -> tuple[str | None, str]:
        """Return (scoped_text, error_message). scoped_text is None on failure."""
        if self.block_marker is None:
            return full_text, ""
        marker_pos = full_text.lower().find(self.block_marker.lower())
        if marker_pos == -1:
            return None, f"block marker missing: {self.block_marker!r}"
        # Find next heading after the marker; scope ends there.
        rest = full_text[marker_pos:]
        match = _HEADING_RE.search(rest, pos=len(self.block_marker))
        scoped_end = marker_pos + (match.start() if match else len(rest))
        return full_text[marker_pos:scoped_end], ""

    def _display_path(self) -> str:
        try:
            return str(self.target.relative_to(REPO_ROOT))
        except ValueError:
            return str(self.target)

    def run(self) -> tuple[bool, str]:
        display = self._display_path()
        if not self.target.exists():
            return False, f"target file missing: {display}"
        full = self.target.read_text(encoding="utf-8")
        scoped, err = self._scoped_text(full)
        if scoped is None:
            return False, f"{display}: {err}"
        scoped_lower = scoped.lower()
        missing_substr = [s for s in self.must_contain if s.lower() not in scoped_lower]
        missing_regex = []
        for entry in self.must_contain_regex:
            if len(entry) == 2:
                label, pattern = entry
                allow_prohibition = False
            else:
                label, pattern, allow_prohibition = entry
            # First try to find an obligation match.
            match = re.search(pattern, scoped, re.IGNORECASE | re.DOTALL)
            if match is None:
                missing_regex.append(label)
                continue
            # Reject if the bullet/paragraph containing the match carries
            # a negation that weakens the obligation (per R2-004 + R3-001
            # + R4-001). The check looks backward from the match start to
            # the start of the current bullet (or paragraph start) and
            # forward from the match end to the next bullet (or blank line
            # / EOF). This catches trailing weakeners like
            # "...obligation. This is not required."
            iterator = re.finditer(pattern, scoped, re.IGNORECASE | re.DOTALL)
            accepted = False
            for m in iterator:
                start, end = m.start(), m.end()
                # Lookback to the start of this bullet/paragraph: previous
                # blank line, list-bullet marker on its own line, or start
                # of scoped text. Capped at 400 chars so very long bullets
                # do not pull in unrelated negation from far above.
                lookback_floor = max(0, start - 400)
                lookback = scoped[lookback_floor:start]
                blank_line = lookback.rfind("\n\n")
                bullet_back_match = list(re.finditer(r"\n\s*-\s", lookback))
                bullet_back = bullet_back_match[-1].start() if bullet_back_match else -1
                last_break_back = max(blank_line, bullet_back)
                bullet_start = (
                    lookback_floor + last_break_back + 1
                    if last_break_back >= 0
                    else lookback_floor
                )
                # Lookahead to the start of the next bullet, blank line,
                # or EOF (capped 400 chars).
                lookahead_ceiling = min(len(scoped), end + 400)
                lookahead = scoped[end:lookahead_ceiling]
                blank_fwd = lookahead.find("\n\n")
                bullet_fwd_match = re.search(r"\n\s*-\s", lookahead)
                bullet_fwd = bullet_fwd_match.start() if bullet_fwd_match else -1
                fwd_breaks = [i for i in (blank_fwd, bullet_fwd) if i >= 0]
                next_break = min(fwd_breaks) if fwd_breaks else -1
                bullet_end = end + next_break if next_break >= 0 else lookahead_ceiling
                window = scoped[bullet_start:bullet_end]
                # Span of THIS obligation match within the window, so the
                # negation filter can distinguish prohibition vocabulary
                # that is the obligation itself ("DO NOT simulate") from
                # a SECOND prohibition elsewhere in the bullet that
                # weakens it (B2 R3-001).
                match_in_window = (start - bullet_start, end - bullet_start)
                if _match_excludes_negation(
                    window,
                    allow_prohibition=allow_prohibition,
                    matched_span=match_in_window,
                ):
                    accepted = True
                    break
            if not accepted:
                missing_regex.append(f"{label} (only negated forms found)")
        problems = []
        if missing_substr:
            problems.append(f"missing keywords: {missing_substr}")
        if missing_regex:
            problems.append(f"missing obligation phrases: {missing_regex}")
        if problems:
            scope_note = f" within {self.block_marker!r} block" if self.block_marker else ""
            return False, f"{display}{scope_note}: {'; '.join(problems)}"
        return True, "OK"


def reference_file_checks() -> list[Check]:
    """Spec §7.1 — 4 reference files. No block scoping; whole-file grep."""
    return [
        Check(
            pattern_id="REF-1 (B1)",
            description="irb_terminology_glossary covers 4 IRB terms with operational distinctions",
            target=REF_DIR / "irb_terminology_glossary.md",
            must_contain=[
                "Anonymity",
                "Confidentiality",
                "De-identification",
                "Pseudonymization",
            ],
        ),
        Check(
            pattern_id="REF-2 (B2)",
            description="psychometric_terminology_glossary distinguishes true reverse-coded vs contrast",
            target=REF_DIR / "psychometric_terminology_glossary.md",
            must_contain=[
                "true reverse-coded",
                "contrast item",
                "acquiescence",
                "recall bias",
            ],
        ),
        Check(
            pattern_id="REF-3 (C1)",
            description="protected_hedging_phrases defines upstream-marked hedge protocol with 5 contract rules",
            target=REF_DIR / "protected_hedging_phrases.md",
            must_contain=[
                "protected hedging phrases",
                "upstream calibration",
                "word budget",
            ],
            must_contain_regex=[
                # Rule 1: conservative inclusion — "include the phrase" is
                # the operative directive (R5-002 mutation showed
                # "ask upstream for advice" was previously accepted).
                (
                    "Rule: Conservative inclusion",
                    r"\bConservative inclusion\b.{0,200}\bWhen in doubt\b.{0,150}\binclude\s+the\s+phrase\b",
                ),
                # Rule 2: anchor every entry — "where … and why" is the
                # specific obligation; bare "must cite" was previously
                # accepted with weakened content.
                (
                    "Rule: Anchor every entry (where + why)",
                    r"\bAnchor every entry\b.{0,200}\bmust\s+cite\s+where\b.{0,200}\bwhy\b",
                ),
                # Rule 3: no duplicates — bullet body must assert
                # "One entry per phrase" then back-reference the count.
                # R5-002 showed bare "One entry per phrase" alone could be
                # suffixed with "is optional" and still pass; require the
                # full "One entry per phrase. The compiler counts ... once"
                # sequence so a tail weakener cannot land between them.
                # Allow Markdown markup (`**`) between the heading word and
                # the body sentence.
                (
                    "Rule: No duplicates",
                    r"\bNo duplicates\b[\s.*\-]{0,10}One entry per phrase\.\s+The compiler counts[^.]{0,150}\bonce\b",
                ),
                # Rule 4: verbatim preservation — both the title and the
                # imperative body ("does not paraphrase") must appear. The
                # body uses "does not paraphrase / substitute" as the
                # prohibition expressing the obligation, so this specific
                # regex needs prohibition exemption (was per-Check before
                # B2 R2-001; now per-regex so other regexes in this Check
                # still reject inverted forms).
                (
                    "Rule: Verbatim preservation",
                    r"\bVerbatim preservation\b.{0,250}\brides\s+verbatim\b.{0,300}\bdoes\s+not\s+paraphrase\b",
                    True,  # allow_prohibition: prohibition-style obligation body
                ),
                # Rule 5: failure surface — must say "rather than dropping",
                # not "while dropping" (R5-002 mutation flipped this).
                (
                    "Rule: Conflict reporting (no silent drop)",
                    r"\breports the conflict\b[^.\n]{0,100}\brather than\s+dropping a protected hedge\b",
                ),
            ],
        ),
        Check(
            pattern_id="REF-4 (word-count)",
            description="word_count_conventions specifies whitespace-split + 3-5% buffer",
            target=REF_DIR / "word_count_conventions.md",
            must_contain=[
                "whitespace",
                "split()",
                "3–5%",
                "hyphenated",
            ],
        ),
    ]


def template_file_checks() -> list[Check]:
    """Spec §7.2 — audit prompt template."""
    return [
        Check(
            pattern_id="TPL-1 (D1)",
            description="codex_audit_multifile_template enumerates 7 audit dimensions",
            target=TPL_DIR / "codex_audit_multifile_template.md",
            must_contain=[
                "cross-ref",
                "hallucination",
                "primary-source integrity",
                "internal coherence",
                "instrument quality",
                "Round-N framing",
                "COI adequacy",
            ],
        ),
        # The report_compiler bundle's Section 4(f) is mandatory three-part:
        # (i) word-count cap-minus-buffer, (ii) protected-hedge verbatim,
        # (iii) abstract no less hedged than body. R1-006 upgraded this from
        # an example to a mandatory contract; lint must verify the contract
        # rides verbatim in the template, not just the prose around it.
        # Scoped to the `report_compiler_agent bundle` clause so scattered
        # text elsewhere in the template cannot satisfy the contract (R3-004).
        Check(
            pattern_id="TPL-2 (4f-compiler)",
            description="audit template encodes mandatory three-part (f) check for report_compiler bundles",
            target=TPL_DIR / "codex_audit_multifile_template.md",
            block_marker="report_compiler_agent bundle (mandatory three-part check)",
            must_contain_regex=[
                # Sub-check (i): whitespace-split cap minus 3-5% buffer
                (
                    "4f sub-check (i) word-count algorithm + buffer",
                    r"len\(body\.split\(\)\).{0,200}\b3[-–]5%\s+buffer\b",
                ),
                # Sub-check (ii): protected_hedges appear verbatim
                # unconditionally. R5-003 mutation showed bare
                # "appear verbatim when possible" was previously accepted;
                # the obligation must be unconditional ("appears verbatim
                # in the abstract" without "when possible" / "if space").
                # The negation post-filter already rejects "when convenient"
                # / "if space allows", so the regex requires the
                # imperative-tense phrasing.
                (
                    "4f sub-check (ii) protected_hedges verbatim (unconditional)",
                    r"every entry of upstream\s+`?protected_hedges`?[^\n]{0,200}\bappears? verbatim in the abstract\b",
                ),
                # Sub-check (iii): "no claim in the abstract is less hedged
                # than its anchor in the body" — anchored on "no claim" so
                # an inverted form ("every claim ... is less hedged") fails.
                (
                    "4f sub-check (iii) less-hedged-than-body prohibition",
                    r"\bno claim in the abstract is less hedged than its anchor in the body\b",
                ),
                # P1 severity assignment for any sub-check failure
                (
                    "4f failures severity P1",
                    r"\bFailure of any sub-check is a P1 finding\b",
                ),
            ],
        ),
    ]


# Block marker every agent-prompt check scopes to. Defined once so the value
# stays in sync across agents.
PROTECTION_BLOCK = "PATTERN PROTECTION (v3.6.7)"


def synthesis_agent_checks() -> list[Check]:
    """Spec §6.1 — synthesis_agent A1-A5 protection.

    Scoped to the PATTERN PROTECTION (v3.6.7) block so keyword presence
    elsewhere in the agent prompt does not count toward passing. All five
    rules use must_contain_regex (not raw must_contain tokens) so the
    weakening filter rejects mutations like "pending verification language
    is optional" (B2 R3-002).
    """
    return [
        Check(
            pattern_id="A1-A5",
            description="synthesis_agent carries 5 narrative-side protection clauses",
            target=SYNTHESIS_AGENT,
            block_marker=PROTECTION_BLOCK,
            must_contain_regex=[
                # A1 — cross-section consistency self-check. Bullet must
                # carry both the imperative pre-list step and the
                # consistency self-check before output. "are recommended"
                # / "may run" / "optional" weakeners are caught by the
                # negation filter (verb list + `is/are recommended` in
                # _ALWAYS_NEGATION_PATTERNS, B2 R4-001 expansion).
                (
                    "A1 effect inventory pre-list + cross-section self-check before output",
                    r"\bpre-list\b[^.\n]{0,200}\beffect inventory\b[^.\n]{0,200}\brun\s+a\s+cross-section consistency self-check\b[^.\n]{0,100}\bbefore output\b",
                ),
                # A2 — pending-verification hedge. "wrap claims in explicit
                # hedge" is the imperative; mutating to "may wrap" or
                # "pending verification language is optional" trips the
                # may-verb weakener (R4-001) and the optional-noun weakener
                # respectively.
                (
                    "A2 pending-verification hedge wrap",
                    r"\bpending verification\b[^.\n]{0,200}\bwrap claims\b[^.\n]{0,200}\bexplicit hedge\b",
                ),
                # A3 — anchor justification. "include a one-line anchor
                # justification" is the imperative; "may include" trips
                # the may-verb weakener (R4-001).
                (
                    "A3 one-line anchor justification (include)",
                    r"\binclude\s+a\s+one[- ]line\s+anchor justification\b",
                ),
                # A4 — quote scope boundary AND surrounding-context handling.
                # Spec §6.1 says "surrounding context paraphrased and
                # unquoted". Without enforcing the second clause, an agent
                # can satisfy "Verbatim quotes only within ..." while
                # mutating context handling to "may be quoted" (R4-002).
                # Two regexes so dropping either half fails lint.
                (
                    "A4 verbatim quotes only within verified phrase boundary",
                    r"\bVerbatim quotes\s+only\s+within\s+the\s+verified phrase boundary\b",
                ),
                (
                    "A4 surrounding context paraphrased and unquoted",
                    r"\bsurrounding context\s+paraphrased\s+and\s+unquoted\b",
                ),
                # A5 — declarative claims about un-provided documents are
                # forbidden AND the conditional-language fallback is
                # required. Spec §6.1 pairs the two: conditional language
                # / explicit gap acknowledgment is the constructive duty,
                # the prohibition is the negative duty. Both must ride.
                (
                    "A5 conditional language fallback for un-provided documents",
                    # Bullet contains "e.g., ..." parenthetical, so match
                    # across periods within the bullet line.
                    r"\bun-provided[^\n]{0,300}\buse\s+conditional language\b[^\n]{0,300}\bexplicit gap acknowledgment\b",
                ),
                (
                    "A5 sentence-bounded injunction",
                    r"declarative claims? about un-provided[^.\n]{0,200}\bare forbidden\b",
                ),
            ],
        )
    ]


def architect_agent_checks() -> list[Check]:
    """Spec §6.2 — research_architect_agent (survey designer mode) B1-B5
    protection. B1, B2, B5 use must_contain_regex with imperative verbs
    anchored so a mutation like "passing through the IRB glossary is
    optional" or "construct equivalence justification is recommended"
    is rejected by the weakening filter (B2 R3-002).
    """
    return [
        Check(
            pattern_id="B1-B5",
            description="research_architect_agent (survey designer) carries 5 instrument-side protection clauses",
            target=ARCHITECT_AGENT,
            block_marker=PROTECTION_BLOCK,
            must_contain_regex=[
                # B1 — IRB terminology pass-through. "must pass through ...
                # before output" is the imperative; the glossary back-pointer
                # is part of the obligation.
                (
                    "B1 IRB terminology pass-through (must, before output)",
                    r"\bmust\s+pass\s+through\b[^.\n]{0,200}\birb_terminology_glossary\.md\b[^.\n]{0,200}\bbefore output\b",
                ),
                # B2 — reverse-coded construct equivalence. "include a one-
                # line construct-equivalence justification" is the imperative
                # that survives mutations like "construct-equivalence
                # justification is recommended".
                (
                    "B2 reverse-coded construct-equivalence justification",
                    r"\breverse-coded\b[^.\n]{0,200}\binclude\s+a\s+one[- ]line\s+construct-equivalence justification\b",
                ),
                # B3 — retrospective items default to event-anchored;
                # calendar-anchored is conditional on a shared event date.
                # Spec wording naturally spans two sentences ("default to..."
                # then "calendar... only when..."), so the gap allows one
                # sentence boundary; the 'only when' tail must sit in the
                # same sentence as 'calendar-anchored' to bind the conditional.
                (
                    "B3 retrospective default + calendar conditional",
                    r"event-anchored[^.\n]{0,200}\.[^.\n]{0,100}\bcalendar[- ]anchored[^.\n]{0,200}\bonly when\b",
                ),
                # B4 — three-part obligation per spec §6.2:
                #   (i) item phrasing must be neutral/balanced,
                #   (ii) chapter argument vocabulary forbidden in items,
                #   (iii) open-text prompts invite all valences.
                # Splitting into three regexes so dropping any one half
                # fails lint (R4-002 mutation evidence: "may use chapter
                # argument vocabulary" replaced (i)+(ii) and bare valences
                # match still passed).
                (
                    "B4 item phrasing neutral/balanced (must)",
                    r"\bItem phrasing\s+must\s+be\s+neutral[/-]balanced\b",
                ),
                (
                    "B4 chapter argument vocabulary forbidden",
                    r"\bChapter argument vocabulary\s+is\s+forbidden\s+in\s+instrument items\b",
                ),
                (
                    "B4 open-text invites all valences",
                    r"\b(?:all valences|positive,? negative,? (?:or|and) neutral)\b",
                ),
                # B5 — option lists must declare primary-source list AND
                # enumerate fully AND prohibit subsetting AND prohibit
                # over-setting AND prohibit scope cross-contamination.
                # All five are the contract per spec §6.2; matching any
                # subset is a silent gap (R4-002 mutation: "Over-setting
                # and scope cross-contamination are allowed" passed even
                # though "No subsetting" remained).
                (
                    "B5 primary-source list + enumerate fully",
                    r"\bprimary-source list\b[^.\n]{0,100}\benumerate(?:s|d)?\s+fully\b",
                ),
                (
                    "B5 no subsetting prohibition",
                    r"\bno\s+subsetting\b",
                ),
                (
                    "B5 no over-setting prohibition",
                    r"\bno\s+over-setting\b",
                ),
                (
                    "B5 no scope cross-contamination prohibition",
                    r"\bno\s+scope cross-contamination\b",
                ),
            ],
        )
    ]


def compiler_agent_checks() -> list[Check]:
    """Spec §6.3 — report_compiler_agent (abstract-only mode) C1-C3 protection."""
    return [
        Check(
            pattern_id="C1-C3",
            description="report_compiler_agent (abstract-only) carries 3 publication-side protection clauses incl. anti-fake-audit guard",
            target=COMPILER_AGENT,
            block_marker=PROTECTION_BLOCK,
            must_contain_regex=[
                # C1 word-count algorithm + buffer. Spec §6.3 pairs the
                # whitespace-split rule with "Reserve 3–5% buffer below
                # hard cap"; both must ride. R4-002 mutation showed
                # buffer deletion still passed.
                (
                    "C1 whitespace-split convention (uses)",
                    r"\bWord budget\s+uses\s+whitespace-split\s+convention\b",
                ),
                (
                    "C1 reserve 3-5% buffer below hard cap",
                    r"\bReserve\s+3[-–]5%\s+buffer\s+below\s+hard cap\b",
                ),
                # C2 temporal disambiguation: imperative + full triple of
                # acceptable forms (year range, past-tense disambiguating
                # verb, "former" prefix). R4-002 evidence: dropping the
                # past-tense + former prefix still passed because only
                # "explicit year range" was lint-required.
                (
                    "C2 reflexivity disclosure must use explicit year range",
                    r"\bReflexivity disclosure\s+must\s+use\s+explicit temporal bounds\b[^.\n]{0,200}\bexplicit year range\b",
                ),
                (
                    "C2 past-tense disambiguating verb form",
                    r"\bpast-tense disambiguating verb\b",
                ),
                (
                    "C2 'former' prefix form",
                    r"['\"]former['\"]\s+prefix\b",
                ),
                # C2 deictic forbidden — paired with above so a mutation
                # that drops the prohibition still fails.
                (
                    "C2 deictic temporal phrases forbidden",
                    r"\bDeictic temporal phrases\b[^.\n]{0,200}\bare forbidden\b",
                ),
                # C1 — protected hedges are budget-protected / non-negotiable
                # / verbatim. Sentence-bounded; negation post-filter rejects
                # "are not non-negotiable" (R2-004) AND must reject inverted
                # "Compression must not preserve protected hedging phrases"
                # (B2 R2-001), so this regex does NOT take prohibition
                # exemption — it is an assertion-style obligation.
                (
                    "C1 protected hedges non-negotiable",
                    r"protected\s+hedg(?:e|ing)\s+phrases[^.\n]{0,200}\b(?:budget[- ]protected|non-negotiable|verbatim)\b",
                ),
                # C3 — canonical Clause 1 line per Step 6 §6.2. The line is
                # one bullet carrying three prohibitions in fixed order:
                # "DO NOT simulate any audit step. DO NOT claim to have run
                # codex/external review. Output metadata must not claim
                # audit-passed state." Phase 6.7 merged the prior two C3
                # regexes (anti-fake-audit pair + output-metadata) into a
                # single line so the bullet is whole-line verbatim — INV-1
                # below enforces presence/uniqueness across all three
                # in-scope prompts; this regex stays here to keep C1-C3
                # mutation coverage intact (R2-001 inverted-must-not, R3-001
                # trailing weakener, R4-001 advisory framing). Pattern is
                # whole-line so all three prohibition tokens (DO NOT × 2 +
                # must not) sit inside the matched span and the negation
                # post-filter does not flag a sibling prohibition as a
                # weakener (B2 R3-001 span-restricted exemption).
                (
                    "C3 canonical Clause 1 line (whole-line verbatim)",
                    # Whitespace-tolerant: every inter-token space inside
                    # the canonical line accepts `\s+` so a Markdown
                    # soft-wrap anywhere inside a sentence (e.g. between
                    # `run` and `codex/external`) is treated as the
                    # same canonical bullet — matches INV-1's
                    # whitespace-normalization contract (codex R5 P2
                    # closure). The trailing `\.(?=\s|\Z)` anchor still
                    # rejects tail weakeners like ` if feasible.` (R1
                    # P2 closure).
                    r"\bDO\s+NOT\s+simulate\s+any\s+audit\s+step\.\s+"
                    r"DO\s+NOT\s+claim\s+to\s+have\s+run\s+codex/external\s+review\.\s+"
                    r"Output\s+metadata\s+must\s+not\s+claim\s+audit-passed\s+state\.(?=\s|\Z)",
                    True,  # allow_prohibition: this IS the prohibition
                ),
            ],
        )
    ]


# ---------------------------------------------------------------------------
# Inversion sweep checks (Phase 6.7 — spec §6 partial inversion rule)
# ---------------------------------------------------------------------------
#
# Spec §6.3 defines INV-1/INV-2/INV-3 as the lint enforcement of the
# §6.2 sweep. These run alongside the keyword/regex Check pipeline above
# but operate at file-list granularity (manifest-driven) rather than
# per-Check, so they are implemented as standalone functions returning
# (pattern_id, description, ok, message) tuples.
#
# - INV-1: each manifest file's PATTERN PROTECTION block carries the
#   canonical Clause 1 line exactly once (presence + uniqueness).
# - INV-2: each manifest file's PATTERN PROTECTION block contains zero
#   sentences matching any of the four Clause 2 violation patterns.
# - INV-3: no agent prompt file outside the manifest carries the canonical
#   Clause 1 line (defends against accidental sweep widening per §9 L2).

INVERSION_MANIFEST = REPO_ROOT / "scripts" / "v3_6_7_inversion_manifest.json"

# Canonical Clause 1 line, byte-aligned with spec §6.2 line 1767. Whitespace
# inside is tolerant (collapse whitespace runs to a single space) so a future
# Markdown reflow that wraps the bullet across two lines does not break the
# match; presence is what matters.
CANONICAL_CLAUSE_1_TEXT = (
    "DO NOT simulate any audit step. "
    "DO NOT claim to have run codex/external review. "
    "Output metadata must not claim audit-passed state."
)

# Spec §6.3 INV-2 regex set (a)-(d). Patterns are written as Python regex
# literals here (`|` for alternation, no Markdown escaping) — the spec
# table renders them as `\|` because raw `|` is the Markdown table-column
# delimiter; the lint reads the underlying regex, not the rendered cell.
# All four compile with re.IGNORECASE only — DOTALL is not needed because
# patterns are applied to bullet text after whitespace normalization
# (newlines collapsed to single spaces), which preserves Markdown
# soft-wrap tolerance (codex R1 P2 closure) while bounding the `.*`
# wildcard to a single bullet (codex R2 P2 closure: prior IGNORECASE |
# DOTALL applied to raw block text let INV-2(a)/(b) match across
# unrelated bullets).
INV2_PATTERNS = [
    ("INV-2(a)", re.compile(r"\bthe orchestrator\b.*\baudit\b", re.IGNORECASE)),
    (
        "INV-2(b)",
        re.compile(
            r"\bcross-model audit (?:follows|covers)\b.*codex_audit_multifile_template",
            re.IGNORECASE,
        ),
    ),
    (
        "INV-2(c)",
        re.compile(
            r"\baudit (?:afterwards?|will be run|is dispatched)\b",
            re.IGNORECASE,
        ),
    ),
    (
        "INV-2(d)",
        re.compile(
            r"\bdownstream audit\b|\bthis output (?:is|will be) audited\b",
            re.IGNORECASE,
        ),
    ),
]

# Frozen v3.6.7 manifest contents per spec §6.3. The manifest file at
# scripts/v3_6_7_inversion_manifest.json is the data; this constant is
# the schema's expected value, used by `_load_inversion_manifest` to
# refuse drifted manifests at lint time. Spec §6.3 line 1807 reserves
# manifest widening for explicit v3.6.8+ work that lands "its own
# version-tagged manifest rather than retroactively widening v3.6.7's";
# this constant locks the v3.6.7 scope so a copy-paste widening
# (codex R1 P2 closure: add fourth file + canonical bullet → INV-1
# passes for all 4, INV-3 skips the new file because it is in
# manifest_set, full pass) can no longer slip past lint.
EXPECTED_MANIFEST_FILES = (
    "deep-research/agents/synthesis_agent.md",
    "deep-research/agents/research_architect_agent.md",
    "deep-research/agents/report_compiler_agent.md",
)


def _load_inversion_manifest() -> tuple[list[str], str | None]:
    """Return (file_list, error_message). file_list paths are repo-relative.

    Validates that the manifest carries exactly the three v3.6.7-scoped
    file paths (per spec §6.3 + EXPECTED_MANIFEST_FILES). Drift, addition,
    deletion, or duplication of entries is rejected — widening to a
    fourth file requires landing a v3.6.8+ manifest with its own scope
    tag, not retroactive edits to this manifest (per spec §6.3 line
    1807).
    """
    if not INVERSION_MANIFEST.exists():
        return [], f"manifest missing: scripts/v3_6_7_inversion_manifest.json"
    try:
        import json
        data = json.loads(INVERSION_MANIFEST.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as exc:
        return [], f"manifest unreadable: {exc}"
    if data.get("scope") != "v3.6.7-only":
        return [], f"manifest 'scope' must be 'v3.6.7-only', got {data.get('scope')!r}"
    files = data.get("files")
    if not isinstance(files, list) or not all(isinstance(p, str) for p in files):
        return [], "manifest 'files' must be a list of strings"
    if len(files) != len(set(files)):
        dupes = sorted({p for p in files if files.count(p) > 1})
        return [], f"manifest 'files' contains duplicate entries: {dupes}"
    if set(files) != set(EXPECTED_MANIFEST_FILES):
        expected = sorted(EXPECTED_MANIFEST_FILES)
        actual = sorted(files)
        return [], (
            f"manifest 'files' must match the v3.6.7 frozen scope. "
            f"Expected (sorted): {expected}. Got (sorted): {actual}. "
            f"To widen scope to additional agents, land a v3.6.8+ "
            f"manifest with its own scope tag per spec §6.3 line 1807; "
            f"do not edit v3.6.7's manifest retroactively."
        )
    return files, None


def _extract_block(text: str, marker: str) -> str | None:
    """Return PATTERN PROTECTION block text, or None if marker missing."""
    pos = text.lower().find(marker.lower())
    if pos == -1:
        return None
    rest = text[pos:]
    match = _HEADING_RE.search(rest, pos=len(marker))
    end = match.start() if match else len(rest)
    return rest[:end]


# Bullet line — Markdown list item starting with `- ` at the start of a
# line, optionally indented. Captures the bullet text including any
# soft-wrapped continuation lines (lines indented more than the bullet
# itself, by Markdown convention typically two spaces). Bullet text ends
# at the next bullet, blank line, or block boundary.
_BULLET_START_RE = re.compile(r"^(\s*)-\s+", re.MULTILINE)


def _iter_bullets(block: str) -> list[tuple[int, str]]:
    """Walk a PATTERN PROTECTION block and yield (line_offset, bullet_text)
    pairs where bullet_text is the bullet's content (without the leading
    `- ` marker) with all whitespace runs (including newlines from soft
    wraps) collapsed to a single space.

    Bullet boundaries: each bullet runs from its `- ` marker to the next
    bullet, blank line (`\\n\\n`), or end of block. This makes INV-1
    (canonical-line-as-bullet) and INV-2 (no-Clause-2-disclosure) operate
    at bullet granularity, which is what the spec §6.3 means by "exactly
    one bullet whose text matches the canonical Clause 1 line verbatim".

    `line_offset` is the 0-indexed character position of the bullet's
    `-` marker inside `block` (used to compute file-line diagnostics).
    """
    starts = list(_BULLET_START_RE.finditer(block))
    bullets: list[tuple[int, str]] = []
    for i, m in enumerate(starts):
        bullet_start = m.start()
        content_start = m.end()
        if i + 1 < len(starts):
            bullet_end = starts[i + 1].start()
        else:
            bullet_end = len(block)
        # Trim at the first blank line within the bullet — a blank line
        # ends the bullet even if no further `- ` appears in the block.
        candidate = block[content_start:bullet_end]
        blank = candidate.find("\n\n")
        if blank >= 0:
            candidate = candidate[:blank]
        normalized = " ".join(candidate.split())
        bullets.append((bullet_start, normalized))
    return bullets


# Audit-specific fragment markers — load-bearing pieces of the canonical
# Clause 1 sentence that uniquely tie a bullet to the v3.6.7 audit
# prohibition (not generic anti-fabrication guidance). Any one of these
# is sufficient to classify a bullet as Clause 1-like.
_CLAUSE_1_AUDIT_FRAGMENTS = (
    "audit step",
    "audit-passed state",
    "codex/external review",
)

# Generic prohibition fragments that, ALONE, are common anti-fabrication
# language and DO NOT imply the v3.6.7 audit prohibition (codex R8 P2:
# `- Do not simulate data or sources.` is legitimate non-audit
# guidance). A bullet carrying one of these must ALSO carry an
# audit-specific fragment to be classified as Clause 1-like.
_CLAUSE_1_GENERIC_FRAGMENTS = (
    "do not simulate",
    "do not claim to have run",
)


def _is_clause_1_like(bullet_text: str) -> bool:
    """True if bullet_text reads as a (possibly weakened) variant of
    the canonical Clause 1 line.

    A bullet is flagged Clause 1-like iff it carries at least one
    audit-specific fragment (audit step / audit-passed state /
    codex/external review). Generic prohibition fragments (`do not
    simulate`, `do not claim to have run`) alone are insufficient —
    they appear in legitimate non-audit anti-fabrication guidance.
    Codex R8 P2 closure: tighten so non-manifest prompts can carry
    `- Do not simulate data or sources.` without tripping INV-3."""
    lowered = bullet_text.lower()
    return any(frag in lowered for frag in _CLAUSE_1_AUDIT_FRAGMENTS)


def _inv1_check_file(rel_path: str) -> tuple[bool, str]:
    """INV-1: canonical Clause 1 line appears as exactly one bullet in
    the PATTERN PROTECTION block, AND no other Clause 1-like bullet
    exists. The bullet's whitespace-normalized text MUST equal the
    canonical Clause 1 text byte-for-byte; prefix weakeners (`When
    feasible, DO NOT simulate ...`), tail weakeners (`... audit-passed
    state if feasible.`), or any near-canonical duplicate all fail.
    Returns (ok, message).

    Codex R2 P2 closure (substring match → bullet-extract + exact
    compare); R6 P2 closure (weakened-duplicate bypass — keep canonical
    bullet, add `- When feasible, DO NOT simulate ...` second bullet,
    exact-count stays 1 and lint passed). The R6 closure flags every
    Clause 1-like bullet via _CLAUSE_1_LIKE_FRAGMENTS and demands each
    one is byte-exact canonical."""
    target = REPO_ROOT / rel_path
    if not target.exists():
        return False, f"file missing: {rel_path}"
    block = _extract_block(target.read_text(encoding="utf-8"), PROTECTION_BLOCK)
    if block is None:
        return False, (
            f"{rel_path}: PATTERN PROTECTION block missing "
            f"(marker {PROTECTION_BLOCK!r} not found)"
        )
    bullets = list(_iter_bullets(block))
    exact = [t for _o, t in bullets if t == CANONICAL_CLAUSE_1_TEXT]
    weakened = [
        t for _o, t in bullets
        if _is_clause_1_like(t) and t != CANONICAL_CLAUSE_1_TEXT
    ]
    if weakened:
        return False, (
            f"{rel_path}: PATTERN PROTECTION block contains "
            f"{len(weakened)} Clause 1-like bullet(s) that do not "
            f"match the canonical text byte-for-byte. Each must equal "
            f"the canonical wording verbatim or be removed. Offending "
            f"bullet(s): {weakened!r}. Expected canonical wording: "
            f"{CANONICAL_CLAUSE_1_TEXT!r}"
        )
    if len(exact) != 1:
        return False, (
            f"{rel_path}: PATTERN PROTECTION block has {len(exact)} "
            f"bullet(s) whose normalized text equals the canonical "
            f"Clause 1 line; expected exactly 1. Expected wording: "
            f"{CANONICAL_CLAUSE_1_TEXT!r}"
        )
    return True, "OK"


def _iter_block_segments(block: str) -> list[tuple[int, str, str]]:
    """Yield (offset, kind, normalized_text) tuples for every
    matched-content segment inside a PATTERN PROTECTION block. `kind`
    is `"bullet"` for `^- ` list items or `"prose"` for non-bullet
    paragraphs (intro paragraph, paragraphs interleaved between bullet
    runs, paragraphs appended after the last bullet — anywhere in the
    block).

    Whitespace-normalised so soft-wrapped Markdown lines collapse into
    single-space sentences. Codex R3 + R4 P2 closures: scanning must
    cover ALL prose in the block, not just the intro paragraph (R3) or
    just the pre-first-bullet region (R4). The spec §6.2 sweep promises
    "zero Clause 2 violation in PATTERN PROTECTION block"; carving out
    any sub-region (post-bullet trailers, between-bullet inserts) gives
    a regression vector.

    Algorithm: paragraph-split the block on blank lines. Each paragraph
    starting with `- ` is treated as a bullet group and walked via
    `_iter_bullets`; each non-bullet paragraph (excluding the section
    heading) is reported as `"prose"`. This handles bullets-then-prose,
    prose-then-bullets, and mixed orderings uniformly.
    """
    segments: list[tuple[int, str, str]] = []
    cursor = 0
    paragraphs = re.split(r"\n\s*\n", block)
    for paragraph in paragraphs:
        offset = block.find(paragraph, cursor)
        if offset < 0:
            offset = cursor
        # Advance the cursor past this paragraph and its trailing
        # blank-line separator (`\n\n`) for the next find().
        cursor = offset + len(paragraph) + 2
        stripped = paragraph.strip()
        if not stripped:
            continue
        # The block heading line (`## PATTERN PROTECTION (v3.6.7)`)
        # is content marker, not contract content.
        if stripped.startswith("## "):
            continue
        if stripped.startswith("- "):
            # Bullet group — may be a single bullet or a wrapped multi-
            # line bullet; delegate to `_iter_bullets` which knows how
            # to walk `- ` markers and collapse soft wraps.
            for bullet_local_offset, bullet_text in _iter_bullets(paragraph):
                segments.append((offset + bullet_local_offset, "bullet", bullet_text))
        else:
            normalized = " ".join(stripped.split())
            segments.append((offset, "prose", normalized))
    return segments


def _inv2_check_file(rel_path: str) -> tuple[bool, list[str]]:
    """INV-2: zero Clause 2 violation hits across the four regex
    patterns (a)-(d), evaluated per segment (intro prose paragraphs +
    bullets, both whitespace-normalized). Returns (ok, error_messages).

    Per-segment evaluation closes codex R2 P2 (cross-bullet `.*`
    over-reach) AND codex R3 P2 (intro-paragraph regression): each
    pattern runs against a single bullet OR a single prose paragraph,
    never spanning unrelated text. Soft-wrap tolerance is preserved by
    pre-normalizing each segment's whitespace."""
    target = REPO_ROOT / rel_path
    if not target.exists():
        return False, [f"file missing: {rel_path}"]
    full = target.read_text(encoding="utf-8")
    block = _extract_block(full, PROTECTION_BLOCK)
    if block is None:
        return False, [
            f"{rel_path}: PATTERN PROTECTION block missing "
            f"(marker {PROTECTION_BLOCK!r} not found)"
        ]
    errors: list[str] = []
    block_offset = full.find(block)
    for segment_offset, kind, normalized in _iter_block_segments(block):
        # Skip the canonical Clause 1 bullet — it inherently contains
        # "audit step" / "audit-passed state" tokens but is the
        # required prohibition, not a disclosure.
        if kind == "bullet" and normalized == CANONICAL_CLAUSE_1_TEXT:
            continue
        for label, pat in INV2_PATTERNS:
            m = pat.search(normalized)
            if m is None:
                continue
            absolute_pos = (block_offset + segment_offset) if block_offset >= 0 else segment_offset
            line_no = full.count("\n", 0, absolute_pos) + 1
            errors.append(
                f"{rel_path}:{line_no}: {label} Clause 2 violation in {kind}: "
                f"{normalized!r}. Sentence must be removed per "
                f"docs/design/2026-04-30-ars-v3.6.7-step-6-orchestrator-hooks-spec.md §6.2."
            )
            # One label per segment is enough; further labels on the
            # same segment would be redundant.
            break
    return (len(errors) == 0), errors


# Directories scanned by INV-3. Spec §6.3 limits scope to agent prompt
# files under deep-research/agents/ and academic-pipeline/agents/. docs/,
# scripts/, and tests/ are excluded — the canonical line legitimately
# appears in the spec, the manifest checker, and test fixtures, and
# scanning those would self-fail.
INV3_SCAN_DIRS = [
    REPO_ROOT / "deep-research" / "agents",
    REPO_ROOT / "academic-pipeline" / "agents",
]


def _inv3_check(manifest_files: list[str]) -> tuple[bool, list[str]]:
    """INV-3: the EXACT canonical Clause 1 line MUST NOT appear in any
    agent prompt outside the manifest. Detects:
      (a) Bullets whose whitespace-normalized text equals
          `CANONICAL_CLAUSE_1_TEXT` byte-for-byte.
      (b) Prose runs whose whitespace-normalized text equals
          `CANONICAL_CLAUSE_1_TEXT` byte-for-byte. Prose runs are
          identified by sliding a 3-sentence window across non-bullet
          text after stripping `^#` heading lines.
    Returns (ok, error_messages).

    Codex R9 P2 closures (architectural rewind on R7+R8 over-extension):
    - The Clause 1-like heuristic is a manifest-internal weakened-
      duplicate guard (INV-1), NOT a manifest-external detector.
      Applied to non-manifest agents, it false-positives any bullet
      mentioning `audit step` for unrelated reasons (e.g. process-
      flow guidance like `- Review each audit step before
      finalizing.`). Spec §6.3 INV-3 wording says "canonical Clause 1
      line found outside the manifest" — that means the actual
      sentence, not a Clause 1-like variant. Variants outside the
      manifest are a separate concern that v3.6.7 does not lint.
    - Prose detection no longer relies on `re.split(r"\\n\\s*\\n", ...)`
      paragraphs (which mis-handle a heading immediately followed by
      the canonical sentence with no blank line). Use line-level
      heading-strip + whitespace-collapse + a 3-sentence sliding
      window so the canonical sentence is detectable regardless of
      surrounding Markdown structure.
    """
    manifest_set = {str(REPO_ROOT / p) for p in manifest_files}
    errors: list[str] = []
    for d in INV3_SCAN_DIRS:
        if not d.is_dir():
            continue
        for path in sorted(d.glob("*.md")):
            if str(path) in manifest_set:
                continue
            text = path.read_text(encoding="utf-8")
            offending_bullets = [
                bt
                for _o, bt in _iter_bullets(text)
                if bt == CANONICAL_CLAUSE_1_TEXT
            ]
            # Line-level heading strip + whitespace collapse on the
            # rest. Heading lines (start with `#`) and bullet lines
            # (`- `) are excluded; remaining lines are joined with a
            # single space. The canonical sentence is detected as a
            # substring with proper sentence boundaries.
            non_bullet_non_heading = "\n".join(
                line for line in text.splitlines()
                if not line.lstrip().startswith("#")
                and not line.lstrip().startswith("- ")
            )
            normalized_prose = " ".join(non_bullet_non_heading.split())
            offending_prose: list[str] = []
            if CANONICAL_CLAUSE_1_TEXT in normalized_prose:
                offending_prose.append(CANONICAL_CLAUSE_1_TEXT)
            if offending_bullets or offending_prose:
                rel = path.relative_to(REPO_ROOT)
                offenders = []
                for bt in offending_bullets:
                    offenders.append(f"bullet: {bt!r}")
                for pr in offending_prose:
                    offenders.append(f"prose: {pr!r}")
                errors.append(
                    f"{rel}: canonical Clause 1 line found outside the "
                    f"v3.6.7 inversion manifest. If this is intentional "
                    f"widening, land a v3.6.8+ scope-tagged manifest per "
                    f"spec §6.3 line 1807 and open the §9 L2 question; "
                    f"do not retroactively widen v3.6.7's manifest. "
                    f"Offender(s): {offenders!r}"
                )
    return (len(errors) == 0), errors


def inversion_sweep_results() -> list[tuple[str, str, bool, str]]:
    """Run INV-1/INV-2/INV-3. Returns list of
    (pattern_id, description, ok, message) tuples — one row per check ID,
    aggregated across files for INV-2 and INV-3."""
    results: list[tuple[str, str, bool, str]] = []
    files, err = _load_inversion_manifest()
    if err is not None:
        results.append(("INV-manifest", "v3.6.7 inversion manifest readable", False, err))
        return results

    # INV-1: per-file presence/uniqueness check, aggregated.
    inv1_errors: list[str] = []
    for f in files:
        ok, msg = _inv1_check_file(f)
        if not ok:
            inv1_errors.append(msg)
    results.append((
        "INV-1",
        f"canonical Clause 1 line present exactly once in each of {len(files)} manifest file(s)",
        len(inv1_errors) == 0,
        "OK" if not inv1_errors else "; ".join(inv1_errors),
    ))

    # INV-2: aggregate Clause 2 violation hits across all manifest files.
    inv2_errors: list[str] = []
    for f in files:
        ok, errs = _inv2_check_file(f)
        if not ok:
            inv2_errors.extend(errs)
    results.append((
        "INV-2",
        "no Clause 2 disclosure phrases (a)-(d) inside PATTERN PROTECTION blocks",
        len(inv2_errors) == 0,
        "OK" if not inv2_errors else "; ".join(inv2_errors),
    ))

    # INV-3: canonical line restricted to manifest files.
    ok, errs = _inv3_check(files)
    results.append((
        "INV-3",
        f"canonical Clause 1 line confined to {len(files)} manifest file(s)",
        ok,
        "OK" if ok else "; ".join(errs),
    ))
    return results


# Environment variable controlling whether agent-prompt checks run.
#
# Spec §9 ships v3.6.7 across multiple steps. Step 1 (this PR) shipped the
# 4 reference files + audit template + this lint. Step 2 (this PR / Step 1+2
# bundle) lands the actual PATTERN PROTECTION (v3.6.7) blocks in the three
# downstream agent prompts. With Step 2 in, the agent-prompt checks are
# default-on so CI enforces the contract.
#
# Set ARS_V3_6_7_AGENT_CHECKS=0 to skip agent-prompt checks (e.g. for a
# repo bisect that crosses a pre-Step-2 commit, or for partial test runs).
_AGENT_CHECKS_ENV = "ARS_V3_6_7_AGENT_CHECKS"


def _agent_checks_enabled() -> bool:
    return os.environ.get(_AGENT_CHECKS_ENV, "1") == "1"


def all_checks() -> list[Check]:
    checks = [
        *reference_file_checks(),
        *template_file_checks(),
    ]
    if _agent_checks_enabled():
        checks.extend([
            *synthesis_agent_checks(),
            *architect_agent_checks(),
            *compiler_agent_checks(),
        ])
    return checks


def main(argv: list[str]) -> int:
    checks = all_checks()
    passed: list[tuple[str, str]] = []
    failed: list[tuple[str, str, str]] = []

    for check in checks:
        ok, msg = check.run()
        entry = (check.pattern_id, check.description)
        if ok:
            passed.append(entry)
        else:
            failed.append((check.pattern_id, check.description, msg))

    inv_results: list[tuple[str, str, bool, str]] = []
    if _agent_checks_enabled():
        inv_results = inversion_sweep_results()
        for pid, desc, ok, msg in inv_results:
            entry = (pid, desc)
            if ok:
                passed.append(entry)
            else:
                failed.append((pid, desc, msg))

    total = len(checks) + len(inv_results)
    deferred_note = ""
    if not _agent_checks_enabled():
        deferred_note = " (agent-prompt checks skipped — ARS_V3_6_7_AGENT_CHECKS=0)"
    summary = (
        f"v3.6.7 pattern-protection static audit: {len(passed)}/{total} "
        f"checks passed{deferred_note}"
    )
    print(summary)
    print()

    if passed:
        print("PASS:")
        for pid, desc in passed:
            print(f"  [{pid}] {desc}")
        print()

    if failed:
        # Failures go to stderr so CI harnesses that route stderr to a failure
        # channel (matching scripts/check_corpus_consumer_protocol.py) surface
        # the diagnostics correctly.
        print("FAIL:", file=sys.stderr)
        for pid, desc, msg in failed:
            print(f"  [{pid}] {desc}", file=sys.stderr)
            print(f"      → {msg}", file=sys.stderr)
        print(file=sys.stderr)
        print(
            f"{len(failed)} check(s) failed. See spec for protection clause wording:",
            file=sys.stderr,
        )
        print(
            "  docs/design/2026-04-29-ars-v3.6.7-downstream-agent-pattern-protection-spec.md",
            file=sys.stderr,
        )
        print(
            "  docs/design/2026-04-30-ars-v3.6.7-step-6-orchestrator-hooks-spec.md (INV-1/2/3)",
            file=sys.stderr,
        )
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
