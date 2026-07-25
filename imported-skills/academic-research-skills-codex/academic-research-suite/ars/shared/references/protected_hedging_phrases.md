# Protected Hedging Phrases

**Spec:** v3.6.7 §7.1 — pattern protection reference for `report_compiler_agent` (abstract-only mode), Pattern C1.

**Audience:** Upstream calibration agents (academic-paper Stage 4, deep-research Phase 3 abstract handoff). The downstream `report_compiler_agent` reads this reference indirectly through the dispatch context that upstream calibration produces.

**Why this exists:** Live ARS pipeline runs surfaced a recurring failure where the abstract compiler, under hard word-count pressure (i.e., a fixed word budget set by the publisher), dropped epistemic hedges that the body of the paper depended on. The fix routes through a roster of protected hedging phrases that ride in the dispatch context to the compiler. A claim qualified by "may," "tentative," "preliminary," or "in this institutional context" in the body became unconditional in the abstract. The compression-driven drift created compression overclaim — the abstract no longer accurately represented the paper's epistemic stance, which is a publication-integrity failure.

The fix is to make hedging phrases **budget-protected**: upstream calibration marks specific phrases as protected, the protected list rides in the dispatch context to the abstract compiler, and the compiler honours the protection ahead of any other compression target.

---

## What counts as a protected hedging phrase

A phrase qualifies as protected when **dropping it changes the paper's truth-claim**, not merely its rhetorical register. Three categories cover most cases:

### 1. Epistemic hedges that bound the claim

Words and phrases that mark a claim as conditional, tentative, or under-evidenced. Removing them upgrades the claim to assertion.

**Examples:**
- "may," "might," "could" (modal hedges on causal or predictive claims)
- "tentative," "preliminary," "exploratory" (status hedges on findings)
- "suggests," "indicates," "is consistent with" (inferential hedges, distinct from "demonstrates," "proves," "establishes")
- "in our sample," "for this cohort," "under the conditions tested" (scope hedges)

**Why protected:** A reader who acts on an unconditional version of the claim takes on more risk than the evidence justifies. In academic abstracts this is overclaim; in policy abstracts this is misinformation.

### 2. Reflexivity / positionality markers

Phrases that disclose the author's relationship to the studied phenomenon. Removing them obscures the position from which the work was done.

**Examples:**
- "from a former evaluator's perspective" (positional)
- "as participants in the [year-range] reform" (involvement)
- "the authors served on the [committee] from [year] to [year]" (institutional role)
- "this analysis draws on the first author's experience as [role]" (experiential)

**Why protected:** Disclosure obligations under most journal policies (BMJ, Nature, social-science conventions) require positionality to ride in the abstract when it materially shapes interpretation. Stripping disclosure for word count violates the policy, not just the rhetorical norm.

### 3. Temporal disambiguation markers

Phrases that pin a claim or a positional statement to a specific time window. Removing them creates temporal ambiguity that downstream readers cannot resolve.

**Examples:**
- "between 2020 and 2024" (explicit year range)
- "during their term as [role] in [year]" (role-bounded period)
- "former [role]" (closed temporal status)
- "at the time of the [event]" — only protected when the event is named immediately adjacent; otherwise the deictic phrase is itself the failure mode (see `feedback_ars_phase2_phase3_downstream_agent_patterns.md`).

**Why protected:** Deictic temporal phrases ("during this period," "at the time," "currently") read differently when separated from their anchoring context. The abstract has no neighbouring context; an abstract-level deictic is unresolvable.

---

## Upstream calibration: how to mark phrases as protected

Upstream calibration runs at the end of paper drafting, after the body text is stable but before abstract compilation. The calibration agent walks the paper and identifies phrases in the three categories above, then emits a `protected_hedges` block in the dispatch payload to the abstract compiler.

### Dispatch block shape

```yaml
protected_hedges:
  epistemic:
    - phrase: "may"
      anchored_at: "Section 4, claim about institutional adoption rate"
      why: "claim is observational, not causal"
    - phrase: "tentative"
      anchored_at: "Section 5, conclusion about policy effect"
      why: "n=12 sites, no comparison group"
  reflexivity:
    - phrase: "as a former evaluator on the [committee] between 2020 and 2024"
      anchored_at: "Author note + Section 1"
      why: "BMJ-equivalent disclosure obligation; informs how reader weights argument"
  temporal:
    - phrase: "between 2020 and 2024"
      anchored_at: "Section 1, paragraph 2; Section 6, conclusion"
      why: "abstract-level deictic ('at the time') would be unresolvable"
```

### Calibration rules

1. **Conservative inclusion.** When in doubt, include the phrase. Calibration cannot recover a hedge it did not list — the compiler treats every entry on the list as non-negotiable, so omitting a phrase removes that protection regardless of intent.
2. **Anchor every entry.** Each protected phrase must cite where in the paper it operates and one-line why. Without the anchor, the abstract compiler cannot judge replacement-vs-preservation when budget is tight.
3. **No duplicates.** One entry per phrase. The compiler counts protected phrases against the budget once.
4. **Calibration is mode-specific.** Deep-research INSIGHT abstracts and academic-paper journal abstracts have different convention (see `word_count_conventions.md`). Calibration runs once per target mode, not once per paper.

---

## Abstract compiler: how protection is honoured

The `report_compiler_agent` abstract-only mode treats protected hedges as **non-negotiable budget**. Concretely:

1. **Budget allocation order.** Protected hedges are reserved before any other content competes for budget, because they are non-negotiable.
   - Step 1: Compute hard cap (whitespace-split, see `word_count_conventions.md`).
   - Step 2: Reserve 3–5% buffer.
   - Step 3: **Reserve words for protected hedges.** Sum the word count of every entry in `protected_hedges` (verbatim). This subtotal is non-negotiable budget.
   - Step 4: Allocate the remaining words to required structural slots (research question, method, finding, implication).
   - Step 5: Spend any words still remaining on rhetorical polish, transitions, secondary findings.

2. **Verbatim preservation rule.** A protected phrase rides verbatim into the abstract. The compiler does not paraphrase, compress, or substitute a synonym for a protected phrase. (A future v3.6.7+ extension may add an optional `approved_synonyms` field to the dispatch block; until then, verbatim only.)

3. **Cut order under budget pressure.** When the draft exceeds budget, cuts come from Step 5 first (rhetorical polish), then Step 4 (compress structural slots), **never** from Step 3 (protected hedges).

4. **Failure surface.** If the abstract cannot fit Steps 1–4 within hard cap, the compiler **reports the conflict** rather than dropping a protected hedge. The conflict goes back to upstream calibration to either renegotiate the protected list or the publisher's word cap.

---

## Where this protocol is enforced

The `report_compiler_agent` abstract-only mode prompt enforces the dispatch-context protocol and the budget allocation order. The authoritative protection clause lives in `deep-research/agents/report_compiler_agent.md` under `PATTERN PROTECTION (v3.6.7)`. This file defines what counts as a protected hedge, the upstream calibration shape, and the compiler's budget allocation order; the agent prompt cites this file by path. Cross-model audit covers protected-hedge preservation under the report_compiler bundle's Section 4(f) check in `shared/templates/codex_audit_multifile_template.md`.

---

## Cross-references

- `shared/references/word_count_conventions.md` — whitespace-split standard, 3–5% buffer rule, publisher conventions.
- `shared/templates/codex_audit_multifile_template.md` — audit dimensions including compression overclaim detection.
- `docs/design/2026-04-29-ars-v3.6.7-downstream-agent-pattern-protection-spec.md` §3.3 (C1) — pattern definition and provenance.
