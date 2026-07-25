# Example: Sub-Claim Decomposition in Editorial Synthesis (§F.3.2 partial-evidence trap)

This example shows the editorial synthesizer's Step 1 → Step 2 → Step 5 flow on a **compound weakness** — the case the §F.3.2 partial-evidence trap exists to catch — and contrasts the old bundle-level aggregation (which buries a minority sub-claim) with the sub-claim decomposition introduced for [#214](https://github.com/Imbad0202/academic-research-skills/issues/214).

It is a focused illustration of one weakness bundle, not a full Phase 0–2 walkthrough (see `hei_paper_review_example.md` for that).

---

## The input: what the 4 reviewers said about one weakness area

The paper reports a multi-site mixed-effects analysis. Three reviewers raised concerns that **look like "one statistics weakness"** but are actually two distinct claims:

- **R1 (Methodology), Confidence 5:** "Two problems. First, the statistical reporting is inconsistent — Table 3 gives standardized betas, Table 4 raw coefficients, with no key. Second, the mixed-model random-effects grouping is never specified: are sites or participants the grouping factor?"
- **R2 (Domain), Confidence 4:** "I agree the random-effects structure is unclear — the paper doesn't say what the grouping variable is."
- **R3 (Cross-disciplinary), Confidence 3:** "The reporting tables were hard to follow; the units shift between tables."
- **EIC, Confidence 4:** Did not comment on the statistics specifically.

---

## ❌ Old behavior — bundle-level aggregation (the trap)

The Step 1 inventory collapses this into a single `Key Weaknesses` cell ("statistics problems"), and Step 2 reaches **one** consensus verdict on the bundle:

> **[CONSENSUS-3] Statistics problems** — R1, R2, R3 agree; EIC silent. Author must fix.

What went wrong: the bundle holds **two** sub-claims with **different** support levels, and the verdict averages them into one. "Random-effects grouping unspecified" was raised by R1 *and* corroborated by R2 — a genuine 2-reviewer consensus. "Inconsistent reporting units" was raised by R1 and R3 but is a different defect. Folding both into one "[CONSENSUS-3]" item produces a single roadmap line that lets the author treat the whole thing as one fix, and the precise grouping-factor defect can be lost inside a vague "clean up the statistics" instruction. Partial support read as full resolution.

---

## ✅ New behavior — Step 1b sub-claim inventory, then per-sub-claim consensus

### Step 1b — Weakness Sub-Claim Inventory

| sub_claim_id | parent_weakness | reviewer_id | position | evidence_pointer | confidence |
|--------------|-----------------|-------------|----------|------------------|------------|
| SC-1 | Statistics | R1 | raised | "random-effects grouping never specified" | 5 |
| SC-1 | Statistics | R2 | corroborated | "random-effects structure is unclear" | 4 |
| SC-1 | Statistics | R3 | not-mentioned | — | — |
| SC-1 | Statistics | EIC | not-mentioned | — | — |
| SC-2 | Statistics | R1 | raised | "Table 3 betas vs Table 4 raw coeffs, no key" | 5 |
| SC-2 | Statistics | R3 | corroborated | "units shift between tables" | 3 |
| SC-2 | Statistics | R2 | not-mentioned | — | — |
| SC-2 | Statistics | EIC | not-mentioned | — | — |

Two atomic sub-claims fall out of the one "statistics" bundle. `not-mentioned` is recorded as silence, not opposition.

### Step 2 — consensus per sub_claim (denominator = 4 non-DA reviewers)

- **SC-1 (random-effects grouping unspecified):** `agree = 2` (R1 raised, R2 corroborated), `conflict = 0`, `silent = 2` (R3, EIC). Two agree, none conflict → a **corroborated finding** (below the CONSENSUS-3 bar of 3/4), action-bearing and prioritized by R1's Confidence-5 weight. **Not a CONSENSUS-3/4 label; not a SPLIT.**
- **SC-2 (inconsistent reporting units):** `agree = 2` (R1 raised, R3 corroborated), `conflict = 0`, `silent = 2` (R2, EIC) → a **corroborated finding**, R1 Confidence-5. **Not a SPLIT.**

Note the threshold discipline: even though every reviewer who *spoke* agreed, neither sub-claim is promoted to CONSENSUS-4 — the denominator is the full panel of 4, not the 2 who spoke, so 2/4 is a corroborated finding, not unanimity. This is exactly the mislabel the absolute-count rule prevents.

Neither sub-claim triggers EIC arbitration — there is no `disputed` position anywhere, so finer granularity did **not** manufacture arbitration load. (Had R2 instead written "the grouping is clearly by site, this is a non-issue," SC-1 would carry a `disputed` position against R1's `raised`, and *then* it would be a genuine SPLIT requiring EIC arbitration.)

### Step 5 — Revision Roadmap (sub-claim-keyed)

Instead of one blurred "fix the statistics" line, two separately-prioritized, traceable items:

> **Priority 1 — Structural (Must Fix)**
> - **[SC-1]** Specify the mixed-model random-effects grouping factor (sites vs participants) and re-state the model. *Raised R1 (conf 5), corroborated R2 (conf 4).*
>
> **Priority 2 — Content Supplementation (Should Fix)**
> - **[SC-2]** Standardize coefficient reporting across Tables 3–4 (one convention + a key). *Raised R1 (conf 5), corroborated R3 (conf 3).*

Each item carries its `sub_claim_id`, traces back to the Step 1b inventory, and flows forward into `academic-paper` revision mode unchanged in format. The minority-risk sub-claim (the grouping factor) is now its own Priority-1 item rather than buried in a bundle.

---

## What this example demonstrates (acceptance for #214)

- **Step 1b inventory** with `sub_claim` as the primary key, alongside the retained Step 1a summary matrix.
- **Per-sub-claim consensus** in Step 2, with `not-mentioned` correctly excluded from both consensus and SPLIT counting.
- **SPLIT bound respected** — no arbitration is triggered absent an explicit conflicting position (the parenthetical shows what *would* trigger one).
- **Revision Roadmap at sub-claim granularity** — the compound weakness yields two correctly-prioritized, traceable items instead of one.
- DA-CRITICAL flow and the v3.6.2 sprint-contract arithmetic path are untouched (neither appears in this general-protocol example).
