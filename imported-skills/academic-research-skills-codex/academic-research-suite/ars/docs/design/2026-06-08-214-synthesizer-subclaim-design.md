# #214 — Sub-claim inventory before consensus aggregation (partial-evidence trap, synthesis layer)

**Status**: design (2026-06-08)
**Issue**: [#214](https://github.com/Imbad0202/academic-research-skills/issues/214) (Kim et al. 2026 META #217)
**Target agent**: `academic-paper-reviewer/agents/editorial_synthesizer_agent.md`
**Paper anchor**: Kim et al. 2026 (arXiv:2605.20668v1) §F.3.2 — the partial-evidence trap is the single largest correctness-error class in AI meta-review (41/54, 76%).
**Sibling**: [#213](https://github.com/Imbad0202/academic-research-skills/issues/213) closed the **citation-audit** layer of the same trap; this is the **editorial-synthesis** layer.

---

## Problem

§F.3.2 failure mode: a multi-part item gets a single binary verdict, so partial support is treated as full resolution.

In the editorial synthesizer, the general Synthesis Protocol Step 1 inventory is a `(Dimension × reviewer)` matrix whose "Key Weaknesses" cell holds *whatever* a reviewer said about weaknesses — and a single weakness bundle often packs several sub-claims (e.g. "statistical reporting is inconsistent **AND** mixed-model grouping is unclear"). Step 2 Consensus Classification then reaches `CONSENSUS-4 / CONSENSUS-3 / SPLIT` on the **whole bundle**, not on each sub-claim. A bundle where 4 reviewers agree on one sub-claim but only 1 raised the other is scored as one consensus verdict, and the minority sub-claim is folded into (or dropped from) the bundle's classification. Same shape as the documented failure: multi-part in, one verdict out.

This is the synthesis-layer sibling of #213. Both layers must **enumerate before aggregating**.

## Scope decision (chosen: prose-layer-only — NOT a mirror of #213)

#213 went heavy (new prompt verdict + normalized schema field `sub_claim_breakdown[]` + lint invariant INV-19 + gold fixtures + calibration subset metric). That weight was justified there because the citation judge emits **machine-readable `claim_audit_result` rows consumed by a deterministic gate** with downstream schema consumers.

The editorial synthesizer is different: its output is a **human-facing Editorial Decision Letter + a Revision Roadmap** consumed by `academic-paper` revision mode as prose. There is **no schema / lint / gold-set substrate** at this layer analogous to the citation gate, and the synthesizer is a prose-producing arbiter, not a row-emitting judge. Inventing a machine-readable sub-claim artifact + a lint to pin it here would be an unrequested abstraction with no deterministic consumer.

**Decision: prose-layer-only.** Change the synthesizer's reasoning + output prompt; add a worked `examples/` before/after; confirm both forbidden-ops lists are not violated. No schema field, no lint invariant, no gold fixture. Vocabulary (`sub_claim`) is aligned with #213 to avoid drift, but #213's schema architecture is **not** imported.

## The primary-key trap (and the faithful fix)

The issue says "Step 1 inventory primary key from `Weakness` to `sub_claim`." A **literal** read — make every report Dimension a sub-claim — breaks the non-weakness rows (`Overall Recommendation`, `Confidence Score`, `# of Questions` are not "sub-claims" and don't decompose). The faithful-to-paper fix decomposes the **weakness/issues portion only**, leaving the reviewer-summary rows intact.

So Step 1 splits in two:

- **Step 1a — Reviewer Summary Matrix** (the current `(Dimension × reviewer)` table, unchanged): Overall Recommendation, Confidence Score, Key Strengths, # of Questions, # of Minor Issues. (The "Key Weaknesses" row stays as a one-line *pointer* into Step 1b.)
- **Step 1b — Weakness Sub-Claim Inventory** (new): each weakness bundle a reviewer raised is decomposed into atomic sub-claims; one row per `(sub_claim, reviewer)` position:

  | sub_claim_id | parent_weakness | reviewer_id | position | evidence_pointer | confidence |

  - `sub_claim_id`: `SC-<n>` (synthesizer-assigned, stable within the synthesis).
  - `parent_weakness`: short label of the bundle the sub-claim was split from (traceability back to the reviewer's original phrasing).
  - `position` ∈ `{raised, corroborated, not-mentioned, disputed}`. **`not-mentioned` is NOT opposition** — a reviewer who never spoke to a sub-claim is silent, not dissenting. Only `disputed` counts as a conflicting position.
  - `evidence_pointer`: where in the reviewer's card the sub-claim is grounded.
  - `confidence`: the reviewer's existing Confidence Score for the finding (drives the existing weighting rule at the sub-claim level).

## Step 2 — consensus per sub-claim

`CONSENSUS-4 / CONSENSUS-3 / SPLIT` are computed **per `sub_claim_id`**, not per bundle. Mechanics unchanged except granularity:

- Consensus count uses `position ∈ {raised, corroborated, disputed}` as "spoke to it"; `not-mentioned` does **not** count as either agreement or opposition (it neither adds to consensus nor manufactures a SPLIT).
- **SPLIT → EIC arbitration fires only when ≥2 reviewers hold explicitly conflicting positions (`disputed` vs `raised/corroborated`) on an action-bearing sub-claim.** A sub-claim that one reviewer raised and others simply didn't mention is a single-reviewer finding (handled by the existing Confidence-Score-Weighting rule), **not** a SPLIT. This bound is the guard against finer granularity flooding EIC arbitration.
- Confidence-Score-Weighting (existing rules) applies at the sub-claim level: a Score-5 sub-claim outweighs opposing Score-2 sub-claims exactly as today.

## DA-CRITICAL — unchanged

DA findings stay tracked independently of the 4-reviewer consensus count (#214 non-goal: do not change DA flow). DA-CRITICAL items are not decomposed into the Step 1b inventory; they keep their existing dedicated Decision-section treatment.

## Revision Roadmap — sub-claim granularity

Step 5 Revision Roadmap construction: each roadmap item traces to a `sub_claim_id` (not just a weakness bundle), so a compound weakness whose sub-claims have different consensus levels produces **separate, correctly-prioritized roadmap items** instead of one blurred item. Roadmap-format compatibility with `academic-paper` revision mode input is preserved (sub_claim_id is additive provenance, not a format change).

## Forbidden-ops compatibility (both lists)

1. **General Synthesis Protocol** has no explicit forbidden-ops block; the governing constraint is the Phase-Boundary "you are not a 6th reviewer / do not produce new review comments." Sub-claim decomposition is **re-organization of existing reviewer content** (splitting what a reviewer already said into its atomic parts), not authoring new findings — compatible. The design adds a one-line guard: *the synthesizer may only decompose claims a reviewer actually made; it must not introduce a sub-claim no reviewer raised.*

2. **v3.6.2 Sprint Contract Synthesizer Protocol** (the separate arithmetic mode, L46-69) is **untouched**. Its forbidden-ops (no aggregation rules beyond `cross_reviewer_quantifier` + `severity`, no averaging, etc.) govern `failure_conditions[]` / `acceptance_dimensions[]` evaluation and are orthogonal to the general protocol's weakness inventory. The new sub-claim protocol carries an explicit applicability line: **"applies to the general Synthesis Protocol only; sprint-contract mode is unaffected."**

## Out of scope

- No schema field, no lint invariant, no gold fixture (see Scope decision).
- No change to upstream reviewer agents (synthesizer is responsible for decomposition; #214 non-goal).
- No change to DA-CRITICAL flow.
- No change to the sprint-contract arithmetic path.

## Acceptance (from #214)

- [ ] Step 1b inventory table documented with `sub_claim` as primary key (Step 1a summary matrix retained).
- [ ] `examples/` sample shows a compound weakness decomposed, with per-sub-claim consensus before/after.
- [ ] Forbidden-ops compatibility (both lists) confirmed in PR description.
- [ ] Revision Roadmap respects sub-claim granularity.

## Verification

- Prose self-consistency: the worked example must round-trip through the new Step 1a/1b/Step 2/Step 5 without contradiction.
- If a line-budget test covers this agent, update its expected count for the added section.
- Paper-derived: full citation to the source; no internal or personal content in the change.
