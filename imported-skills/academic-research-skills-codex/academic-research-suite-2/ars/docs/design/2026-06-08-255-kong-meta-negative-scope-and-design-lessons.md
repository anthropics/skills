# Kong META #255 closeout — negative scope + Tier D design lessons

| | |
|---|---|
| **Status** | Closeout design note for META [#255](https://github.com/Imbad0202/academic-research-skills/issues/255) |
| **Scope** | Documentation only — no schema, no agent prompt, no lint change |
| **Paper anchor** | Kong et al. (2026), *AI for Auto-Research: Roadmap & User Guide*, arXiv:2605.18661 |
| **Verified** | 2026-06-08 — ship-state of #257 / #260 and absence of autonomous mechanisms verified against the tracked repo (see Verification) |

## Why this exists

META #255 mapped the autonomous-research mechanisms surveyed by Kong et al. onto
ARS. Every *feature* sub-issue (Tier A #256–#259, Tier B #260–#262, Tier C #263,
plus the Schema 11 follow-ups #266/#268/#269) is merged. Two closing conditions
remained, both documentation-only and both about ARS's **negative scope** — what
ARS does NOT do, and would not do even if a future paper made it feasible:

1. **Five rejected mechanisms** must land as first-class, enumerated entries with a
   Kong anchor and the philosophy gate that rejects each.
2. **Two Tier D design-lesson docs** (L1, L2) must record the boundaries that are
   load-bearing enough to be applied consistently to future PRs.

This note records the design decisions; the deliverables are the POSITIONING.md
section and the two L-docs.

## Decision 1 — five rejected mechanisms live IN POSITIONING.md, not a new file

The META allowed either POSITIONING.md or a new `NEGATIVE_SCOPE.md`. Decision:
**keep them in POSITIONING.md** as a new `## Rejected mechanisms (autonomous-research
anti-patterns)` section placed right after `## What this is not`.

Rationale: this is scope identity, not usage discipline (`Discouraged uses`) and
not license policy (`Prohibited uses`). A separate file fragments the boundary away
from the one doc readers actually open. A ~25-line enumerated section is within fit;
the rationale that would have bloated it lives in the two L-docs instead.

## Decision 2 — Tier D docs reuse the existing `docs/design/…lX…` convention

The META draft assumed `docs/design-lessons/`. The repo's established convention,
visible in POSITIONING.md's "Boundaries are recorded, not improvised" paragraph, is
that design-lesson docs live in `docs/design/` with an `lX` filename token (the four
Co-Scientist docs `2026-06-02-co-scientist-22X-lX-*.md`). The Kong docs follow that
convention rather than introducing a parallel directory:

- `docs/design/2026-06-08-kong-255-l1-copilot-not-auto-research.md`
- `docs/design/2026-06-08-kong-255-l2-advisory-not-generation.md`

## Decision 3 — the three CONSIDER-vs-REJECT boundary sentences

The load-bearing risk is that a sloppy phrasing either over-claims (looks like we
reject things we shipped — #260 provenance, #257 advisory) or under-claims (leaves a
seam where an auto-gen feature is dressed up as a "fidelity audit"). Each boundary is
phrased to be operationally checkable:

1. **Wording advisory (#257) vs idea generation.** ARS may flag surface-level
   wording / framing patterns in a scholar-supplied research question and ask a
   Socratic follow-up, but it must not propose, substitute, rank, expand, or select
   research hypotheses or questions for the scholar.
2. **Paper2X fidelity audit vs Paper2X generation.** ARS may audit an
   already-authored or externally generated slide / poster / video artifact against
   the manuscript for fidelity, but it must not transform a manuscript into a
   dissemination artifact by choosing the content, narrative, layout, or output
   medium itself.
3. **Experiment provenance intake (#260) vs autonomous experiments.** ARS may ingest
   scholar-declared external experiment provenance and check manuscript claims
   against the declared results, but it must not initiate, run, modify, iterate, or
   treat tool-executed experiment / code outputs as evidence inside the pipeline.

## Decision 4 — L1's operational test is research-state authority

"Copilot, not auto-research" risks reading as a mission-statement platitude. L1 is
load-bearing only because it carries an operational review test about **who controls
the next research-state transition**:

> Does this change let ARS create, select, execute, or advance a research object of
> record — hypothesis, RQ, evidence set, experiment result, claim, manuscript
> section, or dissemination artifact — without an explicit scholar-authored seed or
> scholar confirmation after inspecting the relevant state?

If yes, it crosses into auto-research and is rejected. If no, it stays
copilot/advisory. This gives L1 the same review force as Co-Scientist L1's
red/yellow/green line — not "copilot vibes," but "who owns the state transition?"

## Decision 5 — honesty: recorded boundary, not a runtime guarantee

The docs split the verification note into a verifiable claim and a design
commitment, so the boundary is not mis-stated as a proven property:

- **Verifiable (2026-06-08, against the tracked repo):** first-party ARS does not
  implement an end-to-end autonomous research pipeline, an idea-generation agent, a
  Paper2X generator, an autonomous experiment executor, or a wet-lab automation API.
  The Kong-derived features that did ship (#257 wording advisory, #260 experiment
  provenance intake) are advisory / provenance gates, not autonomous generation or
  execution layers.
- **Design commitment (not a guarantee):** these docs record a first-party scope
  boundary and a review criterion for future changes. They are not a proof that the
  software cannot be modified, a guarantee about forks or downstream deployments, or
  a runtime enforcement mechanism. The phrasing is "first-party ARS treats X as out
  of scope; adding X would require changing the recorded project boundary, not merely
  adding a feature" — never "ARS will never do X."

## Verification

- #257 (wording-pattern advisory) shipped: commit `f0bfc59` (`#277` follow-up) on
  `main`; the advisory's own non-goals already state "does not generate ideas for the
  scholar."
- #260 (experiment provenance intake) shipped: commit `d066340` (PR `#374`) on
  `main`; `shared/contracts/passport/experiment_provenance_entry.schema.json` exists;
  it is a scholar-declared intake + claim-alignment gate, not an execution layer.
- No autonomous mechanism exists: a targeted review of the first-party
  implementation, agent prompts, and schemas found no end-to-end pipeline,
  idea-generation agent, Paper2X generator, autonomous experiment executor, or
  wet-lab automation API. The only `wet_lab` references are domain-evidence-profile
  labels (a discipline label in `intake_agent` / `literature_strategist_agent` /
  `domain_evidence_profiles`); dissemination is handled by separate, non-ARS
  companion skills. So the "no autonomous mechanism today" claim is a reviewed
  finding, not an aspiration.

## Closeout

When the POSITIONING.md section and the two L-docs land and cross-link, META #255's
two remaining checkbox groups (five rejected mechanisms persisted; Tier D L1/L2 docs
landed + cross-linked) are satisfied, and the META can close. The five mechanism
checkboxes and the L1/L2 checkboxes in the META body should be ticked at close with a
pointer to this note.
