# Co-Scientist L3 — which mechanisms transfer to ARS QA, and which do not

| | |
|---|---|
| **Status** | Design lesson — **NOT a proposed feature** |
| **Issue** | [#222](https://github.com/Imbad0202/academic-research-skills/issues/222) |
| **Parent epic** | [#219](https://github.com/Imbad0202/academic-research-skills/issues/219) — Co-Scientist implications for ARS |
| **Paper anchor** | Gottweis et al. (2026), *Accelerating scientific discovery with Co-Scientist*, Nature. DOI [10.1038/s41586-026-10644-y](https://doi.org/10.1038/s41586-026-10644-y) |
| **Verified** | 2026-06-02 — transfer matrix reconciled against the codebase; several originating bindings corrected (see Verification note) |

This is a recorded boundary, not a roadmap item.

## Anchor

- **Paper**: A six-agent multi-agent system designed for *hypothesis generation* in
  biomedicine, with continuous test-time compute scaling reported across 203
  research goals.
- **ARS**: `POSITIONING.md` — "a source-available academic research copilot
  framework" with mandatory checkpoints, max 2 revision loops, and an explicit
  non-claim of autonomy.

## Problem

Co-Scientist and ARS share the multi-agent shape but serve different epistemic
roles. Co-Scientist generates novel hypotheses for experimental validation. ARS
supports a human researcher through the research-to-publication workflow, with
quality assurance as the load-bearing function.

A naive "the paper has six agents, ARS should adopt the six-agent design" approach
would silently change the role ARS plays in the user's research life. A naive "the
paper and ARS are entirely different, nothing transfers" approach would miss
genuinely useful primitives. This document records the boundary, mechanism by
mechanism.

> **The ARS-side cells below were re-derived from the current codebase (2026-06-02),
> not copied from the originating issue.** Several of the issue's original bindings
> projected Co-Scientist vocabulary onto ARS components that do not match. The
> corrected mapping is what stands; the Verification note lists what changed.

## The transferable mechanisms

These can be adopted into ARS when re-framed for the human-leads workflow:

| Co-Scientist mechanism | ARS analogue (verified) | Transfer condition |
|---|---|---|
| Enumeration of alternative hypotheses | **No current analogue.** ARS's `synthesis_agent` is a Phase-3 cross-source *integration* agent (it produces a Synthesis Report — literature matrix, themes, contradictions, gaps); it does not enumerate competing framings. | **Green-line candidate.** If candidate-framing enumeration is added, all candidates must reach the user with no hidden culling (see [L1](2026-06-02-co-scientist-220-l1-hidden-ranking.md)). |
| Structured critique log (Reflection agent's deep verification review) | `source_verification_agent` produces a **Source Quality Matrix** (Source × Level / Venue / Author / Method / Currency / COI), grading the evidence hierarchy. | The matrix is for the user to read. A genuine extension would be a sub-assumption × evidence decomposition; that does not exist today and would be additive, not a relabeling of the quality matrix. |
| Append-only correction / ADD-based variant | **No current analogue.** ARS has no competing-draft fork mechanism. | **Green-line candidate.** If an append-only competing-draft variant is ever added, it must be user-invoked with both drafts visible for A/B selection (per [L1](2026-06-02-co-scientist-220-l1-hidden-ranking.md)). This row records the *constraint*, not a commitment to build it. |
| Observation review (does H explain long-tail observations?) | `devils_advocate_agent` critique at its post-analysis checkpoint (Checkpoint 2 of three). | The DA runs single-pass *per checkpoint*; multi-turn background self-play debate is rejected (see Non-transferable). Note: the DA has **three** mandatory checkpoints overall, not a single pass across the run. |
| External grounding via web search + databases | `bibliography_agent` verification chain: Semantic Scholar (Tier 0) → DOI resolution (Tier 1) → WebSearch spot-check (Tier 2); contamination triangulation adds OpenAlex + Crossref (v3.9.0). | Verified and unverified sources are presented in separate columns with explicit source labels. (ARS does **not** have a "Semantic Scholar → PubMed/arXiv" search fallback; PubMed is a predatory-venue red-flag criterion and arXiv is a preprint-venue label, not search fallbacks.) |

## The non-transferable mechanisms

These conflict with ARS positioning at the paradigm level. Adoption would require
changing ARS positioning, not just adapting the mechanism:

| Co-Scientist mechanism | ARS conflict |
|---|---|
| Open-ended test-time compute scaling (paper L411 "no saturation observed") | Conflicts with `POSITIONING.md`: "Max 2 revision loops, after which remaining issues become 'Acknowledged Limitations' rather than being silently resolved." |
| Autonomous selection of top-K hypotheses (Ranking agent's tournament outcome) | Conflicts with `POSITIONING.md`: "the human decides at every gate." See [L1](2026-06-02-co-scientist-220-l1-hidden-ranking.md). |
| Hidden prompt patching via Meta-review feedback propagation | Conflicts with `POSITIONING.md`: "Failure modes are made visible, not hidden." See [L2](2026-06-02-co-scientist-221-l2-feedback-propagation.md). |
| Domain expert contact identification (paper L1787–1792) | ARS does not identify or surface named individuals as contacts: it works from published sources, not from a directory of people to approach. Adopting this would add a person-targeting capability the framework deliberately does not have. |
| Multi-turn self-play debate inside an agent for high-stakes evaluation | Conflicts with "Failure modes are made visible" — multi-turn background reasoning collapses into a summary that hides the reasoning trajectory. |
| Wet-lab / AlphaFold-style domain-specific autonomous loops | Out of scope for a general academic workflow framework. |

## The agents

Mapping the paper's six agents to ARS equivalents (verified against the
`deep-research/agents/` roster and `academic-pipeline/agents/`):

| Paper agent | ARS equivalent? | Notes |
|---|---|---|
| Generation | Partial | `synthesis_agent` produces integrated findings (Phase 3), not candidate enumeration. Adopting enumeration would be a green-line addition (see [L1](2026-06-02-co-scientist-220-l1-hidden-ranking.md)). |
| Reflection | Yes | `source_verification_agent`, `devils_advocate_agent`, `risk_of_bias_agent` (Cochrane RoB 2 / ROBINS-I). ARS's verification layer is strong; a sub-assumption × evidence decomposition is the genuine gap. |
| Ranking | No, deliberately | No Elo / tournament / top-K mechanism exists. See [L1](2026-06-02-co-scientist-220-l1-hidden-ranking.md) for the red / yellow / green analysis. |
| Proximity | Not adopted | Volume mismatch; ARS does not generate hundreds of candidates per goal. |
| Evolution | Partial | revision-coach + draft re-entry exist. A competing-draft fork variant is a green-line candidate (above); replacing drafts in tournament fashion is rejected. |
| Meta-review | Partial | v3.6.7 PATTERN PROTECTION blocks and the v3.5 `collaboration_depth_agent` (advisory-only). See [L2](2026-06-02-co-scientist-221-l2-feedback-propagation.md) for the user-approval-gate analysis. |

## Application — when this is invoked

When evaluating whether a Co-Scientist (or similar auto-research) mechanism belongs
in ARS, consult this matrix to determine transferability. A mechanism in the
non-transferable table requires a positioning change, not just an adapter. A
"green-line candidate" cell states a constraint on *future* work, not a feature
request — it does not authorize building the thing, only the shape it must
take if built.

## Verification note

Verified against the codebase 2026-06-02. The originating issue's transfer matrix
cited eight ARS internals; six did not match the codebase and are corrected here:

- `synthesis_agent` "produces N candidate framings" → it is a Phase-3 integration
  agent; no candidate enumeration. Recorded as a green-line candidate instead.
- `source_verification_agent` "sub-assumption × evidence matrix" → real output is a
  Source Quality Matrix; the sub-assumption decomposition is a non-existent
  (additive) extension, not the current behavior.
- `ARS_REVISION_FORK=1` → **no such flag exists anywhere in the repo.** The idea is
  kept generically (append-only competing-draft variant) with no coined flag name.
- `devils_advocate_agent` "single-pass critique only" → it runs three mandatory
  checkpoints; the single-pass framing applies per-checkpoint, not across the run.
- `bibliography_agent` "fallback to PubMed / arXiv" → the real chain is S2 → DOI →
  WebSearch (+ OpenAlex / Crossref triangulation); PubMed/arXiv are not search
  fallbacks.
- `risk_of_bias_agent` "reflection layer" → the agent is real, but "reflection
  layer" is not an ARS concept; it is folded into the Reflection-equivalent row
  above without inventing the label.

Verified and kept: the v3.6.7 PATTERN PROTECTION mechanism (shipped, CI-enforced)
and `collaboration_depth_agent` (v3.5.0, advisory-only). This reconciliation is why
the doc is trustworthy as a standalone reference.
