# Co-Scientist L1 — hidden ranking is the red line, not Elo itself

| | |
|---|---|
| **Status** | Design lesson — **NOT a proposed feature** |
| **Issue** | [#220](https://github.com/Imbad0202/academic-research-skills/issues/220) |
| **Parent epic** | [#219](https://github.com/Imbad0202/academic-research-skills/issues/219) — Co-Scientist implications for ARS |
| **Paper anchor** | Gottweis et al. (2026), *Accelerating scientific discovery with Co-Scientist*, Nature. DOI [10.1038/s41586-026-10644-y](https://doi.org/10.1038/s41586-026-10644-y) |
| **Verified** | 2026-06-02 — fully verified against the codebase (see Verification note) |

This is a recorded boundary, not a roadmap item. It exists so that future work and
reviews apply the same line consistently.

## Anchor

- **Paper**: Co-Scientist's Ranking agent (paper L1661–1685) uses Elo-based
  tournaments with pairwise debate to rank hypotheses. Top-ranked candidates enter
  multi-turn debate; lower-ranked candidates get single-turn comparisons. The agent
  selects the top-K for downstream stages.
- **ARS**: `POSITIONING.md` — "the human decides at every gate" (Design philosophy).
  The 10-stage pipeline + mandatory user confirmation does not delegate selection
  decisions to AI.

## Problem

A naive cross-walk would label "Elo + tournament" as fundamentally incompatible
with ARS. That read is wrong.

The real conflict is not the **algorithm** (Elo, pairwise comparison) but the
**system behavior** (AI ranks → AI selects top-K → user sees only the survivors).
The algorithm can be retained if the system behavior changes.

## Boundary

### Red line — DO NOT IMPLEMENT

AI ranks N candidates → AI selects top-K based on its own scores → user sees only
the survivors.

This is hidden selection pressure. Even if the user nominally "approves" the
survivors, their judgment is anchored on a filtered set whose filter criterion they
cannot audit.

### Yellow line — implementable with three conditions

AI ranks N candidates → user sees ALL candidates → user picks → scores and
reasoning are revealed. The ranking informs the design but does not pre-filter or
pre-anchor what the user sees.

Three conditions for the implementation to stay on the yellow line:

1. **All candidates visible.** No silent culling. If N=10 candidates exist, all 10
   reach the user.
2. **Blinded presentation.** The AI's scores and rank labels are not shown
   alongside the candidates up front (they would anchor the user to the AI's
   ranking). Candidates carry anonymous identifiers (Option A, Option B, …); the
   scores become available only after the user has formed an initial preference
   (automatically or on request), and are never used as the default sort key or a
   visible badge.
3. **Randomized order.** First-position bias is well-documented. Presentation order
   is randomized per session, not "top-scored first".

### Green line — preferred default

AI enumerates candidates without ranking. User reads, reasons, and ranks
themselves.

## Why this distinction matters

The boundary is load-bearing because algorithm-level rejection ("no Elo, ever")
loses useful primitives: pairwise comparison is a strong tool for surfacing
trade-offs the user might miss, even when the user makes the final selection.
Behavior-level rejection ("no hidden culling, ever") keeps the primitive while
preserving the discipline.

The reverse is equally true. Permitting "Elo in advisory mode" without the three
conditions silently re-introduces the anchoring pressure, because score labels
alone are sufficient to anchor user judgment.

## Application — when this is invoked

Any PR that introduces ranking, scoring, pairwise comparison, Elo, tournaments, or
top-K selection of candidates is reviewed against the three yellow-line conditions
above before merge. A change that lets the system narrow a candidate set the user
never fully sees crosses the red line and is rejected regardless of how the scores
are computed.

The sibling docs build on this line:
[L2](2026-06-02-co-scientist-221-l2-feedback-propagation.md) (feedback
propagation), [L3](2026-06-02-co-scientist-222-l3-transfer-matrix.md) (mechanism
transfer; its "all candidates visible" transfer conditions point here), and
[L4](2026-06-02-co-scientist-223-l4-control-plane-ownership.md) (who may rank).

## Verification note

Verified against the codebase 2026-06-02. "The human decides at every gate" is
present in `POSITIONING.md`; the 10-stage pipeline and mandatory user confirmation
are real (`academic-pipeline/SKILL.md`). No Elo, tournament, top-K, or
candidate-ranking mechanism exists in ARS today — so the claim "ARS has no hidden
ranking" is a verified fact, not merely an aspiration. This doc therefore records a
boundary for *future* work, not a description of an existing component.
