# Co-Scientist L2 — unapproved feedback propagation is the red line, not feedback propagation itself

| | |
|---|---|
| **Status** | Design lesson — **NOT a proposed feature** |
| **Issue** | [#221](https://github.com/Imbad0202/academic-research-skills/issues/221) |
| **Parent epic** | [#219](https://github.com/Imbad0202/academic-research-skills/issues/219) — Co-Scientist implications for ARS |
| **Paper anchor** | Gottweis et al. (2026), *Accelerating scientific discovery with Co-Scientist*, Nature. DOI [10.1038/s41586-026-10644-y](https://doi.org/10.1038/s41586-026-10644-y) |
| **Verified** | 2026-06-02 — fully verified against the codebase (see Verification note) |

This is a recorded boundary, not a roadmap item.

## Anchor

- **Paper**: The Meta-review agent (paper L1498–1503, L1762–1775) "generates
  feedback applicable to all agents, which is simply appended to their prompts in
  the next iteration — a capability facilitated by the long-context search and
  reasoning capabilities of the underlying Gemini models."
- **ARS**: `POSITIONING.md` — "Failure modes are made visible, not hidden." The
  7-mode AI Research Failure Mode Checklist (v3.2) and Reviewer Calibration Mode
  exist so the user can see where the AI might be wrong.

## Problem

Co-Scientist's Meta-review agent enables learning across iterations without
back-propagation: it observes patterns from a run's reviews and tournament debates,
then appends synthesized feedback into the system prompts of other agents for
subsequent iterations. The mechanism is elegant for the paper's hypothesis-
generation paradigm.

The same mechanism, imported into ARS unmodified, would silently mutate the
behavior of downstream agents in ways the user cannot see. A user observing the
output cannot tell whether a synthesis-stage agent is following its baseline prompt
or operating under a meta-review patch derived from upstream stages. That is hidden
behavior change, which conflicts with ARS positioning.

The conflict is not feedback propagation itself. The conflict is **unapproved**
feedback propagation.

## Boundary

### Red line — DO NOT IMPLEMENT

An observer collects patterns from upstream stages → the system auto-appends
synthesized feedback to a downstream agent's prompt → the user is not informed.

This is invisible behavior change. The user's confidence in the downstream output
assumes the baseline prompt is in effect, but the actual prompt has been mutated.

### Yellow line — implementable with a user-approval gate

An observer collects patterns from upstream stages → the system surfaces the
patterns as an advisory artifact at the next checkpoint → the user reviews and
approves (or rejects, or edits) → THEN the approved feedback is injected into the
downstream agent's prompt.

The user-approval gate is load-bearing. It is the difference between "AI helps the
user calibrate the system" (yellow) and "AI silently calibrates the system" (red).

### Green line — preferred default

Observer surfaces patterns as an advisory artifact only. The user reads the
artifact, optionally adjusts their own instructions in the next round, but no
automatic prompt injection occurs.

## Why this distinction matters

The Co-Scientist paper presents the no-back-prop feedback loop as a strength: it
scales learning without training, requires no fine-tuning, and operates within the
same context window. All three are true.

For ARS, the same property is a liability. Without the user-approval gate, a user
cannot perform the integrity check that `POSITIONING.md` promises ("Failure modes
are made visible"). The user's understanding of why a given output looks the way it
does must remain reconstructible from the artifacts the user has seen.

## Application — when this is invoked

For any ARS feature that proposes cross-stage learning, observer agents, or feedback
propagation, the design review must answer: does the propagated feedback reach a
downstream agent's prompt without passing a user-visible approval checkpoint? If
yes, it crosses the red line. A monotonic provenance flag carried forward unchanged
(see Verification note) is not feedback propagation; an observer that *rewrites a
downstream agent's instructions* is. The boundary is the prompt mutation, not the
information flow.

See [L1](2026-06-02-co-scientist-220-l1-hidden-ranking.md) for the
visible-to-the-user principle this shares, and
[L4](2026-06-02-co-scientist-223-l4-control-plane-ownership.md) for who may write
state.

## Verification note

Verified against the codebase 2026-06-02. "Failure modes are made visible, not
hidden" is present in `POSITIONING.md`; the 7-mode AI Research Failure Mode
Checklist (v3.2) and Reviewer Calibration Mode both exist
(`academic-pipeline/references/ai_research_failure_modes.md`,
`academic-paper-reviewer/references/calibration_mode_protocol.md`). No mechanism in
ARS auto-appends synthesized feedback into a downstream agent's prompt across
iterations. The only cross-stage value carried forward is a monotonic `slr_lineage`
provenance flag (it records that a run originated in a systematic-review context;
it does not mutate any agent's prompt). So the claim "ARS does not silently
propagate feedback" is a verified fact. This doc records a boundary for future
work.
