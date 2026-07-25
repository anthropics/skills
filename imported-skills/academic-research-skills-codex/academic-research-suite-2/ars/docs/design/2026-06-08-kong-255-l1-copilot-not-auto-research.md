# Kong L1 — copilot ≠ auto-research is a state-authority line, not a slogan

| | |
|---|---|
| **Status** | Design lesson — **NOT a proposed feature** |
| **Parent epic** | [#255](https://github.com/Imbad0202/academic-research-skills/issues/255) — Kong et al. 2026 auto-research survey implications for ARS |
| **Paper anchor** | Kong et al. (2026), *AI for Auto-Research: Roadmap & User Guide*, arXiv:2605.18661 |
| **Verified** | 2026-06-08 — verified against the tracked repo (see Verification note) |

This is a recorded boundary, not a roadmap item. It exists so that future work and
reviews apply the same line consistently.

## Anchor

- **Paper**: Kong et al. survey AI auto-research systems organised around eight
  stages × four phases of the research lifecycle — idea generation, autonomous
  experimentation, end-to-end paper pipelines, autonomous peer review, Paper2X
  dissemination. The paper's own cross-cutting conclusion (§7.3.2, §7.4.8) is that
  human-governed collaboration is the most reliable deployment mode and that fully
  autonomous science is not a credible near-term objective.
- **ARS**: `POSITIONING.md` — "the human decides at every gate" (Design philosophy);
  ARS is a human-led copilot, not an autonomous paper-writing system.

## Problem

ARS and an auto-research system can look superficially alike. Both use multi-agent
orchestration, a layered architecture, and simulated critique (ARS runs a five-
reviewer panel plus a Devil's Advocate). A naive cross-walk could read these surface
features as "ARS is most of the way to auto-research" — or, in the other direction, a
reviewer could wave through a new agent on the grounds that "we already have many
agents, one more is fine."

Both reads miss the actual line. The line is not how many agents there are or how
layered the architecture is. It is **who controls the next research-state
transition** — who gets to create, select, execute, or advance a research object of
record, and whether the scholar saw and confirmed the relevant state first.

## Boundary

### The operational review test

Any PR that adds or extends an agent, mode, or automation is reviewed against this
question before merge:

> Does this change let ARS create, select, execute, or advance a **research object of
> record** — hypothesis, RQ, evidence set, experiment result, claim, manuscript
> section, or dissemination artifact — **without** an explicit scholar-authored seed
> or scholar confirmation after inspecting the relevant state?

- **If yes** → it crosses into auto-research and is rejected, regardless of how
  useful or well-tested the mechanism is.
- **If no** → it stays copilot/advisory and is evaluated on its own merits.

### The seams where this is invoked

These are the specific surfaces where ARS could drift across the line if a change
were not tested against the question above:

1. **Multi-agent orchestration.** Adding agents is fine; letting an agent advance the
   pipeline state (select the next stage, accept its own output as final) without a
   scholar gate is not. Mandatory checkpoints are the gate.
2. **Layered architecture.** Layers may transform and annotate; they may not become a
   closed loop that produces a submission-ready object the scholar never confirmed.
3. **Simulated critique.** The reviewer panel and Devil's Advocate critique the
   scholar's draft; they do not author, accept, or act on their own critique. AI
   review is advisory input to the scholar, never a substitute for the scholar's
   decision (and never a substitute for actual peer review).

### What keeps ARS on the copilot side

Three first-class architectural commitments, all already present:

- **Mandatory checkpoints.** FULL and MANDATORY checkpoints cannot be skipped; "full
  mode" is full-pipeline execution, not full autonomy.
- **Scholar-as-author.** The researcher remains the author of every claim, citation,
  experimental design, and interpretation. AI assists; it does not author.
- **Disclosure, not detection.** ARS makes AI assistance visible and discloseable; it
  does not position itself as an autonomous producer whose output passes as
  unassisted.

## Why this distinction matters

Surface-level rejection ("multi-agent systems are auto-research, avoid them") would
throw away orchestration, layering, and simulated critique — all of which are useful
*when the scholar owns every state transition*. State-authority rejection ("no AI-
owned transition of a research object of record") keeps those primitives while
holding the line.

The reverse is equally true. Permitting a new agent on the grounds that "we already
have many" silently re-introduces the risk: the question is never the count, it is
whether the new agent can advance state the scholar has not seen and confirmed.

## Relationship to the sibling Co-Scientist docs

The Co-Scientist analysis recorded a related boundary from a different angle — who may
*rank* and whether the user sees the full candidate set. Those docs and this one share
the same underlying principle (the scholar must see and own the state the system acts
on):
[Co-Scientist L1](2026-06-02-co-scientist-220-l1-hidden-ranking.md) (hidden ranking),
[L2](2026-06-02-co-scientist-221-l2-feedback-propagation.md) (feedback propagation),
[L3](2026-06-02-co-scientist-222-l3-transfer-matrix.md) (mechanism transfer),
[L4](2026-06-02-co-scientist-223-l4-control-plane-ownership.md) (who may write / rank /
route). The Kong [L2](2026-06-08-kong-255-l2-advisory-not-generation.md) sharpens the
specific advisory-vs-generation seam for research questions.

## Verification note

- **Verifiable (2026-06-08, against the tracked repo):** first-party ARS does not
  implement an end-to-end autonomous research pipeline, an idea-generation agent, a
  Paper2X generator, an autonomous experiment executor, or a wet-lab automation API.
  "The human decides at every gate" is present in `POSITIONING.md`; the mandatory
  checkpoints are real (`academic-pipeline/SKILL.md`). The Kong-derived features that
  did ship — wording-pattern advisory (#257) and experiment provenance intake (#260)
  — are advisory / provenance gates, not autonomous generation or execution layers. A
  targeted review of the first-party implementation, agent prompts, and schemas found
  no autonomous mechanism; the only `wet_lab` / slides / experiment references are
  domain-evidence-profile labels or separate, non-ARS companion workflows, not
  automation surfaces.
- **Design commitment (not a guarantee):** this doc records a first-party scope
  boundary and a review criterion for future changes. It is not a proof that the
  software cannot be modified, a guarantee about forks or downstream deployments, or a
  runtime enforcement mechanism.
