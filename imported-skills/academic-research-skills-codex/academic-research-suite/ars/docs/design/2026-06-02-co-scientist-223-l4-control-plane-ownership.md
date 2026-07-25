# Co-Scientist L4 — control-plane ownership: who may write, rank, route

| | |
|---|---|
| **Status** | Design lesson — **NOT a proposed feature** |
| **Issue** | [#223](https://github.com/Imbad0202/academic-research-skills/issues/223) |
| **Parent epic** | [#219](https://github.com/Imbad0202/academic-research-skills/issues/219) — Co-Scientist implications for ARS |
| **Paper anchor** | Gottweis et al. (2026), *Accelerating scientific discovery with Co-Scientist*, Nature. DOI [10.1038/s41586-026-10644-y](https://doi.org/10.1038/s41586-026-10644-y) |
| **Verified** | 2026-06-02 — verified against the codebase; two bindings corrected (see Verification note) |

This is a recorded boundary, not a roadmap item.

## Anchor

- **Paper**: The Context Memory component (paper L1349–1354) "stores and retrieves
  states of the agents and the system during the course of the computation"; the
  Meta-review agent (paper L1498–1503) appends feedback into other agents' prompts;
  the Supervisor agent routes work across the agent coalition.
- **ARS**: the Material Passport, with `state_tracker_agent` as the writer of
  pipeline state; per-stage checkpoint records; `pipeline_orchestrator_agent`-led
  routing under user confirmation. `POSITIONING.md` — "the human decides at every
  gate."

## Problem

Co-Scientist and ARS both have memory, both propagate information across agents,
and both route work between stages. The mechanisms look similar from the outside,
but they answer different questions:

- Co-Scientist's memory is a *shared mutable context* that agents read from and
  write to. The system optimizes for collective learning across the agent coalition.
- ARS's Material Passport is an *authority ledger*. Single-writer discipline
  (`state_tracker_agent`), append-only semantics, and audit-grade restart safety
  are load-bearing properties.

Importing a paper-derived mechanism without making the control-plane ownership
explicit silently shifts ARS from authority-ledger to shared-mutable-context. The
shift is invisible at the surface — the API looks the same — but the integrity
guarantees change.

## The three questions

Every paper-derived mechanism proposal must explicitly answer these. **This document
is their canonical reference.**

### 1. Who may WRITE to state?

ARS state writers:

- Pipeline state (Material Passport): `state_tracker_agent` is the sole writer of
  `pipeline_state`, `current_stage`, blocking flags, and materials. One narrow,
  controlled exception exists and proves the rule: `collaboration_depth_agent` may
  append only to its own `collaboration_depth_history[]` through a dedicated
  append-only interface, and never touches pipeline state. The discipline is
  "one writer per state region", not "literally one agent writes the whole
  passport".
- Checkpoint records: `pipeline_orchestrator_agent` after user confirmation.
- INSIGHT Collection: produced in the **RESEARCH stage** (`deep-research`, socratic
  mode — `socratic_mentor_agent` with the research-question and devil's-advocate
  agents), under the Stage-1 user-confirmed scope. It is a research-stage deliverable,
  not a write performed by `synthesis_agent`.

A new mechanism must either route its writes through these existing writers, or
declare a **new state region** with its own single writer and the same discipline
(audit log, append-only semantics, restart-safety guarantees). It may not add a
second writer to an existing region.

### 2. Who may RANK candidates?

Permitted shapes:

- AI enumerates without ranking (green line — see
  [L1](2026-06-02-co-scientist-220-l1-hidden-ranking.md)).
- AI surfaces scores to the user as advisory information; the user picks (yellow
  line, with L1's three conditions).

Rejected shape:

- AI ranks and the system selects top-K without showing the user the full set (red
  line — hidden culling).

### 3. Who may ROUTE to the next stage?

ARS routing writers:

- `pipeline_orchestrator_agent` computes the next stage from the pipeline
  configuration and the Material Passport state.
- The user confirms each transition at a checkpoint.
- No agent unilaterally decides what stage runs next.

A new mechanism must either route through the orchestrator, or document why a new
routing primitive does not violate the user-confirmation invariant.

## Why this distinction matters

The Co-Scientist paper presents shared mutable context as a strength. Within its
paradigm that is correct: hypothesis generation benefits from continuous information
flow across agents.

ARS's paradigm is different. The Material Passport's value comes precisely from its
single-writer discipline. The same property the paper considers limiting (state
cannot be freely mutated by every agent) is the property that makes ARS auditable.

Without the three questions above, a paper-derived mechanism can preserve the
surface API while silently undermining the discipline. The questions force the
design to be explicit about control-plane ownership before implementation begins.

## Application — when this is invoked

Any mechanism that writes state, ranks candidates, or routes between stages must
answer the three control-plane questions above. This document is their canonical
reference: a design that cannot answer them has not established its control-plane
ownership, and the boundary is unmet until it can.

See [L1](2026-06-02-co-scientist-220-l1-hidden-ranking.md) (who may rank) and
[L2](2026-06-02-co-scientist-221-l2-feedback-propagation.md) (who may mutate a
downstream prompt).

## Non-goals

- Not a prohibition on cross-agent information flow. Information flow is fine; the
  question is which agent has authority to mutate state, which to rank, which to
  route.
- Not a claim that Co-Scientist's shared-mutable-context design is wrong. It is the
  right design for hypothesis generation at the volume the paper operates.

## Verification note

Verified against the codebase 2026-06-02. Two corrections relative to the
originating issue:

1. **Naming.** The writer agent is `state_tracker_agent` (the bare `state_tracker`
   is its schema/role field name); the orchestrator is `pipeline_orchestrator_agent`.
   The single-writer discipline itself is verified (`state_tracker_agent` is sole
   writer of Material Passport state), as are orchestrator-written checkpoint records
   and orchestrator-led routing.
2. **INSIGHT Collection attribution.** The issue listed it as a `synthesis_agent`
   write "after Stage 1". Verified incorrect — INSIGHT Collection is a deep-research
   RESEARCH-stage artifact, and `synthesis_agent` is a Phase-3 integration agent that
   does not produce it. The "who may WRITE" list above reflects the corrected
   attribution.

The substance of the boundary (single-writer authority ledger, orchestrator-led
routing under user confirmation) stands; only these labels were tightened.
