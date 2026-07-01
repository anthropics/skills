# ECD Stage Model

## Tier Model `[v1.1]`

ECD v1.1 uses a 3-question complexity classifier to route tasks into three execution tiers. This prevents simple tasks from suffering the full 10-stage pipeline.

### Complexity Classifier

Before any stage executes, answer these 3 questions silently:

| Question | L1 | L2 | L3 |
|----------|----|----|-----|
| **Q1** Code impact surface | ≤3 files | 4-10 files | >10 files |
| **Q2** Security/correctness risk | UI-only (styling, copy) | Functional logic, APIs | Data loss, auth, payments, PII |
| **Q3** Requirement clarity | Clear, unambiguous | Some details unspecified | Ambiguous ("make it fast") |

`Final tier = max(Q1, Q2, Q3)`. Q3 "ambiguous" → force L3. Greenfield → Q1 defaults to L2. User can override: `--tier lite|standard|full`.

### Tier Definitions

| Tier | Trigger | Stages | Subagents | Token Budget | Example Tasks |
|------|---------|--------|-----------|-------------|---------------|
| **L1 ECD-Lite** | max score = 1 | A-Lite → J-Lite → code → achieve-Lite | 0 | 15k-30k | Dark mode toggle, bugfix, copy change, single-component edit |
| **L2 ECD-Standard** | max score = 2 | A → B → C → D(opt) → E(slim) → H(opt) → J → code → achieve | 0-2 optional | 35k-55k | New API endpoint, medium feature, multi-file change |
| **L3 ECD-Full** | max score = 3 | A → B → C → D → E → F → G → H → J → code → achieve | 5 mandatory | 65k-105k | Auth system, architecture change, security-sensitive, ambiguous reqs |

**L3 is identical to ECD v1.0.** Missing tier fields in existing bundles default to L3.

### Lite Stage Variants

- **A-Lite**: Max 3 clarification questions. Freezes reframed goal, scope, acceptance checks, key assumptions. Skips divergence and deep decomposition.
- **J-Lite**: Compiles A-Lite directly into minimal `90-code-handoff.md`. No companion docs (91/92/95/96/98/99).
- **achieve-Lite**: Run verification command → check first-open UX → verdict. Simplified evidence-based closure.

### L2 Optional Stage Rules

- **D (Critique)**: Run if requirement_units > 5 or cross-cutting concerns exist
- **H (Review)**: Run if handoff has >3 implementation units
- **E (Closure)**: Slim mode — resolve only high-impact dependency gaps, skip execution chain compilation

## Stage Overview

ECD separates the delivery loop into ownership boundaries. Each boundary exists to stop one class of semantic drift.

| Phase | Tiers | Owner | Primary purpose | Main artifact | Real subagents required |
| --- | --- | --- | --- | --- | --- |
| `pre` / A | L1,L2,L3 | parent model | interrogate the request and freeze the approval target | `10-a-preprocess.md` | optional support agents only |
| B | L2,L3 | parent model | generate materially different retained paths | `20-b-divergence.md` | no |
| C | L2,L3 | parent model | freeze requirement units and future coding cut lines | `30-c-requirements.md` | no |
| D | L2,L3 | critique agent + parent model | independently attack vague or wasteful requirements | `40-d-critique.md` | L3: yes / L2: optional |
| E | L2,L3 | parent model | close dependency gaps and execution prerequisites | `50-e-closure.md` | no |
| F | L3 | parent model | run reality probes against the repo and environment | `60-f-probes.md` | no |
| G | L3 | red agent + blue agent + parent model | attack and defend the retained path | `70-g-red-blue.md` | L3: yes |
| H | L2,L3 | review agent + parent model | decide whether the next coder would still need to invent meaning | `80-h-review.md` | L3: yes / L2: optional |
| J | L1,L2,L3 | compile-for-code agent + parent model | compile A-H into a code-ready package | `98-j-compile-for-code.md`, `99-code-handoff.md` | L3: yes / L2: optional / L1: no |
| `code` | L1,L2,L3 | coding model | execute only from the frozen handoff | `Runs/<run-id>/00-code-run.md` | no |
| `achieve` | L1,L2,L3 | closure model | decide whether the run truly achieved acceptance | `Runs/<run-id>/03-achieve.md` | no |

## Shared Truth Surfaces

Two files dominate the workflow:

- `05-constraint-ledger.md`: the shared planning truth surface
- `90-code-handoff.md`: the only truthful `/code` entrypoint

The companion bundle exists to inspect and operationalize those truths:

- `91-canonical-contracts.md`
- `92-constraint-crosswalk.md`
- `95-execution-manifest.md`
- `96-code-batches.md`
- `97-code-preflight.md`
- `98-j-compile-for-code.md`
- `99-code-handoff.md`

## Stage A-Lite `[L1]`

**Tiers:** L1 only.

A streamlined preprocess for simple tasks. Max 3 clarification questions.

### Input

- raw request
- repo facts
- local docs, tests, configs

### Output

- reframed request
- retained scope / excluded scope
- acceptance checks (3-5)
- key assumptions
- compact approval pack

### Exit gate

User explicitly approves the compact approval pack. Remaining unknowns are low-impact implementation details.

### Why A-Lite exists

For tasks like "add a dark mode toggle," the full Stage A interrogation (7+ questions, deep semantic excavation) is overkill. A-Lite freezes just enough semantics for safe execution.

## `pre` And Stage A `[L2, L3]`

`pre` owns the approval gate.

### Input

- raw request
- repo facts
- local docs, tests, configs, and product clues

### Output

- a reframed request
- ambiguity list
- hidden assumptions
- scenario fragments
- approval pack

### Exit gate

You do not leave Stage A until the user explicitly approves the reframed direction.

### Why A exists

If the planning system asks too little here, every later stage becomes cleanup for hidden semantics.

## B / Divergence `[L2, L3]`

Stage B forces option space before convergence.

### Input

- approved Stage A understanding

### Output

- materially different options
- retained option id
- dropped options

### Exit gate

Exactly one retained path survives. Style variants do not count as real options.

## C / Requirements `[L2, L3]`

Stage C turns the retained path into implementation-relevant requirement units.

### Input

- retained option
- constraint ledger

### Output

- requirement units
- interface contracts
- validation targets
- frozen terms

### Exit gate

The package must be specific enough that a coder will not invent product meaning later.

## D / Critique `[L2, L3]`

Stage D is the first independent attack. **Mandatory for L3, optional for L2** (run if >5 requirement units or cross-cutting concerns).

### Input

- retained requirement package

### Output

- critique findings
- conflicts
- dropped pseudo-requirements
- resolution decisions

### Exit gate

If a critique agent is unavailable, the stage must be marked `blocked_by_agent_unavailable`, not silently completed.

## E / Closure `[L2, L3]`

Stage E closes dependency gaps. **L2 (Slim):** resolve only high-impact gaps, skip execution chain. **L3 (Full):** complete dependency chain with execution ordering.

### Input

- retained requirements
- critique decisions

### Output

- end-to-end dependency chain
- dependency gap resolutions
- completion chain

### Exit gate

No unresolved high-impact dependency remains for coding.

## F / Probes `[L3]`

Stage F confronts the plan with repo and environment reality.

### Input

- hypotheses about the target repo, commands, or environment

### Output

- probes
- discarded paths
- surviving paths

### Exit gate

A complete stage needs executable evidence or an explicit inability-to-probe explanation.

## G / Red-Blue `[L3]`

Stage G forces adversarial pressure before approval.

### Input

- retained path
- dependency chain
- probe evidence

### Output

- red-team attacks
- blue-team mitigations
- residual risks

### Exit gate

The bundle must either mitigate attacks or name the residual risk explicitly.

## H / Review `[L2, L3]`

Stage H is the coding-readiness gate. **Mandatory for L3, optional for L2** (run if handoff has >3 implementation units).

### Input

- the full A-H package

### Output

- verdict
- blockers or approval conditions
- rationale
- reentry stage if rejected

### Exit gate

If the next coder would still need to invent product semantics, validation meaning, state behavior, or dependency behavior, H must reject the package.

## J-Lite / Compile For Code `[L1]`

**Tiers:** L1 only.

Compiles A-Lite output directly into a minimal code-ready handoff.

### Input

- approved A-Lite output
- repo facts

### Output

- minimal `90-code-handoff.md` (no companion docs)
- `97-code-preflight.md`

### Exit gate

`code_ready=true` only when the minimal handoff is sufficient for a coder to implement without inventing product meaning.

## J / Compile For Code `[L1, L2, L3]`

Stage J turns planning truth into coder-operable artifacts.

### Input

- converged A-H package
- current handoff state

### Output

- code-ready verdict
- companion docs
- final handoff summary
- reopen stage if blocked

### Exit gate

`code_ready=true` is allowed only when the next coding model can implement without reopening product meaning.

## achieve-Lite `[L1]`

**Tiers:** L1 only.

Lightweight closure for L1 tasks. Based on the minimal handoff.

### Input

- validated L1 bundle
- latest code run evidence
- acceptance checks
- verification evidence

### Output

- achieve verdict: `achieved` / `not_achieved`
- archive status: `archived` / `left_open`
- `Runs/<run-id>/03-achieve.md`

### Exit gate

Acceptance checks pass and first-open UX is not obviously broken.

## `/code` `[L1, L2, L3]`

`/code` is execution, not interpretation.

### Required entry conditions

- a bundle path or handoff path exists
- `90-code-handoff.md` is present
- `ecl.code_handoff.code_ready=true`
- repo target exists

### Required behavior

- read the handoff and explicit references only
- execute implementation units in order
- verify after each unit
- update `97-code-preflight.md`
- record `00-code-run.md` and `01-verification.md`

### Reentry rule

If a high-impact ambiguity appears, stop and reopen the earliest broken stage.

## `/achieve` `[L1, L2, L3]`

`/achieve` decides whether evidence supports closure.

### Input

- validated bundle
- latest truthful code run
- acceptance checks
- verification evidence

### Output

- achieve verdict
- archive status
- archive reason
- next actions

### Exit gate

If acceptance or first-open quality fails, the case stays open.
