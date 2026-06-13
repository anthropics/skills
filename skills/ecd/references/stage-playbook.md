# Stage Playbook v2.1

## Tier Model (v1.1)

ECD v1.1 uses a 3-question complexity classifier to route tasks into three tiers. This playbook documents all three tiers. **L3 (Full) behavior is identical to ECD v1.0.**

### Tier Selection Summary

| Tier | When | Stages | Subagents | Token Target |
|------|------|--------|-----------|-------------|
| **L1 Lite** | ≤3 files, UI-only risk, clear requirements | A-Lite → J-Lite → code → achieve-Lite | 0 | 15k-30k |
| **L2 Standard** | 4-10 files, moderate risk, mostly clear | A → B → C → D(opt) → E(slim) → H(opt) → J → code → achieve | 0-2 | 35k-55k |
| **L3 Full** | >10 files OR high risk OR ambiguous reqs | A → B → C → D → E → F → G → H → J → code → achieve | 5 (all mandatory) | 65k-105k |

### Lite Template Mapping

When the tier is L1, use the `_lite` template variants where they exist:
- `stage-a-lite.md` instead of `stage-a.md`
- `stage-j-lite.md` instead of `stage-j.md`
- `code-handoff-lite.md` instead of `code-handoff.md`
- `constraint-ledger-lite.md` instead of `constraint-ledger.md`

### Micro-Task Fast Path `[v1.2]`

When ALL of the following conditions are met, skip pre/plan entirely and proceed directly to code:

- Estimated code change: **<10 lines**
- Safety/correctness risk: **L1** (UI style/text/layout only)
- Requirement clarity: **clear and unambiguous**

Micro-task behavior:
- No bundle generation, no subagent spawning, no approval pack rendering
- Execute the code change directly → quick verification → done
- Expected Token: **3k-8k**
- If any doubt about the classification, fall back to normal L1-Lite flow

Typical micro-tasks: fixing typos (T02), adjusting font sizes (T06), adding placeholders (T15), modifying hover effects (T17)

## Shared Ledger

`05-constraint-ledger.md` is the single source of truth for:

- retained goal
- confirmed facts
- challenged claims
- frozen constraints
- dropped options
- risks
- dependency chain
- verification semantics
- stage references

After approval closes, user interaction should usually drop sharply. B-H and J should converge in the background unless a new high-impact ambiguity or contradiction appears.

## A-Lite / Preprocess (Lite) `[L1]`

For L1 tasks only. A streamlined version of Stage A that freezes scope without deep semantic excavation.

- treat the raw request as unreliable input (same as Full A)
- inspect repo and workspace facts before asking anything
- ask **maximum 3** clarification questions (vs unlimited in Full A) that maximize semantic coverage
- freeze only what code needs to know: goal, scope boundary, acceptance criteria
- skip: divergence (B), deep decomposition (C), adversarial review (D/G/H), companion docs (91-99)

Required output:
- `user_stated_request`
- `reframed_request`
- `retained_scope`
- `excluded_scope`
- `acceptance_checks` (3-5 concrete checks)
- `key_assumptions`
- `frozen_for_code`

Exit gate:
- the reframed goal and scope boundary are clear enough for execution
- the user has explicitly approved the compact approval pack
- remaining unknowns are genuinely low-impact implementation details

## A / Preprocess `[L2, L3]`

- treat the raw request as unreliable input
- inspect repo and workspace facts before asking the user anything
- extract the likely real goal
- assume the user may not understand their own real goal, constraints, or desired outcomes yet
- surface ambiguity, wrong assumptions, missing facts, hidden preferences, anti-goals, and unstated constraints
- produce clarification questions that maximize semantic coverage before approval
- interrogate across examples, counterexamples, workflows, priorities, tradeoffs, failure handling, edge cases, and acceptance meaning
- stop after producing an approval-ready reframing package with saturated semantic coverage

Required output:

- `user_stated_request`
- `ambiguity_points`
- `dubious_claims`
- `factual_gaps`
- `hidden_assumptions`
- `suspected_real_goals`
- `scenario_fragments`
- `success_signals`
- `non_goals`
- `follow_up_questions`
- `blocking_unknowns`
- `reframed_request`

Exit gate:

- the request has been reframed around the likely real goal
- the user has been questioned enough that hidden product meaning is unlikely to surprise later stages
- the approval pack can be shown to the user

## B / Divergence `[L2, L3]`

- generate materially different options, not style variants
- make each option explain which blind spots it covers
- retain exactly one path

## C / Requirements `[L2, L3]`

- decompose the retained path into requirement units
- freeze implementation-relevant semantics
- shape requirement units so they can later map cleanly into implementation units or task batches
- identify interfaces, validation targets, and non-goals
- capture requirement-to-task traceability and likely cut lines without prematurely inventing file order
- make the package specific enough that a coder will not invent product meaning

## D / Critique `[L2, L3]`

**L2:** Optional. Run only if requirement_units > 3 or cross-cutting concerns exist.
**L3:** Mandatory. Full independent critique with spawned subagent.

- spawn one independent critique agent (mandatory for L3, optional for L2)
- attack vague, contradictory, or wasteful requirements
- remove pseudo-requirements and bad decompositions

## E / Closure `[L2, L3]`

**L2 (Slim):** Identify and resolve high-impact dependency gaps only. Skip execution chain compilation.
**L3 (Full):** Complete dependency chain with execution ordering.

- complete the end-to-end dependency chain
- convert resolved dependencies into a dependency-aware execution chain for later phases, batches, and tasks
- remove hidden prerequisites
- remove hidden prerequisites between planned units, batches, and verification steps
- leave no high-impact dependency gaps for `code`

## F / Probes `[L3]`

- run real executable validation whenever possible
- prefer repo inspection, scripts, tests, experiments, and environment checks
- record hypothesis, method, expected signal, kill criteria, and result

## G / Red-Blue `[L3]`

- spawn independent red and blue agents
- red attacks edge cases, abuse paths, dependency breaks, and invalid states
- blue mitigates, constrains, or accepts residual risk explicitly

## H / Review `[L2, L3]`

**L2:** Optional. Run if handoff has >3 implementation units.
**L3:** Mandatory. Full independent review with spawned subagent.

- spawn one independent review agent (mandatory for L3, optional for L2)
- reject the package if the next coder would still need to invent:
  - product meaning
  - validation meaning
  - state behavior
  - dependency behavior
- verdict must be one of:
  - `approved`
  - `approved_with_conditions`
  - `rejected`

## J-Lite / Compile For Code (Lite) `[L1]`

For L1 tasks only. Compiles A-Lite output directly into a minimal handoff.

- absorb A-Lite output directly (no B-H stages exist)
- compile a minimal `90-code-handoff.md` containing only:
  - `repo_grounding`
  - `frozen_product_decisions`
  - `file_plan`
  - `implementation_units` (simplified: goal + files + verification per unit)
  - `verification_commands`
  - `acceptance_checks`
  - `code_ready`
- skip all companion docs (91/92/95/96/98/99)
- only emit `90-code-handoff.md` and `97-code-preflight.md`
- set `code_ready=true` only when the minimal handoff is sufficient for a coder

## J / Compile For Code `[L1, L2, L3]`

- spawn one independent compile-for-code agent
- absorb the retained A-H result into companion docs and the final code-ready package
- compile execution phases, code batches, and implementation units in dependency order
- compile `97-code-preflight.md` as the shared execution workboard the user and coder will maintain before and during `/code`
- compile review conditions and residual blockers into an explicit code-ready or scaffold verdict
- make the package exportable to OpenSpec-style `proposal/design/tasks` without reinterpretation
- keep `90-code-handoff.md` as the only truthful `/code` entrypoint
- emit companion docs `91/92/95/96/97/98/99` as inspection surfaces, not alternate sources of truth

## Code Handoff `[L1, L2, L3]`

The handoff must freeze:

- approval basis
- repo grounding
- product semantics
- domain/data/UI contracts
- function-level contracts
- file plan
- implementation units
- verification commands
- browser checks
- acceptance checks
- reentry triggers

`code_ready=true` is allowed only when those are explicit and unresolved gaps are empty.

Each implementation unit must also freeze:

- exact changes
- task-ready done signals
- tests to add or update

## `/code`

- read only the handoff plus explicit references
- execute in unit order
- verify as you go
- stop and reenter planning if semantics are still missing

## achieve-Lite / Closure (Lite) `[L1]`

For L1 tasks only. Lightweight closure based on the minimal handoff.

- run the verification command from the handoff
- check that first-open UX is not obviously broken
- verdict: `achieved` or `not_achieved`
- archive status: `archived` or `left_open`
- write `Runs/<run-id>/03-achieve.md`
- do not weaken acceptance criteria after the fact
- do not call achieved if first-load experience is broken
