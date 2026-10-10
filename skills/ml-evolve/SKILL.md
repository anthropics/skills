---
name: ml-evolve
description: Domain-agnostic evolutionary algorithm optimizer. Drives an OpenEvolve-style architecture × parameter search for ANY ML / algorithmic optimization problem. The skill body is fixed; scenario- and algorithm-specific information (objective, search space, branches, evaluator protocol, compute budget, etc.) is supplied through a standardized `task_spec.yaml` input contract — never inlined into this document. Use whenever the user asks to evolve / search / auto-tune an algorithm and provides (or can be guided to provide) a task spec.
---

# ml-evolve — Generic Algorithm Optimizer

## Operating Principle

This skill **does not contain task-specific reasoning, model suggestions, or
domain heuristics**. It is a fixed control loop. Anything that depends on the
user's problem (recsys two-tower retrieval, alpha factor, tabular classifier,
RL policy, prompt program, scheduler, …) MUST arrive as **invocation
parameters** via the `task_spec.yaml` contract defined in
[TASK_SPEC.md](TASK_SPEC.md). The body below is the same for every run.

When invoked:

1. Resolve the task spec (see *Input Resolution*).
2. Validate the spec against the schema. If any required field is missing or
   ambiguous, ask the user once for the missing slots and stop.
3. Execute the fixed *Standard Loop* below using only values from the spec.
4. Report progress strictly in the terms the spec declares (objective name,
   stage labels, branch names from the spec — never invented).

The skill MUST NOT introduce algorithm choices, model families, or search
directions that are not present in `task_spec.yaml` (or in the plan agent's
output, which itself is constrained by the spec). If the spec under-specifies
a decision, defer to the plan agent (`evolve.py plan`) rather than embedding
guidance here.

## Input Resolution

The task spec is resolved in this order; first hit wins:

1. CLI argument: `--task-spec <path>` if the invoking command passes one.
2. Environment variable: `$ML_EVOLVE_TASK_SPEC`.
3. File `task_spec.yaml` (or `.yml` / `.json`) in `$EVOLVE_PROJECT_DIR`.
4. File `task_spec.yaml` in the current working directory.

If none exist, prompt the user to provide one (offer
`templates/task_spec.example.yaml` as a starting point) and stop until they
do.

Once loaded, expose every spec field to subprocesses as
`ML_EVOLVE_SPEC_<UPPER_DOTTED_PATH>` environment variables, plus
`$ML_EVOLVE_SPEC_PATH` pointing at the resolved file. The evaluator and the
plan agent are the only components that may read these.

## Standard Loop (fixed)

The same eight steps run for every task. Stage labels, branch counts, trial
budgets, etc. come from the spec — the steps themselves do not change.

1. **Readiness** — `openevolve_local.py status`. Verify Python + project dir
   + presence of `evaluator.py` and `initial_program.py`.
2. **Init** — if no run exists:
   `evolve.py init --stage <spec.stages[0].name> --num-islands <spec.branches.count> --seed <spec.run.seed>`.
3. **Plan** — `evolve.py plan --force` once if `research_plan.md` is missing
   or scaffold-only. The plan agent reads `$ML_EVOLVE_SPEC_PATH`, the current
   leaderboard, and (if `spec.plan.allow_web` is true) the web. It writes one
   branch per island using **only** the branch slots / hypotheses / model
   family hints declared in `spec.branches[]`. It MUST NOT invent branches
   outside that list.
4. **Select** — `evolve.py select`. Read `mutation_request.md`,
   `research_plan.md`, `leaderboard.md`, `next_candidate.py`.
5. **Mutate** — edit only the EVOLVE block of `next_candidate.py`, staying
   inside the constraints in `spec.candidate.frozen` and `spec.candidate.allowed_mutations`.
6. **Parameter batch** —
   `evolve.py param-batch --stage <spec.stages.search> --trials <spec.search.param_trials> --startup-trials <spec.search.tpe_startup_trials> --parallel-workers <spec.compute.parallel_workers>`.
7. **Promote (periodic)** — every `spec.promotion.every` rounds, or when
   asked: `evolve.py promote --from-stage <spec.stages.search> --to-stage <spec.stages.promote> --top-k <spec.promotion.top_k> --parallel-workers <spec.compute.parallel_workers>`.
8. **Stop** — when any of `spec.budget.iterations`, `spec.budget.target_score`,
   or `spec.budget.patience` triggers.

`spec.run.replan_every`, if set, re-invokes the plan agent every K rounds
without changing the loop.

## Subprocess Tooling

The underlying scripts are reused as-is from the openevolve toolchain:

| Tool | Default path |
| --- | --- |
| `evolve.py`, `openevolve_local.py` | `$ML_EVOLVE_SCRIPTS_DIR` (default `~/.claude/skills/openevolve/scripts/`) |

To pin a specific copy, set `ML_EVOLVE_SCRIPTS_DIR`. The scripts themselves
are already domain-agnostic; do not modify them per-task — task variation
must flow through the spec.

## Evaluator Contract (unchanged across tasks)

`evaluator.py` must:

- accept a candidate path as `sys.argv[1]`;
- read `$ML_EVOLVE_SPEC_PATH` for protocol details (splits, score formula,
  invalid conditions) — these come from `spec.evaluator`;
- print exactly one JSON object on stdout whose last balanced `{...}` carries
  the metrics. Required key: `score` (or `spec.objective.score_key`). Optional
  framework keys: `invalid` (1.0 marks reject), `stage`, `error`.

The skill never edits the evaluator. If the user wants a different protocol,
they update `spec.evaluator` and (if the change is structural) the
`evaluator.py` they own — never this SKILL.md.

## What This Skill Will Refuse To Do

To keep the body stable and the spec authoritative:

- Suggest a model architecture, loss, sampler, or feature set that is not in
  `spec.branches[]` or `spec.candidate.allowed_mutations`.
- Hard-code domain knowledge (recsys-, vision-, NLP-, finance-, etc. specific
  advice) into the loop or the mutation request. Domain context lives in
  `spec.context` and is surfaced verbatim to the plan/mutation agent.
- Change stage semantics, score key, or branch count from the spec.
- Edit `evaluator.py`, the scripts under `$ML_EVOLVE_SCRIPTS_DIR`, or this
  SKILL.md as part of running a task.

If the user asks for one of these mid-run, the skill answers with: "that
belongs in `task_spec.yaml`; please update the spec and restart the run."

## Reporting

After each round, print:

- objective name + current best score + delta vs previous round;
- per-branch (per-island) best, using **the branch names from
  `spec.branches[]`**;
- last evaluator error, if any;
- next planned action.

Final report: `evolve.py report --stage <spec.stages.promote>` plus a
one-paragraph summary that names only objects from the spec (branches,
stages, metrics).

## References

- [TASK_SPEC.md](TASK_SPEC.md) — full schema of the standardized input.
- [METHODOLOGY.md](METHODOLOGY.md) — generic principles (leakage, staging,
  selection) applied to whatever spec the user passes.
- [FEATURES_AND_ACCELERATION.md](FEATURES_AND_ACCELERATION.md) — generic
  acceleration / parallelism guidance, parameterized by `spec.compute`.
- [templates/task_spec.example.yaml](templates/task_spec.example.yaml) — minimal
  spec the user can copy and fill in.

## Safety

- Never print secrets (`OPENAI_API_KEY`, DB URLs, tokens). Spec values
  marked `secret: true` are passed via env, never logged.
- Use `EVAL_TIMEOUT` from `spec.evaluator.timeout_sec` for evaluators that
  may hang.
- Do not push to non-ShopBack remotes. Do not commit anything that the spec
  marks confidential.
