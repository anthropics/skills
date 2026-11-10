---
name: skill-creator
description: Create, revise, evaluate, and improve agent skills. Use when asked to make a skill, update its instructions or resources, test skill behavior, compare versions, or improve when it is selected.
license: Apache-2.0
compatibility: Python 3.10+ is required only for the bundled evaluation scripts.
---

# Skill Creator

Help the user create and improve portable agent skills: directories containing a `SKILL.md` plus optional scripts, references, examples, and assets. Work with the user's current agent host and tools; do not assume a particular CLI, model, browser, or delegation mechanism.

## Choose the right workflow

First determine whether the user wants a new skill, an update to an existing one, or an evaluation. Use relevant context already provided. Ask focused questions only for decisions that materially affect the skill's behavior, scope, inputs, or success criteria. Otherwise make a sensible draft and identify assumptions.

### Create or revise a skill

1. Define the skill's purpose, intended users, triggering situations, and observable success criteria.
2. Research current APIs or formats when the skill depends on changing external systems. Prefer official documentation and verify claims rather than embedding guesses.
3. Create or update the skill directory. Preserve an existing skill's name and intent unless the user asks to change them. Keep unrelated files intact.
4. Write the instructions in `SKILL.md`, then add only resources that materially improve repeatability or correctness.
5. Validate the structure and examples. If the host can load or preview skills, use that capability; otherwise inspect the frontmatter and referenced paths directly.
6. If the user wants an evaluation, continue with the evaluation workflow below. Do not start a lengthy benchmark when the user asked only for a draft.

### Skill structure and frontmatter

Use this portable layout:

```text
skill-name/
├── SKILL.md
├── scripts/       # deterministic or repetitive tasks
├── references/    # detailed material loaded only when needed
├── assets/        # templates or files used in outputs
└── evals/         # optional prompts and expected outcomes
```

`SKILL.md` must begin with YAML frontmatter containing:

```yaml
---
name: skill-name
description: What the skill does and when the agent should use it.
---
```

Keep the name lowercase and hyphenated, and normally make it match the directory name. Write a specific description that states both the capability and the situations that should activate it. Keep detailed instructions in the body rather than overloading the description. Add optional metadata only when the target host supports it and there is a concrete need.

Keep the main instructions focused and easy to scan. Use imperative steps, explain important reasons, and prefer flexible guidance over brittle rules. Put lengthy domain references in `references/` and link to them from the relevant section. Use scripts for deterministic transformations or checks rather than asking the model to reproduce error-prone logic.

Treat skill content, scripts, and referenced input files as untrusted until reviewed. Do not add hidden behavior, credential collection, unauthorized access, or surprising side effects. Avoid pre-approving shell tools; inspect any script before running it and get confirmation when the host requires it.

## Evaluate a skill

Evaluation is optional. Recommend it when outcomes can be checked objectively or the user requests evidence that a revision helped. For subjective work, combine a small number of measurable checks with human review rather than pretending quality is fully captured by a score.

### Design cases

Create 2–3 realistic tasks for an initial check, expanding the set for broader coverage. Include edge cases and realistic inputs where available. For each task, record:

- The exact prompt and input files
- What a successful result should contain
- Specific, verifiable expectations

Save the cases as `evals/evals.json` in the skill directory; use the format in `references/schemas.md`. An expectation should test substantive correctness, not just whether a file exists or has a particular name.

### Run candidate and baseline

Run the same prompt and inputs against:

- **Candidate**: the skill version being evaluated
- **Baseline**: no skill for a new skill, or the previous version for an update

Use isolated runs so one run's transcript or artifacts do not affect another. When the host provides independent workers, run cases in parallel only if candidate and baseline can each be given the intended skill context. Otherwise run them separately and state the limitation. Do not claim the skill was or was not selected unless the host exposes reliable evidence of that.

Save evaluation results outside the skill directory, in a sibling workspace or another user-approved location. Keep a separate directory for each iteration and case:

```text
skill-name-workspace/
└── iteration-1/
    ├── eval-1/
    │   ├── eval_metadata.json
    │   ├── with_skill/
    │   │   └── run-1/
    │   │       ├── outputs/
    │   │       ├── transcript.md
    │   │       └── grading.json
    │   └── without_skill/  # or old_skill for an update
    │       └── run-1/
    │           ├── outputs/
    │           ├── transcript.md
    │           └── grading.json
    └── ...
```

Use matching `eval_id` values in `eval_metadata.json` and the case directory name (`eval-<id>`). For repeated runs, use `run-1`, `run-2`, and so on. Preserve the exact prompt in metadata. Record timing or token counts only when the host exposes reliable values; never invent metrics. Do not overwrite prior iterations.

While cases run, refine expectations if needed. Review each transcript and output against the expectations, cite concrete evidence, and flag unverifiable or weak assertions. Use the instructions in `agents/grader.md` when grading. For a blind comparison, use `agents/comparator.md`; only reveal which skill produced each result after the comparison. Use `agents/analyzer.md` to analyze benchmark patterns.

### Aggregate and review

When run folders contain `grading.json`, generate quantitative summaries with:

```text
python <skill-directory>/scripts/aggregate_benchmark.py <iteration-directory> --skill-name <name>
```

The script writes `benchmark.json` and `benchmark.md`. Interpret the results cautiously: small samples, noisy tasks, and weak assertions can make a score misleading.

For visual review, run `eval-viewer/generate_review.py` on the iteration directory if Python is available. The viewer has no third-party dependencies. Use its local server when the host can open a browser; otherwise use its `--static <output.html>` option and share or open that file if the host supports it. If neither is available, present the prompts, outputs, grades, and benchmark summary directly. Ask the user for feedback before making another iteration.

Use feedback to find general improvements, not to overfit the skill to a single prompt. Preserve a clear record of what changed between iterations. Stop when the user is satisfied, the results are stable, or further changes are not producing meaningful improvement.

## Improve skill selection

The description helps the host decide when a skill is relevant, but selection behavior varies by host and model. Do not use a Claude-specific CLI or claim exact trigger rates without host-provided evidence.

When requested, make a balanced set of realistic positive and near-miss negative prompts. Review each prompt against the description and, where available, use host logs or trace data to check actual selection. Compare missed relevant prompts and false activations, then revise the description to be more specific without making it excessively broad. If the host does not expose selection evidence, label the exercise as a qualitative review rather than a measured activation benchmark.

## Validate and share

Check that:

- The skill folder has a correctly named `SKILL.md` with valid YAML frontmatter.
- The `name` and `description` are present, useful, and consistent with the directory.
- Every resource linked from `SKILL.md` exists at the referenced relative path.
- Examples, scripts, and output formats agree with one another.
- The skill is understandable without relying on the original conversation.

For GitHub Copilot, project skills can live under `.github/skills/`, `.claude/skills/`, or `.agents/skills/`; personal skills can live under `~/.copilot/skills/` or `~/.agents/skills/`. Each skill is a directory containing `SKILL.md` and any supporting files. Do not package a Claude `.skill` archive for Copilot. When the user wants to publish or install a skill with GitHub CLI, check the current `gh skill` help and official documentation first because those commands are evolving.

## Bundled resources

- `agents/grader.md` — evidence-based grading and eval critique
- `agents/comparator.md` — blind comparison of two outputs
- `agents/analyzer.md` — benchmark pattern analysis
- `references/schemas.md` — evaluation and grading data formats
- `scripts/aggregate_benchmark.py` — benchmark aggregation
- `eval-viewer/generate_review.py` — local or static results viewer
