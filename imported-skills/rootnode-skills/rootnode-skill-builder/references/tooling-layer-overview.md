# Tooling Layer Overview

The map of the executable content shipped with `rootnode-skill-builder` v3.0 — what each script does, what each subagent prompt does, how the methodology layer invokes them, and how the layer is maintained against drift from its upstream source. SKILL.md routes the workflow when the methodology decides to invoke tooling; this reference is the catalog and integration guide.

Canonical principle source: `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.12` (multi-environment adaptation discipline) and `root_SKILL_BUILD_DISCIPLINE.md §10` (environment-adaptive degradation discipline).

---

## Table of contents

1. The two-layer architecture
2. Script catalog (`scripts/`)
3. Subagent catalog (`agents/`)
4. Eval-viewer subdirectory (`eval-viewer/`)
5. Integration patterns
6. Tier compatibility summary
7. Drift detection discipline
8. Maintenance cadence
9. What this reference does not do

---

## 1. The two-layer architecture

`rootnode-skill-builder` v3.0 ships with two distinct layers:

- **Methodology layer.** SKILL.md and the 12 reference files. Markdown content the model reads as instructions, applies as judgment, and treats as the canonical source of truth. Methodology is what makes a Skill a Skill — the executable layer alone would be a script collection without procedural guidance.
- **Tooling layer.** 7 Python scripts in `scripts/`, 3 subagent prompt files in `agents/`, and 2 eval-viewer files in `eval-viewer/`. Code and structured prompts the methodology invokes as tools when the build environment supports execution.

The two layers compose. Methodology decides when to invoke tooling; tooling produces structured artifacts; methodology interprets the artifacts and continues the workflow. Neither layer subsumes the other. The boundary between them is documented in `references/skills-spec.md` ("Executable Layer in Skills" section).

The tooling layer is content the build CV produces and ships, not behavior the build CV invokes during the build. The exception is `quick_validate.py`, which is invoked during D1 verification per the build prompt's quality gate procedure. All other scripts and agents are produced as files and then exercised by Skill consumers (the build CV when invoked at runtime, the operator running validation manually, or downstream automation).

## 2. Script catalog (`scripts/`)

Seven Python files. Adapted from upstream Anthropic skill-creator source per the content-class policy (`root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.10` brand-cleanliness; structural contracts preserved verbatim; prose tone-adapted).

### `description_optimizer.py`

**Purpose.** Automated 5-iteration train/test description refinement loop with stream-event triggering detection. Consumes a Skill folder and a trigger eval set; produces revisions with per-iteration train/test scores and a final selected revision.

**Origin.** Fused from upstream `run_loop.py` + `run_eval.py` + `improve_description.py`. The triggering detection mechanism (stream-event monitoring for `content_block_start` with `tool_use` type), the train/test split methodology, and the description improvement prompt structure are preserved verbatim per content class 1.

**Tier compatibility.** Tier A only — requires `claude -p` execution and stream-event monitoring. Tier B falls back to the manual walkthrough procedure documented in `references/description-optimization.md`.

**Invocation pattern.**

```
python scripts/description_optimizer.py \
    --skill-path <path-to-skill> \
    --eval-set <path-to-eval-set.json> \
    --iterations 5 \
    --output-dir <path-to-output>
```

The build CV invokes the optimizer when description refinement is the active workflow and Tier A applies. The optimizer writes per-iteration JSON to the output directory; the methodology layer reads the final selected revision and updates the Skill's frontmatter.

### `package_zip.py`

**Purpose.** Packages a Skill folder as a deployable `.zip` with the rootnode folder structure: `{skill-name}/SKILL.md` + `{skill-name}/references/*.md` + `{skill-name}/scripts/*` + `{skill-name}/agents/*.md` + `{skill-name}/eval-viewer/*` (when present).

**Origin.** Adapted from upstream `package_skill.py` for `.zip` format and v3.0 folder structure (adds `eval-viewer/` inclusion).

**Tier compatibility.** Tier A/B/C compatible — pure file-system operation, no environment dependency.

**Invocation pattern.**

```
python scripts/package_zip.py <skill-path> --output <output-zip-path>
```

The build CV invokes `package_zip.py` at the end of the build pipeline (`§32b.9` of the build prompt). The packaged zip is the deployable artifact; audit artifacts ship separately.

### `quick_validate.py`

**Purpose.** Validates a Skill against D1 spec compliance — frontmatter parse, name format, description length, body line count, allowed metadata fields. Returns non-zero exit on failure.

**Origin.** Adapted from upstream `quick_validate.py`. Extends allowed frontmatter properties to include rootnode `metadata` sub-fields (`author`, `version`, `predecessor`, `original-source`, `notes`, `discipline_post`).

**Tier compatibility.** Tier A/B/C compatible — pure file inspection.

**Invocation pattern.**

```
python scripts/quick_validate.py <skill-path>
```

The build CV invokes `quick_validate.py` during D1 verification (`§32b.7` of the build prompt). Halts on failure.

### `aggregate_benchmark.py`

**Purpose.** Aggregates grader subagent JSON outputs across multiple eval runs into a benchmark report (per the `benchmark.json` schema documented in `references/behavioral-validation.md`).

**Origin.** Adapted from upstream `aggregate_benchmark.py`. Schema alignment with `agents/grader.md` output preserved verbatim.

**Tier compatibility.** Tier A only — requires grader subagent JSON output. Tier B/C produces no benchmark output (no grader runs to aggregate).

**Invocation pattern.**

```
python scripts/aggregate_benchmark.py \
    --runs-dir <path-to-runs> \
    --output <path-to-benchmark.json>
```

Invoked when the build CV runs cross-run benchmark aggregation (typically as part of D9a empirical validation across multiple eval prompts).

### `generate_report.py`

**Purpose.** Generates a static HTML report from `description_optimizer.py` output. Per-iteration train/test results with check/x marks for fast review.

**Origin.** Ported from upstream `scripts/generate_report.py`. HTML generation structure preserved verbatim per content class 1; embedded HTML strings tone-adapted with brand-cleanliness pass per content class 2 + AEA §4.10.

**Tier compatibility.** Tier A only — consumes optimizer output. Tier B/C unused.

**Invocation pattern.**

```
python scripts/generate_report.py \
    --optimizer-output <path-to-optimizer-runs> \
    --output <path-to-report.html>
```

Distinct from the eval-viewer (§4 below). This script produces a per-run static HTML report; the eval-viewer produces an interactive multi-run browser with feedback collection.

### `utils.py`

**Purpose.** Shared utility module. Provides `parse_skill_md()` for parsing frontmatter and body from a SKILL.md file. Used by the other scripts.

**Origin.** Ported verbatim from upstream `scripts/utils.py`. Content class 3 (structural-only — no tone adaptation needed).

**Tier compatibility.** Tier A/B/C compatible — pure library code.

**Invocation pattern.** Not invoked directly; imported by other scripts.

### `__init__.py`

**Purpose.** Empty Python package marker. Required so `scripts/` functions as a Python package for relative imports.

**Origin.** Ported verbatim from upstream as a zero-byte file.

**Tier compatibility.** Not applicable — package marker only.

## 3. Subagent catalog (`agents/`)

Three subagent prompt files. Adapted from upstream Anthropic skill-creator source per the content-class policy: schemas verbatim (content class 1); design principles verbatim (methodology-grade content); instructional prose tone-adapted (content class 2).

### `agents/grader.md`

**Purpose.** Evaluates expectations against an execution transcript and outputs. Returns structured JSON with per-expectation pass/fail and evidence.

**Output schema.** Verbatim from `references/behavioral-validation.md` §10 (the grading schema). Preserves `expectations[]`, `summary`, `execution_metrics`, `timing`, `claims[]`, `user_notes_summary`, and `eval_feedback` fields exactly.

**Design principles.** Two jobs (grade outputs + critique evals); pass/fail criteria with burden-of-proof; no partial credit; objectivity discipline. All preserved verbatim per `references/behavioral-validation.md` §8.

**Tier compatibility.** Tier A only — invoked via Task subagent. Tier B falls back to inline qualitative review by the build CV; Tier C does not produce executable verdicts.

**Invocation pattern.**

```
Task(subagent_type="general-purpose", prompt="<contents of agents/grader.md with parameters>")
```

The methodology layer invokes the grader during D9a empirical comparison (`references/behavioral-validation.md` §3) and during cross-run benchmark aggregation.

### `agents/comparator.md`

**Purpose.** Blindly compares two outputs to determine which better accomplishes the eval task. Returns a winner ("A", "B", or "TIE") with rubric scores and reasoning.

**Output schema.** Verbatim from `references/version-comparison.md` (the comparator schema with `winner`, `reasoning`, `rubric` per output, `output_quality`, and optional `expectation_results`).

**Design principles.** Stay blind (do not infer which Skill produced which output); be specific (cite examples); be decisive (ties should be rare); output quality first (assertions are secondary); be objective. Preserved verbatim per `references/version-comparison.md`.

**Tier compatibility.** Tier A only — subagent isolation is the load-bearing feature. Tier B falls back to inline blind comparison with identifier-leak discipline (`references/version-comparison.md` §"Inline procedure"); Tier C defers comparison.

**Invocation pattern.**

```
Task(subagent_type="general-purpose", prompt="<contents of agents/comparator.md with parameters>")
```

Invoked during version comparison workflows (`references/version-comparison.md`).

### `agents/analyzer.md`

**Purpose.** Post-hoc analysis of comparison results. Reads winner/loser Skills with the verdict in hand; identifies what made the winner better and generates actionable improvement suggestions for the loser.

**Output schema.** Verbatim from `references/version-comparison.md` (the analyzer schema with `comparison_summary`, `winner_strengths`, `loser_weaknesses`, `instruction_following`, `improvement_suggestions`, and `transcript_insights` fields).

**Tier compatibility.** Tier A — invoked via Task subagent after comparator verdict. Tier B falls back to inline analysis by the build CV; Tier C deferred.

**Invocation pattern.**

```
Task(subagent_type="general-purpose", prompt="<contents of agents/analyzer.md with parameters>")
```

Also has a benchmark-mode variant (per `agents/analyzer.md` §"Analyzing Benchmark Results") for surfacing patterns across multiple benchmark runs without suggesting Skill improvements.

## 4. Eval-viewer subdirectory (`eval-viewer/`)

Two files. Ported from upstream `design/skill-creator/eval-viewer/` per content-class policy.

### `eval-viewer/generate_review.py`

**Purpose.** Interactive HTTP-served eval review interface. Reads a workspace directory, discovers runs, embeds output data into a self-contained HTML page, and serves the page via a tiny HTTP server with feedback auto-save. The operator browses multiple eval runs in one view, compares outputs, and submits feedback that the script writes to disk.

**Origin.** Ported from upstream `eval-viewer/generate_review.py`. HTTP server logic, request handlers, feedback collection mechanism, and JSON I/O all preserved verbatim per content class 1; docstrings, prose comments, and CLI help strings tone-adapted per content class 2.

**Tier compatibility.** Tier A only — requires Python execution + browser surface. Tier B/C unused.

### `eval-viewer/viewer.html`

**Purpose.** HTML template loaded by `generate_review.py`. Renders the review interface with multi-run navigation and feedback submission.

**Origin.** Ported from upstream `eval-viewer/viewer.html`. HTML structure, JavaScript event handlers, fetch/feedback POST logic, and CSS class names preserved verbatim per content class 1; page title, headers, branded copy, and visible page comments tone-adapted with full Anthropic-marker removal per content class 2 + AEA §4.10 brand-cleanliness.

**Tier compatibility.** Tier A only.

## 5. Integration patterns

The methodology layer invokes the tooling layer per the patterns documented in `references/multi-environment-adaptation.md`. Common patterns:

**Validate before ship:** SKILL.md "Quality Gate" section directs the build CV to run `scripts/quick_validate.py` against the produced Skill folder. D1 spec compliance verdict is captured before audit artifacts are produced.

**Behavioral comparison:** `references/behavioral-validation.md` §3 (D9a procedure) directs the build CV to invoke `agents/grader.md` against GREEN and RED runs, then compare differentials.

**Description refinement:** `references/description-optimization.md` directs the build CV to invoke `scripts/description_optimizer.py` for automated refinement when Tier A applies.

**Version comparison:** `references/version-comparison.md` directs the build CV to invoke `agents/comparator.md` and `agents/analyzer.md` in sequence for blind A/B comparison.

**Cross-run benchmarking:** When validation runs many configurations, `scripts/aggregate_benchmark.py` aggregates grader outputs into a benchmark report; `scripts/generate_report.py` and/or `eval-viewer/generate_review.py` produces HTML for review.

**Packaging:** `scripts/package_zip.py` builds the deployable artifact at the end of the build pipeline.

## 6. Tier compatibility summary

Quick reference table for which tooling components are available at which tier (full per-script details in §2–§4 above).

| Component | Tier A | Tier B | Tier C |
|---|---|---|---|
| `scripts/description_optimizer.py` | ✓ | manual fallback | manual fallback |
| `scripts/aggregate_benchmark.py` | ✓ | — | — |
| `scripts/quick_validate.py` | ✓ | ✓ | ✓ |
| `scripts/package_zip.py` | ✓ | ✓ | ✓ |
| `scripts/generate_report.py` | ✓ | — | — |
| `scripts/utils.py` (library) | ✓ | ✓ | ✓ |
| `scripts/__init__.py` (marker) | ✓ | ✓ | ✓ |
| `agents/grader.md` | ✓ | inline fallback | n/a |
| `agents/comparator.md` | ✓ | inline fallback | deferred |
| `agents/analyzer.md` | ✓ | inline fallback | deferred |
| `eval-viewer/*` | ✓ | — | — |

## 7. Drift detection discipline

The tooling layer is ported from upstream Anthropic `skill-creator`. Upstream evolves; the port can drift. Drift detection prevents the v3.0 tooling from silently diverging from upstream improvements.

**Detection mechanism:**

- Maintain `design/skill-creator/` as the upstream source-of-truth snapshot in the rootnode-skills repo.
- Periodic comparison: walk each ported file in `rootnode-skill-builder/scripts/`, `agents/`, and `eval-viewer/` against its upstream counterpart in `design/skill-creator/`. Surface differences.
- Categorize differences:
  - **Verbatim-class divergence** (schemas, structural contracts): treat as bugs in the port. File a fix.
  - **Tone-class divergence** (docstrings, prose comments): expected; no action unless the upstream change carries methodology implications.
  - **New upstream content** (new scripts, new schema fields, new agent prompts): evaluate for adoption in a future v3.x or v4.0 update.

**Detection cadence:** Documented in §8 below.

## 8. Maintenance cadence

**Monthly comparison checklist** (low-cost detection):

- Walk each ported file against upstream.
- Note any structural changes (schema fields, function signatures, config patterns).
- Note any new files in upstream not yet ported.
- Decision: file a port-update issue, or note as backlog.

**Quarterly port decision** (higher-cost adoption):

- Review backlog of upstream changes.
- Decide which warrant a v3.x update vs. wait.
- Driver criteria: methodology implications (highest priority); schema contract changes (high priority); new tooling that addresses known v3.0 gaps (medium); cosmetic improvements (low; defer).

**Per-port discipline:**

- When a v3.x update lands, re-run the v3.0 build's quality gate against the updated tooling (D1 spec compliance, D9 behavioral validation if applicable).
- Update this reference's per-script catalog with any new tier compatibility constraints introduced by the upstream change.
- Update the design spec / build prompt for the next release if the upstream change requires methodology updates.

**Anti-pattern:** silent drift. The port is allowed to drift from upstream because no one is comparing. Drift accumulates; eventually the port's behavior contradicts its documentation, or the schema contract breaks against new external consumers. The detection cadence prevents this — silence is the failure mode, not the discipline.

## 9. What this reference does not do

This reference does not specify the implementation details of any script — those live in the script files themselves (`scripts/*.py`). The reference describes what each script does and when to invoke it; the script source is the implementation contract.

This reference does not specify the subagent prompt content — those live in the agent files themselves (`agents/*.md`). The reference describes what each subagent does and when to invoke it; the agent file is the prompt contract.

This reference does not duplicate the per-workflow procedures (description optimization, behavioral validation, version comparison) — those live in their respective references. This reference is the catalog and integration guide; the workflow references are the procedural depth.

This reference does not specify the tier-determination logic in detail — that lives in `references/multi-environment-adaptation.md`. This reference applies the tier model to per-script and per-subagent compatibility.

---

*End of tooling-layer-overview.md.*
