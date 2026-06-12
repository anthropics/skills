---
name: skill-analyzer
description: Skill ROI advisor — reads a skill and compares using it vs. Claude alone across token cost, time, and quality. Two modes: (1) automated — given only a skill name, generates test scenarios from the skill's components; (2) manual — given a skill name and a task, derives the task's workflow phases and scores the skill against each. Reports a per-phase table and VERDICT so the user knows whether to use the skill and for which phases.
requires: claude-code
---

# Skill ROI Advisor

Given a skill name, generate realistic test scenarios for it, then score each scenario phase-by-phase against Claude alone. Write the completed analysis to a file.

## Step 0 — Generate test scenarios (when no task is given)

If the user provides only a skill name (no specific workflow or task):

**First, extract the skill's distinct components — not its phases.**

Read the skill's SKILL.md and all reference files. Then list every distinct piece of guidance the skill contains: specific default values, rules, heuristics, constraints, failure-mode diagnostics, code patterns, decision criteria. Each item on this list is a testable component. Examples of what to extract:

- "LR default: 3e-4" → testable: does this apply to fine-tuning pretrained models?
- "sweep priority: LR → batch → weight decay → warmup" → testable: does this priority hold for non-neural models?
- "time-series split: never shuffle" → testable: does the skill surface this for temporal data tasks?
- "stratified k-fold for imbalanced classes" → testable: does the skill flag this when imbalance is present?
- "MedianPruner with 30–50 trials" → testable: is this budget right for different model sizes and trial costs?

**Then design 2–3 scenarios that stress-test combinations of those components**, not the skill's own phase structure. Each scenario should:
- Be a realistic user task that naturally exercises a *specific subset* of extracted components
- Have its own workflow phases derived from what that task actually requires — not copied from the skill's sections
- Cover different components across scenarios so the full component list gets tested

The scenario's phases might align with the skill's phases, or they might not — that's fine. What matters is that each scenario is chosen because it will reveal whether specific components transfer to that context.

Use these generated scenarios as the input to Steps 1–3 below.

If the user provides a specific task or workflow, skip the component extraction and scenario design above. Instead:

1. Read the target skill's SKILL.md and all reference files
2. Break the user's task into its natural workflow phases — derived from what the task actually requires, not from the skill's section structure
3. Use those phases as the scenario for Steps 1–3

If the user provides only a skill name with no task and no specific workflow — or asks something like "would this help here?" or "is this useful for this project?" — use **project-aware mode**:

1. Read the target skill's SKILL.md and all reference files
2. Read project context in this order:
   - Read `CLAUDE.md` if present
   - Run `ls` on the project root to see top-level structure
   - Read whichever config files exist: `package.json`, `pyproject.toml`, `Makefile`, `requirements.txt`, `go.mod`
   - Skim `src/`, `tests/`, or equivalent source directories for workflow signals
3. Derive 3–5 phases from what actually happens in this project — not from the skill's structure. If the project context is too thin to infer concrete workflows (e.g. a bare repo with no config or source), fall back to Mode 1
4. Score the skill against each phase exactly as in Mode 2
5. Use `Project context: <inferred stack>` as the scenario title (e.g. "Project context: React + Playwright + Node")
6. In the output, name the specific project signals that drove each phase (e.g. "found `tests/` with pytest fixtures → cross-validation phase inferred")

## Step 1 — Get token costs

Locate the skill and run the token counter:
```bash
find ~/.claude/skills ~/.claude/plugins -type d -name "<skill-name>" 2>/dev/null | head -3
python3 {baseDir}/scripts/count_tokens.py <skill-path>
```

The script prints L1/L2/L3 token counts by access level. Use those numbers directly in the per-phase table. For L3, only count the reference/asset files that actually apply to each scenario phase — not all L3 files combined.

## Step 2 — Score quality fit per phase

For each phase in the scenario, score the skill **and** estimate what Claude alone would produce. See `{baseDir}/references/output-guidelines.md` for the score scale and phase verdict rules.

## Step 3 — Estimate time overhead

~900 tokens/second throughput rule:
- L2 load is one-time per session
- L3 loads on first access per phase (not per subsequent access)

## Step 4 — Write output

Read `{baseDir}/assets/output-template.md`. Fill every `{{PLACEHOLDER}}` with real content from Steps 0–3. Follow the instructions in `{baseDir}/references/output-guidelines.md` exactly.

Write the completed file to `skill-analysis-{skill-name}.md` in the current working directory (or the path the user specified).

## Step 5 — Verify

Read the file you just wrote. Check every item in the verification checklist in `{baseDir}/references/output-guidelines.md`. If any item fails, fix the file and re-read to confirm.

## Examples

**Mode 1 — automated (skill name only):**
> "Analyze the ml-trainer skill"

Claude reads `ml-trainer/SKILL.md`, extracts components (LR default 3e-4, sweep priority order, stratified k-fold rule, time-series split constraint), designs 2 scenarios that stress-test different component subsets, scores each phase, and writes `skill-analysis-ml-trainer.md`.

**Mode 2 — manual (skill name + specific task):**
> "Analyze ml-trainer for this task: fine-tuning ResNet-50 on 4,800 chest X-rays with 90/10 class imbalance — baseline, pilot sweeps, Optuna, cross-validation"

Claude skips component extraction, derives 4 phases directly from the task description, scores each phase for skill vs. Claude alone, and writes `skill-analysis-ml-trainer.md` with a per-phase table and VERDICT.

**Mode 2 — different skill domain:**
> "Analyze webapp-testing for this task: write Playwright tests for a React SPA that loads data dynamically"

Claude reads `webapp-testing/SKILL.md`, derives phases (element discovery, script authoring, dynamic-content handling, server lifecycle), scores each, and writes `skill-analysis-webapp-testing.md`.
