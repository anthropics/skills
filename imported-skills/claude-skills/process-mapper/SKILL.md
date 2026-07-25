---
name: process-mapper
description: Use when a BizOps lead, COO, or process-improvement owner needs to document an end-to-end business process (procurement, employee onboarding, incident handoff, customer-onboarding, claims adjudication) in BPMN-style notation, measure cycle times by stage, surface where work spends most of its time waiting vs. being worked, and quantify the gap between processing time and total elapsed time. Pairs Lean / Six Sigma / Theory-of-Constraints canon with deterministic stdlib-only Python tools to produce a process map, a ranked bottleneck list (with severity + root-cause hypothesis), and a cycle-time analysis (P50, P90, value-add ratio, Little's-Law throughput). Distinct from sales-pipeline, system-reliability (SLO), and strategic-OKR work — this is tactical process documentation for internal operations.
version: 2.8.0
author: claude-code-skills
license: MIT
tags: [bizops, process, bpmn, bottleneck, cycle-time, lean, six-sigma, value-stream]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# process-mapper

BPMN-style business process documentation, bottleneck detection, and cycle-time analysis for internal-operations leaders.

## Purpose

Internal-operations work suffers from three recurring failure modes:

1. **Implicit process** — the steps exist only in tribal knowledge, so handoffs drop and onboarding takes weeks.
2. **Invisible waiting** — most of the elapsed time on any business process is queue / wait / approval time, not actual work; teams optimize the wrong stage.
3. **Local optimization** — Goldratt's Theory of Constraints is ignored; resources are added to non-constraint stages, gaining nothing.

This skill produces a documented process map, identifies where work waits, and points the constraint out by name with deterministic logic — not LLM intuition.

## When to use

- Documenting a new business process (procurement intake, vendor onboarding, employee onboarding, incident handoff, expense reimbursement, customer onboarding, claims adjudication).
- An existing process is "too slow" but nobody can name the bottleneck.
- Cycle time is being measured but value-add ratio is not — so the team can't tell whether the process is healthy or waste-heavy.
- Cross-functional handoffs are dropping work and root cause is unclear.

## Workflow

Five-step deterministic flow:

1. **Intake.** Capture the process as a JSON file with one entry per stage: `name`, `owner`, `type` (`value-add` | `wait` | `rework`), `duration_minutes_p50`, `duration_minutes_p90`. Use `assets/process_template.md` and its JSON skeleton.
2. **Map stages.** Run `process_documenter.py` to produce an ASCII swim-lane diagram + a normalized JSON artifact. The swim-lane separates lanes by owner so cross-functional handoffs become visible.
3. **Measure cycle time.** Run `cycle_time_analyzer.py` to compute total P50, total P90, value-add ratio (VA%), and a Little's-Law throughput estimate. Verdict: VA% > 25% = HEALTHY, 10–25% = TYPICAL, < 10% = WASTE-HEAVY.
4. **Detect bottlenecks.** Run `bottleneck_detector.py` with the appropriate `--profile` (saas / services / manufacturing / healthcare). Output is a ranked list with severity (CRITICAL / HIGH / MEDIUM), root-cause hypothesis, and one recommended action per finding.
5. **Recommend.** Pair the bottleneck list with the cycle-time verdict; recommend a single constraint-focused intervention per Goldratt's "subordinate everything to the constraint" rule. Don't recommend optimization of a non-constraint stage.

## Scripts

**`scripts/process_documenter.py`** — Reads a process JSON, validates it, and emits a text-based BPMN-style swim-lane diagram in Markdown (lanes by owner, stages annotated with type + duration). Also outputs a normalized JSON artifact for downstream tools. Stdlib only. `--sample` prints a 6-stage procurement-intake example.

**`scripts/bottleneck_detector.py`** — Applies three deterministic detection rules: (a) stage P50 > 2× mean of value-add stages, (b) wait-state % > 40% of total cycle, (c) rework % > 15%. Thresholds adjust by `--profile` because SaaS, services, manufacturing, and healthcare have different "normal" wait ratios. Output is a ranked list with severity, hypothesis, action.

**`scripts/cycle_time_analyzer.py`** — Computes total P50 and P90 cycle time, value-add ratio (VA%), wait %, rework %, and a Little's-Law throughput estimate (WIP / cycle time). Per Lean canon: VA% > 25% = HEALTHY, 10–25% = TYPICAL (most non-manufacturing processes land here), < 10% = WASTE-HEAVY.

## Quick example

```bash
# Renders a BPMN-style swim-lane diagram + normalized JSON for the built-in 6-stage procurement-intake example
cd business-operations/skills/process-mapper && python3 scripts/process_documenter.py --sample
```

## References

- `references/lean_six_sigma_canon.md` — TIMWOOD wastes, value-stream mapping, Theory of Constraints, Kanban WIP, Little's Law. Cites Womack & Jones, Rother & Shook, Goldratt, Ohno, Liker, Pyzdek, Anderson.
- `references/bpmn_essentials.md` — Pools, lanes, gateways, events, message flows, common notation mistakes. Cites the OMG BPMN 2.0 spec, Silver, Allweyer, Freund/Rücker, OASIS, ISO/IEC 19510:2013.
- `references/bottleneck_anti_patterns.md` — Seven specific anti-patterns drawn from Goldratt, Kim et al., Spear, DORA, Deming, and process-mining research.

## Assumptions

1. The user can provide stage-level cycle-time data (even rough P50 / P90 estimates). If they cannot, the first step is to instrument the process — not to map it.
2. "Process" here means a repeatable business workflow with discrete stages, not a one-off project.
3. The user has authority to act on bottlenecks (or can route findings to someone who does). Without that, the output is academic.
4. Stage `type` is honest: a "value-add" stage labeled as such by the user really does change the work product from the customer's perspective. Mis-labelling waiting as value-add is the most common data-quality failure.

## Anti-patterns

- **Mapping every process at once.** Pick one. Goldratt: the constraint is a single point.
- **Optimizing the non-constraint.** If stage 4 is the bottleneck, speeding up stage 2 just builds inventory in front of stage 4. Subordinate everything to the constraint.
- **Mistaking total cycle time for processing time.** They are almost never the same; VA% reveals the gap.
- **Adding people to a wait-bound process.** Wait time is not solved by more headcount; it's solved by removing the handoff or batch.
- **Treating rework as a separate problem.** Rework loops belong in the process map. Hiding them understates true cycle time.

## Distinct from

- **business-growth skills** — external sales motion, lead-funnel conversion, customer-success retention. Process-mapper is *internal* operations.
- **engineering/slo-architect** — system-reliability SLOs / error budgets / burn-rate alerts. Process-mapper is *business-process* cycle time, not system uptime.
- **c-level-advisor (COO / CEO)** — strategic prioritization of which processes to fix. Process-mapper is the tactical instrument used after that prioritization decision.
- **project-management skills** — Jira / Confluence ticket workflow tooling. Process-mapper is process *design*, not ticket *tracking*.

## Forcing-question library (Matt Pocock grill discipline)

Before invoking the tools, the orchestrator (or `/cs:grill-bizops`) walks the user through these questions **one at a time, with a recommended answer + canon citation**. Never bundled.

1. **"Do you have measured cycle times for the top-3 longest stages, or only estimates?"**
   Recommended: insist on measured data.
   Canon: Goldratt 1984 (*The Goal*) — optimizing estimated bottlenecks reliably attacks the wrong constraint.

2. **"Are you mapping the *current* process (as-is) or the *intended* process (to-be)?"**
   Recommended: map as-is first. To-be after bottleneck is identified.
   Canon: Rother & Shook 1999 (*Learning to See*) — value-stream mapping starts with the current state, always.

3. **"Where do handoffs occur between teams, and how long does each handoff wait?"**
   Recommended: log every handoff with median wait time.
   Canon: Reinertsen 2009 (*Principles of Product Development Flow*) — wait time at handoffs is the largest invisible cost.

4. **"What's your batch size at each stage?"**
   Recommended: drive batch size toward 1 wherever possible.
   Canon: Anderson 2010 (*Kanban*) — batch size correlates 1:1 with cycle time variance.

5. **"What's the rework rate per stage?"**
   Recommended: surface it explicitly; rework loops belong in the map.
   Canon: Pyzdek (*Six Sigma Handbook*) — hidden rework drives 30-50% of total cycle time in service processes.

Walk depth-first. Don't open question 4 before 1-3 are answered. After all 5 are locked, invoke `process_documenter.py` → `bottleneck_detector.py` → `cycle_time_analyzer.py` in sequence.
