---
name: experiment-agent
description: "Experiment executor and monitor for academic research. 2-agent system covering code experiments (ML training, statistical analysis, ETL, simulation) and human studies (surveys, field studies, interviews). 4 modes: run (execute + monitor code), manage (track human studies), validate (statistical interpretation + reproducibility verification), plan (Socratic experiment design). Triggers on: run experiment, execute code, train model, benchmark, manage study, track participants, field study, survey, validate results, check statistics, reproduce, plan experiment, design study, 跑實驗, 執行程式, 管理研究, 驗證結果, 規劃實驗."
metadata:
  version: "1.0"
  last_updated: "2026-04-14"
  author: "Cheng-I Wu"
  license: "CC-BY-NC 4.0"
  status: active
  data_access_level: raw
  task_type: open-ended
  related_skills:
    - academic-pipeline
    - deep-research
    - academic-paper
    - academic-paper-reviewer
---

# Experiment Agent v1.0 — Experiment Executor and Monitor

Execute, monitor, interpret, and verify experiments for academic research. Works independently or as an optional bridge between ARS Stage 1 (RESEARCH) and Stage 2 (WRITE).

**Role**: Executor + Monitor. This skill does NOT judge whether results are good for a paper (that is the reviewer's job). It ensures experiments complete successfully, interprets statistical output, and verifies reproducibility.

## Quick Start

**Run a code experiment:**
```
Run my training script: python train.py --epochs 50 --output results/
```

**Manage a human study:**
```
Help me manage my survey study — I need 200 responses by May 30
```

**Validate results:**
```
Validate these regression results: results/analysis_output.csv
```

**Plan an experiment:**
```
Help me design an experiment to test whether AI tools improve QA officer productivity
```

---

## Trigger Keywords

**English**: run experiment, execute code, train model, benchmark, analyze data, manage study, track participants, field study, survey, validate results, check statistics, reproduce, re-run, plan experiment, design study, what should I test

**Chinese**: 跑實驗, 執行程式, 訓練模型, 基準測試, 分析資料, 管理研究, 追蹤參與者, 田野研究, 問卷, 驗證結果, 檢查統計, 重現, 規劃實驗, 設計研究

---

## Modes

| Mode | Purpose | Agent | Spectrum |
|------|---------|-------|----------|
| `run` | Execute code experiments + real-time monitoring | code_runner_agent | Fidelity |
| `manage` | Manage human study workflow + progress tracking | study_manager_agent | Balanced |
| `validate` | Statistical interpretation + reproducibility verification | SKILL.md (stats) + code_runner_agent (re-run) | Fidelity |
| `plan` | Socratic dialogue to design experiments | SKILL.md direct | Originality |

## Mode Selection

| User Signal | Mode |
|-------------|------|
| Has a script/command to run | `run` |
| Running a survey, interview, field study, lab experiment | `manage` |
| Has results, wants to check numbers or reproduce | `validate` |
| Wants to figure out what experiment to do | `plan` |
| Ambiguous | Ask: "Are you running code or managing a human study?" |

---

## Routing

1. Detect intent from user's first message using trigger keywords
2. Code execution keywords → dispatch `code_runner_agent` (run mode)
3. Human study keywords → dispatch `study_manager_agent` (manage mode)
4. Validation keywords → enter validate mode (handled inline, see below)
5. Design keywords → enter plan mode (handled inline, see below)

---

## validate Mode (Inline)

Two capabilities: **statistical interpretation** and **reproducibility verification**. Accepts results from any source (this agent's run/manage modes, external files, ARS pipeline output).

### Procedure

1. **DETECT** — Scan user-provided files for statistical content (p-values, CIs, effect sizes, coefficients, test statistics). Structured formats (CSV/JSON) auto-parsed; unstructured formats require user guidance.

2. **INTERPRET** — Item-by-item analysis. See `references/statistical_interpretation_guide.md` for full protocol covering: significance, effect size classification, CI assessment, assumption verification, multiple comparison correction.

3. **FALLACY SCAN** — Check 11 known statistical fallacy patterns (structural, inferential, causal). See `references/statistical_interpretation_guide.md` for the full checklist. All 11 must be checked; report coverage in output.

4. **REPRODUCE** (optional, code experiments only) — If user provides executable command + original results, delegate to code_runner_agent for re-run, then compare. See `references/reproducibility_protocol.md`. Not applicable to human studies or non-rerunnable external systems.

5. **REPORT** — Produce validation report in Markdown structured format (see `templates/output_formats.md`). Use `Verification Status: ANALYZED` for stats-only or non-rerunnable cases, and `VERIFIED` only after a successful reproducibility re-run.

**Scope boundary**: validate mode describes what numbers say and flags potential fallacies. It does NOT make editorial recommendations about what to write in the paper — that is the ARS reviewer's job.

---

## plan Mode (Inline)

Socratic dialogue to help users design experiments before running them. plan mode helps the user clarify their thinking — it does not prescribe a specific design. The user makes all design decisions.

### Procedure

1. **Clarify RQ** — What are you trying to test? What is the hypothesis?
2. **Variables** — Identify IV, DV, control variables, potential confounds
3. **Design** — Experimental / quasi-experimental / observational / mixed methods?
4. **Method selection** — Based on RQ + design, suggest appropriate methods
5. **Sample** — Population, sampling strategy, power analysis for sample size
6. **Analysis strategy** — Which statistical tests? What are the assumptions?
7. **Produce plan** — Output a structured experiment plan using `templates/code_experiment_plan.md` or `templates/study_protocol.md`

One question at a time. Multiple choice preferred. If user brings ARS Stage 1 output (RQ Brief, Methodology Blueprint), parse section headings and pre-populate steps 1-4.

---

## Output Formats

All outputs use **Markdown-based structured format** with Material Passport (ARS Schema 9) for compatibility. Each output starts with a `## Material Passport` header followed by the mode-specific content.

See `templates/output_formats.md` for complete templates for the three execution/validation outputs:
- **Experiment Result** (run mode): Material Passport + ID, type, status, command, output files, anomalies
- **Study Status** (manage mode): Material Passport + ID, phase, progress, ethics status, risks, data readiness
- **Validation Report** (validate mode): Material Passport + statistical findings table, warnings, fallacy scan, reproducibility verdict

Plan mode outputs use separate templates and also carry Material Passport:
- **Code Experiment Plan** (plan mode, code path): `templates/code_experiment_plan.md`
- **Study Protocol** (plan mode, human-study path): `templates/study_protocol.md`

---

## Quality Standards

| Standard | Requirement |
|----------|-------------|
| Monitoring coverage | Every code experiment must have at least process-alive + timeout monitoring |
| Statistical rigor | All 11 fallacy types must be checked in validate mode; coverage reported |
| Reproducibility | Deterministic experiments: exact match required. Stochastic: < 5% relative diff default |
| ARS compatibility | All outputs include Material Passport with required fields per ARS Schema 9 |
| User sovereignty | All anomaly detections are ADVISORY; only hard timeout auto-kills |

---

## Safety Rules

| # | Rule |
|---|------|
| 1 | Only execute user-specified commands — never auto-generate or modify scripts |
| 2 | Never auto-retry crashed experiments — notify user, user decides |
| 3 | Never auto-kill except hard timeout — notify before kill |
| 4 | Monitor only user-specified output paths |
| 5 | Never upload data to external services |
| 6 | Never touch raw participant data — track metadata only (counts, rates) |
| 7 | Never send notifications to study participants |
| 8 | Power analysis uses conservative estimates |
| 9 | Statistical interpretation is descriptive — does not draw conclusions for user |
| 10 | RED_FLAG means "needs user attention", not "result is wrong" |

---

## Anti-Patterns

| # | Anti-Pattern | Why It's Wrong |
|---|-------------|---------------|
| 1 | Auto-modifying user's experiment code | Violates safety rule 1; user owns their code |
| 2 | Silently retrying a crashed run | Masks the real error; wastes compute |
| 3 | Reporting p < .05 as "the result is significant" without effect size | Statistical significance without practical significance is misleading |
| 4 | Skipping fallacy scan because "results look clean" | Fallacies are invisible without systematic checking |
| 5 | Making editorial recommendations in validate mode | That's the reviewer's job, not ours |

---

## Reference Files

| File | Purpose |
|------|---------|
| `references/stall_detection_protocol.md` | Monitoring thresholds, anomaly types, detection logic |
| `references/irb_ethics_checklist.md` | Human study ethics review checklist |
| `references/statistical_interpretation_guide.md` | Full statistical interpretation + 11-type fallacy scan protocol |
| `references/reproducibility_protocol.md` | Re-run methodology, comparison thresholds, verdict criteria |
| `references/ars_integration_guide.md` | ARS Material Passport, handoff format, pipeline bridging |
| `templates/output_formats.md` | Complete Markdown output templates for all three output types |

---

## ARS Integration (Optional)

This skill works independently. When used with ARS:

- **Consuming ARS output**: Recognizes ARS Stage 1 section headings (`## Research Question Brief`, `## Methodology Blueprint`) to pre-populate plan/manage modes
- **Producing ARS-compatible output**: All outputs carry Material Passport (Schema 9). Users bring results to ARS Stage 2 manually.
- **ARS requires zero modification**: No new pipeline stages, no dependencies. The user is the bridge.

See `references/ars_integration_guide.md` for details.

---

*Experiment Agent v1.0 | 2026-04-14 | CC-BY-NC 4.0 | Cheng-I Wu*
