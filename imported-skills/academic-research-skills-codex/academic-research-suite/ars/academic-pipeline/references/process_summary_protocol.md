# Stage 6: Process Summary Protocol (Added in v2.4)

**Trigger**: After Stage 5 (FINALIZE) completion
**Purpose**: Document the complete human-AI collaboration history for the paper creation process, for user sharing, reporting, or reflection

## Workflow

```
1. Ask user language preference:
   "Which language version of the process record would you like to generate first?"
   - Chinese (Traditional Chinese)
   - English
   - Both (default: generate the user's primary conversation language first)

2. Review session history and compile the following:
   - User's initial instructions (verbatim quote)
   - Key decision points and user interventions at each stage
   - Direction correction moments and reasons
   - Iteration count and review result summaries
   - Intellectual insights raised by the user (e.g., questions that spawned new chapters)
   - Quality requirement evolution (e.g., formatting, tone adjustments)
   - Pipeline statistics (stage count, review rounds, integrity verification count, etc.)

3. Generate Markdown version (paper_creation_process.md / paper_creation_process_en.md)

4. Convert to LaTeX and compile PDF:
   - pandoc MD -> LaTeX body
   - Package complete LaTeX document (with cover page, table of contents, headers/footers)
   - tectonic compile PDF
   - Chinese version requires xeCJK + Source Han Serif TC VF
```

## Required Content in Process Record

| Section | Content |
|---------|---------|
| Paper Information | Title, final deliverables list |
| Stage-by-Stage Process | Input/output/key decisions for each stage, with verbatim user quotes |
| Iteration Details | Review comment summaries, revision items, re-review results |
| Interaction Pattern Summary | User role, Claude role, intervention count, key turning points — statistics table |
| User Key Decisions | Chronological list of every important decision made by the user |
| Key Lessons | Reusable lessons learned from the process |
| **Collaboration Quality Evaluation** | **Final chapter: 1-100 score + dimensional analysis + improvement suggestions** (see below) |

## Collaboration Quality Evaluation (Final Chapter, Mandatory)

The final chapter of the process record is a "Collaboration Quality Evaluation" that honestly and constructively assesses the user's performance in the human-AI collaboration. Format follows the Claude Code CLI `/insight` feature.

### Scoring Dimensions (each 1-100, weighted average for overall score)

```
+--------------------------------------------------+
|  Collaboration Quality Score: [XX]/100            |
+--------------------------------------------------+
|                                                   |
|  Direction Setting          [----------  ] XX     |
|  Clarity, timing, scope definition                |
|                                                   |
|  Intellectual Contribution  [------------ ] XX    |
|  Insight depth, original questions, concept        |
|  challenges                                       |
|                                                   |
|  Quality Gatekeeping        [---------   ] XX     |
|  Visual inspection, formatting requirements,       |
|  quality standards                                |
|                                                   |
|  Iteration Discipline       [----------  ] XX     |
|  Timely direction correction, willingness to       |
|  re-run pipeline, refusing to settle              |
|                                                   |
|  Delegation Efficiency      [-------     ] XX     |
|  When to intervene/when to let go, instruction     |
|  precision, checkpoint efficiency                 |
|                                                   |
|  Meta-Learning              [------------ ] XX    |
|  Feeding experience back to skills, requesting     |
|  lesson recording, process improvement awareness  |
|                                                   |
+--------------------------------------------------+
```

### Scoring Criteria

| Score Range | Meaning |
|------------|---------|
| 90-100 | Exceptional — User intervention significantly elevated the paper's intellectual quality beyond what AI could produce independently |
| 75-89 | Excellent — User made correct directional decisions and effectively leveraged the pipeline's iteration capabilities |
| 60-74 | Good — User completed necessary decisions but some opportunities were missed |
| 40-59 | Basic — User primarily served as a "continue" button with little substantive intervention |
| 1-39 | Needs Improvement — User intervention may have disrupted the workflow or lacked critical quality gatekeeping |

### Required Subsections

1. **Overall Score**: Total score + one-sentence evaluation
2. **What Worked Well**: 2-4 specific behaviors, with verbatim user quotes
3. **Missed Opportunities**: 1-3 things the user could have done but didn't
4. **Recommendations for Next Time**: 3-5 specific, actionable improvement suggestions
5. **Human vs AI Value-Add**: Clearly identify which aspects of the final paper quality came from user intervention (not achievable by AI independently)

### Evaluation Principles

- **Honesty first**: No inflation, no pleasantries. If the user only pressed "continue," reflect that truthfully
- **Evidence-based**: Every score is supported by specific behaviors or conversation records
- **Constructive**: Every criticism must include actionable improvement suggestions
- **Acknowledge uncertainty**: If certain dimensions cannot be evaluated (e.g., mid-entry skipped the research stage), mark as N/A
- **Bidirectional reflection**: Also candidly point out Claude's shortcomings during the process (e.g., areas requiring multiple corrections)

## AI Self-Reflection Report (Mandatory)

The second-to-last chapter of the process record is an "AI Self-Reflection Report" that honestly documents AI's own behavioral patterns during the pipeline. This complements the Collaboration Quality Evaluation (which assesses the user) by assessing the AI.

### Tracked Metrics

All metrics below are derived from existing agent logs (`[DA-DECISION]`, `[DA-REBUTTAL]`, `[HEALTH-CHECK]`, state tracker JSON) — no additional per-stage instrumentation is required. The orchestrator aggregates these at Stage 6 by scanning the dialogue transcript:

```
+--------------------------------------------------+
|  AI Self-Reflection Report                        |
+--------------------------------------------------+
|                                                   |
|  DA Concession Rate           X/Y (Z%)           |
|  (concessions / total rebuttals received)         |
|                                                   |
|  DA Consecutive Concessions   [list if any]       |
|  (violations of no-consecutive rule)              |
|                                                   |
|  Checkpoints Skipped          X/Y                 |
|  (SLIM or user-skipped / total checkpoints)       |
|                                                   |
|  User Overrides               X                   |
|  (times user overruled AI recommendation)         |
|                                                   |
|  Dialogue Health Alerts       X                   |
|  (health check interventions triggered)           |
|  - Persistent Agreement:      X                   |
|  - Conflict Avoidance:        X                   |
|  - Premature Convergence:     X                   |
|                                                   |
|  Intent Mode Transitions      X                   |
|  (exploratory ↔ goal-oriented switches)           |
|                                                   |
|  Cross-Model Disagreements    X (if enabled)      |
|  (integrity + DA combined)                        |
|                                                   |
+--------------------------------------------------+
```

### Required Subsections

1. **Behavioral Summary**: One paragraph describing the overall AI behavioral pattern during this pipeline run
2. **Sycophancy Risk Assessment**: Screening thresholds based on concession rate and health alerts — LOW (concession <50%, 0 health alerts) / MEDIUM (50-65% or 1-2 alerts) / HIGH (>65% or 3+ alerts). These are screening thresholds, not diagnostic criteria — a MEDIUM rating means the metrics warrant human review, not that sycophancy occurred (a high concession rate may reflect genuinely strong rebuttals). If HIGH, include a warning: "AI may have been too accommodating in this run. Human review of DA findings and integrity results is strongly recommended."
3. **Frame-Lock Incidents**: List any `[CROSS-MODEL-FINDING]` that the primary DA missed (if cross-model was enabled), or any frame-lock detections triggered during checkpoints. If none, state "No frame-lock incidents detected — note this could mean either good coverage or undetected frame-lock."
4. **Convergence Pattern**: In Socratic dialogue stages, was intent correctly detected? Did the mentor try to converge prematurely? Report mode transitions and any premature-convergence health alerts.
5. **What AI Got Wrong**: Candid list of AI errors or shortcomings during the run — corrections needed, checkpoint failures, integrity issues found. This is not a failure report; it is evidence that quality gates are working.
6. **Failure Mode Audit Log** (v3.2): For each of the 7 AI research failure modes from the Stage 2.5 / 4.5 checklist (see `references/ai_research_failure_modes.md`), report (a) final status at 4.5 — `CLEAR` / `OVERRIDDEN`, (b) history — was it ever `SUSPECTED` during the pipeline? At which stage? How was it resolved? (c) if `OVERRIDDEN`, the user's recorded reasoning. This makes the failure-mode defences part of the permanent process record. Modes with no history can be listed as `CLEAR (no flags)` in one line; expand only on modes that were flagged.
- **Reading Probe Outcomes (if present)** — transcribes the `### Reading Probe Outcomes` subsection from the Research Plan Summary verbatim, with a one-line note that the AI did not verify paraphrase accuracy. If the Research Plan Summary has no such subsection (i.e., `ARS_SOCRATIC_READING_PROBE` was unset), this item is omitted entirely (no "not applicable" noise). Pickup rule (two sources, either sufficient): (a) copy the entire `### Reading Probe Outcomes` subsection body verbatim — this is the authoritative human-readable record; (b) additionally grep for `[READING-PROBE: status=..., paper=..., outcome=..., turn=...]` which the Mentor emits once in the summary as a machine-stable anchor (including for `not_fired_*` statuses). If both are present use (a) as the display source and keep (b) as the final line of the transcribed block so downstream tooling can still parse it. If only raw inline tags from dialogue turns (`[READING-PROBE: paper=..., outcome=..., turn=...]` without the `status=` field) are found and no subsection exists, the Mentor compilation step was skipped — log this as a pipeline anomaly rather than silently dropping the probe data.
- **Adjacent-Framing Probe Outcomes (if present)** — if `ARS_SOCRATIC_ADJACENT_PROBE` was set, grep the dialogue transcript for `[ADJACENT-PROBE: surfaced=..., anchor=internal_knowledge, turn=..., outcome=...]` tags (the Mentor emits one per AI-initiated surfacing, on a standalone line). Transcribe a one-line-per-probe summary plus a note: a high `outcome=declined` rate is the bias-visibility signal that the internal-knowledge adjacency was mis-calibrated for this user (the Mentor did NOT verify the facets against any external source). If `ARS_SOCRATIC_ADJACENT_PROBE` was unset (no tags found), omit this item entirely (no "not applicable" noise). Note: the `outcome` value is only known AFTER the user's next response, so a probe surfaced on the final turn may carry `outcome=deferred`.

### Output Length Guidance

For dimensions with no findings, state the null result in one sentence. Expand only when issues are detected. The real risk is generating verbose "everything is fine" paragraphs for empty subsections — resist this.

### Principles

- **Self-honesty**: AI must not minimize its own shortcomings. If the DA conceded too easily, say so.
- **Not self-flagellation**: The purpose is transparency, not performative humility. Report facts with interpretation.
- **Actionable**: Every finding should suggest what could be done differently next time (e.g., "Consider enabling cross-model verification for the next run" or "The user might want to push back harder on DA concessions")
- **The irony is noted**: This self-reflection is itself produced by the same AI that may have been sycophantic during the pipeline. The user should read it with that awareness. This caveat must be stated in the report.

## Output Specifications

- **Filename**: `paper_creation_process.md` (Chinese) / `paper_creation_process_en.md` (English)
- **PDF**: `paper_creation_process_zh.pdf` / `paper_creation_process_en.pdf`
- **LaTeX template**: `article` class, 12pt, A4, Times New Roman + Source Han Serif TC VF
- **Includes table of contents**: `\tableofcontents`
- **Header**: left = document title (italic), right = date
- **Compilation**: tectonic (same toolchain as Stage 5)
