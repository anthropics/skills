# Changelog

## Unreleased

### Contract Fixes

- Clarified `validate` output semantics: `Verification Status` is now `ANALYZED` unless a successful reproducibility re-run upgrades it to `VERIFIED`
- Added Material Passport headers to `plan` mode templates (`code_experiment_plan.md`, `study_protocol.md`)
- Fixed reproducibility guidance for zero-baseline metrics by using a symmetric denominator with epsilon protection
- Reclassified hardware/OS-sensitive runs as `environment-sensitive` comparisons instead of blanket `not applicable`
- Added `CANNOT_VERIFY` and environment-sensitive cases to the documented validation/reproducibility output contract
- Tightened ethics gating so only `READY` can enter study tracking, while `ETHICS_PENDING` still blocks participant recruitment and data collection
- Relaxed consent wording to allow IRB-approved digital, implied, or waived consent paths where appropriate
- Corrected the chi-squared fallback guidance so Fisher's exact is limited to 2x2 tables

## v1.0 (2026-04-09)

### Initial Release

**New Skill: experiment-agent**

- 4 modes: `run` (code experiments), `manage` (human studies), `validate` (statistical interpretation + reproducibility), `plan` (Socratic experiment design)
- 2 agents: `code_runner_agent` (execute + monitor), `study_manager_agent` (plan + track)
- 5 reference protocols: stall detection, IRB ethics checklist, statistical interpretation (11-type fallacy scan), reproducibility verification, ARS integration guide
- 2 templates: code experiment plan, study protocol
- ARS-compatible Material Passport output (Schema 9)
- Independent operation + optional ARS pipeline integration (zero ARS modification)
- Source: Lu et al. (2026, *Nature* 651:914-919) Experiment Progress Manager concept

**Design decisions:**
- Executor + Monitor role only (no quality review — that's ARS reviewer's job)
- All anomaly detections are ADVISORY (user decides, except hard timeout)
- Statistical interpretation is descriptive (flags issues, does not make editorial recommendations)
- validate mode scope boundary: describes what numbers say, does not judge paper quality
- Single-direction ARS dependency: experiment-agent knows ARS format, ARS does not know experiment-agent
