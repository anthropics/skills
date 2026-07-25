# Reproducibility

v2.0 design ensures consistent quality assurance with each execution:

## Standardized Workflow

| Guarantee Item | Mechanism |
|---------------|-----------|
| Integrity check every time | Stage 2.5 + Stage 4.5 are **mandatory** stages, cannot be skipped |
| Consistent review angles | EIC + R1/R2/R3 + Devil's Advocate — five fixed perspectives |
| Consistent verification methods | integrity_verification_agent uses standardized search templates |
| Consistent quality thresholds | Integrity check PASS/FAIL criteria are explicit (zero SERIOUS + zero MEDIUM + zero MAJOR_DISTORTION + zero UNVERIFIABLE) |
| Traceable workflow | Every stage's deliverables are recorded, enabling retrospective audit |

## Audit Trail

When the pipeline ends, state_tracker_agent produces a complete audit trail:

```
Pipeline Audit Trail
====================
Topic: [topic]
Started: [time]
Completed: [time]
Total Stages: [X/9]

Stage 1 RESEARCH: [mode] -> [output count]
Stage 2 WRITE: [mode] -> [word count]
Stage 2.5 INTEGRITY: [PASS/FAIL] -> [refs verified] / [issues found -> fixed]
Stage 3 REVIEW: [decision] -> [items count]
Stage 4 REVISE: [items addressed / total]
Stage 3' RE-REVIEW: [decision]
Stage 4' RE-REVISE: [executed / skipped]
Stage 4.5 FINAL INTEGRITY: [PASS/FAIL] -> [refs verified]
Stage 5 FINALIZE: Ask format style -> MD -> DOCX via Pandoc when available (otherwise instructions) -> LaTeX (apa7/ieee/etc.) -> tectonic -> PDF
Stage 6 PROCESS SUMMARY: Ask language -> MD -> LaTeX -> PDF (zh/en)

Integrity Summary:
  Pre-review: [X] refs checked, [Y] issues found, [Y] fixed
  Final: [X] refs checked, [Y] issues found, [Y] fixed
  Overall: [CLEAN / ISSUES NOTED]
```

## Computational reproducibility (v3.3.5+)

This document defines PROCESS reproducibility — consistent stages, fixed reviewer angles,
explicit pass/fail thresholds. That's one of two meanings of "reproducible."

The other is COMPUTATIONAL re-run — could a third party re-execute the same pipeline and
produce the same (or near-same) output? For that, see [`../../shared/artifact_reproducibility_pattern.md`](../../shared/artifact_reproducibility_pattern.md).

Process reproducibility is enforced at the pipeline level. Computational documentation is
captured in the Material Passport's optional `repro_lock` sub-block. Both are complementary;
neither replaces the other.
