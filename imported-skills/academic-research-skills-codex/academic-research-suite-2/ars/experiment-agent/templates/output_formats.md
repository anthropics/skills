# Output Format Templates

All outputs use Markdown-based structured format with Material Passport for ARS compatibility. Planning templates in `code_experiment_plan.md` and `study_protocol.md` follow the same rule.

## Experiment Result (from run mode)

```markdown
## Material Passport

- Origin Skill: experiment-agent
- Origin Mode: run
- Origin Date: [ISO 8601]
- Verification Status: UNVERIFIED
- Version Label: exp_result_v1

## Experiment Result

- **ID**: [unique id]
- **Type**: [training | analysis | etl | simulation | generic]
- **Status**: [completed | crashed | timeout | stopped_by_user]
- **Command**: [executed command]
- **Working Directory**: [path]
- **Duration**: [seconds]
- **Exit Code**: [int]

### Output Files

| File | Size |
|------|------|
| [path] | [size] |

### Output Summary

[Auto-generated summary of structured output, if available]

### Anomalies Detected

[List of anomalies detected during monitoring, or "None"]
```

## Study Status (from manage mode)

```markdown
## Material Passport

- Origin Skill: experiment-agent
- Origin Mode: manage
- Origin Date: [ISO 8601]
- Verification Status: UNVERIFIED
- Version Label: study_status_v1

## Study Status

- **ID**: [unique id]
- **Type**: [survey | experiment | field_study | interview | mixed]
- **Phase**: [planning | ethics_review | collecting | collected | paused]
- **Design**: [description]
- **Progress**: [current_n] / [target_n] ([completion_rate]%)
- **Timeline**: [start] to [expected_end] — [on_track | behind | ahead]

### Ethics Status

- **Status**: [READY | ETHICS_PENDING | ETHICS_BLOCKED]
- **Blocked Items**: [list or "None"]

### Risks

[List of detected risks with suggestions, or "None"]

### Data Readiness

- **Samples**: [n]
- **Missing Rate**: [rate]
- **Format Consistent**: [yes/no]
- **Ready for Analysis**: [yes/no]
- **Blockers**: [list or "None"]
```

## Validation Report (from validate mode)

```markdown
## Material Passport

- Origin Skill: experiment-agent
- Origin Mode: validate
- Origin Date: [ISO 8601]
- Verification Status: [ANALYZED | VERIFIED]
- Version Label: validation_v1

## Validation Report

- **Source**: [exp_id | external | manual_study]
- **Overall Confidence**: [SOLID | CAUTION | RED_FLAG]

### Statistical Findings

| Metric | Test | Value | Effect Size | Confidence |
|--------|------|-------|-------------|------------|
| [name] | [test] | [stat, p] | [size, class] | [SOLID/CAUTION/RED_FLAG] |

### Warnings

| Type | Detail | Affected |
|------|--------|----------|
| [type] | [detail] | [metrics] |

### Fallacy Scan

- **Coverage**: [N]/11 fallacy types checked

| Fallacy | Severity | Detail | Recommendation |
|---------|----------|--------|----------------|
| [type] | [RED_FLAG/CAUTION/NOTE] | [detail] | [suggestion] |

### Reproducibility (if applicable)

- **Method**: [re-run deterministic | re-run stochastic | re-run environment-sensitive | not run | N/A]
- **Verdict**: [REPRODUCIBLE | PARTIALLY_REPRODUCIBLE | NOT_REPRODUCIBLE | CANNOT_VERIFY | N/A]

| Metric | Original | Re-run | Diff | Status |
|--------|----------|--------|------|--------|
| [name] | [value] | [value] | [diff] | [MATCH/WITHIN_TOLERANCE/MISMATCH] |
```
