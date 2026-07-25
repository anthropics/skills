# Code Experiment Plan

## Material Passport

- Origin Skill: experiment-agent
- Origin Mode: plan
- Origin Date: [ISO 8601]
- Verification Status: UNVERIFIED
- Version Label: code_plan_v1

## Experiment Overview

- **Title**: [descriptive name]
- **Objective**: [what this experiment tests]
- **Hypothesis**: [expected outcome, if any]
- **Type**: [training | analysis | etl | simulation | generic]

## Setup

- **Language/Framework**: [e.g., Python 3.11, PyTorch 2.x]
- **Entry Command**: `[exact command to run]`
- **Working Directory**: `[path]`
- **Dependencies**: [list or "see requirements.txt"]
- **Environment**: [OS, GPU, memory requirements if relevant]

## Inputs

| Input | Path | Description |
|-------|------|-------------|
| [name] | [path] | [what it is] |

## Expected Outputs

| Output | Path | Format | Success Criterion |
|--------|------|--------|------------------|
| [name] | [path] | [CSV/JSON/model/figure] | [e.g., "file exists and > 0 bytes"] |

## Monitoring Configuration

- **Timeout**: [duration, default 30 min]
- **Monitor files**: [paths to watch for progress]
- **Experiment type override**: [if auto-detection should be overridden]
- **Metric file**: [path to loss/metric log, if applicable]
- **Metric key**: [column/field name, if applicable]

## Analysis Plan

- **Primary metric**: [what to look at first]
- **Success threshold**: [e.g., "accuracy > 0.90", "p < .05"]
- **Comparison**: [baseline, previous run, theoretical expectation]
