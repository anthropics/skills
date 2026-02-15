---
name: incident-to-regression
description: Convert incident artifacts into deterministic regression fixtures and CI-ready outputs. Use when users ask to reproduce a failure, build repeatable graders, or emit junit evidence.
license: Apache-2.0
---

# Incident To Regression

Use this skill to transform an observed incident into deterministic regression checks.

## Required Inputs

- `run_source`: run id, runpack path, or equivalent source accepted by `gait regress init`.
- `workdir`: writable working directory where fixtures and outputs will be created.

## Workflow

1. Initialize deterministic fixture from the incident source:
   - `gait regress init --from <run_source> --json`
2. Parse fields from init output and record them:
   - `ok`, `run_id`, `fixture_name`, `fixture_dir`, `config_path`, `next_commands`
3. Execute regression graders:
   - `gait regress run --json`
4. If CI evidence is needed, rerun with JUnit output:
   - `gait regress run --json --junit <junit_path>`
5. Return a concise summary with:
   - source identifier
   - fixture directory and config path
   - status and failed grader count
   - evidence output paths

## Safety And Portability Rules

- Use CLI outputs only; do not infer grader results from config text.
- Treat non-zero regress exit codes as actionable outcomes, not warnings.
- Do not assume repository-specific fixture paths.
- Keep paths relative to the active workspace unless the user explicitly asks for absolute paths.

## Usage Example

```bash
gait regress init --from run_demo --json
gait regress run --json --junit ./artifacts/junit.xml
```

Expected result:
- init output includes `ok=true` and a `fixture_dir`
- run output includes stable `status` and grader failure details
- JUnit file exists at `./artifacts/junit.xml`

## Validation Example

```bash
gait regress run --json > ./artifacts/regress_result.json
python3 - <<'PY'
import json
from pathlib import Path
p = json.loads(Path('./artifacts/regress_result.json').read_text(encoding='utf-8'))
assert p.get('status') in {'pass', 'fail'}
print('validated status:', p.get('status'))
PY
```

Expected result:
- script prints `validated status: pass` or `validated status: fail`

## Provider Notes (Anthropic Claude)

- Ask Claude to use the `incident-to-regression` skill by name when this workflow applies.
- Keep outputs grounded in command results and `--json` payload fields.
