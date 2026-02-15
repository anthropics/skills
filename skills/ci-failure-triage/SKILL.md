---
name: ci-failure-triage
description: Triage CI failures using artifact-first checks. Use when users need fast root-cause isolation from failing runs, integrity verification, and deterministic reruns.
license: Apache-2.0
---

# CI Failure Triage

Use this skill to isolate failing CI causes with deterministic artifact checks.

## Required Inputs

- `failure_target`: failing run id, runpack path, or pack path.
- `baseline_target` (optional): known-good runpack or pack for diff.
- `workdir`: writable directory for triage outputs.

## Workflow

1. Verify the failing artifact first:
   - `gait verify <failure_target> --json`
2. If failure came from regress grading, rerun deterministically:
   - `gait regress run --json`
3. If baseline evidence exists, compute deterministic diff:
   - `gait pack diff <baseline_target> <failure_target> --json`
4. If environment health is uncertain, run diagnostics:
   - `gait doctor --json`
5. Return triage summary:
   - integrity status
   - failing stage and reason codes
   - diff highlights (if provided)
   - exact next command to reproduce

## Safety And Portability Rules

- Never classify root cause without command output evidence.
- Do not rely on CI provider-specific APIs when local artifacts are available.
- Preserve stable exit-code semantics in reporting.
- Keep recommendations reproducible with copy-pastable commands.

## Usage Example

```bash
gait verify ./artifacts/runpack_failed.zip --json
gait doctor --json
gait regress run --json
```

Expected result:
- verify output reports integrity status for the target artifact
- doctor output reports actionable diagnostics
- regress output reports stable pass/fail status and failures

## Validation Example

```bash
gait verify ./artifacts/runpack_failed.zip --json > ./artifacts/verify.json
python3 - <<'PY'
import json
from pathlib import Path
p = json.loads(Path('./artifacts/verify.json').read_text(encoding='utf-8'))
assert 'ok' in p
assert 'manifest_digest' in p
print('validated verify payload keys present')
PY
```

Expected result:
- script prints `validated verify payload keys present`

## Provider Notes (Anthropic Claude)

- Ask Claude to use the `ci-failure-triage` skill by name when this workflow applies.
- Keep outputs grounded in command results and `--json` payload fields.
