---
name: ci-failure-triage
description: Triage CI failures using artifact-first checks. Use when users need fast root-cause isolation from failing runs, integrity verification, and deterministic reruns.
license: Apache-2.0
---

# CI Failure Triage

Use this skill to isolate failing CI causes with deterministic artifact checks.

## Gait Context

Gait is an offline-first runtime for AI agents that enforces tool-boundary policy, emits signed and verifiable evidence artifacts, and supports deterministic regressions.

Use this skill when:
- incident triage requires artifact-first root-cause isolation
- CI gate failures need deterministic reruns tied to a failing artifact
- evidence outputs must be generated from Gait artifacts

Do not use this skill when:
- Gait CLI is unavailable in the environment
- no Gait run/pack artifact or run identifier is available as input

## Required Inputs

- `failure_target`: failing run id, runpack path, or pack path.
- `baseline_target` (optional): known-good runpack or pack for diff.
- `workdir`: writable directory for triage outputs.

## Workflow

1. Verify the failing artifact first:
   - `gait verify <failure_target> --json`
2. Enter an isolated triage workspace:
   - `mkdir -p <workdir> && cd <workdir>`
3. If failure came from regress grading, bind reruns to the requested target:
   - `gait regress init --from <failure_target> --json`
   - `gait regress run --json`
4. If baseline evidence exists, compute deterministic diff:
   - `gait pack diff <baseline_target> <failure_target> --json`
5. If environment health is uncertain, run diagnostics:
   - `gait doctor --json`
6. Return triage summary:
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
mkdir -p ./triage && cd ./triage
gait regress init --from ../artifacts/runpack_failed.zip --json
gait regress run --json
gait doctor --json
```

Expected result:
- verify output reports integrity status for the target artifact
- regress init output references the requested `failure_target`
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
