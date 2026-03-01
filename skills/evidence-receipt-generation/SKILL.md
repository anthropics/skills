---
name: evidence-receipt-generation
description: Generate portable evidence receipts from run artifacts. Use when users ask for ticket-ready proof, receipt footers, or integrity-backed handoff metadata.
license: Apache-2.0
---

# Evidence Receipt Generation

Use this skill to generate integrity-backed receipts that are portable across CI, tickets, and audit handoff.

## Gait Context

Gait is an offline-first runtime for AI agents that enforces tool-boundary policy, emits signed and verifiable evidence artifacts, and supports deterministic regressions.

Use this skill when:
- incident triage needs portable receipt handoff proof
- CI gate failures require receipt/evidence attachment
- evidence outputs must be generated from Gait artifacts

Do not use this skill when:
- Gait CLI is unavailable in the environment
- no Gait run/pack artifact or run identifier is available as input

## Required Inputs

- `source`: run id, runpack path, or pack path.
- `out_path` (optional): destination file for JSON receipt output.

## Workflow

1. Verify integrity before receipt generation:
   - `gait verify <source> --json`
2. Generate receipt from source artifact:
   - when `out_path` is provided: `gait run receipt --from <source> --json > <out_path>`
   - when `out_path` is omitted: `gait run receipt --from <source> --json`
3. Parse receipt fields for handoff from `out_path` (if set) or stdout:
   - `ok`, `run_id`, `manifest_digest`, `ticket_footer`, `bundle`
4. Return concise evidence block containing:
   - source identifier
   - manifest digest
   - ticket footer text
   - verification status

## Safety And Portability Rules

- Never invent digests, run ids, or receipt text.
- Treat failed verification as a blocking state for receipt publication.
- Keep receipt output machine-readable and transportable.
- Avoid environment-specific absolute paths in final handoff.

## Usage Example

```bash
gait demo --json
mkdir -p ./artifacts
gait verify run_demo --json
gait run receipt --from run_demo --json > ./artifacts/receipt.json
```

Expected result:
- verify returns `ok=true` for intact artifacts
- receipt file contains a non-empty `ticket_footer` suitable for issue or PR evidence

## Validation Example

```bash
gait demo --json
mkdir -p ./artifacts
gait run receipt --from run_demo --json > ./artifacts/receipt.json
python3 - <<'PY'
import json
from pathlib import Path
p = json.loads(Path('./artifacts/receipt.json').read_text(encoding='utf-8'))
assert p.get('ok') is True
assert str(p.get('ticket_footer', '')).strip()
print('validated receipt footer present')
PY
```

Expected result:
- script prints `validated receipt footer present`

## Provider Notes (Anthropic Claude)

- Ask Claude to use the `evidence-receipt-generation` skill by name when this workflow applies.
- Keep outputs grounded in command results and `--json` payload fields.
