---
name: evidence-receipt-generation
description: Generate portable evidence receipts from run artifacts. Use when users ask for ticket-ready proof, receipt footers, or integrity-backed handoff metadata.
license: Apache-2.0
---

# Evidence Receipt Generation

Use this skill to generate integrity-backed receipts that are portable across CI, tickets, and audit handoff.

## Required Inputs

- `source`: run id, runpack path, or pack path.
- `out_path` (optional): destination file for JSON receipt output.

## Workflow

1. Verify integrity before receipt generation:
   - `gait verify <source> --json`
2. Generate receipt from source artifact:
   - `gait run receipt --from <source> --json`
3. Parse receipt fields for handoff:
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
gait verify ./artifacts/runpack.zip --json
gait run receipt --from ./artifacts/runpack.zip --json
```

Expected result:
- verify returns `ok=true` for intact artifacts
- receipt returns a non-empty `ticket_footer` suitable for issue or PR evidence

## Validation Example

```bash
gait run receipt --from ./artifacts/runpack.zip --json > ./artifacts/receipt.json
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
