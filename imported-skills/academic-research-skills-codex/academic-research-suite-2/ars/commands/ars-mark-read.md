---
description: ARS /ars-mark-read — record human-read signal for one or more citation keys
model: sonnet
---

Acknowledge that the user has personally read the source(s) backing the named citation key(s), so the next finalizer pass can promote `<!--ref:slug LOW-WARN-->` to `<!--ref:slug ok-->` for each acknowledged slug. Per v3.6.8 spec §3.6, the signal is stored in a session-scoped peer file `<passport-stem>_human_read_log.yaml` next to the active Material Passport; `literature_corpus[]` is adapter-owned and is NEVER mutated to carry `human_read_source`.

The dispatching agent substitutes `<path>` below with the active Material Passport path from session context before executing (the quoting is preserved so paths containing spaces remain a single argument). The CLI handles validation (citation_key must exist in `literature_corpus[]`; on miss emit `[ARS-MARK-READ ERROR: citation_key '<slug>' not in literature_corpus[]]` and refuse to write), 4 fail-fast environment checks (no active passport / passport not found / parent unreadable / read-log unwritable), and append-only write per §3.6 firm rule 3.

Implementation:
```bash
python3 scripts/ars_mark_read.py $ARGUMENTS --passport-path "<path>"
```

Mode reference: `docs/design/2026-04-30-ars-v3.6.8-trust-provenance-and-drift-transparency-spec.md` §3.6 + Step 7.
