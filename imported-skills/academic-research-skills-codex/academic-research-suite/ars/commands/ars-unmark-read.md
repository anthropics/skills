---
description: ARS /ars-unmark-read — rescind a prior human-read mark for one or more citation keys
model: sonnet
---

Rescind a previously recorded human-read signal for the named citation key(s). Per v3.6.8 spec §3.6 firm rule 3, the session-scoped peer file `<passport-stem>_human_read_log.yaml` is append-only: rescind writes a `rescinded_at: <ISO 8601>` field on the matching entry rather than deleting it, so audit replay can reconstruct the user's signal trajectory. The next finalizer pass will demote `<!--ref:slug ok-->` back to `<!--ref:slug LOW-WARN-->` for each rescinded slug.

The dispatching agent substitutes `<path>` below with the active Material Passport path from session context before executing (the quoting is preserved so paths containing spaces remain a single argument). The CLI requires the citation_key to exist in `literature_corpus[]` AND to have an unrescinded prior mark in the read-log; hard-fails otherwise with the canonical `[ARS-MARK-READ ERROR: ...]` message.

Implementation:
```bash
python3 scripts/ars_mark_read.py $ARGUMENTS --passport-path "<path>" --unmark
```

Mode reference: `docs/design/2026-04-30-ars-v3.6.8-trust-provenance-and-drift-transparency-spec.md` §3.6 + Step 7.
