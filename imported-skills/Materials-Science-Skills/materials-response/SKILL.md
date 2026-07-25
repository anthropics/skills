---
name: materials-response
version: "1.2.0"
stability: stable
description: Use when drafting, auditing, or strengthening point-by-point reviewer response letters for materials science and engineering manuscripts.
---

1. Read `manifest.yaml` paths from disk, including `always_load`.
2. Apply profile-first routing; detect all seven axes.
3. State `Route: response_task=...;comment_type=...;journal_family=...;tone=...;material_family=...;domain=...;experiment_type=...`.
4. Read selected paths; load shared evidence, weakness, stance, or ethics on demand.
5. Keep stable IDs; choose ACCEPT_TEXT, ACCEPT_ANALYSIS, SOFTEN_CLAIM, DISAGREE, or AUTHOR_INPUT_NEEDED.
6. Use the output contract for packages, audits, and proof.
7. Emit the package and composed `response-handoff`.
8. Check actions in the revised manuscript.

- Never invent evidence, locations, dates, or revisions.
- Missing proof requires `AUTHOR_INPUT_NEEDED` and blocked or drafted status.
- Keep concern, strategy, action, evidence, proof, input, and status separate.
