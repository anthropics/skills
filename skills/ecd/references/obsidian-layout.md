# Obsidian Layout

## Default Folder

Render the bundle under:

`<vault-root>/Topics/Evolution-Constraint-Language/<date>-<case-slug>/`

If `output_root` is provided, use that base folder instead. If the caller passes `--output`, use the explicit directory.

## Required Files

- `00-overview.md`
- `05-constraint-ledger.md`
- `10-a-preprocess.md`
- `20-b-divergence.md`
- `30-c-requirements.md`
- `40-d-critique.md`
- `50-e-closure.md`
- `60-f-probes.md`
- `70-g-red-blue.md`
- `80-h-review.md`
- `90-code-handoff.md`
- `91-canonical-contracts.md`
- `92-constraint-crosswalk.md`
- `95-execution-manifest.md`
- `96-code-batches.md`
- `97-code-preflight.md`
- `98-j-compile-for-code.md`
- `99-code-handoff.md`

Optional:

- `00-overview-map.canvas`
- `Runs/<run-id>/00-code-run.md`
- `Runs/<run-id>/01-verification.md`
- `Runs/<run-id>/02-reentry.md` only when `/code` blocks or refuses
- `Runs/<run-id>/03-achieve.md` when `/achieve` is executed; this note is the acceptance-and-archive closure record
- `OpenSpec/changes/<case-slug>/proposal.md`
- `OpenSpec/changes/<case-slug>/design.md`
- `OpenSpec/changes/<case-slug>/tasks.md`
- `OpenSpec/specs/<case-slug>/spec.md`

## Section Order

For `00-overview.md`:

1. Title
2. Summary
3. Source request
4. Final outcome
5. Stage status index
6. Paths
7. Structured block

For every stage note:

1. Title
2. Navigation line
3. Goal
4. Narrative
5. Key points
6. Decisions
7. Open questions
8. Next actions
9. Structured block

For artifact notes such as `05` and `90`:

1. Title
2. Link back to `[[00-overview]]`
3. Goal or role summary
4. Key sections exposing frozen content
5. Structured block

## Link Conventions

- Link every note back to `[[00-overview]]`.
- Link stage notes to immediate previous and next notes when they exist.
- Keep wikilinks filename-based without `.md`.
- Link `00-code-run.md` to `[[90-code-handoff]]`.
- Link `01-verification.md`, `02-reentry.md`, and `03-achieve.md` back to `[[00-code-run]]`.
