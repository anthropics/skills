# OpenSpec Mapping

Use this reference when the user wants OpenSpec-compatible outputs in addition to the ECL bundle.

## Mapping

- `00-overview.md` + `05-constraint-ledger.md` + `10-a-preprocess.md` -> `proposal.md`
- `30-c-requirements.md` + retained option from `20-b-divergence.md` -> `specs/<change>/spec.md`
- `40-d-critique.md` + `50-e-closure.md` + `70-g-red-blue.md` + `95-execution-manifest.md` -> `design.md`
- `95-execution-manifest.md` + `96-code-batches.md` + `90-code-handoff.md` implementation units -> `tasks.md`

## Rules

- Export only after the approval gate is closed and A-H plus J have converged.
- Reflect the frozen path, not discarded alternatives.
- Preserve the same constraints, success semantics, and acceptance rules.
- Treat `tasks.md` as a dependency-aware execution view, not a flat dump of unit names.
- `tasks.md` should expose batch order, verification checkpoints, and done signals whenever the ECL bundle has them.
- If `code_ready=false`, the exported OpenSpec pack must also communicate that coding is not ready.
