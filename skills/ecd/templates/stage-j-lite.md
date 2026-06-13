# Stage J-Lite Template `[L1]`

## Goal

Compile A-Lite output directly into a minimal code-ready handoff. No companion docs.

## Must Capture

- `code_ready`: boolean — set true only when the next coding model can implement without inventing product meaning
- `blocking_gaps`: any unresolved issues that prevent code_ready=true
- `repo_grounding`: repo facts the plan depends on
- `frozen_product_decisions`: high-impact product semantics that may not drift
- `file_plan`: file-by-file change plan
- `implementation_units`: simplified units (goal + files + verification per unit)
- `verification_commands`: command-level checks
- `browser_checks`: user-visible walkthrough checks (if applicable)
- `acceptance_checks`: what must be true to call the work done
- `allowed_decisions`: what the coder may decide
- `forbidden_decisions`: what the coder must not decide
- `reentry_triggers`: what would force a return to planning

## Exit Gate

- `90-code-handoff.md` is complete and truthful
- `code_ready=true` is justified
- No companion docs (91/92/95/96/98/99) are needed for L1
