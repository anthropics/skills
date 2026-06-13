# Code Handoff Lite Template `[L1]`

## Goal

Provide the only truthful entrypoint for `/code` in L1 tasks. Minimal surface compared to the Full handoff.

## Must Capture

- `code_ready`: boolean
- `approval_basis`: what the user approved in A-Lite
- `repo_grounding`: repo facts the plan depends on
- `frozen_product_decisions`: high-impact product semantics that may not drift
- `file_plan`: file-by-file change plan
- `implementation_units`: each unit captures goal, files, exact changes, verification, done signals
- `verification_commands`: command-level checks
- `browser_checks`: user-visible walkthrough checks (if web app)
- `acceptance_checks`: what must be true to call the work done
- `allowed_decisions`: what the coder may decide independently
- `forbidden_decisions`: what the coder must not decide
- `reentry_triggers`: what would force a return to planning
- `unresolved_gaps`: must be empty for code_ready=true

## Each Implementation Unit Must Capture

- goal
- files (concrete paths)
- exact change list
- verification (per unit)
- done signals
