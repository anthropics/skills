# Handoff Quality Bar

Use this reference before setting `ecl.code_handoff.code_ready=true`.

## Core Rule

The handoff is code-ready only if the next coding model can implement without inventing high-impact meaning.

If the coder would still need to ask what the product means, how data should behave, or how success is judged, the handoff is not ready.

## Required Freeze Surface

The handoff must explicitly freeze:

- `repo_grounding`: repo facts that the plan depends on
- `frozen_product_decisions`: high-impact product semantics that may not drift
- `domain_model`: key entities, fields, states, and invariants
- `data_contract`: persistence or API behavior, even if the answer is "browser local state only"
- `ui_contract`: routes, panels, forms, views, and empty/error/loading states
- `function_contracts`: the concrete functions or modules the coder must create or modify
- `file_plan`: file-by-file change plan
- `implementation_units`: ordered execution units
- `verification_commands`: command-level checks
- `browser_checks`: user-visible walkthrough checks
- `acceptance_checks`: what must be true to call the work done

## Implementation Unit Bar

Every implementation unit should answer:

- what it changes
- why it exists
- which files it owns
- which functions or modules it creates or edits
- which earlier units it depends on
- how the coder verifies it before moving on
- what "done" means for that unit

## Web App Quality Bar

For React, Next.js, or Vite work, also freeze:

- state ownership
- optimistic or pessimistic persistence behavior
- copy for visible failure states
- browser interactions that must work on first open
- whether tests alone are sufficient or a browser pass is mandatory
- the exact visible UI pattern, not a disjunction such as "grouped or labeled"

## Failure Rule

If any of the above is left to "implementer decides", `code_ready` must remain `false`.
