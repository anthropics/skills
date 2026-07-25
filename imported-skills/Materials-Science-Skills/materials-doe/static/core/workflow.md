# DOE Workflow

## 1. Frame the objective

Classify the task as screening, characterization, optimization, robust design,
statistical mixture design, or engineering mix proportioning. Record responses,
candidate factors, units, ranges, hard constraints, and practical run limits.

## 2. Resolve the route

Select `design_mode`, material routes, deliverable, and output format from the
manifest. Read each resolved file once. Do not load a companion skill until a
handoff is requested.

## 3. Validate inputs

Before matrix generation:

- confirm every factor and level or bound;
- distinguish independent factors from components constrained to a total;
- identify controls, blocks, nuisance variables, and interaction risks;
- define replication, center points, and randomization;
- reject infeasible component bounds or impossible run counts.

Use `[needs data: ...]` for missing decisions.

## 4. Build and verify the design

Generate the selected matrix with coded and natural units. Verify the invariant
required by that route: balance and orthogonality, alias structure, estimable
quadratic terms, or mixture totals and bounds. Keep standard order separate
from randomized run order.

## 5. Define analysis

Name the model, effects, diagnostics, lack-of-fit or error estimate, and
confirmation strategy. Do not claim power, significance, or an optimum without
the inputs or observations required to support it.

## 6. Deliver and hand off

Return the factor table, matrix, assumptions, verification result, analysis
plan, and unresolved decisions. Emit `experiment-record.yaml` by default using
the shared schema. Add CSV, scripts, methods prose, figures, or downstream
skill handoffs only when requested.
