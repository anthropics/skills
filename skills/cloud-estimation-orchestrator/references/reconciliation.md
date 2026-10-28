# Reconciliation before consolidation

Read when estimates overlap, earlier work exists or sources disagree. Apply
the final checks to the merged model before building the workbook.

## Normalise evidence and coverage

Compare each existing estimate against scope, environment, deliverable,
acceptance criterion, date, units and evidence. Preserve its source and
exclusions. A matching task label or an earlier budget does not prove delivery.
Separate completed work, funded-but-unperformed work, partial coverage and
work outside the agreed scope.

Use an explicit reconciliation ledger keyed by stable task ID. In task notes
record gross low/likely/high JH, proven covered JH on the same basis, net
additional JH and the reason. Net equals gross minus evidenced coverage;
if coverage exceeds gross, resolve the scope mismatch before proceeding.
The task's three numeric JH fields contain net additional effort. Already
covered or excluded rows remain traceable with zero additional JH and an
explanation. Do not invent equal low/likely/high values to fill unknowns.

Coverage of initial setup does not cover recurring operations. Represent
Build and Run as separate tasks with separate acceptance evidence and units.
Keep recurring work monthly; convert an annual baseline explicitly.

## Assign owners and stable IDs

Before domain handoff, maintain a shared deliverable-to-owner register and
reserve IDs by scope and environment. Infrastructure provisioning, pipeline
integration and security validation may concern one component while producing
different deliverables. Keep those distinct; shared activities such as
logging setup or restore testing have one counted owner.

For each incoming task, compare scope, environment, deliverable, acceptance
criterion and dependencies. Use semantics and evidence, not label similarity:

- Same ID and same work: retain one canonical row and combine source evidence;
  do not add the JH estimates together.
- Different IDs for the same work: choose a stable canonical ID, record aliases
  in notes and rewrite all dependency references before dropping duplicates.
- Same ID but different work or conflicting numbers: record the conflict and
  resolve it with the domain owner. Do not keep whichever row arrived last.
- Overlapping but different work: split the scope into owned deliverables and
  obtain revised net effort from the relevant domains.

Then enforce unique task IDs, no missing dependencies, no self-references and
no cycles through the shared model loader. Independently enforce uniqueness
and semantic de-duplication of inventory, architecture, sources, risks,
decisions and cost rows: the loader does not validate all those identities.
Merge identical shared assumptions once; contradictory values remain a
decision, never an average.

## Price contradictory branches

When sources disagree on a material requirement, capture both statements,
their dates and authority. Create a decision with question, alternatives,
owner role, deadline, evidence needed and status. Domain outputs must quantify
each branch's Build JH, monthly Run JH, recurring cloud and non-cloud costs,
capacity and residual risk at an equal service perimeter.

The three standard scenarios are service/resilience variants, not arbitrary
architecture-branch names. Evaluate incompatible architectures or scope
branches as separate complete models, each using the same three scenarios.
Retain the branch comparison and numerical deltas in decision rationale and
notes. Merge only the selected branch's tasks into the final model; never
combine mutually exclusive effort registers. If no branch is selected,
label the current branch provisional and keep final delivery blocked where
the choice is required.

Provider alternatives may share the same task register while occupying
separate cost groups. Never sum competing providers into the recommendation's
total. Compare three-year TCO using the same horizon and perimeter: one-off
Build, monthly human Run, provider charges and non-cloud OPEX, with explicit
growth, commitments, FX and price-date assumptions. Reference calculation
cells for any numeric comparison stated in prose.

## Schedule and topology reconciliation

Place tasks on calendar periods respecting prerequisites, available roles,
working days and capacity assumptions. Count Build JH allocated to each
period; compare with available JH and record every overload in risks and
decisions. Sequence labels alone do not prove a feasible schedule. Run demand
uses recurring operations capacity; it is not added to one-off delivery JH.

Create the explicit flow register from the same inventory IDs used for
architecture decisions. Record edge ID, endpoints, purpose and evidence.
Draw before the final estimate, then resolve topology findings with the
owning domains and update affected JH and costs. Re-render after such changes.
Check every node and flow across all environments, including cross-zone and
cross-environment connections. No implicit arrow may stand in for evidence.

## Final reconciliation evidence

Before delivery, produce a compact check register with the artifact examined,
expected result, observed count, pass/fail and unresolved action. Include:

- Gross/covered/net ledger and the canonical-ID alias map; all net task JH
  reconcile to separate Build and monthly Run synthesis values.
- Each task lot covered in phasing, plus period allocations and capacity
  checks; all overloads visible and unresolved dependencies surfaced.
- Provider/environment/scenario cost totals, verified price sources, explicit
  incomplete prices and separation of alternatives and non-cloud OPEX.
- Final diagram manifest IDs against inventory, all edge endpoints against
  the flow register, and the inspected render after workbook recalculation.
- Every numeric prose assertion mapped to its calculated source and supplied
  to the workbook validator, including TCO or scheduling extensions checked
  independently when outside the standard validator's scope.
- Recalculation engine and native-opening status; workbook validator `ok`
  and zero counts for errors, stale/missing caches, semantic mismatches,
  table/filter overlaps, reconciliation errors and forbidden identifiers.

A mechanical structure test checks frontmatter and resource paths only. It
cannot prove routing quality, measured evidence, coverage decisions or gate
enforcement. Validate those later with an independent synthetic request and
inspection of the produced workbook, model and check register.
