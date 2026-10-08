---
name: cloud-architecture-advisor
description: Compare VPS, virtual machines, serverless containers, managed platforms, microservices and Kubernetes against workload and operating constraints. Use for an ADR-style hosting recommendation, rejected alternatives and explicit effort, cost and risk tradeoffs.
---

# Cloud architecture advisor

**Created by the repository maintainers.** This open-source skill provides
generic architecture decision methodology without client-specific inputs.

**Licence:** CC BY 4.0. Share and adapt for any purpose with credit to the
repository maintainers. Include the full licence in the distributed bundle.

**Feedback & support:** Route methodology feedback to the maintainer contact
that distributed the suite; use a public issue tracker only once one exists.
Correct execution mistakes before proposing methodology changes.

Produce an ADR-style recommendation and rejected options in the common
`EstimateModel`, with a validated XLSX as the primary deliverable. In a
consolidated estimate, hand records to the shared merge. Quantify scoped
infrastructure effort in JH (jour-homme); eight hours per JH is editable.
Keep Build JH, monthly Run JH, cloud OPEX and non-cloud OPEX separate.

## Compare within scope

Read [references/decision-matrix.md](references/decision-matrix.md) to frame
hosting alternatives, evidence, suitability and output mappings. Read
[references/domain-contract.json](references/domain-contract.json) for the
machine-readable record interface. Compare only relevant alternatives at
equal service perimeter, workload, growth horizon and recovery targets.

Establish environments, team capability, portability, compliance, operator
responsibilities and cost horizon. Classify components as live, partially
deployed, planned or unknown; measure live behaviour and estimate unfinished
work. Where access is missing, produce a read-only measurement instrument
and a blocking measurement task rather than inventing load or capacity.

Distinguish hosting runtime from application decomposition: microservices may
run on several hosting types. An architecture option may require application
refactoring; record that dependency and its separate owner, exclusion and
unknown effort. Do not include it in infrastructure JH or recommend the
option as fully costed without the missing application estimate. Containers
alone do not justify Kubernetes; detailed cluster work belongs to its domain.
Provider selection, load simulation, security controls and delivery pipeline
implementation require their own domain scope and owners.

Reject infeasible options before scoring. Compare workload fit, team skills,
portability, resilience, compliance, operating burden and cost horizon using
visible criteria and evidence. Expose unknown criteria and sensitivity to
weights; a weighted score cannot waive a mandatory constraint. State why the
chosen option wins, why others lose, residual risks and the conditions that
would change the recommendation.

## Connect decisions to estimates

Reconcile prior estimates and proven coverage before adding architecture
assessment or infrastructure work. Contradictions become explicit priced
decision branches. Draw each candidate's inventory and evidenced flows before
finalising its estimate; every untraceable edge becomes an issue or assumption.

Compare `Economique`, `Standard` and `Resilient` within each eligible hosting
option. Scenarios express service-level variants, not different architecture
names. Keep alternative work and cost branches separate; the common model
has no branch selector, so do not sum mutually exclusive candidates. Use
one complete model/workbook per alternative and one selected-model workbook
for the recommendation, with comparable deltas in its decision notes.

Build cost drivers from system behaviour, including usage, network/egress,
observability, registry/build, support, backups and recovery. Verify mutable
prices against current official sources or authorised billing exports and
record region, SKU, unit, currency, capture date and confidence. Keep unknown
prices `A chiffrer` in assumptions and decisions; never turn them into zero
numeric cost rows. Show transferred operator JH beside managed-service fees.
State the horizon and any growth or discount assumptions for TCO.

Project scoped tasks onto periods and compare Build JH with available
capacity. Use the locally supplied common loader, builder, renderer,
recalculation adapter and validator. Preserve all twelve sheets, editable
inputs and formulas; mark irrelevant sections `Non applicable` with a reason.

Read [references/common-methodology.md](references/common-methodology.md) when
constructing the complete model or using the local workbook runtime.

## Pre-delivery gate

Re-read these rules and the relevant reference against the final artifacts.
Record pass/fail and counts for these checks:

- Option, decision, risk and cost-driver records map to the common contract;
  the recommendation and rejected options preserve evidence and ADR status.
- All mandatory constraints are met; comparisons share scope and horizon;
  unknown measurements or criteria remain explicit and recommendation
  sensitivity is checked. Required unknowns block an unconditional decision.
- Alternative models remain separate; shared work has one owner; net JH are
  supported by coverage evidence; application changes stay separately scoped.
- Scenarios keep the same perimeter, operational burden and recovery targets
  are visible, and effort/cost deltas reconcile with the chosen branch.
- Prices and usage have dated sources; incomplete prices or application
  dependencies prevent claiming complete TCO. Build, Run/month, cloud OPEX
  and non-cloud OPEX stay separate; calendar overloads are reported.
- Model loads, dependencies resolve, diagrams match inventory and flow
  evidence, and recalculation/cached-value checks pass. Reopen the workbook;
  validate all numeric narrative assertions and diagram IDs, with zero
  formula, total-reconciliation and table/filter-overlap errors.
- Anonymisation returns zero forbidden identifiers, followed by a combined
  review of names, paths, topology, dates and amounts for re-identification.
- Every referenced resource exists; skill delivery requires its full licence
  and self-contained, manifest-matching `.skill` archive with no build artifacts.

Repair failures and rerun affected checks. If a mandatory input or decision
is unavailable, retain a labelled draft with the precise blocker. Deliver
the validated XLSX and model with rationale, exclusions, remaining decisions,
verification evidence and recalculation engine disclosed.
