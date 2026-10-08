---
name: cloud-estimation-orchestrator
description: Consolidate multi-domain cloud and hosting estimates into one reconciled Excel workbook with delivery effort in JH and separate recurring costs. Use for shared intake, domain routing, existing-estimate reconciliation and prevention of double counting.
---

# Cloud estimation orchestrator

**Created by the repository maintainers.** This open-source skill coordinates
generic cloud estimation methodology; it contains no client-specific inputs.

**Licence:** CC BY 4.0. Share and adapt for any purpose with credit to the
repository maintainers. The distributed bundle must include the full licence.

**Feedback & support:** Send methodology feedback to the maintainers through
the contact that distributed the suite. Use a public issue tracker only once
one exists. Correct execution mistakes before treating them as methodology
changes.

Produce one merged, de-duplicated `EstimateModel` and one validated `.xlsx`.
The workbook is the primary deliverable. Delivery effort stays in JH
(jour-homme), with eight hours per JH as an editable default. Separate one-off
Build JH, monthly Run JH, cloud OPEX and non-cloud OPEX; never present their
sum as a usable workload or budget. Currency conversion uses an explicit TJM.

## Intake and domain ownership

Read [references/intake.md](references/intake.md) at intake to establish the
scope, evidence status and exact common model interface. Gather shared inputs
once, then route only the domains required by the request:

| Need | Domain skill | Ownership boundary |
|---|---|---|
| Provisioning and infrastructure work | `infra-work-estimator` | Landing zone, networks, services and infrastructure delivery |
| Hosting architecture alternatives | `cloud-architecture-advisor` | Architecture suitability and operational tradeoffs |
| Kubernetes suitability or platform work | `kubernetes-architect` | Cluster and platform responsibilities; containers alone do not justify Kubernetes |
| Build, delivery and security pipelines | `cicd-devsecops-estimator` | Pipeline controls, promotion, rollback and runners |
| Host security baseline | `server-hardening-estimator` | Server controls and restore evidence; application security requires explicit scope |
| Sizing and workload sensitivity | `hosting-capacity-simulator` | Capacity from measured load or labelled assumptions |
| Provider comparison | `cloud-provider-selector` | Eligibility, services, implementation effort and three-year TCO |
| Billing and usage optimisation | `finops-optimizer` | Measured baseline, savings, action effort and reversibility |
| Source-to-target transition | `cloud-migration-estimator` | Inventory, rehearsal, cutover, integrity, rollback and hypercare |
| Inventory-consistent topology | `cloud-architecture-diagrammer` | Explicit components and flows; diagram before final estimation |

Select these instruction sets without implying permission to spawn agents or
perform cloud mutations. Preserve the user's existing authorisation. If a
required domain skill is unavailable, record the uncovered scope and request
the necessary input; do not invent that domain's estimates.

Classify components as live, partially deployed, planned or unknown. Measure
live parts and estimate unfinished work. When access is missing, provide a
read-only measurement instrument and make its execution a blocking first
task; report unknown measurements explicitly.

## Consolidation

Read [references/reconciliation.md](references/reconciliation.md) when prior
estimates, overlapping responsibilities or contradictory sources exist, and
before merging domain outputs.

Give each domain the same scope, inventory IDs, assumptions, currency,
scenario definitions and source register. Require complete structured
outputs matching `EstimateModel`; narrative estimates alone cannot enter the
merge. Assign one owner to each shared deliverable, preserve stable task IDs
and resolve dependency aliases before loading the merged model.

Reconcile gross effort, proven existing coverage and net additional JH before
adding work. Keep measured, estimated and assumed values distinguishable.
Price incompatible requirements as separate decision branches and expose
their JH, recurring cost and risk deltas. Never silently select a convenient
source or add mutually exclusive options together.

Build the bill of materials from behaviour, including network and egress,
observability, build and registry, support, backups and recovery. Verify
mutable prices against current official sources or authorised billing
exports; record provider, service/SKU, region, unit, currency, capture date,
URL and confidence. Unverified prices remain `A chiffrer`, with affected
totals explicitly incomplete.

Use `Economique`, `Standard` and `Resilient` at the same service perimeter.
Keep accepted risks, RPO/RTO targets, transferred operator work and recurring
JH visible. Project Build work onto periods and compare it with available
capacity; surface overloads and dependencies before finalising.

## Draw, build and validate

Draw the topology from the merged inventory and explicit flow register before
finalising the estimate. Resolve every unknown node or edge into evidence, an
assumption or an open decision. Inspect the render for labels and crossing
flows. Use neutral symbols by default; official icon packs need verified
provenance and usage terms. The embedded diagram and workbook inventory must
describe the same components and flows.

Use the suite's shared model loader, workbook builder, diagram renderer,
recalculation adapter and workbook validator; their exact call interfaces and
limitations are in the intake reference. Keep all twelve contract sheets,
including explicit `Non applicable` explanations for irrelevant sections.
Keep scenario selection, totals and conversions as formulas. Preserve editable
inputs, named ranges and tables; never overlay sheet filters on table ranges.

Recalculate, then reopen in formula and values-only modes. Supply all numeric
prose assertions and diagram node IDs to the validator. Its default success
does not check omitted assertions or prove that an invented flow is real.
Use native Excel or LibreOffice when available. A calibrated Python fallback
must be disclosed; it cannot satisfy a required native-opening check.

Read [references/common-methodology.md](references/common-methodology.md) when
constructing the complete model or using the local workbook runtime.

## Pre-delivery gate

Re-read these rules and the relevant references against the final artifacts.
Record a positive pass/fail result and count for each check:

- The merged model loads; IDs are unique, dependencies resolve without cycles,
  domain ownership is complete, and covered work is counted only once.
- The workbook has all required sheets and columns, numeric JH in order,
  valid scenarios, separate Build/Run totals, and comparable alternatives.
- Recalculation succeeded; cached values are present; formula errors,
  semantic mismatches, table/filter overlaps and reconciliation errors are zero.
- Detail, phasing, synthesis and every numeric prose statement reconcile;
  provider/environment/scenario cost groups match; unresolved prices and
  decisions cannot masquerade as complete totals.
- Diagram node IDs match inventory IDs, flow endpoints match the flow
  register, and the embedded final render was inspected after recalculation.
- The confidentiality scan returns zero forbidden identifiers. Independently
  review names, domains, paths, topology, dates and amounts across all examples
  for combined re-identification; a pattern scan alone is insufficient.
- Every referenced resource exists in the delivered set. When delivering the
  skill itself, require the full licence, manifest-matching self-contained
  `.skill` bundle and a clean archive listing with zero build artifacts.

Any failed or unevaluated required gate stops final delivery. Repair and rerun
the affected checks; if external evidence or a decision is required, report
the precise blocker and retain the artifact as a labelled draft. Deliver the
validated XLSX with its merged model and validation evidence, stating selected
scenario, exclusions, remaining assumptions and the recalculation engine.
