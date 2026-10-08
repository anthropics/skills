---
name: infra-work-estimator
description: Estimate infrastructure delivery and operating effort in JH for landing zones, networks, compute, data services, observability, recovery and infrastructure as code. Use for infrastructure work breakdowns and coverage reconciliation; application development needs separate scope.
---

# Infrastructure work estimator

**Created by the repository maintainers.** This open-source skill provides
generic infrastructure estimation methodology without client-specific inputs.

**Licence:** CC BY 4.0. Share and adapt for any purpose with credit to the
repository maintainers. Include the full licence in the distributed bundle.

**Feedback & support:** Route methodology feedback to the maintainer contact
that distributed the suite; use a public issue tracker only once one exists.
Correct execution mistakes before proposing methodology changes.

Produce infrastructure records in the shared `EstimateModel` and a validated
XLSX as the primary deliverable. In a consolidated estimate, hand the records
to the shared merge before generating its workbook. Effort remains JH
(jour-homme); eight hours per JH is an editable default. Keep one-off Build
JH, monthly Run JH, cloud costs and non-cloud OPEX separate.

## Scope and work breakdown

Read [references/task-catalogue.md](references/task-catalogue.md) when
decomposing the requested infrastructure and mapping it to the common model.
The catalogue is a coverage prompt, not a mandatory bill of work. Read
[references/domain-contract.json](references/domain-contract.json) for the
machine-readable input/output interface.

Establish service perimeter, environments, existing coverage, responsible
roles, acceptance evidence and exclusions. Cover landing zones, accounts or
projects, networks, DNS, certificates, compute, storage, databases, cache,
messaging, observability, backup, recovery, IaC and operational documentation
only where required. Application code, business features, application tests
and data transformation do not enter infrastructure JH. Assign interfaces
with pipeline, hardening, Kubernetes and migration work to one owner before
counting shared deliverables.

Classify each component as live, partially deployed, planned or unknown.
Measure live components and estimate remaining work. Where access is missing,
describe a read-only measurement instrument and make its execution the first
blocking task for dependent estimates. Keep assumptions labelled; an unknown
measurement cannot be filled by an invented value.

Reconcile earlier estimates using gross effort, proven covered effort and
net additional JH. Split partially covered tasks at the acceptance boundary.
Conflicting sources become explicit decision branches with effort, cost and
risk deltas. Draw inventory components and evidenced flows before finalising
the estimate; untraceable edges require an assumption or open decision.

## Estimate and deliver

Give each task stable IDs, a lot, environment, role, prerequisites,
dependencies, deliverable, acceptance criterion, expected evidence, source
and confidence. Estimate low, likely and high JH from task-specific drivers,
including repeatable automation and remaining verification. Treat uncertainty
as a stated driver rather than a hidden percentage. Numerical JH are net
additional effort; preserve gross and covered values in notes.

Build the service bill of materials from behaviour, including metered network
and egress, observability, registry/build, support, backup and recovery.
Verify mutable prices at runtime from current official sources or authorised
billing exports; retain SKU, region, unit, currency, capture date and source.
Unverified prices remain `A chiffrer` in assumptions and decisions, with
incomplete totals disclosed. Do not insert text or placeholder zero in numeric
cost fields. Non-cloud OPEX belongs in separate sourced assumptions.

Keep `Economique`, `Standard` and `Resilient` at equal service scope. Record
accepted risks, recovery targets and transferred monthly operator JH.
Project tasks onto calendar periods and compare required Build JH with
available capacity; elapsed duration and parallel work are not summed effort.
Use the shared loader, builder, diagram renderer, recalculation adapter and
validator supplied locally in the distribution. Preserve all twelve contract
sheets, formula-driven selection/totals and editable assumptions; explain
irrelevant sections with `Non applicable`.

Read [references/common-methodology.md](references/common-methodology.md) when
constructing the complete model or using the local workbook runtime.

## Pre-delivery gate

Re-read these instructions and the relevant reference against the final model
and workbook. Record pass/fail and item counts for these checks:

- Model records match the domain contract; task IDs and dependencies resolve;
  each task lot has a phase; infrastructure ownership and exclusions are clear.
- Every live claim has evidence; remaining work is net of proven coverage;
  application work and shared deliverables are counted in the assigned domain.
- JH ranges are finite, ordered and reconcile with phase and synthesis totals;
  Build, Run/month and recurring costs stay distinct; calendar overloads show.
- Scenario scope is comparable; price sources are dated and verified;
  required missing measurements, prices or decisions block a complete estimate.
- Diagram IDs match inventory and its flows match evidence. Recalculation
  succeeds, formula caches exist, and the reopened workbook has no formula,
  reconciliation, narrative-total or table/filter-overlap errors. Supply all
  numeric prose assertions and diagram IDs to the shared validator.
- Anonymisation returns zero forbidden identifiers; review the combined
  names, paths, topology, dates and amounts for re-identification as well.
- Referenced resources exist in the delivered set; delivery of this multi-file
  skill requires a self-contained `.skill` bundle, full licence and clean
  manifest-matching archive with no build artifacts.

Repair failures and rerun affected checks. When evidence or an unresolved
decision prevents completion, retain a labelled draft and state the blocker.
Deliver the validated XLSX, common model and verification evidence with
scenario, exclusions, assumptions and recalculation engine disclosed.
