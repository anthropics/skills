---
name: cloud-migration-estimator
description: Estimate cloud migration work in JH from live inventory, documentation drift, source-write constraints and source-to-target service mapping. Use for preparation, rehearsal, transfer, cutover, integrity, rollback, decommissioning and hypercare plans with an XLSX estimate.
---

# Cloud migration estimator

**Created by the repository maintainers.** This open-source skill provides
generic migration methodology without client-specific inputs.

**Licence:** CC BY 4.0. Share and adapt for any purpose with credit to the
repository maintainers. Include the full licence in the distributed bundle.

**Feedback & support:** Route methodology feedback to the maintainer contact
that distributed the suite; use a public issue tracker only once one exists.
Correct execution mistakes before proposing methodology changes.

Produce migration records in the common `EstimateModel` and a validated
XLSX as the primary deliverable. For a consolidated estimate, return records
for the common merge. Express effort in JH (jour-homme), with eight hours
per JH editable. Separate Build JH, monthly Run JH, cloud OPEX and non-cloud
OPEX; bounded hypercare belongs to Build, continuing operations to Run.

## Establish the source and intervention boundary

Read [references/migration-workflow.md](references/migration-workflow.md)
for method selection and lifecycle acceptance evidence. Read
[references/domain-contract.json](references/domain-contract.json) for
required fields and bindings to the common model.

Fix source and target perimeter, environments, owners, migration waves,
data sensitivity, acceptable outage and RPO/RTO. Start with authorised
read-only live inventory and representative usage from every source
account/project in scope. Record identity, capture date, scope, failures
and resource counts, including explicit zero counts. Classify components
as live, partially deployed, planned or unknown. Written documentation is
evidence of intent: reconcile it against the live snapshot and retain an
explicit drift register with observed state, documented state, consequence,
owner and resolution. Never silently choose the convenient source.

If access is missing, produce a read-only measurement instrument and a
blocking execution task. Mark evidence incomplete and affected estimates
provisional; do not invent inventory, size or transfer duration.

Record whether the source may be modified, exactly which changes, by whom
and under what existing authority. Use `forbidden`, `owner-only`,
`scoped-authorised` or `unknown`; unknown permission is never authorisation.
Check replication settings, agents, credentials, DNS, write freezes,
firewall rules, remediation and deletion against this policy before
selecting a method. An estimation request does not authorise deployment,
cutover or source mutation. Preserve authority already supplied by the user.

## Price the migration lifecycle

Map stable source IDs to target inventory IDs and explain compatibility,
data semantics, ownership and service differences. Include external actors
and dependencies as inventory records. Draw current, transfer and target
flows from these records before finalising effort. An untraceable edge or
incompatible boundary becomes an issue or assumption and a priced decision
branch; no unsupported connection is drawn as fact.

For each wave cover preparation, rehearsal, data transfer, cutover,
integrity checks, rollback, decommissioning and hypercare. Each phase has
low/likely/high JH, responsible role, prerequisites, dependency IDs,
deliverable, acceptance criterion and observable evidence. Preserve an
excluded or owner-performed phase with its reason and handoff; exclusion
from our work does not remove the dependency. Reconcile existing coverage
to gross, covered and net additional JH and assign shared work one owner.

Keep workload JH separate from elapsed transfer and outage time. Derive
duration from measured volume, effective throughput, change rate and
rehearsal results. Compare `Economique`, `Standard` and `Resilient` at equal
service scope and explicit recovery targets. Keep mutually exclusive
methods in separate complete models; the common model has no branch
selector. Project tasks onto periods and flag capacity overloads.

Expose egress, transfer tooling, temporary dual running, backup, monitoring
and target operating costs separately. Verify mutable prices against
current official sources or authorised billing exports with provider,
service/SKU, region, unit, currency, capture date, URL and confidence.
Missing prices remain `A chiffrer`. Use the locally supplied common loader,
builder, renderer, recalculation adapter and validator. Keep all twelve
sheets, derived formulas and cached values; mark irrelevant sections
`Non applicable` with a reason.

Read [references/common-methodology.md](references/common-methodology.md) when
constructing the complete model or using the local workbook runtime.

## Pre-delivery gate

Re-read these rules and the workflow against the final artifacts. Record
pass/fail and counts for these checks:

- Inventory evidence and drift register cover every source scope; missing
  measurements have explicit blocking tasks.
- Every proposed source write has an allowed actor and scope; methods,
  cutover, rollback and decommissioning respect that constraint.
- Mappings resolve both inventory IDs; diagram nodes and evidenced flows
  match the workbook; unresolved topology issues are visible.
- All eight lifecycle phases have evidence and JH or an explicit exclusion;
  rollback includes post-cutover writes and irreversible boundaries.
- Detail, gross/covered/net JH, monthly Run, costs, scenarios, phasing and
  prose reconcile. Reopen recalculated XLSX in formula and values modes,
  scan formula errors and report the engine and cache status.
- Sweep all public files and examples, jointly, for identifying names,
  domains, accounts, IPs, paths, topology, dates and copied amounts. Report
  findings count and remove traceable data. Resolve relative links from
  their containing document; verify resources and full CC BY licence in
  the clean multi-file `.skill` archive before public delivery.
