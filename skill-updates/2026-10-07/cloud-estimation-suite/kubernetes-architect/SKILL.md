---
name: kubernetes-architect
description: Assess Kubernetes suitability and estimate cluster topology, node pools, platform delivery and recurring operations in JH. Use for Kubernetes architecture or cluster estimates when workload needs and team capability warrant orchestration.
---

# Kubernetes architect

**Created by the repository maintainers.** This open-source skill provides
generic, anonymised Kubernetes architecture and estimation methodology.

**Licence:** CC BY 4.0. Share and adapt with credit to the repository
maintainers. Include the full licence in the distributed bundle.

**Feedback & support:** Send methodology feedback to the maintainer contact
that distributed the suite; use a public tracker once one exists. Correct
execution mistakes before proposing methodology changes.

Produce records in the shared `EstimateModel` and a validated XLSX as the
primary deliverable. For a consolidated estimate, merge records before
generating the workbook. Keep one-off Build JH, Run JH/month, cloud spend and
non-cloud OPEX separate. Eight hours per JH is an editable assumption.

## Decide whether Kubernetes fits

Establish workload isolation, deployment and scaling requirements, service
and recovery targets, environments and the team's operational capability.
Compare simpler hosting against Kubernetes at equal service scope. Containers
alone do not justify a cluster. Record the workload benefit, operational
owner, alternatives, added Build/Run JH and accepted risks in an explicit
decision. If the simpler option satisfies the requirements with less burden,
recommend it; document the assessment without inventing cluster work.

Read [references/cluster-checklist.md](references/cluster-checklist.md) when
Kubernetes is retained or an existing cluster needs assessment. Read
[references/domain-contract.json](references/domain-contract.json) when
emitting records. Cover control-plane responsibility, node pools, scheduling,
autoscaling, ingress, storage, secrets, policy, upgrades, observability,
backup, multi-zone placement and disaster recovery as applicable. Introduce
a service mesh only for a documented requirement whose benefit exceeds its
operational burden.

## Size and estimate the platform

Use sourced peaks and allocatable resources, including system workloads.
Without measurements, expose low/base/high workload assumptions and a
measurement task before claiming precise capacity. Make pod requests/limits,
utilisation targets, scaling ceilings, headroom and failure reserve editable
workbook inputs. Link each pool to workload, environment, placement and
scenario; test both normal capacity and surviving capacity after the stated
node or zone failure. Autoscaling delay and external quotas are constraints.

Classify existing capability as live, partially deployed, planned or unknown.
Only evidenced coverage offsets effort. Where access is missing, define a
read-only measurement instrument and blocking verification task. Show gross,
covered and net additional JH; split partially covered acceptance criteria.

Estimate platform tasks using workload-specific low/likely/high JH, with
stable IDs, owners, dependencies, deliverables, acceptance criteria, expected
evidence, sources and confidence. Include initial engineering and monthly
operations: upgrades, policy maintenance, incident response, capacity review,
backup/restore verification and recovery exercises. Assign shared network,
pipeline, hardening and migration deliverables to one domain owner.

Keep `Economique`, `Standard` and `Resilient` at comparable service scope.
Show each scenario's availability, recovery and monthly operating burden.
Maintain workload uncertainty bands separately from these service scenarios.
Record quantity drivers for control plane, nodes, volumes, load balancers,
network, registry, observability, support and backup. Retrieve changing prices
at runtime from current official sources or authorised exports; do not store
current prices in this skill. Missing prices remain `A chiffrer` assumptions
and decisions, never invented zero or text in numeric cost fields.

Read [references/common-methodology.md](references/common-methodology.md) when
constructing the complete model or using the local workbook runtime.

## Pre-delivery gate

Re-read this skill and the selected reference against the final model and
workbook. Emit pass/fail and nonempty item counts for the applicable checks:

- The Kubernetes decision states workload/team justification and alternatives;
  optional mesh, multi-zone and DR choices have requirements and owners.
- Pool and topology IDs match inventory; requests fit allocatable capacity;
  headroom, scaling limits and node/zone failure calculations remain visible.
- Platform tasks and recurring operations match the domain contract; Build
  and Run/month are separate, evidence supports coverage, shared work is
  counted once, and task dependencies/phases resolve.
- All three scenarios have equivalent service perimeter, explicit accepted
  risks and dated sources. Missing measurements and costs label incompleteness.
- The locally supplied shared loader, builder, diagram renderer,
  recalculation adapter and validator preserve all twelve workbook sheets.
  Reopen the recalculated XLSX and verify formula caches, totals, table/filter
  boundaries, diagram inventory IDs and every numerical prose assertion.
- Anonymisation returns zero forbidden identifiers; also check combinations
  of names, paths, topology, dates and quantities for re-identification.
- All referenced resources exist. Deliver this multi-file skill as a clean,
  self-contained `.skill` bundle with full licence and verified archive list.

Repair failed checks and rerun them. Preserve a labelled draft when a missing
measurement or unresolved decision prevents a complete estimate. Deliver the
validated XLSX, model and verification evidence with assumptions, exclusions
and recalculation engine stated.
