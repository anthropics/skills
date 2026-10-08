---
name: server-hardening-estimator
description: Estimate server and operating-system hardening work and recurring security operations in JH, with control boundaries, verification evidence and residual risk. Use for host security estimates; application security is included only when explicitly requested.
---

# Server hardening estimator

**Created by the repository maintainers.** This open-source skill provides
generic server security estimation methodology.

**Licence:** CC BY 4.0. Share and adapt for any purpose with credit to the
repository maintainers. Include the full licence in the distributed bundle.

**Feedback & support:** Route methodology feedback to the maintainer contact
that distributed the suite; use a public issue tracker once one exists.
Correct execution mistakes before proposing methodology changes.

Produce common `EstimateModel` records and a validated XLSX as the primary
deliverable. In a consolidated estimate, submit records to the shared merge
before generating its workbook. Keep one-off Build JH, monthly Run JH,
provider costs and non-cloud OPEX separate; eight hours per JH is an editable
default. Estimation never authorises changes to a live host.

## Scope and controls

Read [references/control-catalogue.md](references/control-catalogue.md) for
requested control decomposition, acceptance evidence and scope interfaces.
Read [references/domain-contract.json](references/domain-contract.json) when
emitting structured records. Choose controls from the actual host exposure,
service needs and operating ownership; the catalogue is not a mandatory bill.

Establish fleet/OS families, environments, management access, criticality,
baseline/version, patch windows, recovery targets, security operators and
exceptions. Identify provider-managed versus user-managed boundaries.
Application security remains excluded unless explicitly requested; label its
separate scope, owner and effort when included. Prevent overlap with cloud
identity, network infrastructure, platform controls, pipeline scans and
migration/recovery by assigning every shared result one task owner.

Classify controls/components as live, partially deployed, planned or unknown.
Inspect actual effective configuration and dated evidence, not intended
templates. When access is unavailable, specify a read-only measurement
instrument and required permissions, create a blocking task and retain
unknowns as assumptions. Never turn a missing scan or inaccessible host into
evidence of compliance or a guessed zero finding count.

Cover identity, privileged access, bastion or zero-trust access, network
policy, baseline, patching, endpoint protection, logging, backup, restore,
vulnerability management, certificate rotation, incident readiness and
evidence where requested. Every control names boundary, implementation task,
acceptance criterion, expected verification evidence and remaining risk.
Validate allowed and denied cases when relevant, including management access
and service health. Retain explicit exceptions with owner, review date and
compensating controls; installed software alone does not prove protection.

## Estimate and deliver

Give Build and Run tasks distinct IDs, lots, environments, roles,
prerequisites/dependencies, deliverables, sources, confidence and ordered
finite low/likely/high JH. Estimate by host variation, proven reuse, change
windows, verification and evidence gaps. Show gross, proven covered and net
additional JH; numerical ranges are the net. Split partial controls at their
acceptance boundary. Monthly Run notes name cadence, fleet/event drivers,
operator responsibility and evidence for reviews, patching and rehearsals.
Control setup once and ongoing maintenance are different deliverables.

Record residual risks with impact, probability, mitigation, owner and status,
linked to affected task IDs in notes/mitigation. Do not state blanket
compliance from a partial technical baseline. Missing control evidence,
unsupported OS lifecycle, access dependencies and recovery gaps are decisions
or blockers. Draw evidenced management, logging, protection and recovery
flows from inventory before finalising the estimate.

Keep `Economique`, `Standard`, `Resilient` at equal service scope, showing
accepted risks and transferred operator JH. Allocate lots to calendar periods
against capacity; patch/recovery elapsed windows are not summed effort.
Identify protection licences, bastion/access services, logs, backup storage
and traffic cost drivers. Verify runtime prices from current official sources
or authorised billing exports. Missing prices stay `A chiffrer` assumptions
and decisions, with unpriced numeric cost rows omitted and totals incomplete.

Use the locally supplied shared loader, workbook builder, diagram renderer,
recalculation adapter and validator. Keep all twelve sheets, formula-driven
selection/totals and editable assumptions; explain irrelevant sections as
`Non applicable`.

Read [references/common-methodology.md](references/common-methodology.md) when
constructing the complete model or using the local workbook runtime.

## Pre-delivery gate

Re-read these instructions and relevant references against the final records
and workbook; record pass/fail and item counts:

- Every selected control has a boundary, implementation task, effective
  verification evidence and residual risk assessment; exceptions have owners.
- Domain keys match the common model; IDs/dependencies resolve, lots have
  phases and application/shared work belongs to its explicit owner.
- Claimed coverage has dated proof; Build and Run/month remain separate;
  ranges, coverage subtraction, period workload and synthesis reconcile.
- Access/network checks include allowed and refused cases; backup completion
  includes tested recovery and objective evidence; no control is accepted
  solely because its template, agent or policy exists.
- Scenario scope is equal; required missing evidence, decisions or prices
  block final completion; residual exposure is visible beside recommendations.
- Diagram IDs and flows match inventory/evidence. Recalculation succeeds with
  caches; reopened formula/value views have no formula, narrative-total,
  reconciliation or table/filter-overlap errors. Give the shared validator
  numeric prose assertions and diagram IDs; disclose the engine used.
- Anonymisation reports zero forbidden identifiers; inspect combined examples
  for re-identification. All document-relative resources resolve. Deliver the
  multi-file skill as a clean, manifest-matching `.skill` bundle with full
  licence and no build artifacts.

Repair and rerun affected checks. Keep a labelled draft when blockers remain.
Deliver XLSX, common model and validation evidence with scope, exclusions,
assumptions, operating ownership and limitations disclosed.
