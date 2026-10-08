---
name: cicd-devsecops-estimator
description: Estimate CI/CD and DevSecOps delivery work and recurring operations in JH, with pipeline stages, security gates, acceptance evidence, promotion and recovery. Use for delivery pipeline work breakdowns; application feature development requires separate scope.
---

# CI/CD and DevSecOps estimator

**Created by the repository maintainers.** This open-source skill provides
generic delivery pipeline estimation methodology.

**Licence:** CC BY 4.0. Share and adapt for any purpose with credit to the
repository maintainers. Include the full licence in the distributed bundle.

**Feedback & support:** Route methodology feedback to the maintainer contact
that distributed the suite; use a public issue tracker once one exists.
Correct execution mistakes before proposing methodology changes.

Produce common `EstimateModel` records and a validated XLSX as the primary
deliverable. For a consolidated estimate, submit records to the shared merge
before generating its workbook. Keep one-off Build JH, monthly Run JH,
provider costs and non-cloud OPEX separate; eight hours per JH is an editable
default, never a substitute for the effort estimate.

## Scope and evidence

Read [references/pipeline-catalogue.md](references/pipeline-catalogue.md) to
decompose requested stages, define completion evidence and assign interfaces.
Read [references/domain-contract.json](references/domain-contract.json) when
emitting structured records. Catalogue entries are scope prompts, not an
automatic bill of work.

Establish repositories, artifact types, environments, release frequency,
runner trust boundaries, existing tests, gate policy, release owners and
recovery targets. Classify live, partially deployed, planned and unknown
components. Measure live execution and failure data; estimate only remaining
work. Without access, specify a read-only collection instrument, permissions
and expected results, then create a blocking measurement task rather than
inventing durations, scan coverage or runner utilisation.

Cover source controls, build, test integration, registry, provenance, scans,
IaC pipelines, promotion, approvals, migrations, rollback, ephemeral
environments, runners, evidence and operations where required. Test creation
and application/schema changes have an explicit scope and owner; pipeline
wiring must not silently absorb application development. Assign provisioning,
host hardening and migration interfaces once, referencing their owning task
IDs. Identify incompatible release choices as decision branches rather than
summing mutually exclusive work.

For each stage/control, name its boundary, implementer, acceptance criterion,
expected evidence, source and confidence. A configured gate is unproven until
an allowed case succeeds and a rejected case fails at the expected boundary.
If execution succeeds in one environment and fails in another, inspect trust,
identity, runtime and path differences before changing the gate; satisfying a
trust requirement never means disabling verification.

## Estimate and deliver

Give Build and Run tasks separate IDs, ordered finite low/likely/high JH,
lots, roles, environments, prerequisites and dependencies. Base estimates on
stage drivers and evidence gaps, not universal JH allowances. Record gross,
evidenced covered and net additional JH; numerical ranges are the net. Split
partial coverage at the acceptance boundary. Run JH are per month with
frequency, event volume and operator ownership in notes, including triage,
runner maintenance and release support. Provisioning once is not charged
again for each pipeline using the same runner or registry.

Draw runner, repository, registry, deployment and evidence flows from
inventory and sources before finalising work. Unsupported edges become
assumptions or decisions. Keep `Economique`, `Standard`, `Resilient` at equal
service scope, showing risks and human JH transferred by cheaper automation.
Schedule task lots against period capacity; release elapsed time is not
summed effort. Identify build-minute, runner, storage, scan, evidence and
network cost drivers without shipping current prices. Verify any runtime
price from current official sources or authorised billing exports. Missing
prices remain `A chiffrer` assumptions/decisions, with unpriced numeric rows
omitted and affected totals declared incomplete.

Use the locally supplied shared model loader, workbook builder, diagram
renderer, recalculation adapter and validator. Preserve all twelve contract
sheets and editable, formula-driven scenario selection and totals; explain
irrelevant sections as `Non applicable`.

Read [references/common-methodology.md](references/common-methodology.md) when
constructing the complete model or using the local workbook runtime.

## Pre-delivery gate

Re-read these instructions and relevant references against the final records
and workbook; record pass/fail and item counts:

- Domain fields map to existing model keys; stages, boundaries and evidence
  are traceable; task IDs/dependencies resolve and every lot has a phase.
- Covered work has dated proof; Build and Run/month remain separate;
  shared results have one owner; ranges and calendar totals reconcile.
- Gate evidence includes allowed and refused cases; rollback evidence
  addresses schema/data compatibility, not merely an old image deployment.
- Scenarios compare equal scope; required missing evidence, decisions or
  verified prices block complete delivery; residual risks have owners.
- Diagram IDs/flows match inventory/evidence. Recalculation succeeds with
  formula caches; reopened formula/value views have no formula, total,
  narrative or table/filter-overlap errors. Supply numeric prose assertions
  and final diagram IDs to the shared validator; disclose the engine used.
- Anonymisation reports zero forbidden identifiers; check combined examples
  for re-identification. All document-relative resources resolve. Deliver
  this multi-file skill as a clean, manifest-matching `.skill` bundle with
  full licence and no build artifacts.

Repair and rerun affected checks. Retain a labelled draft when blockers
prevent completion. Deliver XLSX, common model and validation evidence with
scope, exclusions, assumptions and operating responsibility disclosed.
