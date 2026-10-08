---
name: hosting-capacity-simulator
description: Translate measured workload peaks or explicit uncertainty bands into hosting resource capacity, minimum instances, scaling ceilings and failure reserves. Use for sizing and sensitivity across hosting options without claiming benchmark precision from unmeasured traffic.
---

# Hosting capacity simulator

**Created by the repository maintainers.** This open-source skill provides
generic, anonymised hosting capacity modelling and estimation methodology.

**Licence:** CC BY 4.0. Share and adapt with credit to the repository
maintainers. Include the full licence in the distributed bundle.

**Feedback & support:** Route methodology feedback to the maintainer contact
that distributed the suite; use a public tracker once published. Correct
execution mistakes before proposing changes to the methodology.

Produce the shared `EstimateModel` and a validated XLSX as the primary
deliverable; merged estimates generate the workbook after consolidation.
Keep Build JH, Run JH/month, cloud costs and non-cloud OPEX separate. Eight
hours per JH is an editable default. This skill models capacity; a hosting
or Kubernetes selection still requires workload and team justification.

## Establish the workload evidence

Scope workload, environment, latency/service targets, observation period,
growth horizon and failure event. Prefer measured simultaneous peaks with
their sampling window, percentile definition, hardware/runtime context and
source. Distinguish provisioned capacity from consumed demand. Averages and
uncorrelated maxima are not interchangeable peaks.

If measurements are absent, publish explicit low/base/high workload bands
with derivations and confidence. Create an owned measurement/load-test task
with instrument, prerequisites, acceptance criterion and expected evidence;
make it block decisions that need precision. Access gaps require a read-only
measurement instrument and initial blocking task. Do not invent a per-instance
benchmark from a traffic count or imply the assumptions are observations.

Read [references/capacity-model.md](references/capacity-model.md) for units,
formulae, failure treatment and sensitivity. Read
[references/domain-contract.json](references/domain-contract.json) for the
typed input schema and shared output mappings. Validate each normalised input
payload using [scripts/validate_capacity.py](scripts/validate_capacity.py).
Its standard-library function `validate_capacity_inputs` returns validated
quantities or raises a field-specific error; it is a bounded contract validator,
not a general JSON Schema engine. It validates input quantities, not sizing
adequacy. Missing, non-finite or untyped quantities require correction.

## Calculate and compare

Use canonical CPU, memory, storage, IOPS, bandwidth and concurrency units.
Expose utilisation target, scaling limit and failure-domain reserve together
with per-unit effective capacity, overhead and rounding as editable inputs.
Calculate the binding resource, minimum ready instances and capacity remaining
under the stated failure. Test node, zone and shared-backend constraints
individually; merely adding a spare instance does not establish zone resilience.

Separate workload low/base/high sensitivity from `Economique`, `Standard` and
`Resilient` service scenarios. Show saturation, latency assumptions, growth,
scaling delays, quota ceilings, infeasible choices and recovery targets at equal
service scope. Keep mutually exclusive hosting alternatives in separate
models/workbooks so their capacities, JH and costs are never summed.

Translate quantity drivers into inventory and platform/capacity work into JH
tasks with stable IDs, owners, dependencies and acceptance evidence. Include
measurement, load validation and recurring capacity review where in scope.
Reconcile gross, covered and net additional effort against proven live work;
assign shared measurement and platform deliverables to one owner. Project
Build JH onto phases/calendar capacity; elapsed time is not summed effort.

Do not embed prices in capacity assumptions. Verify mutable prices at runtime
from official sources or authorised exports, preserving SKU, region, currency,
unit and capture date. Unverified prices remain `A chiffrer` assumptions and
decisions with incomplete totals disclosed; never insert text or invented zero
into numeric cost fields.

Read [references/common-methodology.md](references/common-methodology.md) when
constructing the complete model or using the local workbook runtime.

## Pre-delivery gate

Re-read this skill and the relevant reference against the completed model and
workbook. Record pass/fail and explicit input/result counts for these checks:

- All nine typed dimensions validate with their canonical units; provenance,
  measured/assumed status, period and scenario/band scope remain traceable.
- Effective capacities, utilisation/headroom, reserve and rounding are visible;
  normal and failure calculations reconcile and binding resources are named.
  Indivisible storage, zone/data placement and quotas have separate checks.
- Assumed peaks have low/base/high bands and a measurement task; sensitivity
  results expose bottleneck changes and infeasible bounds without fake precision.
- Records match the common contract; dependencies/phases resolve, net JH is
  evidenced, Build and Run/month stay distinct and shared work is counted once.
- Use the locally supplied shared loader, builder, diagram renderer,
  recalculation adapter and validator. Preserve all twelve sheets and reopen
  the recalculated XLSX to check caches, totals and table/filter boundaries.
  Supply every numeric prose assertion and inventory diagram ID to validation.
  Verify capacity calculations separately when the common validator cannot.
- Anonymisation reports zero forbidden identifiers; check combined names,
  paths, workload amounts, dates and topology for re-identification as well.
- All linked files exist in the delivered set. This multi-file skill needs a
  self-contained `.skill` bundle with full licence and a clean verified archive.

Repair failed checks and rerun them. Missing evidence or an unresolved choice
keeps the estimate a labelled draft. Deliver the validated XLSX, model and
verification evidence with assumptions, exclusions and recalculation engine.
