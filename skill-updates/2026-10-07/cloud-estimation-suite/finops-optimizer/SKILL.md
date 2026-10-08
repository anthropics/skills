---
name: finops-optimizer
description: Analyse cloud billing and usage for rightsizing, scheduling, commitments, lifecycle, egress, observability, architecture and waste savings. Use for a quantified opportunity register with measured or forecast baselines, implementation and operating JH, risk, reversibility and validation evidence.
---

# FinOps optimizer

**Created by the repository maintainers.** This open-source skill provides
generic cloud-cost optimisation methodology without client-specific inputs.

**Licence:** CC BY 4.0. Share and adapt for any purpose with credit to the
repository maintainers. Include the full licence in the distributed bundle.

**Feedback & support:** Route methodology feedback to the maintainer contact
that distributed the suite; use a public issue tracker only once one exists.
Correct execution mistakes before proposing methodology changes.

Produce an evidence-backed savings register in the common `EstimateModel`
and a validated XLSX as the primary deliverable. For consolidated estimates,
return records for the common merge. Express effort in JH (jour-homme), with
eight hours per JH editable. Separate Build JH, monthly Run JH, cloud OPEX
and non-cloud OPEX; cloud savings do not erase operator work.

## Establish a comparable baseline

Read [references/optimisation-catalogue.md](references/optimisation-catalogue.md)
for opportunity drivers, validation, overlap and total reconciliation. Read
[references/domain-contract.json](references/domain-contract.json) for the
required opportunity fields and common record bindings.

Fix accounts/projects in scope, services, environments, billing period,
currency, commercial policy and SLA/RPO/RTO before modelling savings.
Classify components as live, partially deployed, planned or unknown. Use
authorised billing exports and provider measurements for live resources;
reconcile exports to invoices/control totals and observe representative
usage, peaks and seasonality. Record amortisation, discounts, credits and tax.

Label baseline kind `measured-billing` or `forecast`, with period, coverage,
evidence and confidence. Proposed savings start as `forecast`; use
`validated-measured` only after implementation and a comparable post-change
measurement. Measured billing alone does not make proposed savings measured.
Do not blend the two kinds into an unlabelled total. Missing access triggers
a read-only measurement instrument and blocking execution task, not invented
usage, a universal savings percentage or an assumed idle resource.

## Model actionable opportunities

Each opportunity needs a stable ID, baseline, action, savings range, one-off
JH, monthly recurring JH, risk, reversibility and validation method. Link
these records by ID in their notes/rationale; the common model has no typed
savings row. Store monetary low/likely/high savings, currency, period,
derivation and status in the decision rationale, with editable inputs in
assumptions. Acceptance evidence belongs to its implementation task.

For each action preserve the same service scope and recovery targets, or
make any reduction a separate explicit decision. Derive costs from usage
and complete metered-service behaviour, including displaced costs and work.
Reconcile existing coverage before adding implementation tasks; show gross,
covered and net JH, give shared work one owner and expose priced branches
for contradictions. Application changes remain separately owned dependencies
unless explicitly scoped. Draw affected inventory and evidenced flows before
finalising savings, especially changed network or data paths.

Do not execute resizing, deletion, commitments or other cloud mutations as
part of an analysis request. Mark approval and rollback dependencies for a
later authorised implementation. Unknown baseline or target price leaves
`A chiffrer`, not zero savings. Verify mutable target prices against current
official pages, catalogues, calculators or authorised billing exports with
provider, service/SKU, region, unit, currency, capture date, URL and confidence.

Combine opportunities only after removing overlap and applying dependencies
in a stated order. Show gross cloud savings, displaced expenses, additional
Run JH, Build JH cost, net benefit and payback separately. Preserve original
JH beside editable TJM conversions. Compare `Economique`, `Standard` and
`Resilient` within each scope; keep mutually exclusive action branches in
separate complete models because the common model has no branch selector.
Project scoped work onto periods and flag capacity overloads.

Run the catalogue's two independent reconciliations. Use the locally supplied
common loader, builder, renderer, recalculation adapter and validator. Keep
all twelve sheets, editable inputs, derived formulas and cached values;
mark irrelevant sections `Non applicable` with a reason.

Read [references/common-methodology.md](references/common-methodology.md) when
constructing the complete model or using the local workbook runtime.

## Pre-delivery gate

Re-read these rules and relevant references against the final artifacts.
Record pass/fail and counts for these checks:

- Every opportunity has all eight fields, linked common records, effort
  ranges, monthly cadence and observable validation evidence.
- Baselines, periods and savings status distinguish measured billing,
  forecasts and validated post-change savings; measurement gaps block claims.
- Service perimeter, peaks and SLA/RPO/RTO survive the proposed action;
  residual risk, rollback cost/time and commitment irreversibility are visible.
- Savings overlap, commercial charges, credits, displaced costs and human
  operations are reconciled; incompatible alternatives are not aggregated.
- Prices have dated sources or `A chiffrer`; two independent totals agree
  with detail, synthesis and all numeric narrative assertions.
- Model loading, dependencies, diagram/inventory consistency, native or
  calibrated fallback recalculation and cached values pass. Reopen the XLSX;
  obtain zero formula, reconciliation and table/filter-overlap errors and
  disclose the recalculation engine.
- Anonymisation scan returns zero forbidden identifiers; combined review of
  names, paths, topology, dates and amounts rules out re-identification.
- Every relative resource exists; skill delivery uses the full licence and
  a self-contained, manifest-matching `.skill` archive without build artifacts.

Repair failures and rerun affected checks. Retain a labelled draft with exact
blockers when evidence is unavailable. Deliver the validated XLSX and model,
prioritised register, exclusions, remaining decisions and verification evidence.
