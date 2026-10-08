---
name: cloud-provider-selector
description: Compare cloud providers using eligible regions, managed services, commercial terms, implementation and operating effort, and three-year TCO. Use for a visible weighted provider recommendation with equal service scope and explicit recovery feasibility.
---

# Cloud provider selector

**Created by the repository maintainers.** This open-source skill provides
generic provider-selection methodology without client-specific inputs.

**Licence:** CC BY 4.0. Share and adapt for any purpose with credit to the
repository maintainers. Include the full licence in the distributed bundle.

**Feedback & support:** Route methodology feedback to the maintainer contact
that distributed the suite; use a public issue tracker only once one exists.
Correct execution mistakes before proposing methodology changes.

Produce a provider recommendation, rejected alternatives and comparable
three-year TCO in the common `EstimateModel`. The primary deliverable is a
validated XLSX; consolidated estimates receive these records for merging.
Express effort in JH (jour-homme), with eight hours per JH editable. Separate
Build JH, monthly Run JH, cloud OPEX and non-cloud OPEX.

## Establish eligible alternatives

Read [references/scoring.md](references/scoring.md) for eligibility, scoring,
TCO and independent reconciliation. Read
[references/domain-contract.json](references/domain-contract.json) for the
common-model bindings and required comparison inputs.

Fix the same workloads, service perimeter, environments, growth, SLA and
RPO/RTO targets for every candidate. Classify components as live, partially
deployed, planned or unknown. Use measured usage and costs for live resources;
label target costs as forecasts. If access is missing, produce a read-only
measurement instrument and blocking measurement task; never invent usage.

Verify residency and required service availability in each proposed region,
including backup locations and dependent control planes. List and count
eligible regions before claiming multi-region disaster recovery. Fewer than
two eligible, independent regions disqualifies a multi-region design;
multiple zones in one region cannot satisfy that requirement. Reject failing
mandatory constraints before scoring; unresolved mandatory evidence blocks
an unconditional recommendation.

Use visible criteria, weights, scores, scale definitions and supporting
evidence, including commercial policy and implementation/operation JH. Test
weight sensitivity and explain which conditions would change the choice.
Never rank providers solely by advertised monthly infrastructure price.
Transferred operator responsibilities must appear in Build and Run JH.

## Compare complete costs and work

Reconcile existing estimates and proven coverage before adding tasks. Show
gross, covered and net additional JH; give shared work one owner. Contradictory
inputs become priced decision branches. Application refactoring and detailed
migration remain separate dependencies and estimates unless explicitly scoped.
Draw each option's inventory and evidenced flows before finalising costs;
untraceable edges become issues or assumptions.

For each provider compare `Economique`, `Standard` and `Resilient` at equal
service perimeter. Keep mutually exclusive providers in separate complete
models/workbooks because the common model has no provider branch selector.
Return one selected-model workbook and explicit deltas for alternatives.
Project Build JH onto periods and expose capacity overloads and prerequisites.

Verify current prices with official pricing pages, catalogues, calculators or
authorised billing exports. Every price needs provider, SKU/service, region,
unit, currency, capture date, source URL and confidence. Record commercial
terms, support, commitments and price validity. Unverifiable prices remain
`A chiffrer` in assumptions and decisions; never put disguised zero prices in
numeric cost rows or claim a complete TCO with missing inputs.

Calculate three-year TCO with editable assumptions and formulas, including
implementation JH converted by TJM, recurring operator JH, cloud consumption,
support, backups, egress and other scoped costs. Show measured baseline,
forecast cost and JH separately; a monthly cost snapshot is insufficient.
Run the two independent reconciliations specified in the scoring reference.
Use the locally supplied common loader, builder, renderer, recalculation
adapter and validator. Preserve twelve sheets; mark irrelevant sections
`Non applicable` with a reason rather than dropping them.

Read [references/common-methodology.md](references/common-methodology.md) when
constructing the complete model or using the local workbook runtime.

## Pre-delivery gate

Re-read these rules and relevant references against the final artifacts.
Record pass/fail and counts for these checks:

- Mandatory eligibility is evidenced and eligible regions counted; recovery
  claims match independence, replication and tested RPO/RTO feasibility.
- Criteria, weights, uncertainty, sensitivity and rejected options are
  visible; comparison uses equal service perimeter and three-year horizon.
- Build and monthly Run JH map to their contract records; shared coverage
  has evidence and one owner; alternative branches are not summed together.
- Every cost has dated provenance; measured billing and forecasts are
  labelled; unverified prices and terms retain `A chiffrer` blockers.
- Two independently derived totals reconcile to detail, synthesis and every
  numeric narrative assertion. No monthly-price-only ranking survives.
- Model loading, diagram/inventory consistency, formula recalculation and
  cached values pass; reopen the XLSX and obtain zero formula, reconciliation
  or table/filter-overlap errors. Disclose the recalculation engine.
- Anonymisation scan returns zero forbidden identifiers; combined review of
  names, topology, paths, dates and amounts rules out re-identification.
- Relative resources exist; delivery uses a self-contained `.skill` archive
  with full licence, matching manifest and no build artifacts.

Repair failures and rerun affected checks. Missing mandatory information
leaves a labelled draft with precise blockers. Deliver the validated XLSX,
model, rationale, exclusions, open decisions and verification evidence.
