# Provider eligibility, scoring and TCO

Use this reference when comparing providers. Record bindings live in the
sibling [domain-contract.json](domain-contract.json); they preserve the
common model without adding provider-specific columns.

## Eligibility before preference

Record provider/region candidates, required services and official evidence
with capture date. A region counts only if residency, legal/commercial
eligibility, needed SKUs/services and data/control-plane locations meet the
same requirements. Distinguish available, unavailable and unverified.
Record the eligible-region count, excluded regions and exclusion reasons.
An unverified region cannot count as eligible.

Multi-region DR requires at least two eligible regions with independent
failure domains, compatible replication/backup capabilities, acceptable
latency and evidenced recovery procedures. Counting two regions is necessary,
not sufficient: verify data completeness, dependency failover, restoration
capacity, required services during failure and RPO/RTO with measurements or
an explicit rehearsal task. If only one region qualifies, offer a distinct
single-region recovery alternative with changed targets for decision; do
not silently claim unchanged regional-disaster protection.

## Visible scoring

For each criterion retain its ID, definition, weight, scoring scale, provider
score, evidence, unknowns and weighted contribution as comparison assumptions.
Weights must be non-negative with a positive sum. Normalise by their sum and
use a disclosed common score scale; compute contribution = normalised weight
times score. Publish both criterion-level detail and the aggregate formula.
Choose weights from user priorities before viewing the outcome; do not tune
them to a preferred provider. Leave unknown scores unresolved, with score
bounds for sensitivity rather than a favourable default.

| Criterion | Evidence and comparison boundary |
|---|---|
| Region eligibility and residency | Eligible-region list/count, workload and backup data locations; mandatory gates apply before weights |
| Managed-service coverage | Service-by-service capability, version, limits and operator responsibilities at the same perimeter |
| SLA and recovery | Contract scope, exclusions, dependencies, redundancy and evidenced RPO/RTO feasibility |
| Support | Hours, escalation, response targets, fees and required customer operating duties |
| Skills | Current team capability, training/onboarding and retained operator responsibilities |
| IaC maturity | Supported resources, state/import, drift and reproducible provisioning evidence |
| Portability | Data export, interfaces, licence constraints and exit/rebuild work |
| Commercial policy | Commitment term, payment/upfront cash, discount eligibility, minimum spend, cancellation, renewals, quotas, tax and price validity |
| Implementation JH | Scoped low/likely/high Build effort including onboarding, transfer and acceptance |
| Recurring operations JH | Low/likely/high Run JH per month with cadence, task coverage and growth drivers |
| Three-year TCO | Complete, comparable cost perimeter and horizon, uncertainty and omitted-input blockers |

Vary material weights and usage/growth/commercial assumptions. Report ties,
ranking reversals and break-even conditions. A high aggregate score cannot
override a residency or recovery gate. Explain a recommendation with the
criteria that actually distinguish providers, not the monthly price alone.

## Three-year cost model

Use a common three-year horizon (`tco_horizon_years = 3`) and currency. For
the default twelve months per year this gives 36 months; expose the period
convention and any partial month. Use the same workload/growth path and
scenario for all candidates. Preserve native price currencies with dated
conversion sources before normalisation. State tax treatment and nominal
versus discounted-cash-flow convention; do not mix conventions.

TCO = Build JH cost + other one-off costs + sum over horizon months of
(cloud OPEX + Run JH cost + non-cloud OPEX). Convert each Build and Run JH
using the applicable editable TJM; keep source JH visible. With constant
inputs, the monthly sum can use the declared horizon-month multiplier;
growth, ramp-up or changing commercial terms require a period schedule.

Include compute, database, storage, backup/restore, cross-zone/region traffic,
egress, observability, registry/build, support, licences, residual commitments
and scoped migration/exit dependencies. Do not add both commitment upfront
cash and the same amortised payment; show cash-flow separately if useful.
Time-limited credits are dated and shown as a separate case. Price quotations
and billing exports carry provider, SKU, region, unit, currency, capture date,
URL/reference and confidence. Billing exports measure the existing baseline;
they do not prove a target provider's future unit prices.

The common cloud-cost rows represent monthly recurring quantities; encode
period schedules and non-cloud costs as editable, labelled assumptions and
derived formulas using stable named ranges/table columns. Keep each provider
in a separate complete model and link comparison results through decisions.
Do not add incompatible costs to one model or hide unsupported TCO formulas
in static text. Missing prices stay `A chiffrer`, visibly block completeness
and are excluded from claims of full TCO rather than silently zeroed.

## Two independent reconciliations

1. Rebuild source-line totals from quantities, applicable unit prices and
   period factors. Independently aggregate by provider, environment, service,
   scenario and month. Add Build JH conversion and monthly Run/non-cloud
   schedule once; compare to workbook detail and synthesis.
2. Recompute the horizon total from the original BOM, task JH and dated
   commercial/period schedule through a separate calculation path that does
   not read the workbook's synthesis or reuse its total formulas. For measured
   baseline months independently tie billing totals to provider invoices or
   export control totals, classifying taxes, credits and exclusions. Compare
   this result to the first reconciliation and every numeric narrative claim.

Record both results, residuals, rounding tolerance and incomplete-cost count.
Two sums of the same synthesis cell are one calculation, not independent
checks. Reconcile scopes before explaining differences as rounding.

## Common output mapping

Emit named assumptions for scope, region eligibility/count, criteria/weights,
commercial policy, horizon, TJM, monthly cadence and price provenance.
Provider decisions retain criterion contributions, TCO/JH deltas, rejection
reasons, evidence IDs, sensitivity, chosen status and unresolved blockers in
`rationale`. Build and Run tasks link back to that decision with prerequisites,
acceptance evidence and low/likely/high JH; keep Run cadence in notes and
assumptions. Risk records capture failed/unknown gates and owners. Source
records retain original dates/URLs and revalidation actions. Inventory,
architecture, scenarios and phasing use the ordinary common records.
