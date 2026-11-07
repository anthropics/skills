# FinOps opportunities and validation

Use this reference to derive savings from evidence. Required common record
bindings live in the sibling [domain-contract.json](domain-contract.json).
No opportunity category supplies a fixed saving percentage or current price.

## Baseline and opportunity record

Record measured period, workload, billing allocation/coverage, region, SKU,
quantity, units, currency and source. Baseline kind is `measured-billing`
only when an authorised export/invoice supports it; planned usage is a
`forecast`. Usage metrics without financial evidence are measured usage
feeding a forecast cost. Record peaks and seasonality rather than optimising
against a convenient average. Label proposed savings `forecast`, even with
a measured baseline. After implementation label `validated-measured` only
with a comparable post-change period and attribution evidence.

Every opportunity groups these required fields under a stable ID:

| Field | Required content |
|---|---|
| Baseline | Amount/usage, period, currency/unit, kind, source, scope and coverage |
| Action | Exact change, affected services and prerequisite/overlap IDs |
| Savings range | Low/likely/high money per stated period, derivation, status, confidence and exclusions |
| One-off JH | Build low/likely/high, gross/covered/net, role, dependencies and delivery evidence |
| Recurring JH | Run low/likely/high per month, cadence and volume/event drivers; retained work plus additional work |
| Risk | Capacity, performance, security, recovery or commercial downside, mitigation and owner |
| Reversibility | Revert steps, data preservation, time/cost, conditions and irreversible parts |
| Validation method | Before/after metrics, acceptance thresholds, observation window, evidence and workload-normalisation method |

An explicit zero can mean no additional recurring effort if evidenced;
missing effort is unknown, never inferred as zero. Mark incomplete values
`A chiffrer` in labelled assumptions/decisions and add the measurement or
estimation task. Do not create an invalid numeric cloud-cost/task row as a
placeholder. Baseline and target models remain separate to avoid summing
two states; per-opportunity decisions reference both and preserve deltas.

## Candidate catalogue

| Category | Evidence and action drivers | Risk/reversibility and validation |
|---|---|---|
| Rightsizing | Peak CPU/memory/IOPS/concurrency, throttling and utilisation history; evaluate smaller sizes or scaling bounds | Preserve headroom/failure reserve; price rollback; compare representative load, latency/error SLO and throttling before/after |
| Scheduling | Ownership, service hours, start/stop dependencies, jobs and restart duration; schedule eligible idle windows | Define wake-up/runbook and exceptions; verify no missed jobs or customer windows and meter stopped/runtime hours |
| Commitments | Stable eligible demand after rightsizing/scheduling, existing coverage, term, payment and discount rules | Show utilisation/coverage downside, break-even and locked spend; do not describe contracts as easily reversible; validate billing allocation and realised effective rate |
| Storage lifecycle | Data age/access, retention/legal hold, size, retrieval/operations and early-deletion/minimum-duration fees | Prove recoverability and retention before changing/deleting; include restore latency/retrieval/rehydration costs and validate lifecycle counts plus recovery tests |
| Egress | Measured flows, direction, endpoints, zones/regions, CDN/cache behaviour and tariffs; reduce transfers or change placement | Verify residency, cache correctness, dependency availability and latency; compare volume/path billing and SLO under the same demand |
| Observability | Ingestion/cardinality, duplication, retention, query usage and response needs; tune collection/sampling/tiering | Preserve required audit/security evidence and incident detection; validate expected event coverage and query/recovery requirements plus billed volumes |
| Architecture | Evidence of inefficient service boundaries, managed/operator split and scaling limits; model an alternative | Include rebuild/migration, additional Run JH, app-owner dependencies and rollback; validate performance/recovery and full comparable TCO |
| Waste removal | Ownership and dependency evidence for unattached/idle resources, obsolete snapshots/IPs/licences and abandoned environments | An idle metric alone is not deletion authority; owner decision and retained backup/revert path precede implementation; validate removed billing with no missing service dependency |

Estimate action-specific acceptance evidence and operating work rather than
assigning universal JH. Commitments follow demand reduction modelling because
unused locked capacity may prevent the claimed cash saving. Removing a shared
resource must account for all consumers, including dormant recovery paths.

## Net benefit, overlap and prioritisation

Gross cloud savings = comparable baseline cloud cost minus target cloud cost.
Show displaced cloud charges (egress/retrieval/requests), non-cloud OPEX,
additional monthly Run JH converted by editable TJM, and Build JH cost.
Net recurring benefit subtracts the additional recurring human and non-cloud
costs; distinguish cash savings from amortised cost and avoided future spend.
Payback uses one-off cost divided by positive net recurring benefit with its
period stated; a zero/negative denominator is `Non applicable`, not an error.
When recurring work is reduced, evidence the time actually released rather
than assuming cash headcount savings.

Never sum independent headline percentages. Apply compatible actions in
declared sequence to the residual baseline and account for joint discounts,
commitment coverage and minimum charges. Mark alternative actions mutually
exclusive. Keep a dependency/overlap register and show standalone savings
separately from incremental combined savings. Rank feasible opportunities by
net benefit, delivery JH/capacity, payback, confidence, risk and reversibility;
unmeasured savings remain provisional. A synthetic example is rightsizing
followed by commitments: commitment coverage must use the reduced demand,
not the original quantity, and locked unused spend may remain payable.

Maintain equivalent service scope and SLA/RPO/RTO for each scenario; a relaxed
target requires a separate decision. Changes in growth, demand, taxes,
credits, region, amortisation or billing basis must be reconciled before
claiming realised savings. Report uncertainty and seasonality separately
from rounding, and avoid extrapolating a short low-demand window as annual
measured savings.

## Pricing and two independent reconciliations

Refresh mutable unit prices and terms through official provider pricing
pages/calculators/catalogues or authorised billing evidence. Retain provider,
service/SKU, region, unit, currency, capture date, source URL/reference,
confidence and revalidation action. An export measures the existing bill;
target SKU/region/term prices still require verification. If verification
fails, use `A chiffrer` and withhold complete savings/TCO claims.

1. Independently aggregate original billing lines by account, service,
   environment and period and tie them to invoice/export control totals.
   Explain credits, tax, refunds, support and unallocated items. Independently
   rebuild target amounts from quantity/price/meter factors and the residual
   action sequence; compare both baseline and target with workbook detail,
   synthesis and their derived gross/net saving.
2. Recompute from the original usage/BOM, commercial schedule and task JH
   through a separate calculation path that does not read synthesis totals
   or reuse the workbook's saving formulas. Check the portfolio baseline
   minus final target after overlaps and displaced costs, then deduct Build
   and Run costs for the same horizon. For realised savings also tie the
   independent post-change bill to the validated observation window.

Record two results, scope/period, tolerance, residual and unknown-count.
Residuals need a traceable explanation; repeating the same summary formula
does not provide independence. Check every static numerical claim against
its calculated source and keep measured/forecast totals separately labelled.

## Mapping without schema extensions

Baseline and editable savings inputs are assumptions keyed by opportunity
ID. Decisions hold action, monetary ranges/period/currency, status, overlap,
reversibility and linked baseline/task/risk/source IDs in `rationale`.
Implementation task acceptance/evidence holds the validation method; Run
task notes hold cadence, cost drivers and the derivation into monthly JH.
Risk records preserve owners and mitigations; cloud costs represent the
selected target, with quantity/price provenance. Scenarios, inventory,
architecture and phasing use their ordinary common records. Convert money
only through formulas; do not change numeric cloud costs to text or add
undocumented model fields to represent incomplete opportunities.
