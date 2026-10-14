# Hosting decision matrix and model mapping

Read for architecture alternatives and ADR recommendations. Reuse the
requested workload, evidence date, environments, growth horizon, compliance
and recovery targets throughout the comparison. Ask only for inputs that
materially change eligibility, effort, cost or the recommendation.

## Option dimensions

| Alternative | Suitability evidence to seek | Operator work and dependencies to expose |
|---|---|---|
| VPS | Simple service perimeter, predictable resource needs, supported location and recovery path | Guest OS, patching, monitoring, backups, restore tests and provider support limits |
| Virtual machines | OS/runtime control, compatible images, measured capacity and required failure domains | Image lifecycle, scaling, networking, failover and infrastructure automation |
| Serverless containers | Compatible runtime, startup/latency behaviour, concurrency, request duration and state handling | Service limits, external state, scaling floor, deployment and observability responsibility |
| Managed platforms | Required runtime/features, service availability, data portability and recovery evidence | Application compatibility, platform limits, migration/exit dependencies and remaining operator duties |
| Microservices | Independent release/scaling needs, service ownership and operational capability | Application decomposition and data boundaries as separate scope; distributed failure, delivery and observability overhead |
| Kubernetes | Demonstrated scheduling/platform needs, team capacity and ecosystem constraints | Cluster/platform engineering, upgrades, capacity, ingress, policy and recovery owned by the Kubernetes domain |

Microservices is an application structure, while the other alternatives
describe hosting choices. Compare complete combinations where it matters,
rather than treating decomposition as a replacement for compute. Do not
invent application rewrite JH. Expose the missing estimate and decision owner.
Kubernetes requires an evidenced platform need; containers alone are not one.

## Criteria and eligibility

First test hard constraints: required location/residency, supported runtime,
data/control requirements, availability, RPO/RTO feasibility, service limits
and available operating capability. Record a failed constraint and its source
as a rejected-option decision. Unknown evidence is not a passing constraint.

For eligible options, create an inspectable matrix with criteria, weights,
score meanings, evidence, confidence and unknowns. Suggested criteria are:

- Workload: steady/bursty load, state, latency, concurrency and growth.
- Team: existing skills, support coverage and ability to own the service.
- Portability: data/service coupling, exit effort and required runtime control.
- Resilience: failure domains, recovery dependencies and testable RPO/RTO.
- Compliance: eligible locations and evidence/control responsibilities.
- Operational burden: one-off Build and monthly Run JH by responsible role.
- Cost horizon: same usage, growth, currency and horizon for each alternative.

Agree score anchors and weights from priorities; do not ship universal
weights or rate cards. Treat unknown scores as unresolved criteria rather
than zero-quality or best-quality evidence. Compare the outcome under plausible
priority/load variations. If the recommendation flips, expose the threshold
as a decision instead of hiding it in a weighted average. Avoid a numeric
precision that exceeds the evidence.

## Effort, cost and scenarios

Use net scoped infrastructure JH after proving existing coverage. Architecture
assessment tasks require a deliverable and acceptance evidence; do not add a
generic percentage on top of another domain's design work. Keep selected
task ownership and reference external dependencies without duplication.

Construct bills of materials from request/usage behaviour, including network
and egress, observability, registry/build, support, backup and recovery. A
managed fee can replace operator work only when responsibility is actually
transferred; otherwise retain the monthly Run JH. Keep non-cloud OPEX in
separately sourced assumptions, with its own subtotal and horizon.

Current official prices or authorised exports must identify provider,
service/SKU, region, unit, currency, capture date, source URL and confidence.
Verify eligibility and technical limits against current official material
when they determine the decision. Record measured usage separately from
forecasts. Missing price records belong in assumptions, risks and decisions
as `A chiffrer`; do not provide zero-cost placeholders. Disclose incomplete
totals and block a complete recommendation if the missing evidence is required.

Each eligible alternative has `Economique`, `Standard`, `Resilient` at the
same service perimeter. Explain accepted risks and recovery targets for each
variant; resilience requires evidence beyond a redundancy label. Keep low,
likely and high task JH ordered and finite. Use `Build` for one-off work and
`Run` for JH/month. Project Build work onto periods with available capacity;
record allocations, overloads and milestones in assumptions/phase notes.

There is no typed alternative/branch selector in the current common model.
Keep one complete model/workbook per mutually exclusive alternative. The
selected-model workbook contains chosen tasks/costs; its decisions describe
the alternatives and their independently checked deltas. Do not use task
`scenario_override` to select a hosting alternative, or add all candidate
cost rows into one set of scenario totals.

## ADR and common output records

[domain-contract.json](domain-contract.json) lists exact
record keys. Option and cost-driver are domain record types mapped to existing
model sections, not new top-level fields. Preserve stable option and source
IDs in notes so the comparison, diagram and ADR can be traced.

| Workflow output | Model mapping | XLSX destination |
|---|---|---|
| Boundary, selected alternative, exclusions and incomplete totals | `metadata.notes` | `00_Lisez-moi` |
| Criterion weights/scores, capacity and cost drivers | `assumptions` | `01_Hypotheses` |
| Evidence-based quantities and component states | `inventory` | `02_Inventaire` |
| Option record: component/type/environment/provider/decision, criterion evidence in notes | `architecture` | `03_Architecture` |
| Scoped design, measurement and infrastructure work | `tasks` | `04_Taches_JH` |
| Verified recurring service rows for this alternative | `cloud_costs` | `05_Couts_cloud` |
| Equal-perimeter service-level variants | `scenarios` | `06_Scenarios` |
| Task lots, milestones, period capacity and allocations | `phasing` | `07_Phasage` |
| Residual exposure, missing criteria and dependencies | `risks` | `08_Risques` |
| ADR context, selected/rejected option and reasons | `decisions` | `09_Arbitrages` |
| Dated measurements, service constraints and official prices | `sources` | `10_Sources` |
| Reconciled effort, costs and recommendation | Derived formulas | `11_Synthese` |

In each ADR `question` states the context/problem, `option` identifies the
selected or rejected option, `rationale` records evidence and consequences,
`status` identifies proposed/accepted/rejected, and `source` links the evidence.
Use rationale for JH/cost deltas, owner role, decision deadline, alternatives,
residual risk and conditions that reopen the decision. An accepted choice
requires the relevant user's decision or an existing authorised constraint;
do not promote an agent recommendation to an accepted ADR silently.

Cost-driver records use unique `assumptions.key`, `value`, `unit`, `status`,
`source`, `notes`. Keep option/environment/scenario, quantity basis, growth,
horizon, confidence and impact in notes. Store verified quantity/price inputs
as numeric cloud-cost rows only when all required values are available.

## Full model and artifact checks

Read the locally supplied common model and workbook contract at serialisation.
Emit all eleven `EstimateModel` fields, including empty arrays; `metadata`
contains `title`, `date`, `currency`, `effort_unit`, `notes` with effort unit
`JH`. Include unique assumptions `scenario_global`, `taux_journalier`,
`mois_par_an` and editable `heures_par_jh` (default 8). TJM and months/year
are finite non-negative numbers; missing conversion inputs stay unconfirmed
and prevent complete monetary conversion. All three valid scenarios appear
exactly once, and costs use the metadata currency after sourced conversion.

Task IDs are unique, dependencies are task-ID arrays without self-reference,
unknown IDs or cycles, and every lot maps to a phase. Use valid scenario
overrides only. Load the model with the locally supplied `load_model` before
building the workbook. Keep all twelve contract sheets; explain `Non
applicable` sections without removing the schema. Preserve formula totals,
editable inputs and scenario selection.

Draw the topology before final estimation using inventory IDs and explicit,
evidenced edge source/target pairs. Diagram input is separate from architecture
decision rows. Inspect the renderer's final output; unknown edges cannot be
silently inferred. Provide the explicit diagram input to `build_workbook`.
Recalculate with the supplied adapter, inspect its returned engine, success,
cache counts and errors, then reopen formulas and values. Native opening is
required where available; a calibrated fallback must be disclosed and does
not prove a required native-opening check. Supply numeric prose assertions
and manifest node IDs to `validate_workbook`; independently verify criterion
scores, TCO/deltas, capacity calculations and flow evidence, which the common
validator cannot establish from omitted inputs.
