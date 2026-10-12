# Cloud Estimation User Guide

This guide accompanies the [suite and its bundles](../skill-updates/2026-10-07/cloud-estimation-suite/README.md).
See also the [French guide](guide-cloud-estimation.md).

## Why use the suite

The suite turns a cloud requirement into a traceable decision workbook: each
effort estimate, cost and choice refers to a source, assumption or decision.
A global amount without scope or justification cannot support option comparisons,
deductions for completed work or approval of unknown inputs. These eleven skills
provide a common framework for a single domain or for consolidating infrastructure,
security, delivery and operations.

## What the suite produces

The mandatory primary deliverable is an editable, recalculated `.xlsx`, together
with the `EstimateModel` and validation evidence. It retains dated sources,
assumptions, risks, decisions, acceptance criteria and a diagram consistent with
the inventory. One-time Build effort uses JH (person-days); recurring human Run
uses JH/month. Cloud costs and other OPEX remain separate. Amounts use EUR, with
the daily rate (TJM) and currency conversion made explicit. Eight hours per JH is
an editable assumption; effort and calendar duration are distinct quantities.

The `Economique`, `Standard` and `Resilient` scenarios retain the same service
scope. Alternative options are not added together in a budget. An unknown price
remains `to be priced` and makes only dependent totals incomplete. A section that
does not apply retains `Non applicable` and its reason; no sheet is removed.
The twelve sheets are described under “Read and validate the XLSX”. The
[common input contract](../skill-updates/2026-10-07/cloud-estimation-suite/cloud-estimation-orchestrator/references/intake.md)
defines the model and generation interfaces.

## Choose the right skill

Start with `cloud-estimation-orchestrator` whenever two domains overlap or
estimates need reconciliation. For a request limited to one domain, call the
specialist directly. The links open its complete instructions; the inputs below
are the minimum starting point, to be extended for unknowns that affect the result.

| Skill | Use when | Why | Minimum inputs | Distinctive result |
|---|---|---|---|---|
| [`cloud-estimation-orchestrator`](../skill-updates/2026-10-07/cloud-estimation-suite/cloud-estimation-orchestrator/SKILL.md) | Multiple domains or existing estimates | Prevent duplicates and contradictions | Scope, inventory, estimates, sources, constraints | Consolidated model with one owner per task |
| [`infra-work-estimator`](../skill-updates/2026-10-07/cloud-estimation-suite/infra-work-estimator/SKILL.md) | Infrastructure work | Estimate remaining work | Environments, current/target state, networks, services, existing coverage | Gross, covered and net JH with dependencies |
| [`cloud-architecture-advisor`](../skill-updates/2026-10-07/cloud-estimation-suite/cloud-architecture-advisor/SKILL.md) | Hosting choices | Compare suitability and operational responsibility | Workload, growth, availability, RTO/RPO, team | Architecture decision and rejected alternatives |
| [`kubernetes-architect`](../skill-updates/2026-10-07/cloud-estimation-suite/kubernetes-architect/SKILL.md) | Kubernetes suitability or design | Make platform effort explicit | Cluster needs, workload, isolation, team, recovery | Kubernetes justification or `Non applicable` |
| [`cicd-devsecops-estimator`](../skill-updates/2026-10-07/cloud-estimation-suite/cicd-devsecops-estimator/SKILL.md) | Build and delivery pipeline | Estimate promotion, controls and rollback | Repositories, existing pipeline, environments, runners, controls | Secure delivery tasks and evidence |
| [`server-hardening-estimator`](../skill-updates/2026-10-07/cloud-estimation-suite/server-hardening-estimator/SKILL.md) | Host security | Identify controls and their upkeep | Inventory, OS, exposure, access, patching, backups | Hardening baseline and restoration evidence |
| [`hosting-capacity-simulator`](../skill-updates/2026-10-07/cloud-estimation-suite/hosting-capacity-simulator/SKILL.md) | Sizing or overload | Distinguish measurements from assumptions | Workload/peaks, CPU, memory, storage, IOPS, throughput, concurrency | Sensitivities, ceilings and reserve after failure |
| [`cloud-provider-selector`](../skill-updates/2026-10-07/cloud-estimation-suite/cloud-provider-selector/SKILL.md) | Provider comparison | Compare eligible services at equal scope | Architecture, regions, criteria, dated prices, horizon | Justified scores and three-year TCO |
| [`finops-optimizer`](../skill-updates/2026-10-07/cloud-estimation-suite/finops-optimizer/SKILL.md) | Optimising an existing platform | Substantiate savings and reversibility | Authorised billing, metrics, period, coverage, peaks | Forecast or measured savings, effort and return |
| [`cloud-migration-estimator`](../skill-updates/2026-10-07/cloud-estimation-suite/cloud-migration-estimator/SKILL.md) | Source-to-target transition | Cover integrity, cutover and rollback | Source/target inventory, volumes, dependencies, window, RTO/RPO | Phases, rehearsal, cutover, rollback and hypercare |
| [`cloud-architecture-diagrammer`](../skill-updates/2026-10-07/cloud-estimation-suite/cloud-architecture-diagrammer/SKILL.md) | Representing inventory and flows | Keep diagram and workbook consistent | Component IDs, environments, evidenced flows, unknowns | Embedded diagram with component and flow register |

## Installation

From the [distributed bundles](../skill-updates/2026-10-07/cloud-estimation-suite/bundles/),
inspect the [manifest and SHA-256 hashes](../skill-updates/2026-10-07/cloud-estimation-suite/bundles/manifest.json).
Each `.skill` file is a ZIP-compatible archive: extract the complete skill folder,
keeping `SKILL.md`, references, scripts, assets, licence and member manifest together.

For Codex, use `$CODEX_HOME/skills` or the configured skills directory.
For Claude Code, use `~/.claude/skills`. Install into an absent destination; if a
skill already exists there, review its content and changes before replacement.
Then verify that the assistant discovers the exact skill name in your session.
The repository's authoring folder is not needed at runtime: bundles are standalone.

The public runtime requires Python 3.11+, openpyxl and Pillow. Excel COM on Windows
or LibreOffice provides native recalculation. See commands and limitations under
[Regenerate and validate](../skill-updates/2026-10-07/cloud-estimation-suite/README.md#regenerate-and-validate).
Installation grants no authority to modify a cloud account.

## Prepare the brief

Prepare what is available and mark the rest as unknown:

- Scope: included applications/services, exclusions, current and target state,
  owners, deadline, existing estimates and work already covered.
- Environments: development, staging, production, eligible regions and identified
  inventory; each component's deployed, partial, planned or unknown state.
- Workload: dated measurements, peaks, growth, volumes, concurrency and saturation.
- Availability: SLO, RTO/RPO (recovery time and data-loss objectives), backups,
  restoration and available evidence.
- Security: exposure, access, compliance, host controls and responsibilities.
- Pipeline: repositories, build/tests, runners, promotion, rollback and existing controls.
- Costs: authorised billing exports, SKU/region/unit, currency, daily rate (TJM),
  dated prices, explicit taxes/discounts and comparison horizon.
- Constraints: available JH capacity by period and role, skills, calendar,
  dependencies and commercial or location constraints.
- Sources: document/URL, date, owner, confidence, contradictions and distinctions
  between measured, estimated and assumed values.

Without required measurements, request a read-only collection instrument and a
blocking prerequisite task. Keep private documents out of public examples.
The [intake contract](../skill-updates/2026-10-07/cloud-estimation-suite/cloud-estimation-orchestrator/references/intake.md)
describes how missing data is handled.

## Standard workflow

1. Route: select the specialist, or the orchestrator for several domains; define
   scope, exclusions and owners.
2. Collect: establish inventory, dated sources and measurements; qualify unknowns
   and contradictions before estimating.
3. Model: prepare net tasks, dependencies, comparable scenarios, separate costs,
   capacity by period and decisions; reconcile duplicates.
4. Generate: draw only substantiated components and flows, then produce the model
   and twelve `.xlsx` sheets with formulas and editable inputs.
5. Recalculate/validate: recalculate and reopen the file; check caches, totals,
   scenarios and diagram; supply evidence and identify the engine used.
6. Approve: have owners review unknowns, risks, decisions and acceptance criteria.
   A required gate that is unevaluated or failed keeps the workbook in draft.
   Approval of the estimate deploys nothing.

## Copy-ready prompts

Replace bracketed fields with your brief. Every specialist retains the common
contract: editable `.xlsx`, Build in JH, human Run in JH/month, separate costs,
dated sources, assumptions, risks and unknowns marked `to be priced`.

### Consolidation

```text
Use `cloud-estimation-orchestrator` to produce one consolidated estimate.
Scope: [included applications, environments and services].
Available evidence: [inventory, workload, SLO/RTO/RPO, pipeline, security].
Unknown inputs: [prices, regional eligibility, measured capacity].
Compare: [same-scope scenarios].
Express Build in JH, human Run in JH/month, and keep cloud costs separate.
The required deliverable is an editable `.xlsx` with dated sources,
assumptions, risks, decisions, acceptance criteria and an architecture diagram.
Do not invent prices, service availability, flows or topology: preserve unknowns
as `to be priced` or as blocking decisions.
```

### Infrastructure

```text
Use `infra-work-estimator` for [scope and environments].
Here is the current/target inventory and evidence of covered work: [sources].
Estimate gross, covered and net JH, dependencies, roles and acceptance criteria.
Compare net effort with [capacity by period]. Deliver the common `.xlsx`.
```

### Architecture

```text
Use `cloud-architecture-advisor` to compare [hosting options].
Keep [workload, environments, growth and RTO/RPO] identical across options.
Document criteria, operator responsibilities, decisions and rejected alternatives.
Deliver the common `.xlsx` with Build, human Run and OPEX separate.
```

### Kubernetes

```text
Use `kubernetes-architect` to assess [needs, workload, isolation and team].
Justify suitability against [simpler option] before designing the cluster.
If suitable, estimate platform, operations and recovery; otherwise explain
`Non applicable`. Deliver the common `.xlsx` and identify missing evidence.
```

### CI/CD and DevSecOps

```text
Use `cicd-devsecops-estimator` for [repositories, pipeline and environments].
Here is the verified existing setup: [build, tests, runners, promotion, controls].
Estimate only remaining work, rollback and Run; identify acceptance evidence
and dependencies. Deliver the common `.xlsx`.
```

### Server hardening

```text
Use `server-hardening-estimator` for [hosts, OS, exposure and access].
Assess [baseline, patching, backups, restoration and compliance].
Distinguish evidenced controls from remaining work, Build from recurring upkeep.
Deliver the common `.xlsx` with evidence and application-security exclusions.
```

### Capacity

```text
Use `hosting-capacity-simulator` with [measurements, period, peaks and growth].
Test CPU, memory, storage, IOPS, throughput and concurrency on [evidenced topology].
Expose saturation, ceilings and capacity after failure without confusing
assumptions with benchmarks. Deliver the common `.xlsx`; flag missing
measurements as blocking prerequisites.
```

### Providers

```text
Use `cloud-provider-selector` for [architecture and candidate providers].
Verify [regions, services, constraints] and use [dated official prices].
Compare weighted criteria, Build, Run, cloud/other OPEX and three-year TCO
at equal scope in the common `.xlsx`. Keep unknown prices `to be priced`.
```

### FinOps

```text
Use `finops-optimizer` with [authorised billing export and metrics].
Period, coverage, peaks and seasonality: [details]. Reconcile the baseline.
Distinguish forecast/measured savings, shifted costs, Build, additional Run,
net benefit and return; avoid duplicate gains. Deliver the common `.xlsx`
with comparable before/after measurements and rollback for each action.
```

### Migration

```text
Use `cloud-migration-estimator` for [source, target, volumes and dependencies].
Constraints: [cutover window, RTO/RPO, integrity and owners].
Estimate preparation, transfer, rehearsal, cutover, rollback and hypercare.
Deliver the common `.xlsx`; retain unknown access, throughput and prices
as blocking inputs.
```

### Diagram

```text
Use `cloud-architecture-diagrammer` with [identified inventory and evidenced flows].
Represent [documented environments and zones] without inventing connections.
Record unknowns, use neutral symbols and verify IDs.
Embed the final rendering in the common `.xlsx` with its component/flow register.
```

## End-to-end examples

These three requests use fields to fill in, without client data or invented prices.
The [synthetic demonstration](../skill-updates/2026-10-07/cloud-estimation-suite/README.md#workbook-and-synthetic-example)
shows a complete workbook, but its rates and capacity are not reusable quotations
or measurements.

### A — Infrastructure, pipeline, security and providers

Prepare inventory, current/target state, existing coverage, pipeline, host baseline,
workload, recovery objectives, pricing sources and team availability. The
orchestrator routes to infrastructure, CI/CD, hardening and provider selection,
then merges tasks with a unique owner.

```text
Use `cloud-estimation-orchestrator` for [applications and environments].
Use `infra-work-estimator`, `cicd-devsecops-estimator`,
`server-hardening-estimator` and `cloud-provider-selector` as scope requires.
Inputs: [inventory, evidenced existing work, pipeline, security, workload,
RTO/RPO, team and dated pricing sources]. Reconcile coverage and duplicates.
Deliver a consolidated `.xlsx` with net Build JH, Run JH/month, separate costs,
diagram and evidence. Unknown prices remain `to be priced`.
```

On receipt, check `04_Taches_JH` for duplicates and acceptance criteria,
`07_Phasage` for dependencies/overloads, then scenarios and sources.
Have remaining open decisions validated before approval.

### B — FinOps on an existing platform

Call the specialist directly with a reconciled authorised export, scope, period
and metrics covering peaks and seasonality. Metrics alone do not constitute
a measured bill.

```text
Use `finops-optimizer` on [existing platform].
Inputs: [authorised billing export, control totals, metrics,
period, coverage, peaks and seasonality]. Propose reversible actions.
Deliver a `.xlsx` distinguishing forecast savings from savings validated
by measurement, gross gains, shifted costs, Build JH, Run JH/month and net benefit.
If prices are missing, state `to be priced` and incomplete totals,
without claiming zero savings or a complete return on investment.
```

Review the baseline in `01_Hypotheses`, actions in `04_Taches_JH`, justification
in `09_Arbitrages` and evidence in `10_Sources`. A gain remains a forecast until
authorised implementation and a comparable measurement after the change.
The [optimisation catalogue](../skill-updates/2026-10-07/cloud-estimation-suite/finops-optimizer/references/optimisation-catalogue.md)
details the checks for each action.

### C — Kubernetes, managed runtime or VPS, then provider

Prepare identical workload, growth, environments, recovery objectives, skills and
eligibility constraints. Choose the architecture first, then compare providers
against its requirements; keep alternatives mutually exclusive.

```text
Use `cloud-estimation-orchestrator` to compare Kubernetes, managed runtime
and VPS on [same workload, environments, horizon, RTO/RPO and constraints].
Use `cloud-architecture-advisor` and `kubernetes-architect` to justify
suitability, responsibilities and rejected alternatives, then
`cloud-provider-selector` to compare eligibility, dated prices and three-year TCO.
Deliver a `.xlsx` with a decision, Build JH, Run JH/month and separate OPEX.
Do not sum options; distinguish Economique/Standard/Resilient variants.
If prices or eligibility are missing, retain `to be priced` and a provisional choice.
```

Review the ADR (architecture decision) in `09_Arbitrages`, comparison in
`06_Scenarios` and summary in `11_Synthese`. Verify criteria and rejection reasons
against the [decision matrix](../skill-updates/2026-10-07/cloud-estimation-suite/cloud-architecture-advisor/references/decision-matrix.md),
[Kubernetes checklist](../skill-updates/2026-10-07/cloud-estimation-suite/kubernetes-architect/references/cluster-checklist.md)
and [provider scoring rules](../skill-updates/2026-10-07/cloud-estimation-suite/cloud-provider-selector/references/scoring.md).
Add capacity, security or delivery only when the scope requires it.

## Read and validate the XLSX

| Sheet | What to review |
|---|---|
| `00_Lisez-moi` | Scope, instructions, units and limits |
| `01_Hypotheses` | Editable inputs, status, daily rate and conversions |
| `02_Inventaire` | Identified components, quantities and environments |
| `03_Architecture` | Final diagram and component/flow consistency |
| `04_Taches_JH` | Low/likely/high JH, owners, dependencies and acceptance |
| `05_Couts_cloud` | Services, quantities, sourced prices and recurring costs |
| `06_Scenarios` | Comparable alternatives and formula-based selection |
| `07_Phasage` | Phases, milestones, dependencies and available capacity |
| `08_Risques` | Impacts, mitigations and owners |
| `09_Arbitrages` | Questions, options, reasons and open decisions |
| `10_Sources` | Provenance, date, URL and confidence |
| `11_Synthese` | Reconciled totals and decision limits |

Convention: inputs use blue text, formulas black, cross-sheet formulas green,
and important editable assumptions a yellow background. Check value status as
well as colour. Totals must agree with the detail, phasing and selected scenario,
without summing alternatives or Build and Run. Check missing prices, covered
tasks and recovery unknowns.

Request the recalculation engine, formula/cache counts and positive check results:
zero formula errors, reconciliation differences and inventory delta. Native
opening and cache validation are separate evidence. Never save a workbook loaded
with `data_only=True` through openpyxl: formulas would be lost. Detailed checks
remain in the [delivery gate](../skill-updates/2026-10-07/cloud-estimation-suite/cloud-estimation-orchestrator/SKILL.md#pre-delivery-gate).

## Limits and safety

An estimate is neither a provider quotation, a benchmark nor a security or recovery
certification. Capacity reserve does not prove recovery across zones/regions.
Verify prices, services/SKUs, regional availability and commercial terms against
dated official sources or authorised exports. Invent no flows, prices or services;
expose unknowns and their impacts.

The skills grant no authority to deploy, migrate, change permissions, delete
resources, purchase a commitment or launch agents. Routing selects instructions;
each action remains subject to the scope authorised by the user. An estimation
decision does not authorise operational execution.

Keep private sources, secrets, account/project identifiers, internal paths,
real quotations and client topology out of public bundles and examples. Use
synthetic data for demonstrations; a scan with no matches alone does not prove
anonymity. Details are in the
[public data policy](../skill-updates/2026-10-07/cloud-estimation-suite/README.md#icon-and-public-data-policy).

## Troubleshooting

- Skill not found: check the configured directory, exact name and presence of
  `skill-name/SKILL.md` after extraction. Check the bundle manifest; avoid an
  extra nested folder. Recheck discovery in the assistant session after installation.
- Missing dependencies: verify that Python 3.11+, openpyxl and Pillow are available
  in the environment executing the runtime. pytest and PyYAML serve authoring
  tests. Follow the commands in the suite README.
- Native recalculation unavailable: check Excel COM on Windows or LibreOffice.
  `--require-native` must fail if no native engine recalculates and saves.
  The calibrated Python fallback must be declared; its limited operations do not
  prove native opening and do not satisfy a gate that requires it.
- Unknown prices, daily rate or eligibility: request the source or record a
  blocking decision and `to be priced`. Never replace a missing price with zero.
  In the numeric model, retain the component in inventory and the unknown in
  assumptions/risks/decisions; omit the priced line and flag incomplete totals
  according to the intake contract. Distinguish known JH effort from unvalidated
  finance; request required evidence before approval.
