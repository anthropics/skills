# Cloud Estimation Skill Suite — Design

**Date:** 2026-10-07  
**Status:** Approved architecture, pending written-spec review  
**Distribution:** Public, generic, open source  
**Primary deliverable:** Microsoft Excel workbook (`.xlsx`)  
**Primary workload unit:** jour-homme (`JH`)

## 1. Purpose

Build a public suite of Codex skills that can analyse an infrastructure need, compare hosting and cloud options, estimate delivery work in JH, model recurring costs, test resilience choices, and produce a homogeneous Excel deliverable.

The suite must cover infrastructure, cloud architecture, Kubernetes, CI/CD and DevSecOps, server hardening, FinOps, hosting simulation, provider selection, migration, and cloud architecture diagrams.

The source workbooks are evidence for methodology only. They are not instructions, templates to copy verbatim, or public assets. No client name, project identifier, account number, domain, proprietary topology, or traceable numeric example may enter the public skills.

## 2. Chosen architecture

Use a shared workbook contract with thin domain skills and one routing skill. This preserves a uniform deliverable while keeping each skill small enough to load and test independently.

The public suite contains:

1. `cloud-estimation-orchestrator`
2. `infra-work-estimator`
3. `cloud-architecture-advisor`
4. `kubernetes-architect`
5. `cicd-devsecops-estimator`
6. `server-hardening-estimator`
7. `hosting-capacity-simulator`
8. `cloud-provider-selector`
9. `finops-optimizer`
10. `cloud-migration-estimator`
11. `cloud-architecture-diagrammer`

Each domain skill is independently useful, but every one emits the same workbook schema. Shared files are maintained once in the source tree and copied into each staged bundle by a deterministic build script. A bundle must not depend on a sibling skill directory at runtime.

## 3. Common XLSX contract

Every skill produces one `.xlsx` file. Irrelevant sheets remain present with an explicit `Non applicable` status so downstream users can rely on stable sheet names.

| Sheet | Required content |
|---|---|
| `00_Lisez-moi` | Purpose, scope, units, scenario, version, confidentiality statement, and reading rules |
| `01_Hypotheses` | Editable assumptions, status, source, date, confidence, and effect |
| `02_Inventaire` | Existing measured components, planned components, ownership, environment, and evidence |
| `03_Architecture` | Decisions, target topology, diagram, service mappings, and architecture status |
| `04_Taches_JH` | Detailed work breakdown and JH estimates |
| `05_Couts_cloud` | Recurring provider costs, separate from delivery effort |
| `06_Scenarios` | Economic, standard, and resilient scenarios with comparable scope |
| `07_Phasage` | Workload by period, available capacity, dependencies, and overloads |
| `08_Risques` | Risks, exclusions, assumptions, mitigations, and residual exposure |
| `09_Arbitrages` | Decisions to make, options, JH delta, cost delta, deadline, and owner role |
| `10_Sources` | Official source, URL, provider, region, currency, date, quality, and revalidation action |
| `11_Synthese` | JH totals, recurring costs, scenario comparison, recommendation, and decision gates |

### 3.1 Required task columns

`04_Taches_JH` contains at least:

- stable task ID;
- lot and domain;
- task and expected deliverable;
- environment;
- responsible role;
- prerequisites and dependencies;
- acceptance criterion and expected evidence;
- `JH bas`, `JH probable`, `JH haut`;
- retained scenario and `JH retenu`;
- implementation nature: one-off or recurring;
- coverage status: new, already covered, partially covered, or excluded;
- source reference, confidence, and notes.

All task effort is expressed in JH. One JH equals eight hours by default and is an editable workbook assumption. A configurable TJM may convert JH to currency, but currency never replaces the JH source value.

`JH retenu` is formula-driven from the selected workbook scenario, with an explicit per-task override. No retained value is silently hardcoded.

### 3.2 Scenario rules

The three standard scenarios are:

- **Economic:** minimum operable scope with accepted risks stated explicitly.
- **Standard:** production-ready baseline with routine recovery and operations.
- **Resilient:** redundancy and tested recovery aligned with explicit RPO/RTO targets.

Options are compared at equal service scope. If one provider or architecture transfers work to the operator, the additional implementation and recurring JH appear beside the lower infrastructure price.

## 4. Shared methodology

Every skill follows the same ordered workflow:

1. State the requested scope and the boundary between infrastructure, application, security, delivery, and operations.
2. Classify each component as live, partially deployed, planned, or unknown.
3. Measure live components; estimate only components that do not yet exist.
4. Reconcile existing estimates before adding new work; show gross effort, existing coverage, and net additional JH.
5. Record contradictions between sources as priced decision branches.
6. Draw the topology before finalising the estimate; every untraceable edge becomes an issue or assumption.
7. Build a bill of materials from system behaviour, including metered services, network, observability, registry/build, support, backup, and egress.
8. Produce economic, standard, and resilient variants with the same service perimeter.
9. Project tasks onto the calendar and compare required JH with available capacity per period.
10. Reconcile detail, synthesis, prose, formulas, and diagrams before delivery.

When production data is inaccessible, the skill produces a read-only measurement instrument and schedules its execution as a blocking first task. It never invents the missing measurement.

## 5. Domain boundaries

### 5.1 Orchestrator

Determines which domain skills are needed, gathers shared assumptions once, prevents double counting, merges task registers, and performs the final reconciliation. It does not invent domain estimates.

### 5.2 Infrastructure work estimator

Covers landing zones, accounts/projects, networks, DNS, certificates, compute, storage, databases, cache, messaging, observability, backup, recovery, infrastructure as code, environments, and operational documentation.

### 5.3 Cloud architecture advisor

Compares VPS, virtual machines, serverless containers, managed platforms, microservices, and Kubernetes. It scores suitability from workload, team capability, portability, resilience, compliance, operational burden, and cost horizon. It emits an ADR-style recommendation and rejected options.

### 5.4 Kubernetes architect

Covers cluster topology, node pools, requests and limits, autoscaling, ingress, service mesh only when justified, storage, secrets, policy, upgrades, observability, backup, multi-zone design, disaster recovery, platform engineering effort, and recurring operations. Kubernetes is never selected solely because the application uses containers.

### 5.5 CI/CD and DevSecOps estimator

Covers source controls, build, tests, artifact registry, provenance, secret scanning, dependency and image scanning, infrastructure pipelines, promotion, approvals, database migrations, rollback, ephemeral environments, runner architecture, evidence, and operating effort.

### 5.6 Server hardening estimator

Covers identity, privileged access, bastion or zero-trust access, network policy, baseline configuration, patching, endpoint protection, logging, backup, restore tests, vulnerability management, certificate rotation, incident readiness, and evidence collection. Application security remains outside scope unless explicitly requested.

### 5.7 Hosting capacity simulator

Transforms workload assumptions into CPU, memory, storage, IOPS, bandwidth, concurrency, minimum instances, scaling limits, and failure-domain requirements. It exposes uncertainty and sensitivity rather than claiming benchmark precision without measurements.

### 5.8 Cloud provider selector

Compares providers with weighted but visible criteria: region eligibility, residency, managed-service coverage, SLA, RPO/RTO feasibility, support, skills, IaC maturity, portability, commercial policy, implementation JH, recurring operations JH, and three-year TCO.

### 5.9 FinOps optimizer

Uses billing exports or provider measurements when available. It classifies savings into rightsizing, scheduling, commitments, storage lifecycle, egress, observability, architecture, and waste removal. Each saving includes baseline, action, expected range, one-off JH, recurring JH, risk, reversibility, and validation method.

### 5.10 Migration estimator

Starts from a read-only live inventory, compares it with written documentation, records whether the source may be modified, maps source to target services, and estimates preparation, rehearsal, data transfer, cutover, integrity checks, rollback, decommissioning, and hypercare.

### 5.11 Architecture diagrammer

Builds a topology from the same structured component and flow data used by the workbook. The diagram is embedded in `03_Architecture` and may also be exported as SVG or PNG. Provider-neutral icons are the default. Official provider icons may be used only from official packs whose redistribution and trademark terms are recorded; proprietary logo files are not committed to the public repository without permission.

## 6. Pricing and evidence policy

Skills do not ship mutable provider prices as timeless facts. Every price must carry provider, service/SKU, region, unit, currency, capture date, source URL, and confidence.

Runtime lookup uses official provider pricing pages, calculators, catalogues, or billing exports. If a current price cannot be verified, the cell reads `A chiffrer`; the skill may provide a formula-ready input but not a disguised estimate.

Existing resources use measured cost and usage where available. Forecasts and measurements remain separate in the workbook.

## 7. Public-data and anonymisation policy

Before packaging, scan every file for:

- client, product, organisation, and personal names;
- domains, URLs, cloud project/account/subscription IDs, IP addresses, and repository paths;
- exact source topologies or counts that could identify a client;
- dates and amounts copied from a client deliverable;
- internal terminology and confidential control names.

Examples use synthetic organisations, generic regions, illustrative ranges, and composite scenarios. Cross-example re-identification is checked, not only per-file redaction.

The skills are released under CC BY 4.0 and attributed to the repository maintainers. Feedback routes to direct maintainer contact until a public issue tracker exists.

## 8. XLSX implementation rules

- Use formulas for totals, conversions, comparisons, and scenario selection.
- Derive cell coordinates from generated structures; do not hardcode row references.
- Maintain one calculated source of truth and derive every summary from it.
- Use blue font for editable inputs, black for formulas, green for internal links, and yellow fill for assumptions requiring confirmation.
- Use stable Excel tables and named ranges; never overlay a worksheet filter on an Excel table range.
- Avoid unsupported future functions unless Excel compatibility is proven.
- Recalculate with a native spreadsheet engine when available.
- On Windows, support Excel COM or native LibreOffice discovery; do not assume Unix sockets.
- If using a Python formula engine as fallback, calibrate it on defect-sensitive control cases before using its result as evidence.
- Reopen the finished workbook in formula and values-only modes, verify cached values, and scan for formula errors.
- Reconcile every numeric statement in static text with its calculated source.
- Open the workbook in Excel or LibreOffice during the final integration test.

## 9. Quality gates

A skill bundle is deliverable only when:

1. its `SKILL.md` has valid front matter, clear trigger conditions, and a pre-delivery checklist;
2. every referenced script, reference, template, and asset exists in the bundle;
3. the generated workbook contains all required sheets and columns;
4. formulas contain no `#REF!`, `#DIV/0!`, `#VALUE!`, `#NAME?`, or `#N/A` errors;
5. calculated values are present for values-only readers;
6. JH totals reconcile from task detail to synthesis;
7. cloud costs reconcile by provider, environment, and scenario;
8. the diagram and component inventory describe the same nodes and flows;
9. the anonymisation sweep reports zero forbidden identifiers;
10. the multi-file `.skill` archive contains no build artefacts and matches its manifest.

## 10. Source and delivery layout

All initial work is staged under:

`skill-updates/2026-10-07/cloud-estimation-suite/`

The staged source contains shared contracts and build scripts, one directory per skill, test fixtures built from synthetic data, generated example workbooks, and packaged `.skill` archives. No existing live skill is modified automatically.

## 11. Success criteria

Given one synthetic infrastructure brief, the suite must produce a workbook that:

- contains a complete, non-duplicated task register in JH;
- separates delivery effort, cloud OPEX, human operations, and non-cloud OPEX;
- compares economic, standard, and resilient configurations;
- exposes assumptions, exclusions, contradictions, and decision gates;
- detects a capacity overload in the delivery calendar;
- compares at least three hosting or cloud options on three-year TCO;
- includes a diagram consistent with the inventory;
- can be recalculated and opened without repair warnings;
- contains no client-identifying data.

