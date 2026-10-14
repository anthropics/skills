# Server control catalogue and common-model mapping

Use controls appropriate to the requested threat/exposure and operating
boundary. A host baseline is versioned and scoped; it is not a statement of
full organisational or application compliance. Evidence records distinguish
implemented configuration, effective behaviour and accepted exceptions.

## Control deliverables

| Boundary/control | Implementation task and verification evidence | Separate recurring JH drivers |
|---|---|---|
| Identity | Map host/service identities and lifecycle to intended roles; effective membership/export, successful intended login and refused disabled/unapproved identity | Joiner/mover/leaver handling, service-identity rotation, access review |
| Privileged access | Bound elevation, emergency access and audit; permitted role test, denied ordinary-user elevation and attributable privilege event | Entitlement review, emergency-access rehearsal, exception expiry |
| Bastion or zero-trust management | Choose justified access path and identity/session controls; successful authorised session, refused direct/untrusted path and retrieved session evidence | Access infrastructure upkeep, policy review, credential/session incident handling |
| Network policy | Bound listening services, host firewall and required flows; effective rules/listeners plus allowed service path and denied unintended path | Rule drift review, service changes and exception expiry |
| Baseline configuration | Apply versioned OS-specific settings with scoped exceptions; effective-state report, known failed control and service compatibility/health result | Drift monitoring, baseline revisions and exception review |
| Patching | Supported lifecycle, staged rollout and recovery procedure; version inventory, test-host patch/reboot result, service health and recovery rehearsal | Advisory intake, patch cycles, urgent changes and post-patch checks |
| Endpoint protection | Configure justified coverage and response with named operator; fleet heartbeat/coverage, safe controlled detection, routed alert and recorded response | Alert triage, agent/signature updates, coverage gaps |
| Logging | Collect security/service events with retention, timestamps and limited access; triggered event reaches sink, operator retrieves it and unauthorised reader is denied | Missing-log/alert triage, retention/access review and ingestion tuning |
| Backup | Bound system/configuration/data coverage, keys and restore dependencies; successful scoped backup with integrity/retention/access checks | Failed-job triage, retention/capacity review and key availability |
| Restore tests | Recover in isolation and prove service/data integrity; restore log, usable service, integrity checks and measured recovery against explicit RPO/RTO | Periodic rehearsal, runbook drift and remediation |
| Vulnerability management | Define authenticated fleet scan, prioritisation and exceptions; report proves target/credential coverage, a known test finding is detected, remediation retest closes it | New findings, prioritisation, retesting and exception expiry |
| Certificate rotation | Inventory endpoints/issuers/owners and renewal route; handshake/chain evidence, controlled renewal and expiry alert plus refused invalid certificate | Renewal/rotation, expiry monitoring and trust-store upkeep |
| Incident readiness | Scope escalation, isolation authority, evidence preservation and recovery; tabletop or isolated rehearsal with alert acknowledgement, timeline and restored-service checks | On-call response, rehearsals, contact/runbook maintenance |
| Evidence collection | Link control, host group, source/date and exception to retrievable proof; sampled complete control trail, authorised retrieval and denied unauthorised access | Audit preparation, evidence expiry/retention and access review |

Evidence criteria name the target set, collection method, capture date,
baseline/tool version and expected result. A scan with no authenticated
targets or an empty event stream cannot prove absence of vulnerabilities or
presence of logging. Test known outcomes in safe isolated scope; do not run
destructive vulnerability exploits on production to justify an estimate.

## Boundaries, exceptions and effort

Provider-managed services can transfer OS patching/agent ownership to the
provider; validate the responsibility boundary rather than adding impossible
host tasks. Cloud account access, network provisioning, cluster admission
policy and pipeline scanning may have other owners. Cite their task IDs and
evidence once, with local verification only where it proves a distinct host
acceptance result. Backup policy and a recovery rehearsal are distinct, but
the same recovery proof is not charged to several domains.

Application authentication/authorisation, secure code review, application
penetration tests and business-logic fixes remain excluded unless explicitly
requested. If included, name the application boundary, tasks and owner
separately. A missing OS control cannot be dismissed by an application scan.

Store `control_boundary`, scoped baseline/version, host-group inventory IDs,
gross/covered/net effort, proof references and residual-risk IDs in task
notes. Each control has `task`, `acceptance_criterion` and `expected_evidence`;
link actual dated reports through sources. Put residual exposure in risk
records, including no material residual risk where justified, and preserve
owners/mitigations/status. For accepted exceptions, record review/expiry and
compensating controls in mitigation/status and decision notes.

Build task JH estimate implementation, scoped review, acceptance checks and
handover once. Separate Run tasks estimate JH/month from fleet variation,
cadence, event volume and handling time. Annual restore/access rehearsals
are converted using their stated cadence, not charged as monthly full events.
Record conversion assumptions and derivations explicitly. A synthetic fleet
with a shared baseline has one baseline authoring task, variation-specific
validation tasks and recurring drift/patch work; reuse never eliminates
verification on affected OS/service variants. No universal JH values apply.

Without access, create a read-only measurement task that collects OS/version,
effective access/rules, patch state, agent/scan coverage, logging and recovery
evidence as required. Dependent acceptance estimates reference that task;
required evidence gaps block a complete hardening claim. Recovery objectives
need measured restore results; a successful backup log is insufficient.

## Model and workbook interface

Read [domain-contract.json](domain-contract.json) for exact keys and
`domain_fields` mappings. Control boundary uses task notes, implementation
uses task text, and evidence uses `expected_evidence`. Build and Run JH
belong to separate Task rows; residual risk uses common risk records.
Bindings do not add fields to `EstimateModel`.

| Record | Model section | Sheet |
|---|---|---|
| Implementation, verification and monthly operations | `tasks` | `04_Taches_JH` |
| Host groups, access, protection, log and recovery components | `inventory` | `02_Inventaire` |
| Management/recovery boundaries and choices | `architecture` | `03_Architecture` |
| Cadence, hours/JH, coverage gaps and non-cloud OPEX | `assumptions` | `01_Hypotheses` |
| Control exposure, exceptions and compensating measures | `risks` | `08_Risques` |
| Baseline exceptions, ownership and option decisions | `decisions` | `09_Arbitrages` |
| Dated settings, tests, reports and official price evidence | `sources` | `10_Sources` |
| Equal-scope variants and task-lot milestones | `scenarios`, `phasing` | `06_Scenarios`, `07_Phasage` |

The full JSON has all eleven `EstimateModel` sections. Metadata contains
title, date, currency, effort_unit `JH` and scope/exclusions in notes
(`00_Lisez-moi`). Unique required assumptions are `scenario_global`,
`taux_journalier`, `mois_par_an`; the last two are finite non-negative
numbers. Unconfirmed TJM blocks complete monetary conversion; add editable
`heures_par_jh` default 8. Preserve each `Economique`, `Standard`, `Resilient`
once. All task fields are strings except finite non-negative ordered
`jh_low <= jh_likely <= jh_high`, task-ID dependency arrays and nullable/empty/
valid `scenario_override`. Dependencies resolve without self-reference or
cycles after merge. Every lot matches `phasing.phase`. Build is one-off;
Run is JH/month with cadence and driver derivations in notes/assumptions.

Verified costs map to `cloud_costs` / `05_Couts_cloud` with finite
non-negative quantity, unit price and monthly multiplier, valid scenario
and metadata currency. Capture SKU, region, billing unit, capture date and
official source in notes/sources. Missing prices remain `A chiffrer`
assumptions, risks and decisions; omit unpriced numeric rows and mark totals
incomplete. Non-cloud protection/support costs remain sourced assumptions.
`11_Synthese` contains derived formulas. Do not sum mutually exclusive
management/recovery choices; use separate complete models or checked decision
deltas. Calendar allocations/capacity use phase notes and assumptions with
independent arithmetic checks, since no dedicated calendar fields exist.

Diagram nodes use inventory IDs; explicit source/target/label edges need
evidence, not assumed connectivity from decision rows. Use `load_model`,
`build_workbook`, `recalculate` and `validate_workbook` from locally supplied
tooling. Inspect engine/status/cache counts/errors, reopen formula/value
views, and provide numeric prose assertions and final diagram IDs to the
validator. Disclose calibrated fallback limits; fallback cannot satisfy a
required native-opening check. Preserve all sheets as `Non applicable`
where irrelevant.
