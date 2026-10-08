# Pipeline catalogue and common-model mapping

Use the requested stages only. Estimate reusable setup once, then explain
incremental work by repository, artifact type, environment and trust boundary.
Do not infer security coverage from an installed tool or a green empty scan.

## Stage deliverables

| Stage/control | Implementation and completion evidence | Separate recurring JH drivers |
|---|---|---|
| Source controls | Branch/tag protection, peer review and identity policy; exported rules plus permitted and refused change attempts | Access review, exception expiry, policy drift |
| Build | Versioned reproducible build and cache boundary; clean build log, artifact digest and controlled rebuild result | Failed build triage, toolchain/cache maintenance |
| Tests | Wire scoped test suites and quality gates; reports with non-zero expected test counts plus a seeded failing case blocking release | Flaky-test triage and gate tuning; authoring application tests has a separate owner |
| Artifact registry | Publish/pull policy, immutable versions and retention; digest-pinned publish/pull evidence, denied unauthorised push and cleanup rehearsal | Retention review, storage review, access rotation |
| Provenance | Build identity, artifact inputs and attestation validation; attestation tied to digest and refused altered/untrusted artifact | Signing identity rotation, provenance review |
| Secret scanning | Scope history and new changes, response/exception policy; synthetic detected secret blocks merge, clean control passes, revoked test credential proof | Finding triage, revocation response and exception review |
| Dependency scanning | Lockfile/SBOM coverage and severity policy; dependency report tied to artifact plus a known finding triggering the selected gate | Advisory intake, remediation routing, temporary exception expiry |
| Image scanning | Scan shipped image digest and runtime layers; report/digest match with a failing control and explicit coverage limitations | New finding review, rebuild coordination, exception review |
| IaC pipeline | Plan/apply separation, state locking and limited identity; reviewed plan, lock contention test, denied unauthorised apply and drift evidence | Module updates, drift triage and policy maintenance |
| Promotion | Promote the same verified digest through environments; trace from build to deployed digest and rejected unapproved candidate | Release support and deployment failure triage |
| Approval | Role separation and bounded exceptions; approval audit trail plus denied self-approval/unapproved production promotion | Approver/access review and exception expiry |
| Database migrations | Order/version/compatibility gates and migration ownership; rehearsal on synthetic representative data, validation and tested recovery path | Migration review and release rehearsal support |
| Rollback | Trigger, last-known-good artifact and data recovery route; isolated failed-release rehearsal with health checks and measured recovery against target | Recovery rehearsals and runbook maintenance |
| Ephemeral environments | Scoped creation, isolation and cleanup; health evidence, forbidden network/secret access and verified TTL/deletion including dependent resources | Leak review, quota management and cleanup failures |
| Runner architecture | Hosted or self-managed choice, isolation and capacity; queue/concurrency measurement, controlled untrusted job and credential expiry evidence | Image patching, capacity, incident response and runner rotation |
| Evidence retention | Link change, reviews, tests, scans, approvals, artifact and deployment with retention/access policy; retrieve one full release trail and reject unauthorised retrieval | Retention/access audit, evidence retrieval and storage review |
| Operations/handover | Named operator, escalation and runbooks; supervised failed-job/failed-release response with acknowledgement and recovery result | On-call/release assistance, incident triage and periodic rehearsal |

A scan acceptance criterion identifies input scope, version/date, finding
policy, exception owner and expiry. A clean report without expected scanned
items cannot prove coverage. Use safe synthetic findings in isolated test
boundaries; estimation does not authorise production changes or disclosure
of genuine secrets. Logs and exported evidence must redact credentials.

## Boundary decisions and effort

Registry/runner provisioning may belong to infrastructure; runner OS controls
to hardening; workload deployment integration to delivery; cluster policy to
the platform owner. Assign one acceptance result to one task and reference
that task elsewhere. Database migration execution belongs to this domain only
when requested; schema design, data transformations and whole-system cutover
keep their application/migration owners. Scanning and gates identify risk;
they do not imply that vulnerability remediation is included automatically.

Keep forward-compatible schema changes, destructive changes and restoration
choices explicit. Deploying an earlier artifact does not reverse a committed
data migration. If recovery is unknown, record a residual risk and blocking
rehearsal instead of promising rollback.

Record `pipeline_stage`, repository/artifact scope, trust boundary and
coverage proof in `tasks.notes`. Every stage has an acceptance criterion and
`expected_evidence` reference; use separate Build and Run IDs. Estimate Run
as JH/month from editable event counts, frequency and handling time, including
rare rehearsal effort spread over its stated cadence. Put the conversion and
derivation in notes/assumptions; provider build minutes are monetary usage,
not human JH. Do not hide human release work inside a platform subscription.

For synthetic illustration, one shared runner bootstrap is one Build task;
per-environment wiring and monthly patch/triage are separate tasks. Sharing a
runner reduces setup repetition, while distinct trust zones can require
separate isolation work. No fixed JH values follow from this example.

## Model and workbook interface

Read [domain-contract.json](domain-contract.json) for exact record keys and
the `domain_fields` bindings. Those bindings describe existing model fields,
not extra top-level fields. Pipeline stage uses task notes; evidence uses
`expected_evidence`; one-off and recurring JH use different Task records.

| Record | Model section | Sheet |
|---|---|---|
| Stage work and monthly operations | `tasks` | `04_Taches_JH` |
| Repository, runner, registry, evidence store | `inventory` | `02_Inventaire` |
| Runner/promotion trust decisions and flows | `architecture` | `03_Architecture` |
| Frequencies, unknown inputs and non-cloud OPEX | `assumptions` | `01_Hypotheses` |
| Failure exposure and mitigation | `risks` | `08_Risques` |
| Gate exceptions and incompatible options | `decisions` | `09_Arbitrages` |
| Dated reports, settings exports and price evidence | `sources` | `10_Sources` |
| Equal-scope variants and task-lot milestones | `scenarios`, `phasing` | `06_Scenarios`, `07_Phasage` |

The full JSON contains all eleven `EstimateModel` sections. Metadata carries
title, date, currency, effort_unit `JH` and scope/exclusions in notes
(`00_Lisez-moi`). Required unique assumptions are `scenario_global`,
`taux_journalier`, `mois_par_an`; TJM/month count are finite non-negative
numbers. An unconfirmed TJM blocks complete monetary conversion. Add editable
`heures_par_jh` default 8. Preserve each `Economique`, `Standard`, `Resilient`
once. Task ranges satisfy finite non-negative
`jh_low <= jh_likely <= jh_high`; all other fields are strings except the
task-ID dependency list and nullable/empty/valid `scenario_override`.
Dependencies resolve without self-reference or cycles; every lot matches
`phasing.phase`. `nature = Build` is one-off; `nature = Run` is JH/month.

Verified provider cost rows in `cloud_costs` go to `05_Couts_cloud`: keep
quantity, unit price and monthly multiplier finite/non-negative, scenario
valid and currency equal to metadata. Capture SKU, region, billing unit,
capture date and official price source in notes/sources. Missing prices
remain `A chiffrer` assumptions, risks and decisions; omit unpriced cost
rows and disclose incomplete totals. `11_Synthese` is derived by formulas.
Never combine mutually exclusive architecture branches in one total; use
separate complete models or independently reconciled decision deltas.

Calendar allocations/capacity use phase notes and assumptions, with checked
arithmetic; the model has no dedicated calendar fields. Diagram nodes use
inventory IDs and edges use explicit endpoints/labels with source evidence,
not implied connections from decision rows. Load with `load_model`, generate
with `build_workbook`, recalculate with `recalculate`, then inspect returned
engine/status/cache counts/errors. Reopen formulas and values and call
`validate_workbook` with numeric prose assertions and final diagram IDs.
Disclose a calibrated fallback; it cannot prove a native-opening requirement.
