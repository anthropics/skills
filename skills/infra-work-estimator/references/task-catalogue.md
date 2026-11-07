# Infrastructure task catalogue and output mapping

Read for requested infrastructure work only. Use component IDs consistently
in inventory, architecture, tasks, evidence and diagrams. Do not add a task
merely because it appears below or because a product can provide the feature.

## Coverage prompts

| Work area | Deliverable and acceptance evidence | Principal effort drivers |
|---|---|---|
| Landing zone, accounts/projects | Environment and ownership boundaries, access/budget policies, validated bootstrap | Existing organisation, environments, policy exceptions and approvals |
| Networks | Addressing, routing, segmentation and connectivity with permitted/denied path checks | Links, routes, failure domains, legacy constraints, access dependencies |
| DNS and certificates | Owned zones, resolution and certificate lifecycle, tested renewal | Delegation, domains as anonymised quantities, exposure and rotation responsibility |
| Compute | Reproducible instances or managed runtime, health and restart evidence | Images, environment variations, scaling requirements and existing coverage |
| Storage | Provisioned volumes/object storage with access and lifecycle validation | Growth, durability, retention, encryption and performance evidence |
| Databases | Service configuration, access and connectivity with backup/restore evidence | Engine compatibility, replicas, recovery objectives and operating responsibility |
| Cache | Configured cache and demonstrated eviction/failure behaviour | Working set, persistence, topology and failure tolerance |
| Messaging | Queues/topics and demonstrated delivery, retry and dead-letter behaviour | Throughput, ordering, retention, consumers and failure semantics |
| Observability | Signals, dashboards, alerts and routing with triggered alert evidence | Services, retention, cardinality, integrations and operator ownership |
| Backup and recovery | Policies, isolated recovery rehearsal and measured recovery evidence | Data volume, recovery dependencies, RPO/RTO and rehearsal scope |
| Infrastructure as code | Versioned reproducible environment and drift/state-management checks | Existing modules, state boundaries, reuse and promotion ownership |
| Environments and documentation | Configured environment differences, runbooks and operating handover | Environment count, access, operators, service dependencies and evidence gaps |

Do not ship universal JH values. Explain low/likely/high drivers for each
deliverable. A repeatable automated task may have a setup effort plus an
incremental effort per environment; disclose both and avoid multiplying a
shared setup across every environment. Include verification, review and
handover when they are needed to meet the acceptance criterion.

## Ownership and coverage

Infrastructure provisioning of a database is distinct from schema changes
or data migration. Runtime provisioning is distinct from application
containerisation or feature development. Registry provisioning may be
infrastructure work, while pipeline gates and promotion belong to delivery.
Network access policy can overlap with hardening; backup tests can overlap
with migration or recovery. Name one owner and refer to its task ID from
other domains rather than billing the same result twice.

Keep inventory states and their dated source in `inventory.notes`. For a
partially deployed component, distinguish proven deployed coverage from
remaining acceptance work. Record gross JH, covered JH, proof and net JH in
`tasks.notes` and `coverage`; numeric ranges represent the net. Excluded
work remains a stated exclusion with its owner and interface. A zero net
task is valid only when evidence proves full coverage, not to conceal an
unknown estimate.

For incompatible requirements, keep each branch in its own complete model or
retain only selected work in the final model and independently checked deltas
in decision notes. The current schema has no architecture-branch selector;
never sum mutually exclusive tasks or cost rows into one scenario total.

When production access is missing, specify the read-only collection method,
required permission, measurements and expected evidence. Emit a measurement
task and make dependent sizing/provisioning work depend on it. Do not execute
mutations merely to measure. Unknown inputs belong in assumptions and risks.

## Model and XLSX mapping

[domain-contract.json](domain-contract.json) lists the
required keys for emitted record types. Read the locally supplied common
model and workbook contract when constructing the full JSON. All eleven
`EstimateModel` sections must exist, including empty arrays; `metadata` is
an object with `title`, `date`, `currency`, `effort_unit` and `notes`.

| Finding or workflow output | Model section | Workbook destination |
|---|---|---|
| Service perimeter, exclusions, incomplete totals | `metadata.notes` | `00_Lisez-moi` |
| Measurements, provisional inputs, capacity and non-cloud OPEX | `assumptions` | `01_Hypotheses` |
| Live/partial/planned/unknown components and quantities | `inventory` | `02_Inventaire` |
| Topology choices and service mappings | `architecture` | `03_Architecture` |
| Provisioning, measurement, tests, handover and operating work | `tasks` | `04_Taches_JH` |
| Verified bill-of-materials prices and usage | `cloud_costs` | `05_Couts_cloud` |
| Equal-scope variants and accepted recovery tradeoffs | `scenarios` | `06_Scenarios` |
| Lots, dependencies, period allocations and milestones | `phasing` | `07_Phasage` |
| Missing evidence, constraints and residual exposure | `risks` | `08_Risques` |
| Contradictory inputs, exclusions needing agreement and option deltas | `decisions` | `09_Arbitrages` |
| Dated measurement, estimate and official price evidence | `sources` | `10_Sources` |
| Reconciled totals, capacity and recommendation | Derived formulas | `11_Synthese` |

Use `metadata.effort_unit = JH`. Required assumptions are unique keys
`scenario_global`, `taux_journalier`, `mois_par_an`; the last two are finite
non-negative numbers. Add editable `heures_par_jh` with default 8. A missing
TJM is an explicit unconfirmed input and blocks complete monetary conversion.
Preserve each of `Economique`, `Standard`, `Resilient` exactly once.

All task fields other than numeric JH, `dependencies` and `scenario_override`
are strings. Dependencies are task-ID arrays without self-reference, unknown
IDs or cycles after merge. Use finite non-negative
`jh_low <= jh_likely <= jh_high`; `scenario_override` is null, empty or a valid
scenario. `nature` is `Build` (one-off) or `Run` (JH/month). Each `lot` needs a
matching `phasing.phase`. Record allocations, period capacity and overload
calculations in phase notes and assumptions; the schema has no typed calendar
allocation field. Validate those calculations independently.

Verified `cloud_costs` use finite non-negative quantities, unit prices and
monthly multipliers, with one metadata currency and a valid scenario.
Identify SKU, region, billing interval, verification status and price capture
date in notes/source records. A multiplier converts metered units to monthly
usage, not growth. Missing prices stay in inventory plus an `A chiffrer`
assumption, risk and decision; omit the unpriced numeric cost row and mark
affected totals incomplete. A required missing price blocks final delivery.

Topology rendering uses a separate node/edge input, not architecture decision
rows. Nodes carry inventory IDs; edges carry stable IDs and explicit source,
target and label. Record evidence for every flow in assumptions/sources;
unknown flows are flagged before drawing. The locally supplied renderer can
draw neutral nodes without inferred connections. Inspect its final render.

Load the complete JSON with `load_model`, then generate the workbook with
`build_workbook`, providing the evidenced diagram input. Use `recalculate`
and inspect its returned engine, `ok`, cache counts and errors. Reopen formulas
and cached values. Pass numeric prose assertions and final diagram inventory
IDs to `validate_workbook` and inspect its errors, counts and grouped totals.
Use a native spreadsheet engine when available; disclose a calibrated fallback
and do not claim a required native-opening check from fallback results.
Keep every sheet, explaining irrelevant sections as `Non applicable`.
