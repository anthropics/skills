# Cluster assessment and estimation

Use this reference after the suitability decision, or for an existing cluster.
The rows prompt coverage; they do not mandate every platform feature. Scope
the provider/distribution and supported release before drafting executable
configuration. Verify mutable support, quota and API details against official
documentation at execution time. This methodology contains no fixed release
or price assumptions.

## Trace the decision into topology

Compare managed and self-managed control planes on responsibility, availability,
upgrade ownership and Build/Run JH. Record environments, cluster isolation,
regional boundaries, failure domains and operational access. A multi-zone
control plane does not prove workload or data availability across zones.
Show only evidenced network and dependency flows using inventory IDs.

| Area | Inputs and architectural choice | Acceptance evidence and effort drivers |
| --- | --- | --- |
| Node pools | Allocatable CPU/memory, system overhead, workload classes, quotas, min/max nodes, zones, labels/taints and placement constraints | Per-pool requests fit; scheduling and failure-placement tests; IaC and capacity-review JH |
| Requests and limits | Simultaneous peaks, per-pod requests, CPU throttling tolerance, memory working set, sidecars and DaemonSets | Scheduling uses requests; observed throttling/OOM and load test support limits; workload tuning JH |
| Autoscaling | Pod and node bounds, scaling signals, startup time, saturation thresholds, queue backlog and provision latency | Sustained and burst tests include scale-out delay; quotas/ceiling failure becomes a risk; configuration and tuning JH |
| Ingress and traffic | Public/private entry, TLS ownership, routing, health checks, external LB and egress dependencies | Probe and failover evidence; certificate rotation/ingress maintenance JH; mesh requires a separate decision |
| Storage | Access modes, attach limits, zone binding, durability, throughput/IOPS and restore semantics | Stateful placement, attach and restore tests; backend limits considered independently of nodes; engineering JH |
| Secrets and identity | Workload identity, secret store, rotation, RBAC and operator access | Access/rotation tests and responsibility matrix; never include secret values in estimates; maintenance JH |
| Policy | Network isolation, admission/pod security, image provenance and exceptions | Positive/negative enforcement tests and owned exceptions; policy engineering/review JH |
| Upgrades | Control-plane, node and add-on compatibility, release cadence, drain capacity, disruption budgets and rollback limits | Staging upgrade/recovery evidence and version-specific support sources; initial procedure and recurring upgrade JH |
| Observability | SLOs, metrics/logs/traces, retention, alert ownership, cardinality and platform overhead | Alert delivery and actionable runbooks; ingestion quantities and recurring triage/tuning JH |
| Backup and recovery | Cluster configuration, application state, volume/database backup, retention and external dependencies | Recovery order, independent backup failure domain, restore integrity and measured RPO/RTO; recurring restore-test JH |
| Multi-zone and DR | Workload spread, largest-zone loss, quorum/data placement, cross-region replication and traffic switch | Test surviving resources and data accessibility; DR is not inferred from availability zones; exercise/build JH |
| Platform engineering | IaC, bootstrap, templates, platform documentation, support model and handover | Reproducible deployment and operator acceptance; own shared CI/CD, hardening or migration interfaces once |

Record excluded areas with a rationale and `Non applicable`, rather than
adding unused technology. Separate the time needed to develop a platform
capability from the effort needed each month to operate it. Monthly Run JH
reflect cadence times effort, incident assumptions, staffed responsibility
and automation evidence; annual or quarterly activities are amortised with
their cadence visible. Calendar availability and on-call coverage are separate
from summed effort.

## Capacity and failure calculations

Node advertised capacity is reduced by OS/kubelet reservations, DaemonSets,
observability and other platform consumption before scheduling application
requests. Resource requests size scheduling; limits are not a capacity promise.
Check each indivisible pod fits a eligible node, then enforce affinity,
anti-affinity, taints, volumes and zone constraints. Aggregated CPU/memory
division is a lower bound until placement succeeds.

Expose per-pool normal node demand, min/max nodes, target utilisation and the
resource bottleneck. For loss of one interchangeable node, N+1 means sufficient
surviving allocatable capacity with one node unavailable. For a zone outage,
subtract all nodes in the largest affected zone and recheck every workload's
eligible pools, pod/data placement and quorum. A single spare node does not
represent loss of a whole zone. State whether the survivor count is ready at
failure or relies on provisioning; scaling delay must meet recovery targets.
Upgrade surge/drain capacity and outage reserve use a declared concurrent-event
assumption; avoid silently double counting or assuming they can never coincide.

The capacity simulator can supply measured quantities and sensitivity records;
this skill owns Kubernetes scheduling constraints and platform overhead. Share
their IDs and sources rather than estimating the same measurement task twice.

## Common-model interface

Read [domain-contract.json](domain-contract.json) for field names and workbook
destinations. Emit node pools as `inventory` capacity units linked through
notes to their topology and sizing assumptions; emit topology as `architecture`
rows and suitability/mesh/recovery choices as `decisions`. Store pool bounds,
allocatable resources, pod counts, requests/limits, zone counts and reserve
calculations as scoped `assumptions`, with units and calculation/source evidence.

Platform tasks use `nature=Build`; recurring operations use `nature=Run` and
JH/month, keeping the cadence in notes. Both use the shared Task fields,
including low/likely/high JH, dependency IDs, acceptance criterion and expected
evidence. Link each lot to a phase and reconcile net additional effort against
evidenced prior coverage. Risks and sources retain their common-model records.

Unknown prices are assumptions/decisions, not numeric CloudCost rows. Verify
any sourced cloud prices separately at runtime. Complete shared workbooks use
all twelve sheets; do not invent new top-level EstimateModel fields. If a
contract choice cannot represent distinct mutually exclusive topologies safely,
emit separate complete models/workbooks and record the comparison decision.
