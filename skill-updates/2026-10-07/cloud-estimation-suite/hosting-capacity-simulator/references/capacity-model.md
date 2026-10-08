# Capacity inputs, calculations and uncertainty

Use for sizing a scoped workload/environment under one service scenario and
one workload band. Read [domain-contract.json](domain-contract.json) for the
machine-readable interface. The helper
[validate_capacity.py](../scripts/validate_capacity.py) checks this contract
with the standard library before calculation. It does not validate that a
chosen instance or topology meets the workload.

## Typed inputs and provenance

| Input | Canonical unit and type | Meaning |
| --- | --- | --- |
| cpu | vCPU, finite nonnegative number | Simultaneous consumed compute demand; convert measured millicores explicitly |
| memory | GiB, finite nonnegative number | Working-set demand including required caches; 1 GiB = 2^30 bytes |
| storage | GiB, finite nonnegative number | Required usable data capacity at the horizon, including explicit growth/retention |
| iops | operations/s, finite nonnegative number | Required operations rate with read/write mix, block size and latency stated |
| bandwidth | Mbit/s, finite nonnegative number | Sustained/burst transfer demand; 1 Mbit = 10^6 bits, eight bits per byte |
| concurrency | requests, nonnegative integer | Simultaneous in-flight requests/jobs, with service-time and queue definition |
| utilisation_target | ratio, finite number greater than 0 and at most 1 | Fraction of effective capacity allowed at the sizing target |
| scaling_limit | instances, positive integer | Maximum permitted comparable capacity units in this model, after quotas/budget constraints |
| failure_domain_reserve | instances, nonnegative integer below scaling_limit | Units simultaneously unavailable in the chosen failure event |

Every dimension is required; an evidenced absence may be explicit zero, but
an unknown is never zero. Keep uncertainty outside the numeric payload as
scoped assumption records: status, source, period, derivation, confidence and
workload band. Use key prefixes containing workload, environment, scenario and
band to prevent collisions. Persist nine numeric values in `assumptions`,
not as new top-level model fields. The finite-value/cross-field checks go
beyond the JSON-Schema-style numeric bounds.

CPU performance depends on the actual architecture/runtime; identical vCPU
counts do not establish equivalent throughput. Memory demand depends on
working set and concurrency. An IOPS number needs device/backend latency,
throughput and burst/credit context. Bandwidth needs ingress/egress direction,
protocol overhead, and shared link limits. Concurrency does not determine CPU
or memory without service-time and per-request behaviour evidence.

Use aligned workload windows when summing services. If peaks are not aligned,
state the aggregation assumption and test its sensitivity. Identify which
quantities were consumed measurements, configured limits, provider capacities
or inferred assumptions. Demand and per-unit capacity both need provenance.
Zero effective unit capacity for positive demand makes that option infeasible.

## Normal, failure and scaling calculations

Expose input references and formula/derivation in the workbook. Capacity
calculations must be inspectable and repeatable independently of the narrative.
Let D_d be demand in dimension d and C_d the effective capacity of one eligible
unit after system/sidecar/platform overhead. Let u_d be the utilisation target
for that dimension. Use the typed baseline target unless an explicit scoped
override is justified; avoid applying one CPU target blindly to durable storage.

For horizontally divisible dimensions, n_d = ceil(D_d / (C_d * u_d)).
The demand-driven normal count is max(n_d) across applicable dimensions,
subject to independent availability, quorum and placement minima. Concurrency
uses measured or explicitly assumed safe concurrency per unit. Record the
binding resource and its utilisation. Do not multiply by extra headroom if
the target already includes it: reserved headroom is 1 - u_d. Additional growth,
deployment surge and incident margin must have their own explicit rationale.

Treat shared databases, shared storage and nonpartitionable/stateful workloads
as separate capacities. Adding application replicas does not multiply a shared
backend's IOPS, storage or bandwidth. A dataset needing one larger volume cannot
be divided across smaller volumes without a justified partitioning design.
For replicated data, distinguish usable storage from replication/backup copies.
Check attach limits, throughput and zone-bound data placement separately.

For r interchangeable units lost, n_ready >= n_normal + r. Expose r and the
result explicitly; N+1 means r = 1 for one node loss. For a zone failure, verify
n_ready - nodes_in_largest_affected_zone >= n_normal, then check workload
eligibility, data access and quorum. Use actual placement, not an average zone
size, and model the unavailable count in the typed reserve. Other common
failure modes need their own row; a node reserve never proves region recovery.

Compare n_ready and burst demand against scaling_limit. An infeasible result
stays infeasible; do not clamp the calculation to the limit and call it safe.
Ready capacity must handle the stated recovery interval. Capacity that may
appear after scale-out depends on provisioning/startup lag, quota availability
and downstream saturation. Include a backlog/service-level estimate only when
its arrival-rate, service-time and queueing assumptions are stated; no benchmark
or statistical precision is inferred from these arithmetic bounds.

Worked synthetic illustration: demand of 12 vCPU with 4 effective vCPU per
unit and target 0.75 gives 4 normal units. If memory requires 5 units, the
binding count is 5; one-node loss requires 6 ready units. Placing those six
as 2/2/2 across zones leaves only 4 after a zone loss, so the topology fails
that target despite satisfying N+1. These are illustrative assumptions, not
measured performance or a default recommendation.

## Sensitivity and measurement tasks

Use sourced peaks when available; retain low/base/high uncertainty for uncertain
growth or transferability. Without measured demand or per-unit capacity, publish
three explicit bands and an owned measurement task before dependent approval.
The task identifies instrumentation or load harness, safe environment, realistic
request mix, acceptance window, saturation/latency thresholds and expected raw
evidence. Measurements must not mutate production without separate authority.

Test demand growth, per-unit throughput, working set, storage growth,
utilisation target, failure placement and scaling ceiling. Show which changes
alter the bottleneck, violate recovery targets or exceed the maximum. Low/base/high
bands are workload uncertainty, while `Economique`, `Standard` and `Resilient`
are service/cost/operating choices. Scope both dimensions visibly; keep the
common Scenario names unchanged and represent bands as assumption/result rows.
Capacity refinement must not quietly change the service perimeter.

## Emit the shared model and workbook

Sizing inputs and capacity results map to `assumptions` with numeric values,
canonical units, status, source and notes containing input IDs, derivation,
band and topology. Emit inventory units/counts and `architecture` decisions
using stable linked IDs. Measurement and capacity-validation tasks use common
Task fields and Build JH; recurring capacity review uses Run JH/month. Include
dependency IDs, acceptance criterion, expected evidence and low/likely/high JH.
Unknown measurements become risks and measurement prerequisites, not invented
numeric cells. Sourced pricing is separate from capacity and retrieved at runtime.

Keep effective capacities, headroom, minima, reserve and scaling ceilings as
editable cells, with result formulas tied to those cells wherever the local
builder supports them. The shared builder/validator guarantees only its declared
formula contract: if capacity formulas are not supported, use a dedicated
calculation pass, retain the derivation and recompute after edits before claiming
current results. Never label a frozen derived value dynamically calculated.
Check these domain calculations independently against emitted workbook inputs
and results; common aggregate validation alone does not prove the sizing math.

Preserve all twelve workbook sheets, selected scenario, source dates and
formula-driven shared totals. Explain irrelevant sections as `Non applicable`.
Recalculate and reopen the file, then reconcile JH, scenarios, quantities,
diagram inventory and every numerical statement before delivering.
