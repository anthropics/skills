# Migration method and lifecycle

Use [domain-contract.json](domain-contract.json) for record bindings.
The common model has no typed migration wave: link inventory, assumptions,
decisions, architecture and tasks by stable IDs in notes. Store evidence
references in inventory notes, with capture date, collection scope and
state; store the original read-only snapshot as a protected source artifact.
Keep private evidence out of public example bundles.

## Select a feasible method

Before choosing tooling, resolve source-write policy and application
consistency requirements. A source read can still require existing
privileges or impose load: record the allowed observation window and
identity, and avoid exposing secrets in the inventory export.

| Candidate method | Source dependency to check | Estimate consequence |
|---|---|---|
| Continuous database replication | Parameter changes, logs, privileged credentials, slots or agent installation | Price approved setup, change capture, lag monitoring and cleanup; otherwise reject the method |
| Snapshot or logical export | Existing export rights, compatible restore tooling, consistent checkpoint | Price export/restore and reconciliation; include owner-operated write freeze if required and allowed |
| Managed object transfer | Existing read credentials, new credential creation, ACL or agent changes | Use existing authorised access or price an owner handoff; do not invent public access |
| Network or DNS cutover | Zone/registrar ownership, certificate readiness, cache/TTL, firewall authority | Price the allowed control point and propagation checks; do not assume source DNS is writable |
| Source retirement | Delete authority, retention, legal hold and recovery window | If source writes are forbidden, deliver a retirement dossier to its owner and show the external dependency |

When every viable consistency method needs an unavailable source write,
record a blocking decision with alternatives and their effort/outage impact.
A read-only source does not imply a usable write freeze, CDC, newly created
credentials or unrestricted exports. An owner's action needs an identified
owner and agreement; it is not a workaround that magically grants rights.

Synthetic example: a database source forbids parameter changes but its
operator permits a bounded maintenance freeze and existing export access.
Choose consistent export/restore rather than assume replication. Price the
operator's freeze dependency and target validation. If no freeze is allowed
either, retain consistency as an unresolved decision instead of promising
zero data loss.

## Cover each wave

The following phases are coverage categories, not an instruction to execute
all actions. Preserve conditional rollback and excluded phases in the
register; do not schedule the rollback branch as a successful-cutover
dependency. Record wave/phase and source-write requirements in task notes.

| Phase | Deliverable and acceptance evidence |
|---|---|
| Preparation | Evidence-backed inventory and drift, compatible target, tested identities, backup/restore readiness and approved intervention boundary |
| Rehearsal | Representative restore/transfer report, measured duration/lag, functional tests and a timed rollback exercise |
| Data transfer | Versioned checkpoint, volume/count reconciliation, retriable copy plan, measured throughput and encrypted transfer evidence |
| Cutover | Named go/no-go authority, outage budget, ordered dependency runbook, DNS/network checks and application acceptance at target |
| Integrity | Predefined counts, checksums or domain invariants appropriate to data, authenticated read/write smoke tests, delta and exception register |
| Rollback | Trigger thresholds, decision deadline, executable return path, recovery evidence and handling of writes accepted on the target |
| Decommissioning | Accepted recovery window, retention/hold decision, owner-authorised retirement evidence or owner handoff dossier |
| Hypercare | Bounded support window, incident/rollback watch, performance checks, operator knowledge transfer and signed exit criteria |

Treat rollback feasibility as a design input before rehearsal. Define the
last reversible point; switching DNS back is insufficient when the target
has accepted new writes. Price reverse replication, replay/reconciliation
or explicit loss acceptance where feasible and authorised. Do not promise
rollback after destruction or incompatible data transformation.

Use measured data size and effective throughput to estimate elapsed time,
then add measured consistency/delta, restore, validation and propagation
durations. Transfer runtime is not staff JH. Quantify human attendance,
automation, parallel waves and waiting separately. Assign overlap/dual-run
duration as an editable assumption; show transient costs alongside ongoing
target costs rather than mislabelling them as permanent OPEX.

Reconcile the phase matrix against the task register and the task register
against the JH synthesis independently. Reconcile source-target IDs and
transfer paths against the topology, then check the policy against each
source mutation, including rollback and retirement. Record coverage counts
and unresolved owners explicitly; a zero-issue result needs a positive
marker, not an empty listing.
