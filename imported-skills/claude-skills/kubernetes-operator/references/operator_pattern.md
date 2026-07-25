# The operator pattern

An operator is a controller that reconciles a Custom Resource (CR) toward its declared spec. It encodes operational knowledge — installation, upgrades, backups, failover — that would otherwise live in tribal knowledge or runbooks.

## When you need an operator

Build an operator when:
- The application has nontrivial **lifecycle operations** (backup, restore, version upgrade, failover) that go beyond a simple Deployment
- The application has **statefulness or topology** that Helm/Deployment can't express (leader election, peer discovery, rolling state migration)
- Multiple teams need to provision instances of the application via **a Kubernetes API**, not a custom UI
- The application's operational discipline is documented in runbooks but unevenly applied

Don't build an operator when:
- A **Helm chart** is enough (most stateless apps fit here)
- A **CronJob** can run the operational task on a schedule
- The custom logic is a **one-time migration** (use a Job)
- Three engineers can manage it via Deployment + ConfigMap

## Operator pattern shape

```
┌────────────────────────────────────────────────────────┐
│  apiVersion: apps.example.com/v1alpha1                 │
│  kind: MyApp                       ← Custom Resource   │
│  spec:                                                 │
│    replicas: 3                     ← user's intent     │
│    version: 1.4.2                                      │
│  status:                                               │
│    conditions:                     ← controller's view │
│      - type: Ready                                     │
│        status: "True"                                  │
│    phase: Running                                      │
└────────────────────────────────────────────────────────┘
                       ↑
                       │ owns
                       │
┌────────────────────────────────────────────────────────┐
│  controller.Reconcile(ctx, req) ⟶ ctrl.Result, error   │
│   1. read CR (the spec) from the cache                 │
│   2. read actual state (Pods, Services, ConfigMaps)    │
│   3. diff actual against desired                       │
│   4. act idempotently to converge                      │
│   5. update status with observed state                 │
│   6. return RequeueAfter or done                       │
└────────────────────────────────────────────────────────┘
```

Reconcile runs whenever:
- The CR changes
- A child resource changes
- A periodic resync fires (default 10h, configurable)
- An explicit requeue from a previous run

## Spec vs status — the cardinal split

| spec | status |
|---|---|
| Authored by the user | Authored by the controller |
| Mutable through `kubectl edit` | Mutable only via the status subresource |
| Captures *intent* | Captures *observed reality* |
| Triggers reconcile | Does NOT trigger reconcile (when subresource is enabled) |

Violating the split is the #1 cause of operator bugs:
- Mutating spec from the controller → user changes get overwritten
- Updating status without the subresource → status update triggers spec reconcile → loop

## Reconcile must be idempotent

Reconcile is called repeatedly for the same state. The function must:

- Produce the same outcome regardless of call count
- Use `Create-or-Update` patterns (`controllerutil.CreateOrUpdate`)
- Compare current state to desired before writing
- Never assume "this is the first time we've seen this resource"

Idempotence test: if reconcile is called 100 times in a row with the same spec and no external change, the system must converge after the first call and do nothing on the next 99.

## OwnerReferences and cascading deletion

Every child resource the operator creates must have its `OwnerReferences` set to the parent CR. Then:
- Deleting the CR deletes children automatically
- The garbage collector handles orphan cleanup
- The operator doesn't need explicit teardown logic for owned resources

External resources (cloud DBs, S3 buckets, DNS records) don't have OwnerReferences. Use **finalizers** to clean them up.

## Finalizers

A finalizer blocks deletion until the controller has cleaned up external state.

```
1. User: kubectl delete myapp foo
2. API server: sets metadata.deletionTimestamp; does NOT delete
3. Controller: sees deletionTimestamp; does cleanup; removes finalizer
4. API server: deletion now proceeds
```

Without a finalizer, external resources orphan. With one, the controller has a guaranteed hook to run cleanup before the CR disappears.

## Conditions

The standard pattern for status reporting:

```yaml
status:
  conditions:
    - type: Ready          # type values are operator-defined
      status: "True"        # True | False | Unknown
      reason: "AllReady"    # PascalCase, programmatic
      message: "All replicas ready"  # human-readable
      lastTransitionTime: "2026-05-08T12:00:00Z"
    - type: Reconciling
      status: "False"
      reason: "Idle"
      lastTransitionTime: "2026-05-08T12:00:00Z"
```

Use `meta/v1.Conditions` and `meta/v1.SetStatusCondition` from kubebuilder/controller-runtime — don't roll your own.

## Webhooks

Two types:

- **ValidatingWebhook** — reject invalid CRs at admission (better than failing in reconcile)
- **MutatingWebhook** — fill in defaults / inject sidecars (use sparingly; surprising side effects)

Run webhooks in the same controller binary or a sidecar; cert-manager rotates the certs.

## Anti-patterns

- **Imperative reconcile**: "if event = create, do X; if event = update, do Y". Wrong shape. Reconcile = make actual=desired regardless of how we got here.
- **No status subresource**: status updates re-trigger reconcile.
- **Status mutation in many places**: centralize in a `setStatus` helper.
- **Reconcile depending on event order**: events can be missed; reconcile must converge from any starting state.
- **Long reconcile (>2 min)**: blocks the work queue; split work via RequeueAfter.

## Decision flow: when an operator is the right answer

```
Need: I want to manage <X> in Kubernetes.

Is <X> a stateless web app?           → Deployment + Service. Done.
Is <X> a stateless web app with config?  → Deployment + ConfigMap.
Need version upgrade automation?       → Helm. Done.
Need stateful behaviour (leader, peers)? → StatefulSet.
Need application-aware operations
  (backup, version migration, repair)?  → Operator.
Need to expose <X> as a k8s resource
  to other teams?                       → Operator.
```

When in doubt: start with Helm. Move to an operator only when Helm can't express the operational logic.
