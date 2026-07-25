# The reconcile loop

Reconcile is the heart of an operator. Most operator bugs are reconcile-loop bugs. The patterns below are deterministic — copy them.

## Skeleton — `Reconcile(ctx, req)`

```go
func (r *MyAppReconciler) Reconcile(ctx context.Context, req ctrl.Request) (ctrl.Result, error) {
    log := log.FromContext(ctx)

    // 1. Fetch the CR
    var cr appsv1alpha1.MyApp
    if err := r.Get(ctx, req.NamespacedName, &cr); err != nil {
        if apierrors.IsNotFound(err) {
            return ctrl.Result{}, nil  // CR is gone; nothing to do
        }
        return ctrl.Result{}, err  // transient error → requeue
    }

    // 2. Handle deletion via finalizer
    if !cr.DeletionTimestamp.IsZero() {
        return r.reconcileDelete(ctx, &cr)
    }
    if !controllerutil.ContainsFinalizer(&cr, finalizerName) {
        controllerutil.AddFinalizer(&cr, finalizerName)
        return ctrl.Result{}, r.Update(ctx, &cr)
    }

    // 3. Mark Reconciling
    meta.SetStatusCondition(&cr.Status.Conditions, metav1.Condition{
        Type: "Reconciling", Status: metav1.ConditionTrue,
        Reason: "InProgress", Message: "Converging to desired state",
        ObservedGeneration: cr.Generation,
    })

    // 4. Do the work, idempotently
    res, err := r.reconcileNormal(ctx, &cr)

    // 5. Update status (always — even on error)
    if statusErr := r.Status().Update(ctx, &cr); statusErr != nil {
        log.Error(statusErr, "failed to update status")
        return res, errors.Join(err, statusErr)
    }

    return res, err
}
```

## The 5-step shape

1. **Fetch the CR.** Handle `NotFound` cleanly — the CR may have been deleted between event and reconcile.
2. **Handle deletion.** If `DeletionTimestamp` is set, run cleanup, remove finalizer, return.
3. **Set Reconciling condition.** Mark that the controller is working.
4. **Do work idempotently.** Use `CreateOrUpdate`, compare desired-vs-actual, only act on differences.
5. **Update status.** Even on error — partial progress is signal.

## Idempotence patterns

### Pattern: CreateOrUpdate

```go
deployment := &appsv1.Deployment{ObjectMeta: metav1.ObjectMeta{Name: cr.Name, Namespace: cr.Namespace}}
op, err := controllerutil.CreateOrUpdate(ctx, r.Client, deployment, func() error {
    deployment.Spec.Replicas = &cr.Spec.Replicas
    deployment.Spec.Template.Spec.Containers = buildContainers(&cr.Spec)
    return controllerutil.SetControllerReference(&cr, deployment, r.Scheme)
})
if err != nil { return ctrl.Result{}, err }
log.Info("deployment", "operation", op)  // "created", "updated", or "unchanged"
```

This pattern is idempotent by construction.

### Pattern: SetControllerReference

Always set the OwnerReference so cascading deletion works:

```go
controllerutil.SetControllerReference(&cr, child, r.Scheme)
```

### Pattern: Finalizer for external resources

```go
const finalizerName = "myapp.apps.example.com/finalizer"

func (r *MyAppReconciler) reconcileDelete(ctx context.Context, cr *appsv1alpha1.MyApp) (ctrl.Result, error) {
    if !controllerutil.ContainsFinalizer(cr, finalizerName) {
        return ctrl.Result{}, nil
    }
    if err := r.deleteExternalResources(ctx, cr); err != nil {
        return ctrl.Result{RequeueAfter: 30 * time.Second}, err
    }
    controllerutil.RemoveFinalizer(cr, finalizerName)
    return ctrl.Result{}, r.Update(ctx, cr)
}
```

## Error handling and requeue

| Situation | Return |
|---|---|
| Permanent error (bad spec) | `ctrl.Result{}, nil` + condition with reason |
| Transient error (API timeout, throttling) | `ctrl.Result{}, err` (auto-requeue with backoff) |
| Need a retry in N seconds | `ctrl.Result{RequeueAfter: 30*time.Second}, nil` |
| Done; no follow-up | `ctrl.Result{}, nil` |

**Don't use `time.Sleep` inside reconcile.** It blocks the work queue, starving other reconciles. Use `RequeueAfter`.

## Status update patterns

```go
// Set a condition
meta.SetStatusCondition(&cr.Status.Conditions, metav1.Condition{
    Type: "Ready", Status: metav1.ConditionTrue,
    Reason: "AllReady", Message: "all components healthy",
    ObservedGeneration: cr.Generation,
})

// Track observed generation
cr.Status.ObservedGeneration = cr.Generation

// Update status — uses /status subresource
if err := r.Status().Update(ctx, &cr); err != nil { ... }
```

**Never** call `r.Update(ctx, &cr)` to update status. It uses the spec subresource, which the user owns.

## Read once, decide, act

Don't observe the world repeatedly during reconcile. The cache is read-only and consistent within a single reconcile pass:

```go
// Good: read once, decide, act
var pods corev1.PodList
r.List(ctx, &pods, client.InNamespace(cr.Namespace), client.MatchingLabels{"app": cr.Name})
desired := computeDesired(&cr, &pods)
applyDesired(ctx, r.Client, desired)

// Bad: observe-act-observe-act
for _, container := range cr.Spec.Containers {
    pod := r.Get(...)               // re-reading the cache
    if needsRestart(pod) {
        r.Delete(...)
        pod = r.Get(...)             // again
        ...
    }
}
```

## Predicates — filter events you don't care about

```go
func (r *MyAppReconciler) SetupWithManager(mgr ctrl.Manager) error {
    return ctrl.NewControllerManagedBy(mgr).
        For(&appsv1alpha1.MyApp{}).
        Owns(&appsv1.Deployment{}).
        WithEventFilter(predicate.GenerationChangedPredicate{}).  // ignore status-only updates
        Complete(r)
}
```

`GenerationChangedPredicate` skips reconciles when only status changed — important to avoid loops.

## Leader election

Always enable leader election when running >1 controller replica:

```go
mgr, _ := manager.New(cfg, manager.Options{
    LeaderElection:   true,
    LeaderElectionID: "myapp-operator-leader",
})
```

Without it: split-brain. Two controllers both think they own the resource and fight.

## Performance — bounded reconcile time

A reconcile pass should complete in <30s for typical work, <2min for heavy work. Longer = the work queue starves other reconciles.

If work takes longer:
- Break into phases; emit `RequeueAfter` between them
- Move long-running work to a separate process (Job)
- Cache expensive computations on `cr.Status`

## Logging conventions

```go
log := log.FromContext(ctx).WithValues("phase", "create-deployment")
log.Info("creating deployment", "name", cr.Name)
log.Error(err, "failed to create deployment")
```

- Use `log.FromContext(ctx)` — picks up controller-runtime's contextual logger
- Use `Info` for normal flow, `Error` for retryable failures
- Add structured fields, not formatted strings

## Anti-patterns checklist

- `time.Sleep` inside reconcile → starves queue; use `RequeueAfter`
- `os.Exit` / `log.Fatal` → kills the controller; return an error
- `panic` → same; return an error
- `r.Update` to set status → use `r.Status().Update`
- `r.Update` of the CR while the user could be editing it → use `r.Status().Update` or use Patch
- Reading the same resource multiple times in one reconcile → read once
- Reconcile body > 80 lines → extract `reconcileXxx` subroutines per phase
- HTTP calls without `ctx` → can't cancel during shutdown
- No requeue path for transient errors → silent failures
- Missing `OwnerReferences` on children → cascading deletion broken
