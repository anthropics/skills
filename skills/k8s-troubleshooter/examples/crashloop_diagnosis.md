# Example: Diagnosing CrashLoopBackOff

This example demonstrates how to diagnose and fix a pod stuck in CrashLoopBackOff.

## Scenario

A deployment's pods keep restarting with CrashLoopBackOff status.

## Step 1: Identify the Problem

```bash
$ kubectl get pods -n production
NAME                        READY   STATUS             RESTARTS   AGE
my-app-7d4b8c9f5-abc12      0/1     CrashLoopBackOff   5          10m
my-app-7d4b8c9f5-def34      0/1     CrashLoopBackOff   5          10m
```

## Step 2: Check Pod Events

```bash
$ kubectl describe pod my-app-7d4b8c9f5-abc12 -n production
...
Events:
  Type     Reason     Age                From               Message
  ----     ------     ----               ----               -------
  Normal   Scheduled  10m                default-scheduler  Successfully assigned production/my-app-7d4b8c9f5-abc12 to node-1
  Normal   Pulled     9m (x5 over 10m)   kubelet            Container image "myregistry/my-app:v2.0" already present on machine
  Normal   Created    9m (x5 over 10m)   kubelet            Created container my-app
  Normal   Started    9m (x5 over 10m)   kubelet            Started container my-app
  Warning  BackOff    4m (x20 over 9m)   kubelet            Back-off restarting failed container
```

## Step 3: Check Container Logs

```bash
# Current logs (might be empty if container crashes immediately)
$ kubectl logs my-app-7d4b8c9f5-abc12 -n production

# Previous container logs (shows what happened before crash)
$ kubectl logs my-app-7d4b8c9f5-abc12 -n production --previous
Error: DATABASE_URL environment variable not set
Traceback (most recent call last):
  File "/app/main.py", line 15, in <module>
    db_url = os.environ["DATABASE_URL"]
KeyError: 'DATABASE_URL'
```

## Step 4: Root Cause Identified

The application requires a `DATABASE_URL` environment variable that is not set.

## Step 5: Fix the Issue

Check if the ConfigMap or Secret exists:

```bash
$ kubectl get configmap app-config -n production
Error from server (NotFound): configmaps "app-config" not found

$ kubectl get secret app-secrets -n production
NAME          TYPE     DATA   AGE
app-secrets   Opaque   2      30d
```

The ConfigMap is missing. Create it:

```bash
$ kubectl create configmap app-config -n production \
  --from-literal=DATABASE_URL="postgresql://user:pass@db-host:5432/mydb"
configmap/app-config created
```

Or update the deployment to use the existing secret:

```yaml
# deployment.yaml
spec:
  containers:
  - name: my-app
    env:
    - name: DATABASE_URL
      valueFrom:
        secretKeyRef:
          name: app-secrets
          key: database-url
```

## Step 6: Verify the Fix

```bash
$ kubectl rollout restart deployment/my-app -n production
deployment.apps/my-app restarted

$ kubectl get pods -n production -w
NAME                        READY   STATUS    RESTARTS   AGE
my-app-8e5c9d0f6-ghi56      1/1     Running   0          30s
my-app-8e5c9d0f6-jkl78      1/1     Running   0          25s
```

## Using the Diagnostic Script

You can also use the provided diagnostic script:

```bash
$ python scripts/diagnose_pod.py my-app-7d4b8c9f5-abc12 -n production

Diagnosing pod: my-app-7d4b8c9f5-abc12
Namespace: production
--------------------------------------------------

Pod Phase: Running

Issues Found (2):
  1. Container 'my-app' is in CrashLoopBackOff
  2. Container 'my-app' has restarted 5 times

Recommendations (2):
  1. Check container logs with --previous flag
  2. Verify application configuration and dependencies

--------------------------------------------------
Recent Logs:
Attempting to get previous container logs...
Error: DATABASE_URL environment variable not set
...
```

## Common CrashLoopBackOff Causes

1. **Missing environment variables** - Application requires env vars not provided
2. **Missing ConfigMaps/Secrets** - Referenced configs don't exist
3. **Application bugs** - Code crashes on startup
4. **Permission issues** - Container can't access required resources
5. **Resource constraints** - OOMKilled due to memory limits
6. **Dependency unavailable** - Database or service not reachable
7. **Invalid command/entrypoint** - Container command fails
