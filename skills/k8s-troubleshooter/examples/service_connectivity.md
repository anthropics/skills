# Example: Diagnosing Service Connectivity Issues

This example demonstrates how to diagnose and fix service connectivity problems.

## Scenario

An application cannot connect to a backend service within the cluster.

## Step 1: Identify the Problem

```bash
# Application logs show connection errors
$ kubectl logs frontend-pod-abc123 -n production
Error: Connection refused to http://backend-service:8080/api/health
```

## Step 2: Check Service Exists

```bash
$ kubectl get svc backend-service -n production
NAME              TYPE        CLUSTER-IP      EXTERNAL-IP   PORT(S)    AGE
backend-service   ClusterIP   10.96.45.123    <none>        8080/TCP   7d
```

## Step 3: Check Endpoints

```bash
$ kubectl get endpoints backend-service -n production
NAME              ENDPOINTS   AGE
backend-service   <none>      7d
```

**Problem identified**: Service has no endpoints!

## Step 4: Check Service Selector

```bash
$ kubectl get svc backend-service -n production -o yaml | grep -A5 selector
  selector:
    app: backend
    version: v2
```

## Step 5: Check Pod Labels

```bash
$ kubectl get pods -n production --show-labels | grep backend
backend-pod-xyz789   1/1   Running   0   1h   app=backend,version=v1
backend-pod-abc123   1/1   Running   0   1h   app=backend,version=v1
```

**Root cause**: Service selector expects `version: v2` but pods have `version: v1`.

## Step 6: Fix the Issue

Option A: Update the service selector:

```bash
$ kubectl patch svc backend-service -n production -p '{"spec":{"selector":{"app":"backend","version":"v1"}}}'
service/backend-service patched
```

Option B: Update the pod labels (via deployment):

```bash
$ kubectl patch deployment backend -n production -p '{"spec":{"template":{"metadata":{"labels":{"version":"v2"}}}}}'
deployment.apps/backend patched
```

## Step 7: Verify the Fix

```bash
$ kubectl get endpoints backend-service -n production
NAME              ENDPOINTS                           AGE
backend-service   10.244.1.5:8080,10.244.2.8:8080    7d

# Test connectivity from within cluster
$ kubectl run test --rm -it --image=busybox --restart=Never -- wget -qO- http://backend-service:8080/api/health
{"status": "healthy"}
pod "test" deleted
```

## Using the Diagnostic Script

```bash
$ python scripts/diagnose_service.py backend-service -n production

Diagnosing service: backend-service
Namespace: production
--------------------------------------------------

Service Type: ClusterIP
Selector: {'app': 'backend', 'version': 'v2'}
Port: 8080 -> 8080 (TCP)

Matching Pods: 0
Ready Pods: 0
Ready Endpoints: 0

Issues Found (2):
  1. Service has no endpoints (no ready pods matching selector)
  2. No pods found matching service selector

Recommendations (2):
  1. Check if pods with matching labels exist and are ready
  2. Verify pods have labels: {'app': 'backend', 'version': 'v2'}
```

## Common Service Connectivity Issues

1. **Selector mismatch** - Service selector doesn't match pod labels
2. **No ready pods** - Pods exist but aren't passing readiness probes
3. **Wrong port** - Service targetPort doesn't match container port
4. **Network policies** - NetworkPolicy blocking traffic
5. **DNS issues** - CoreDNS not resolving service names
6. **Namespace mismatch** - Service and pods in different namespaces

## DNS Troubleshooting

```bash
# Check CoreDNS is running
$ kubectl get pods -n kube-system -l k8s-app=kube-dns
NAME                       READY   STATUS    RESTARTS   AGE
coredns-5644d7b6d9-abcde   1/1     Running   0          30d
coredns-5644d7b6d9-fghij   1/1     Running   0          30d

# Test DNS resolution
$ kubectl run dnstest --rm -it --image=busybox --restart=Never -- nslookup backend-service.production.svc.cluster.local
Server:    10.96.0.10
Address 1: 10.96.0.10 kube-dns.kube-system.svc.cluster.local

Name:      backend-service.production.svc.cluster.local
Address 1: 10.96.45.123 backend-service.production.svc.cluster.local
```

## Network Policy Check

```bash
# List network policies
$ kubectl get networkpolicies -n production
NAME              POD-SELECTOR   AGE
deny-all          <none>         7d
allow-frontend    app=backend    7d

# Check if policy allows traffic
$ kubectl describe networkpolicy allow-frontend -n production
...
Spec:
  PodSelector:     app=backend
  Allowing ingress traffic:
    To Port: 8080/TCP
    From:
      PodSelector: app=frontend
...
```
