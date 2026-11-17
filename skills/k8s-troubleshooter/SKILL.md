---
name: k8s-troubleshooter
description: Systematic Kubernetes troubleshooting skill for diagnosing pod failures, service connectivity issues, resource problems, and cluster health. Provides decision trees, diagnostic scripts, and workflows for common K8s issues including CrashLoopBackOff, OOMKilled, ImagePullBackOff, pending pods, and networking problems.
license: Complete terms in LICENSE.txt
---

# Kubernetes Troubleshooting

This skill provides systematic approaches to diagnose and resolve common Kubernetes issues. Use the decision trees below based on the symptom you're investigating, or run the diagnostic scripts for automated analysis.

## Diagnostic Scripts

This skill includes helper scripts for automated diagnosis:

| Script | Purpose | Usage |
|--------|---------|-------|
| `diagnose_pod.py` | Diagnose pod issues (CrashLoopBackOff, OOMKilled, etc.) | `python scripts/diagnose_pod.py <pod-name> [-n namespace]` |
| `diagnose_service.py` | Diagnose service connectivity problems | `python scripts/diagnose_service.py <service-name> [-n namespace]` |
| `cluster_health.py` | Check overall cluster health | `python scripts/cluster_health.py [-n namespace] [--json]` |

**Quick Start:**
```bash
# Diagnose a specific pod
python scripts/diagnose_pod.py my-pod-name --namespace production

# Diagnose service connectivity
python scripts/diagnose_service.py my-service --namespace production

# Check cluster health
python scripts/cluster_health.py
python scripts/cluster_health.py --namespace production  # specific namespace
python scripts/cluster_health.py --json                  # JSON output
```

## Example Walkthroughs

See the `examples/` folder for detailed troubleshooting scenarios:

- `crashloop_diagnosis.md` - Step-by-step guide to diagnose CrashLoopBackOff
- `service_connectivity.md` - Troubleshooting service connectivity issues
- `node_issues.md` - Diagnosing and resolving node-level problems

## Quick Reference: Common Commands

```bash
# Pod status and events
kubectl get pods -n <namespace>
kubectl describe pod <pod-name> -n <namespace>
kubectl logs <pod-name> -n <namespace> [--previous]

# Resource usage
kubectl top pods -n <namespace>
kubectl top nodes

# Service and networking
kubectl get svc -n <namespace>
kubectl get endpoints -n <namespace>
kubectl get networkpolicies -n <namespace>

# Cluster health
kubectl get nodes
kubectl get componentstatuses
kubectl cluster-info
```

## Decision Tree: Pod Not Running

```
Pod Status?
├─ Pending
│   └─ Check: kubectl describe pod <name>
│       ├─ "Insufficient cpu/memory" → Scale cluster or adjust resource requests
│       ├─ "No nodes match selector" → Check nodeSelector/affinity rules
│       ├─ "PersistentVolumeClaim not found" → Check PVC exists and is bound
│       ├─ "Unschedulable" → Check taints/tolerations
│       └─ "FailedScheduling" → Check resource quotas and limits
│
├─ CrashLoopBackOff
│   └─ Check: kubectl logs <pod> --previous
│       ├─ Application error → Fix application code/config
│       ├─ Missing config/secrets → Verify ConfigMaps and Secrets exist
│       ├─ Permission denied → Check SecurityContext and RBAC
│       └─ No logs → Check if container starts at all (entrypoint issue)
│
├─ ImagePullBackOff / ErrImagePull
│   └─ Check: kubectl describe pod <name>
│       ├─ "unauthorized" → Check imagePullSecrets
│       ├─ "not found" → Verify image name and tag
│       ├─ "connection refused" → Check registry connectivity
│       └─ "manifest unknown" → Tag doesn't exist in registry
│
├─ OOMKilled
│   └─ Container exceeded memory limit
│       ├─ Increase memory limits in pod spec
│       ├─ Check for memory leaks in application
│       └─ Profile application memory usage
│
├─ CreateContainerConfigError
│   └─ Check: kubectl describe pod <name>
│       ├─ ConfigMap not found → Create missing ConfigMap
│       ├─ Secret not found → Create missing Secret
│       └─ Invalid mount path → Fix volumeMounts configuration
│
└─ Running but not Ready
    └─ Check: kubectl describe pod <name>
        ├─ Readiness probe failing → Check probe configuration and endpoint
        ├─ Liveness probe failing → Application may be hanging
        └─ Init containers not complete → Check init container logs
```

## Decision Tree: Service Connectivity Issues

```
Service not accessible?
├─ From inside cluster
│   ├─ Check endpoints: kubectl get endpoints <svc-name>
│   │   ├─ No endpoints → Pods not matching selector or not ready
│   │   └─ Has endpoints → DNS or network policy issue
│   │
│   ├─ Test DNS: kubectl run test --rm -it --image=busybox -- nslookup <svc-name>
│   │   ├─ DNS fails → Check CoreDNS pods and config
│   │   └─ DNS works → Check network policies
│   │
│   └─ Test connectivity: kubectl run test --rm -it --image=busybox -- wget -qO- <svc-name>:<port>
│       ├─ Connection refused → App not listening on expected port
│       ├─ Timeout → Network policy blocking traffic
│       └─ Works → Issue is with calling application
│
└─ From outside cluster (LoadBalancer/NodePort/Ingress)
    ├─ LoadBalancer
    │   ├─ Check EXTERNAL-IP: kubectl get svc <name>
    │   │   ├─ <pending> → Cloud provider issue or quota
    │   │   └─ Has IP → Check cloud firewall rules
    │   └─ Check cloud load balancer health checks
    │
    ├─ NodePort
    │   ├─ Check node firewall allows NodePort range (30000-32767)
    │   └─ Verify node is reachable
    │
    └─ Ingress
        ├─ Check ingress controller pods are running
        ├─ Verify ingress rules: kubectl describe ingress <name>
        ├─ Check TLS certificate if using HTTPS
        └─ Verify backend service and endpoints
```

## Decision Tree: Node Issues

```
Node not Ready?
├─ Check: kubectl describe node <name>
│   ├─ MemoryPressure → Node running out of memory
│   │   └─ Evict pods or add capacity
│   ├─ DiskPressure → Node running out of disk
│   │   └─ Clean up images: docker system prune
│   ├─ PIDPressure → Too many processes
│   │   └─ Check for fork bombs or runaway processes
│   ├─ NetworkUnavailable → CNI plugin issue
│   │   └─ Check CNI pods (calico, flannel, etc.)
│   └─ Unknown → Kubelet not reporting
│       └─ SSH to node and check kubelet: systemctl status kubelet
│
└─ Node unreachable
    ├─ Check cloud provider console for instance status
    ├─ Check if node was terminated/preempted
    └─ Verify network connectivity to control plane
```

## Decision Tree: Deployment Issues

```
Deployment not progressing?
├─ Check: kubectl rollout status deployment/<name>
│
├─ Stuck at "Waiting for rollout"
│   └─ Check: kubectl describe deployment <name>
│       ├─ "ProgressDeadlineExceeded" → Pods failing to become ready
│       ├─ "MinimumReplicasUnavailable" → Check pod issues above
│       └─ "ReplicaSetUpdated" but pods not ready → Check pod events
│
├─ Rollback needed
│   └─ kubectl rollout undo deployment/<name>
│
└─ Check revision history
    └─ kubectl rollout history deployment/<name>
```

## Diagnostic Workflow: Step-by-Step

When troubleshooting any Kubernetes issue, follow this systematic approach:

### Step 1: Gather Context
```bash
# What namespace?
kubectl config get-contexts
kubectl get namespaces

# What's the current state?
kubectl get all -n <namespace>
```

### Step 2: Check Events
```bash
# Recent events (often reveals the root cause)
kubectl get events -n <namespace> --sort-by='.lastTimestamp' | tail -20

# Events for specific resource
kubectl describe <resource-type> <name> -n <namespace>
```

### Step 3: Check Logs
```bash
# Current logs
kubectl logs <pod-name> -n <namespace>

# Previous container logs (if crashed)
kubectl logs <pod-name> -n <namespace> --previous

# All containers in pod
kubectl logs <pod-name> -n <namespace> --all-containers

# Follow logs
kubectl logs -f <pod-name> -n <namespace>
```

### Step 4: Interactive Debugging
```bash
# Exec into running container
kubectl exec -it <pod-name> -n <namespace> -- /bin/sh

# Debug with ephemeral container (K8s 1.23+)
kubectl debug <pod-name> -it --image=busybox -n <namespace>

# Debug node
kubectl debug node/<node-name> -it --image=busybox
```

### Step 5: Resource Analysis
```bash
# Check resource usage
kubectl top pods -n <namespace>
kubectl top nodes

# Check resource quotas
kubectl get resourcequotas -n <namespace>
kubectl describe resourcequota <name> -n <namespace>

# Check limit ranges
kubectl get limitranges -n <namespace>
```

## Common Fixes

### Fix: Pod stuck in Pending due to resources
```yaml
# Reduce resource requests in pod spec
resources:
  requests:
    memory: "64Mi"  # Lower if possible
    cpu: "100m"     # Lower if possible
  limits:
    memory: "128Mi"
    cpu: "500m"
```

### Fix: ImagePullBackOff with private registry
```bash
# Create image pull secret
kubectl create secret docker-registry regcred \
  --docker-server=<registry-url> \
  --docker-username=<username> \
  --docker-password=<password> \
  -n <namespace>

# Reference in pod spec
spec:
  imagePullSecrets:
  - name: regcred
```

### Fix: Service not finding pods
```bash
# Verify selector matches pod labels
kubectl get svc <name> -o yaml | grep -A5 selector
kubectl get pods --show-labels

# Labels must match exactly
```

### Fix: DNS not resolving
```bash
# Check CoreDNS is running
kubectl get pods -n kube-system -l k8s-app=kube-dns

# Check CoreDNS logs
kubectl logs -n kube-system -l k8s-app=kube-dns

# Test DNS resolution
kubectl run dnstest --rm -it --image=busybox --restart=Never -- nslookup kubernetes.default
```

## Best Practices

1. **Always check events first** - `kubectl describe` output includes recent events that often reveal the root cause immediately.

2. **Use labels effectively** - Consistent labeling makes troubleshooting easier: `kubectl get pods -l app=myapp`

3. **Set resource requests and limits** - Prevents resource starvation and makes debugging easier.

4. **Use namespaces** - Isolate workloads and make it easier to scope troubleshooting.

5. **Enable pod disruption budgets** - Prevents accidental outages during maintenance.

6. **Check multiple replicas** - If one pod fails, check if others are affected to determine if it's a pod-specific or cluster-wide issue.

7. **Preserve evidence** - Before deleting failing pods, capture logs and describe output for analysis.

## Emergency Commands

```bash
# Force delete stuck pod
kubectl delete pod <name> -n <namespace> --force --grace-period=0

# Cordon node (prevent new pods)
kubectl cordon <node-name>

# Drain node (evict pods safely)
kubectl drain <node-name> --ignore-daemonsets --delete-emptydir-data

# Uncordon node (allow pods again)
kubectl uncordon <node-name>
```
