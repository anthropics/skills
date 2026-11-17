# Example: Diagnosing Node Issues

This example demonstrates how to diagnose and resolve node-level problems.

## Scenario

Pods are stuck in Pending state and nodes show NotReady or resource pressure.

## Step 1: Check Node Status

```bash
$ kubectl get nodes
NAME      STATUS     ROLES           AGE   VERSION
node-1    Ready      control-plane   30d   v1.28.0
node-2    NotReady   worker          30d   v1.28.0
node-3    Ready      worker          30d   v1.28.0
```

## Step 2: Investigate NotReady Node

```bash
$ kubectl describe node node-2
...
Conditions:
  Type                 Status    Reason                       Message
  ----                 ------    ------                       -------
  MemoryPressure       False     KubeletHasSufficientMemory   kubelet has sufficient memory available
  DiskPressure         True      KubeletHasDiskPressure       kubelet has disk pressure
  PIDPressure          False     KubeletHasSufficientPID      kubelet has sufficient PID available
  Ready                False     KubeletNotReady              container runtime network not ready
...
Events:
  Type     Reason                   Age                From        Message
  ----     ------                   ----               ----        -------
  Warning  FreeDiskSpaceFailed      5m (x10 over 1h)   kubelet     failed to garbage collect required amount of images
  Warning  ImageGCFailed            5m                 kubelet     failed to garbage collect required amount of images
```

**Problem identified**: Node has disk pressure due to accumulated container images.

## Step 3: SSH to Node and Investigate

```bash
# Check disk usage
$ ssh node-2 "df -h"
Filesystem      Size  Used Avail Use% Mounted on
/dev/sda1       100G   95G    5G  95% /
/dev/sdb1       500G  450G   50G  90% /var/lib/containerd

# Check container runtime disk usage
$ ssh node-2 "sudo crictl images | wc -l"
247

$ ssh node-2 "sudo du -sh /var/lib/containerd"
420G    /var/lib/containerd
```

## Step 4: Clean Up Disk Space

```bash
# Remove unused images on the node
$ ssh node-2 "sudo crictl rmi --prune"
Deleted: sha256:abc123...
Deleted: sha256:def456...
...

# Or for Docker runtime
$ ssh node-2 "sudo docker system prune -af"

# Check disk space after cleanup
$ ssh node-2 "df -h /"
Filesystem      Size  Used Avail Use% Mounted on
/dev/sda1       100G   60G   40G  60% /
```

## Step 5: Verify Node Recovery

```bash
$ kubectl get nodes
NAME      STATUS   ROLES           AGE   VERSION
node-1    Ready    control-plane   30d   v1.28.0
node-2    Ready    worker          30d   v1.28.0
node-3    Ready    worker          30d   v1.28.0

$ kubectl describe node node-2 | grep -A5 Conditions
Conditions:
  Type                 Status  Reason                       Message
  ----                 ------  ------                       -------
  MemoryPressure       False   KubeletHasSufficientMemory   kubelet has sufficient memory available
  DiskPressure         False   KubeletHasNoDiskPressure     kubelet has no disk pressure
  Ready                True    KubeletReady                 kubelet is posting ready status
```

## Using the Cluster Health Script

```bash
$ python scripts/cluster_health.py

Kubernetes Cluster Health Check
==================================================

Checking nodes...
Checking pods...
Checking PersistentVolumeClaims...
Checking deployments...

==================================================
HEALTH REPORT
==================================================

Nodes: 2/3 healthy
  - Node node-2 has DiskPressure
  - Node node-2 is NotReady

Pods with issues: 5
  - production/my-app-abc123: Pending
  - production/my-app-def456: Pending
  ...

==================================================
Overall Status: ISSUES DETECTED
Total Issues: 7
```

## Common Node Issues and Fixes

### MemoryPressure

```bash
# Check memory usage
$ kubectl top nodes
NAME      CPU(cores)   CPU%   MEMORY(bytes)   MEMORY%
node-2    1500m        75%    15000Mi         95%

# Find memory-hungry pods
$ kubectl top pods --all-namespaces --sort-by=memory | head -10

# Evict pods if necessary
$ kubectl drain node-2 --ignore-daemonsets --delete-emptydir-data
```

### DiskPressure

```bash
# Clean up container images
$ ssh node-2 "sudo crictl rmi --prune"

# Clean up unused volumes
$ ssh node-2 "sudo crictl rmp $(sudo crictl pods -q)"

# Check for large log files
$ ssh node-2 "sudo find /var/log -size +100M -exec ls -lh {} \;"
```

### PIDPressure

```bash
# Check process count
$ ssh node-2 "ps aux | wc -l"

# Find processes by count
$ ssh node-2 "ps aux --sort=-pid | head -20"

# Check for fork bombs or runaway processes
$ ssh node-2 "sudo pstree -p | head -50"
```

### Kubelet Not Running

```bash
# Check kubelet status
$ ssh node-2 "sudo systemctl status kubelet"

# Check kubelet logs
$ ssh node-2 "sudo journalctl -u kubelet --since '1 hour ago' | tail -50"

# Restart kubelet
$ ssh node-2 "sudo systemctl restart kubelet"
```

### Network Not Ready

```bash
# Check CNI plugin pods
$ kubectl get pods -n kube-system -l k8s-app=calico-node
$ kubectl get pods -n kube-system -l app=flannel

# Check CNI configuration
$ ssh node-2 "ls -la /etc/cni/net.d/"

# Restart CNI pods if needed
$ kubectl delete pods -n kube-system -l k8s-app=calico-node
```

## Preventive Measures

1. **Set up monitoring** - Use Prometheus/Grafana to monitor node resources
2. **Configure image garbage collection** - Adjust kubelet GC thresholds
3. **Use resource quotas** - Prevent any single namespace from consuming all resources
4. **Set pod resource limits** - Ensure pods can't consume unlimited resources
5. **Regular maintenance** - Schedule periodic cleanup of unused resources

```yaml
# Example: Kubelet configuration for image GC
apiVersion: kubelet.config.k8s.io/v1beta1
kind: KubeletConfiguration
imageGCHighThresholdPercent: 85
imageGCLowThresholdPercent: 80
evictionHard:
  memory.available: "100Mi"
  nodefs.available: "10%"
  imagefs.available: "15%"
```
