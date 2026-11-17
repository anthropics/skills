---
name: arcgis-enterprise-k8s
description: Deploy, configure, and operate ArcGIS Enterprise on Kubernetes — system requirements, deployment profiles (Development/Standard/Enhanced Availability), EKS/AKS/GKE/OpenShift support, persistent volume planning, load balancer configuration, TLS setup, upgrade procedures, and operational troubleshooting. Use this skill whenever the user mentions ArcGIS Enterprise on Kubernetes, ArcGIS K8s deployment, Esri Enterprise K8s sizing, ArcGIS PVC planning, ArcGIS upgrade, or diagnosing pod failures in an ArcGIS namespace — even if they just say "deploy ArcGIS" or "ArcGIS on EKS" without further detail.
---

# arcgis-enterprise-k8s

Deploy and operate ArcGIS Enterprise on Kubernetes (version 12.0). Covers sizing, cloud platform specifics, storage planning, networking, and the deployment workflow.

## When to use

- Planning or executing a new ArcGIS Enterprise K8s deployment
- Sizing nodes and storage for a given profile (Dev / Standard / Enhanced)
- Choosing load balancer type (L4 vs L7) on AWS/Azure/GCP
- Configuring persistent volumes and storage classes
- Upgrading between ArcGIS Enterprise K8s versions
- Diagnosing failing pods or CrashLoopBackOff in an ArcGIS namespace

Do NOT use for:
- ArcGIS Enterprise traditional (Windows/Linux VM deployment — separate installer)
- ArcGIS Online (Esri-managed SaaS — no customer K8s access)
- ArcGIS Pro (desktop client — no K8s component)

---

## Supported platforms (v12.0)

| Platform | Notes |
|----------|-------|
| Amazon EKS | K8s 1.32–1.33 |
| Azure AKS | K8s 1.32–1.33 |
| Google GKE | K8s 1.32–1.33 |
| Red Hat OpenShift (RHOS) | K8s 1.32–1.33 |
| VMware Tanzu | K8s 1.32–1.33 |
| RKE2 | K8s 1.32–1.33 |

**Architecture:** x86_64 only. Worker nodes must be Linux. ARM not supported.

---

## Deployment profiles and sizing

| Profile | Min Nodes | Total vCPU | Total RAM | Use case |
|---------|-----------|-----------|-----------|----------|
| Enhanced Availability | 7 | 56 vCPU | 224 GiB | Production HA |
| Standard Availability | 4 | 32 vCPU | 128 GiB | Production single-site |
| Development | 3 | 24 vCPU | 96 GiB | Dev/test only |

**Per-node minimum**: 8 vCPU, 32 GiB RAM, 200 GiB root disk.

### AWS EKS recommended node types

| Profile | Node type | Count |
|---------|-----------|-------|
| Enhanced | m6i.4xlarge (16 vCPU / 64 GiB) | 7+ |
| Standard | m6i.4xlarge | 4 |
| Development | m6i.2xlarge (8 vCPU / 32 GiB) | 3 |

---

## Persistent volume planning

ArcGIS Enterprise requires multiple PVs. Plan storage classes before deployment — PV configuration cannot be changed without redeployment.

| Data store | Storage type | Access mode | Notes |
|------------|-------------|-------------|-------|
| In-memory cache | Block (SSD) | RWO | Redis/Ignite |
| Item packages | Object/Block | RWX | Shared across pods |
| Queue | Block | RWO | Message broker |
| Relational DB (×2) | Block (SSD) | RWO | PostgreSQL |
| Spatiotemporal/index | Block (SSD) | RWO | Elasticsearch |
| Usage metrics | Block | RWO | |

**Recommendation**: Use dynamic provisioning via a `StorageClass`. On EKS use `gp3` (not `gp2`). On AKS use `managed-premium`. On GKE use `pd-ssd`.

```yaml
# Example EKS storage class
apiVersion: storage.k8s.io/v1
kind: StorageClass
metadata:
  name: arcgis-ssd
provisioner: ebs.csi.aws.com
parameters:
  type: gp3
  encrypted: "true"
volumeBindingMode: WaitForFirstConsumer
reclaimPolicy: Retain
```

---

## Networking

### FQDN — plan before deploying

The FQDN is set at deployment time and **cannot be changed** without a full redeploy. Use a real DNS name (e.g., `arcgis.agency.gov`), not an IP address.

```bash
# Verify DNS resolves before deployment
nslookup arcgis.agency.gov
```

### Load balancer selection

| Type | AWS | Azure | GCP | On-prem |
|------|-----|-------|-----|---------|
| L4 (TCP passthrough) | NLB | Azure Load Balancer | TCP LB | MetalLB |
| L7 (TLS termination) | ALB | Application Gateway | HTTP LB | NGINX/Traefik |

Esri recommends L4 (TCP passthrough) for simplicity — TLS termination is handled by ArcGIS pods directly.

### IP capacity planning

- Initial deployment: **47–66 pod IPs** (varies by profile)
- Reserve extra IPs for scaling and rolling upgrades
- VPC/subnet CIDR must have sufficient free addresses

### TLS certificate requirements

- Must include FQDN in both **Common Name** and **Subject Alternative Name**
- Minimum 2048-bit RSA or 256-bit EC key
- Full chain (cert + intermediates) required
- Self-signed NOT supported in production

```bash
# Check cert covers the FQDN
openssl x509 -in arcgis.crt -text -noout | grep -A2 "Subject Alternative"
```

---

## Deployment workflow

### Prerequisites

```bash
# Client workstation: RHEL 9, Ubuntu 24.04, or AlmaLinux 9
# Required tools:
kubectl version --client
aws eks update-kubeconfig --name <cluster> --region <region>  # EKS
az aks get-credentials --resource-group <rg> --name <cluster> # AKS
```

### Deploy steps (EKS example)

```bash
# 1. Download deployment scripts from My Esri
# 2. Extract and configure
tar -xzf arcgis-enterprise-k8s-12.0.tar.gz
cd arcgis-enterprise-k8s-12.0

# 3. Edit configure.json for your environment
cp configure-template.json configure.json
# Set: fqdn, deployment_profile, storage_class, license_file

# 4. Run deployment
./arcgis-enterprise-k8s.sh deploy -c configure.json

# 5. Verify pods
kubectl -n arcgis get pods
kubectl -n arcgis get pvc
kubectl -n arcgis get ingress
```

### Post-deployment

```bash
# Get initial admin credentials
kubectl -n arcgis get secret arcgis-initial-admin -o jsonpath='{.data.password}' | base64 -d

# Access Manager
https://arcgis.agency.gov/arcgis/manager
```

---

## Common operations

### Check pod health

```bash
kubectl -n arcgis get pods -o wide
kubectl -n arcgis describe pod <pod-name>
kubectl -n arcgis logs <pod-name> --previous  # crashed pod logs
```

### CrashLoopBackOff diagnosis

| Component | Common cause | Fix |
|-----------|-------------|-----|
| `arcgis-server` | Insufficient memory | Increase node RAM or adjust requests/limits |
| `postgres-*` | PVC not bound | Check storage class, PVC events |
| `ingress-*` | TLS cert issue | Verify cert secret, FQDN match |
| `spatiotemporal-*` | Disk full | Expand PV or clean indices |

### Scale services

```bash
# ArcGIS Enterprise K8s uses its own scaling API, not kubectl scale
# Use Manager UI or REST API:
curl -X POST "https://arcgis.agency.gov/arcgis/admin/services/<service>/edit" \
  -d "minInstancesPerNode=2&maxInstancesPerNode=4"
```

### Upgrade procedure

1. Back up all PVs and the `arcgis` namespace config
2. Download new deployment scripts from My Esri
3. Run upgrade script — rolling restart, pods stay available during upgrade
4. Verify all pods reach `Running` state
5. Run post-upgrade validation from Manager

```bash
./arcgis-enterprise-k8s.sh upgrade -c configure.json
kubectl -n arcgis rollout status deployment --timeout=30m
```

---

## Licensing

- License is file-based (`.json` from My Esri)
- Applied during initial deployment
- For ArcGIS Pro: version 3.6 required for latest features; 2.8+ for publishing
- Enterprise geodatabase: version 10.9.0.2.8 or later for external data store registration

---

## Backup and DR

```bash
# Snapshot all PVCs before upgrade or maintenance
kubectl -n arcgis get pvc -o name | while read pvc; do
  kubectl -n arcgis annotate $pvc "backup/timestamp=$(date +%Y%m%d)"
done

# Use cloud-native snapshots (EKS: EBS Snapshots, AKS: Managed Disk Snapshots)
# Esri also provides webgisdr for content backup
```

---

## Additional resources

- Deployment docs: `https://enterprise-k8s.arcgis.com/en/latest/`
- System requirements: `https://enterprise-k8s.arcgis.com/en/latest/deploy/system-requirements.htm`
- My Esri (downloads/license): `https://my.esri.com`
- Community: `https://community.esri.com/t5/arcgis-enterprise-on-kubernetes`

## Example prompts

- *"How many nodes do I need for ArcGIS Enterprise on Kubernetes in production HA mode?"*
- *"What storage class should I use for ArcGIS PVCs on EKS?"*
- *"One of my ArcGIS pods is in CrashLoopBackOff. How do I diagnose it?"*
- *"Can I change the FQDN after ArcGIS Enterprise Kubernetes is deployed?"*
- *"Walk me through upgrading ArcGIS Enterprise Kubernetes to the latest version."*
- *"How many IP addresses do I need to reserve in my VPC subnet for an ArcGIS deployment?"*
- *"Show me a StorageClass manifest for ArcGIS on EKS using gp3."*

## Related skills

- [`k8s-nextjs-deploy`](./k8s-nextjs-deploy/SKILL.md) — general Kubernetes deployment patterns and failure diagnosis
- [`ubuntu24-stig`](./ubuntu24-stig/SKILL.md) — OS hardening for self-managed worker nodes
- [`login-gov`](./login-gov/SKILL.md) — federal identity integration if fronting ArcGIS with login.gov
