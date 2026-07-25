---
name: azure-aks-edge-essentials
description: Expert knowledge for Azure Kubernetes Service Edge Essentials development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when managing AKS Edge/Arc clusters, Arc onboarding, IoT/AI workloads, TPM access, or camera/OPC UA integration, and other Azure Kubernetes Service Edge Essentials related development tasks. Not for Azure Kubernetes Service (AKS) (use azure-kubernetes-service), Azure IoT Edge (use azure-iot-edge), Azure Stack Edge (use azure-stack-edge), Azure Container Apps (use azure-container-apps).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-05"
  generator: "docs2skills/1.0.0"
---
# Azure Kubernetes Service Edge Essentials Skill

This skill provides expert guidance for Azure Kubernetes Service Edge Essentials. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L88 | Diagnosing and fixing AKS Edge/Arc cluster issues: creation/upgrade failures, networking, storage, security, logs/diagnostics, VMware/Windows Server problems, and known errors/workarounds. |
| Best Practices | L89-L96 | Best practices for AKS Edge/Arc: applying Azure Policy, recovering clusters after management VM loss, and safely upgrading Kubernetes/workload clusters via PowerShell or Admin Center |
| Decision Making | L97-L109 | Guidance on choosing AKS Edge/Arc vs cloud/on-prem, supported versions/add-ons, monitoring, pricing/licensing, support, and planning migrations or retirement of older AKS/Windows Server setups |
| Architecture & Design Patterns | L110-L116 | Designing AKS on Windows Server for Azure Local: high availability on two-node setups, SDN VNet architectures, and deployment patterns for AKS Arc target clusters. |
| Limits & Quotas | L117-L131 | Hardware/software requirements, IP and scale limits, quotas, and support policies for AKS Edge/Arc on Azure Local, bare metal, VMware, and Windows Server deployments. |
| Security | L132-L167 | Identity, RBAC, certificates, SSH, gMSA, and container security for AKS Edge/Arc/Hybrid, including Entra/AD auth, key rotation, workload identity, and secure access to nodes and clusters. |
| Configuration | L168-L254 | Configuring AKS Edge/Arc/hybrid clusters: networking, storage, load balancers, proxies, autoscaling, monitoring, Windows/Linux node pools, offline/Arc connectivity, and deployment templates. |
| Integrations & Coding Patterns | L255-L314 | Managing and integrating AKS Edge/AKS Arc/hybrid clusters: Arc onboarding, CLI/PowerShell cmdlets, storage/CSI, networking, logging/backup, IoT/AI workloads, TPM access, and camera/OPC UA discovery. |
| Deployment | L315-L351 | Deploying, upgrading, and managing AKS Edge/AKS hybrid/AKS Arc clusters and nodes (Windows & Linux), including installs, updates, node pools, offline/disconnected ops, and lifecycle tasks. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Run AKS Arc diagnostic checker for cluster failures | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-arc-diagnostic-checker |
| Resolve known issues in AKS enabled by Azure Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-arc-known-issues |
| Validate and troubleshoot AKS Edge secret encryption | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-howto-secret-encryption |
| Collect and use AKS Edge Essentials logs for troubleshooting | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-resources-logs |
| Troubleshoot common AKS Edge Essentials issues | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-troubleshoot-overview |
| Retrieve kubelet logs from AKS Arc nodes | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-get-kubelet-logs |
| Troubleshoot common Kubernetes issues in AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-troubleshoot |
| Review known issues and workarounds for AKS Arc on VMware | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-vmware-known-issues |
| Request support and troubleshoot AKS Arc on VMware | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-vmware-support-troubleshoot |
| Use troubleshooting guide for AKS Arc on VMware errors | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-vmware-troubleshooting-guide |
| Resolve AKS Arc cluster creation failures after Azure Local upgrade | https://learn.microsoft.com/en-us/azure/aks/aksarc/cluster-create-fails-after-azure-local-upgrade |
| Fix K8sVersionValidation errors in AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/cluster-k8s-version |
| Fix AKS Arc cluster unhealthy after Kubernetes upgrade | https://learn.microsoft.com/en-us/azure/aks/aksarc/cluster-unhealthy-after-kubernetes-upgrade |
| Fix AKS Edge Arc cluster stuck upgrading | https://learn.microsoft.com/en-us/azure/aks/aksarc/cluster-upgrade-status |
| Troubleshoot BGP with FRR and MetalLB in AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/connectivity-troubleshoot |
| Resolve AKS Arc control plane configuration validation errors | https://learn.microsoft.com/en-us/azure/aks/aksarc/control-plane-validation-errors |
| Resolve undeleted PDBs when removing AKS Edge clusters | https://learn.microsoft.com/en-us/azure/aks/aksarc/delete-cluster-pdb |
| Mitigate AKS Arc issues after storage volume deletion | https://learn.microsoft.com/en-us/azure/aks/aksarc/delete-storage-volume |
| Remove deleted AKS Arc clusters still visible in portal | https://learn.microsoft.com/en-us/azure/aks/aksarc/deleted-cluster-visible |
| Monitor and troubleshoot etcd secret encryption in AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/encrypt-secrets |
| Resolve repeated Entra prompts with kubectl and RBAC on AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/entra-prompts |
| Fix AKS Arc cluster create or scale failures due to VHD image issues | https://learn.microsoft.com/en-us/azure/aks/aksarc/gallery-image-not-usable |
| Collect on-demand AKS Arc logs for Microsoft support | https://learn.microsoft.com/en-us/azure/aks/aksarc/get-on-demand-logs |
| Fix GPU-enabled AKS Arc cluster creation failures | https://learn.microsoft.com/en-us/azure/aks/aksarc/gpu-enabled-cluster-issue |
| Diagnose and fix 'MOC unreachable' errors for AKS on Azure Local | https://learn.microsoft.com/en-us/azure/aks/aksarc/infrastructure-operation-failures |
| Handle general known issues when running AKS on Windows Server | https://learn.microsoft.com/en-us/azure/aks/aksarc/known-issues |
| Fix Azure Arc enable/disable errors on AKS workload clusters | https://learn.microsoft.com/en-us/azure/aks/aksarc/known-issues-arc |
| Resolve installation errors for AKS on Windows Server (AKS Arc) | https://learn.microsoft.com/en-us/azure/aks/aksarc/known-issues-installation |
| Diagnose and fix networking issues in AKS on Windows Server | https://learn.microsoft.com/en-us/azure/aks/aksarc/known-issues-networking |
| Resolve security and identity errors in AKS Arc clusters | https://learn.microsoft.com/en-us/azure/aks/aksarc/known-issues-security |
| Troubleshoot storage-related problems in AKS on Windows Server | https://learn.microsoft.com/en-us/azure/aks/aksarc/known-issues-storage |
| Fix problems uninstalling AKS Arc on Windows Server | https://learn.microsoft.com/en-us/azure/aks/aksarc/known-issues-uninstall |
| Address upgrade issues for AKS on Windows Server (AKS Arc) | https://learn.microsoft.com/en-us/azure/aks/aksarc/known-issues-upgrade |
| Work around Windows Admin Center issues for AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/known-issues-windows-admin-center |
| Troubleshoot AKS Arc management and workload cluster failures | https://learn.microsoft.com/en-us/azure/aks/aksarc/known-issues-workload-clusters |
| Troubleshoot kube-apiserver connectivity from Arc Resource Bridge | https://learn.microsoft.com/en-us/azure/aks/aksarc/kube-api-server-unreachable |
| Resolve control plane disk exhaustion from kube-apiserver audit logs in AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/kube-apiserver-log-overflow |
| Monitor Kubernetes object events in AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/kubernetes-monitor-object-events |
| Fix .local domain network validation error in AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/network-validation-error-local |
| Troubleshoot AKS Arc network validation errors | https://learn.microsoft.com/en-us/azure/aks/aksarc/network-validation-errors |
| Repair AKS Edge KMS plugin with PowerShell | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/repair-aksedgekms |
| Collect AKS hybrid PowerShell module event logs | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/get-akshcieventlog |
| Collect AKS hybrid pod logs into zip archive | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/get-akshcilogs |
| Repair AKS hybrid host certificates with Repair-AksHciCerts | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/repair-akshcicerts |
| Repair AKS hybrid cluster certificates with Repair-AksHciClusterCerts | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/repair-akshciclustercerts |
| Resolve AKS Arc storage provisioning and volume imbalance issues | https://learn.microsoft.com/en-us/azure/aks/aksarc/storage-provision-issue |
| Use Support.AksArc PowerShell module for diagnostics | https://learn.microsoft.com/en-us/azure/aks/aksarc/support-module |
| Mitigate high resource usage by AKS Arc telemetry pod | https://learn.microsoft.com/en-us/azure/aks/aksarc/telemetry-pod-resources |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply Azure policy best practices to AKS on Windows Server | https://learn.microsoft.com/en-us/azure/aks/aksarc/policy-guidance |
| Restore AKS Arc clusters after management VM failure | https://learn.microsoft.com/en-us/azure/aks/aksarc/restore-aks-cluster |
| Upgrade AKS Arc workload clusters with PowerShell | https://learn.microsoft.com/en-us/azure/aks/aksarc/upgrade |
| Upgrade AKS Arc Kubernetes version via Admin Center | https://learn.microsoft.com/en-us/azure/aks/aksarc/upgrade-kubernetes |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose supported add-ons and extensions for AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/add-ons |
| Understand AKS Edge Essentials pricing and licensing options | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-pricing |
| Choose monitoring and logging options for AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-monitor-logging |
| Choose between AKS cloud, edge, and on-premises | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-platforms-compare |
| Plan for AKS on Windows Server architecture retirement | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-windows-server-retirement |
| Evaluate AKS on Windows Server pricing and trials | https://learn.microsoft.com/en-us/azure/aks/aksarc/pricing |
| Understand AKS on Windows Server support and responsibility | https://learn.microsoft.com/en-us/azure/aks/aksarc/support-policies |
| Select supported Kubernetes versions for AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/supported-kubernetes-versions |
| Plan migration from AKS Arc 2019 to 2022 | https://learn.microsoft.com/en-us/azure/aks/aksarc/windows-server-migration-guide |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Understand AKS on Windows Server availability on two-node Azure Local | https://learn.microsoft.com/en-us/azure/aks/aksarc/deploy-cluster-on-two-node-hci |
| Deploy AKS Arc target clusters across SDN VNets | https://learn.microsoft.com/en-us/azure/aks/aksarc/deploy-target-clusters-virtual-networks |
| Architect AKS on Windows Server with SDN virtual networking | https://learn.microsoft.com/en-us/azure/aks/aksarc/software-defined-networking |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| System and storage requirements for AKS on Azure Local | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-arc-local-requirements |
| Understand preview limitations for AKS on bare metal | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-bare-metal-preview-limitations |
| Check system requirements for AKS Edge Essentials hosts | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-system-requirements |
| Plan IP address capacity for AKS Arc production | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-hci-ip-address-planning |
| Support policies and limitations for AKS on Azure Local | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-on-azure-local-support-policy |
| Review AKS Arc on VMware cluster scale limits | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-vmware-scale-requirements |
| Track AKS Arc on Azure Local release changes | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-whats-new-local |
| Review tested resource limits and VM sizes for AKS on Windows Server | https://learn.microsoft.com/en-us/azure/aks/aksarc/concepts-support |
| Plan AKS Arc multi-rack IP address capacity | https://learn.microsoft.com/en-us/azure/aks/aksarc/multi-rack/plan-aks-ip-address |
| Check AKS on Azure Local multi-rack scale limits | https://learn.microsoft.com/en-us/azure/aks/aksarc/multi-rack/scale-requirements |
| AKS on Azure Local cluster and node pool scale limits | https://learn.microsoft.com/en-us/azure/aks/aksarc/scale-requirements |

### Security
| Topic | URL |
|-------|-----|
| Configure AD single sign-on to AKS Arc API server | https://learn.microsoft.com/en-us/azure/aks/aksarc/ad-sso |
| Use Key Manager to rotate AKS Edge service account keys | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-howto-key-manager |
| Configure workload identity on AKS Edge Essentials | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-workload-identity |
| Set up Azure RBAC authorization for AKS Arc clusters | https://learn.microsoft.com/en-us/azure/aks/aksarc/azure-rbac-aks-hybrid |
| Use Azure RBAC to control kubeconfig access in AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/azure-rbac-local |
| Manage certificates for secure communication in AKS on Windows Server | https://learn.microsoft.com/en-us/azure/aks/aksarc/certificates-overview |
| Apply security concepts for AKS on Windows Server clusters | https://learn.microsoft.com/en-us/azure/aks/aksarc/concepts-security |
| Configure SSH keys for AKS Arc cluster nodes | https://learn.microsoft.com/en-us/azure/aks/aksarc/configure-ssh-keys |
| Implement container security in AKS on Windows Server | https://learn.microsoft.com/en-us/azure/aks/aksarc/container-security |
| Enable Microsoft Entra authentication for AKS Arc clusters | https://learn.microsoft.com/en-us/azure/aks/aksarc/enable-authentication-microsoft-entra-id |
| Encrypt Kubernetes etcd secrets in AKS on Azure Local | https://learn.microsoft.com/en-us/azure/aks/aksarc/encrypt-etcd-secrets |
| Control AKS Arc access with Entra ID and Kubernetes RBAC | https://learn.microsoft.com/en-us/azure/aks/aksarc/kubernetes-rbac-entra-id |
| Configure Kubernetes RBAC with Microsoft Entra ID in AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/kubernetes-rbac-local |
| Configure access and identity for AKS on Azure Local | https://learn.microsoft.com/en-us/azure/aks/aksarc/multi-rack/concepts-security-access-identity |
| Configure Azure RBAC for AKS on Azure Local multi-rack | https://learn.microsoft.com/en-us/azure/aks/aksarc/multi-rack/use-azure-rbac |
| Configure gMSA-based AD authentication for AKS Windows containers | https://learn.microsoft.com/en-us/azure/aks/aksarc/prepare-windows-nodes-gmsa |
| Add gMSA credential spec for AKS hybrid | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/add-akshcigmsacredentialspec |
| Enable AKS hybrid Active Directory auth with Install-AksHciAdAuth | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/install-akshciadauth |
| Install gMSA webhook addon on AKS hybrid with Install-AksHciGmsaWebhook | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/install-akshcigmsawebhook |
| Rotate AKS hybrid cloud agent CA certificates with Invoke-AksHciRotateCACertificate | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/invoke-akshcirotatecacertificate |
| Create AKS hybrid SSH configurations with New-AksHciSSHConfiguration | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/new-akshcisshconfiguration |
| Delete AKS hybrid gMSA credential specs with Remove-AksHciGmsaCredentialSpec | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/remove-akshcigmsacredentialspec |
| Restrict SSH access to AKS Arc virtual machines | https://learn.microsoft.com/en-us/azure/aks/aksarc/restrict-ssh-access |
| Restrict SSH access to AKS Arc virtual machines | https://learn.microsoft.com/en-us/azure/aks/aksarc/restrict-ssh-access-22h2 |
| Review AKS Arc security bulletins and mitigations | https://learn.microsoft.com/en-us/azure/aks/aksarc/security-bulletins |
| Configure multiple administrators for AKS on Windows Server | https://learn.microsoft.com/en-us/azure/aks/aksarc/set-multiple-administrators |
| SSH into Windows and Linux worker nodes in AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/ssh-connect-to-windows-and-linux-worker-nodes |
| Securely connect to AKS Arc nodes using SSH | https://learn.microsoft.com/en-us/azure/aks/aksarc/ssh-connection |
| Configure trusted certificate bundles for AKS Arc hosts | https://learn.microsoft.com/en-us/azure/aks/aksarc/update-certificate-bundle |
| Manage infrastructure and Kubernetes certificates in AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/update-certificates |
| Validate signed container images in AKS on Azure Local | https://learn.microsoft.com/en-us/azure/aks/aksarc/validate-signed-container-images |
| Configure workload identity federation on AKS Arc clusters | https://learn.microsoft.com/en-us/azure/aks/aksarc/workload-identity |

### Configuration
| Topic | URL |
|-------|-----|
| Configure scheduling for mixed Linux/Windows AKS Arc clusters | https://learn.microsoft.com/en-us/azure/aks/aksarc/adapt-apps-mixed-os-clusters |
| Configure node taints for AKS Arc clusters | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-arc-use-node-taints |
| Configure AKS on bare metal cluster via ARM template | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-bare-metal-create-cluster-arm-template |
| Define AKS on bare metal clusters using Bicep | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-bare-metal-create-cluster-bicep |
| Review system requirements for AKS on bare metal | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-bare-metal-system-requirements |
| Configure networking for AKS Edge Essentials clusters | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-concept-networking |
| Configure AKS Edge Essentials via aksedge-config.json | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-deployment-config-json |
| Enable GPU acceleration in AKS Edge Essentials | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-gpu |
| Connect AKS Edge Essentials clusters to Azure Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-howto-connect-to-arc |
| Expose Kubernetes services on AKS Edge Essentials | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-howto-expose-service |
| Advanced AKS Edge Essentials configuration and scripts | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-howto-more-configs |
| Configure multiple NICs for AKS Edge Essentials Linux nodes | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-howto-multi-nic |
| Configure AKS Edge Essentials for offline installation | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-howto-offline-install |
| Prepare and configure machines for AKS Edge Essentials | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-howto-setup-machine |
| Configure nested virtualization for AKS Edge Essentials | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-howto-setup-nested-environment |
| Uninstall AKS Edge Essentials from host machines | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-howto-uninstall |
| Update AKS Edge Essentials clusters online | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-howto-update |
| Use GitOps with Arc-enabled AKS Edge Essentials | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-howto-use-gitops |
| Use Local Path Provisioner storage on AKS Edge Essentials | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-howto-use-storage-local-path |
| Configure external NFS storage for AKS Edge Essentials | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-howto-use-storage-nfs |
| Update AKS Edge Essentials clusters offline | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-hybrid-howto-update-offline |
| Configure Arc-enabled logical networks for AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-networks |
| Configure Kubernetes extension for AKS Arc on VMware | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-vmware-install-kubernetes-extension |
| Retrieve admin kubeconfig for AKS Arc on VMware clusters | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-vmware-retrieve-kubeconfig |
| Configure cluster autoscaler for AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/auto-scale-aks-arc |
| Configure Kubernetes cluster labels in AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/cluster-labels |
| Configure container networking for AKS on Windows Server applications | https://learn.microsoft.com/en-us/azure/aks/aksarc/concepts-container-networking |
| Configure node VM networking for AKS on Windows Server | https://learn.microsoft.com/en-us/azure/aks/aksarc/concepts-node-networking |
| Create and integrate custom load balancers with AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/configure-custom-load-balancer |
| Configure HAProxy load balancer for AKS Arc clusters | https://learn.microsoft.com/en-us/azure/aks/aksarc/configure-load-balancer |
| Use CSI disk drivers and storage classes in AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/container-storage-interface-disks |
| Use CSI disk drivers and storage classes in AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/container-storage-interface-disks-windows-server |
| Configure CSI file drivers for SMB/NFS in AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/container-storage-interface-files |
| Configure CSI file drivers for SMB/NFS in AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/container-storage-interface-files-windows-server |
| Enable and query AKS Arc control plane metrics | https://learn.microsoft.com/en-us/azure/aks/aksarc/control-plane-metrics |
| Deploy MetalLB load balancer on AKS Arc via CLI | https://learn.microsoft.com/en-us/azure/aks/aksarc/deploy-load-balancer-cli |
| Deploy MetalLB extension for AKS Arc using Azure portal | https://learn.microsoft.com/en-us/azure/aks/aksarc/deploy-load-balancer-portal |
| Disable Windows node pool feature on older AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/disable-windows-nodepool |
| Enable Windows node pools on AKS Arc clusters | https://learn.microsoft.com/en-us/azure/aks/aksarc/howto-enable-windows-node-pools |
| Configure Kubernetes audit logging for AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/kubernetes-monitor-audit-events |
| Create and manage node pools in AKS on Azure Local | https://learn.microsoft.com/en-us/azure/aks/aksarc/manage-node-pools |
| Configure Prometheus and EFK monitoring for AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/monitor-logging |
| Configure custom HTTPS proxy for AKS on Azure Local | https://learn.microsoft.com/en-us/azure/aks/aksarc/multi-rack/aks-customer-proxy |
| Configure GPU-enabled node pools for AKS on Azure Local | https://learn.microsoft.com/en-us/azure/aks/aksarc/multi-rack/deploy-gpu-node-pool |
| Configure MetalLB extension on AKS Arc clusters | https://learn.microsoft.com/en-us/azure/aks/aksarc/multi-rack/deploy-load-balancer-cli |
| Configure network prerequisites for AKS Arc multi-rack | https://learn.microsoft.com/en-us/azure/aks/aksarc/multi-rack/network-system-requirements |
| Scale and manage multiple HAProxy load balancers in AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/multiple-load-balancers |
| Configure network prerequisites for AKS Arc clusters | https://learn.microsoft.com/en-us/azure/aks/aksarc/network-system-requirements |
| Provision and manage persistent volumes in AKS on Windows Server | https://learn.microsoft.com/en-us/azure/aks/aksarc/persistent-volume |
| Update noProxy and certificate settings in AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/proxy-change |
| Use AKS Edge Essentials PowerShell cmdlets | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/ |
| Install required AKS Edge host OS features | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/install-aksedgehostfeatures |
| Create AKS Edge deployment configuration JSON | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/new-aksedgeconfig |
| Generate AKS Edge scale configuration template | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/new-aksedgescaleconfig |
| Configure AKS Edge Kubernetes upgrade policy | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/set-aksedgeupgrade |
| Test AKS Edge Azure Arc connection status | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/test-aksedgearcconnection |
| Validate AKS Edge network parameters pre-deployment | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/test-aksedgenetworkparameters |
| Disable Azure Arc connection on AKS hybrid | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/disable-akshciarcconnection |
| Enable Azure Arc connection on AKS hybrid | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/enable-akshciarcconnection |
| Get AKS hybrid autoscaler profile settings | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/get-akshciautoscalerprofile |
| Retrieve AKS hybrid deployment billing status | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/get-akshcibillingstatus |
| Get AKS hybrid cluster virtual network settings | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/get-akshciclusternetwork |
| Get AKS hybrid host configuration settings | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/get-akshciconfig |
| Initialize AKS hybrid nodes with Initialize-AksHciNode | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/initialize-akshcinode |
| Deploy Prometheus-based monitoring on AKS hybrid with Install-AksHciMonitoring | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/install-akshcimonitoring |
| Create AKS hybrid autoscaler profiles with New-AksHciAutoScalerProfile | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/new-akshciautoscalerprofile |
| Define AKS hybrid cluster networks with New-AksHciClusterNetwork | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/new-akshciclusternetwork |
| Configure AKS hybrid load balancers with New-AksHciLoadBalancerSetting | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/new-akshciloadbalancersetting |
| Create AKS hybrid network settings with New-AksHciNetworkSetting | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/new-akshcinetworksetting |
| Create AKS hybrid proxy configurations with New-AksHciProxySetting | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/new-akshciproxysetting |
| Create AKS hybrid storage containers with New-AksHciStorageContainer | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/new-akshcistoragecontainer |
| Remove AKS hybrid autoscaler profiles with Remove-AksHciAutoScalerProfile | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/remove-akshciautoscalerprofile |
| Remove AKS hybrid cluster networks with Remove-AksHciClusterNetwork | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/remove-akshciclusternetwork |
| Update AKS hybrid autoscaler profiles with Set-AksHciAutoScalerProfile | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/set-akshciautoscalerprofile |
| Scale and configure AKS hybrid clusters with Set-AksHciCluster | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/set-akshcicluster |
| Update AKS hybrid host configuration with Set-AksHciConfig | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/set-akshciconfig |
| Scale and modify AKS hybrid node pools with Set-AksHciNodePool | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/set-akshcinodepool |
| Configure AKS hybrid offline download with Set-AksHciOffsiteConfig | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/set-akshcioffsiteconfig |
| Register AKS hybrid with Azure using Set-AksHciRegistration | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/set-akshciregistration |
| Retrieve admin kubeconfig for AKS Arc clusters | https://learn.microsoft.com/en-us/azure/aks/aksarc/retrieve-admin-kubeconfig |
| Configure proxy server settings for AKS on Windows Server | https://learn.microsoft.com/en-us/azure/aks/aksarc/set-proxy-settings |
| Interpret AKS Arc validation tests before installation | https://learn.microsoft.com/en-us/azure/aks/aksarc/validation-tests |
| Configure AKS Arc autoscaler profile parameters | https://learn.microsoft.com/en-us/azure/aks/aksarc/work-with-autoscaler-profiles |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Connect to AKS on bare metal via Arc proxy | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-bare-metal-connect-to-cluster |
| Create AKS Arc clusters using Hybrid Container Service REST API | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-create-clusters-api |
| Discover and stream ONVIF cameras with Akri on AKS Edge | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-how-to-akri-onvif |
| Discover OPC UA servers with Akri on AKS Edge | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-how-to-akri-opc-ua |
| Access TPM from AKS Edge Essentials Linux VM | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-howto-access-tpm |
| Deploy Azure IoT Operations on AKS Edge Essentials | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-howto-deploy-azure-iot |
| Deploy Kubernetes metrics server on AKS Edge Essentials | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-edge-howto-metric-server |
| Use az aksarc CLI commands for AKS Arc management | https://learn.microsoft.com/en-us/azure/aks/aksarc/aksarc |
| Back up AKS Arc clusters to Blob or MinIO with Velero | https://learn.microsoft.com/en-us/azure/aks/aksarc/backup-workload-cluster |
| Connect AKS on Windows Server clusters to Azure Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/connect-to-arc |
| Deploy AI models on AKS Arc with KAITO operator | https://learn.microsoft.com/en-us/azure/aks/aksarc/deploy-ai-model |
| Deploy from Azure Container Registry to AKS on Windows Server | https://learn.microsoft.com/en-us/azure/aks/aksarc/deploy-azure-container-registry |
| Deploy from Azure Container Registry to AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/deploy-container-registry |
| Collect AKS Arc logs using az aksarc CLI | https://learn.microsoft.com/en-us/azure/aks/aksarc/logs |
| Manage AKS Arc node pools with az aksarc | https://learn.microsoft.com/en-us/azure/aks/aksarc/nodepool |
| Add-AksEdgeNode PowerShell reference for AKS Edge clusters | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/add-aksedgenode |
| Connect-AksEdgeArc PowerShell reference for Arc onboarding | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/connect-aksedgearc |
| Copy-AksEdgeNodeFile PowerShell reference for node file transfer | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/copy-aksedgenodefile |
| Disconnect-AksEdgeArc PowerShell reference for Arc removal | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/disconnect-aksedgearc |
| Get-AksEdgeDeploymentInfo PowerShell reference for AKS Edge | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/get-aksedgedeploymentinfo |
| Get-AksEdgeEventLog PowerShell reference for log collection | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/get-aksedgeeventlog |
| Get-AksEdgeKubeConfig PowerShell reference for kubeconfig retrieval | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/get-aksedgekubeconfig |
| Get-AksEdgeLogs PowerShell reference for full log export | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/get-aksedgelogs |
| Get-AksEdgeManagedServiceToken PowerShell reference | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/get-aksedgemanagedservicetoken |
| Get-AksEdgeNodeAddr PowerShell reference for node IP/MAC | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/get-aksedgenodeaddr |
| Use Get-AksEdgeNodeConnectivityMode PowerShell cmdlet | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/get-aksedgenodeconnectivitymode |
| Use Get-AksEdgeNodeName PowerShell cmdlet | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/get-aksedgenodename |
| Use Get-AksEdgeUpgrade to query upgrade policy | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/get-aksedgeupgrade |
| Run SSH commands with Invoke-AksEdgeNodeCommand | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/invoke-aksedgenodecommand |
| Use AksHci PowerShell module to manage AKS hybrid | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/ |
| Access AKS hybrid cluster credentials for kubectl | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/get-akshcicredential |
| Use Get-AksHciNodePool to list AKS hybrid node pools | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/get-akshcinodepool |
| Retrieve AKS hybrid proxy settings with Get-AksHciProxySetting | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/get-akshciproxysetting |
| Get AKS hybrid registration info using Get-AksHciRegistration | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/get-akshciregistration |
| Download AKS hybrid release bits with Get-AksHciRelease | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/get-akshcirelease |
| Query AKS hybrid storage containers with Get-AksHciStorageContainer | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/get-akshcistoragecontainer |
| List AKS on Azure Local updates using Get-AksHciUpdates | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/get-akshciupdates |
| Check AKS hybrid Kubernetes version with Get-AksHciVersion | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/get-akshciversion |
| List supported AKS hybrid VM sizes with Get-AksHciVmSize | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/get-akshcivmsize |
| Install CSI NFS plugin on AKS hybrid with Install-AksHciCsiNfs | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/install-akshcicsinfs |
| Install CSI SMB plugin on AKS hybrid with Install-AksHciCsiSmb | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/install-akshcicsismb |
| Use Sync-AksHciBilling to trigger AKS hybrid billing sync | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/sync-akshcibilling |
| Use Test-UpdateAksHci to check AKS hybrid support window | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/test-updateakshci |
| Use Uninstall-AksHci to remove AKS hybrid deployment | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/uninstall-akshci |
| Use Uninstall-AksHciAdAuth to remove AKS hybrid AD auth | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/uninstall-akshciadauth |
| Use Uninstall-AksHciCsiNfs to remove AKS hybrid NFS CSI | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/uninstall-akshcicsinfs |
| Use Uninstall-AksHciCsiSmb to remove AKS hybrid SMB CSI | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/uninstall-akshcicsismb |
| Use Uninstall-AksHciGmsaWebhook to remove AKS hybrid gMSA webhook | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/uninstall-akshcigmsawebhook |
| Use Uninstall-AksHciMonitoring to remove AKS hybrid monitoring | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/uninstall-akshcimonitoring |
| Use Update-AksHci to upgrade AKS hybrid host Kubernetes | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/update-akshci |
| Use Update-AksHciCertificates to rotate AKS hybrid management certs | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/update-akshcicertificates |
| Use Update-AksHciCluster to upgrade AKS hybrid workload clusters | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/update-akshcicluster |
| Use Update-AksHciClusterCertificates to rotate AKS hybrid workload certs | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/update-akshciclustercertificates |
| Integrate Secrets Store CSI and Key Vault with AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/secrets-store-csi-driver |
| List and select AKS Arc VM sizes via CLI | https://learn.microsoft.com/en-us/azure/aks/aksarc/vmsize |
| Configure AKS Arc virtual networks using az aksarc | https://learn.microsoft.com/en-us/azure/aks/aksarc/vnet |

### Deployment
| Topic | URL |
|-------|-----|
| Uninstall AKS cluster provisioning preview before AKS Arc upgrade | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-hybrid-preview-uninstall |
| Check AKS Arc on VMware system requirements and support | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-vmware-system-requirements |
| Upgrade Kubernetes and OS for AKS Arc clusters | https://learn.microsoft.com/en-us/azure/aks/aksarc/cluster-upgrade |
| Operate AKS Arc clusters in disconnected Azure Local | https://learn.microsoft.com/en-us/azure/aks/aksarc/disconnected-operations-aks |
| Deploy Windows node pools and apps on AKS Arc | https://learn.microsoft.com/en-us/azure/aks/aksarc/howto-create-windows-node-pools |
| Upgrade Windows Server versions on AKS Arc node pools | https://learn.microsoft.com/en-us/azure/aks/aksarc/howto-upgrade-windows-os |
| Upgrade AKS on Azure Local multi-rack Kubernetes clusters | https://learn.microsoft.com/en-us/azure/aks/aksarc/multi-rack/cluster-upgrade |
| Create new AKS Edge deployment with PowerShell | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/new-aksedgedeployment |
| Remove AKS Edge deployment from machine | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/remove-aksedgedeployment |
| Remove a local AKS Edge node from cluster | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/remove-aksedgenode |
| Drain AKS Edge node before removal | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/set-aksedgenodetodrain |
| Update AKS Edge control plane nodes | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/start-aksedgecontrolplaneupdate |
| Start AKS Edge node VM with PowerShell | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/start-aksedgenode |
| Start AKS Edge Essentials node update process | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/start-aksedgeupdate |
| Update AKS Edge worker nodes with PowerShell | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/start-aksedgeworkernodeupdate |
| Stop AKS Edge node VM with PowerShell | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/stop-aksedgenode |
| Verify AKS Edge deployment creation status | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/test-aksedgedeployment |
| Check AKS Edge node VM creation status | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/aks-edge-ps/test-aksedgenode |
| Add physical node to AKS hybrid deployment | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/add-akshcinode |
| Disable offline image download for AKS hybrid | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/disable-akshciofflinedownload |
| Revert AKS hybrid from preview to stable channel | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/disable-akshcipreview |
| Enable offline image download for AKS hybrid | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/enable-akshciofflinedownload |
| Enable AKS hybrid preview update channel | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/enable-akshcipreview |
| List AKS hybrid managed Kubernetes clusters | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/get-akshcicluster |
| Check available AKS hybrid cluster upgrades | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/get-akshciclusterupdates |
| List available Kubernetes versions for AKS hybrid | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/get-akshcikubernetesversion |
| Install AKS hybrid using Install-AksHci PowerShell cmdlet | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/install-akshci |
| Create AKS hybrid clusters using New-AksHciCluster | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/new-akshcicluster |
| Create AKS hybrid node pools with New-AksHciNodePool | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/new-akshcinodepool |
| Delete AKS hybrid clusters using Remove-AksHciCluster | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/remove-akshcicluster |
| Remove physical AKS hybrid nodes with Remove-AksHciNode | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/remove-akshcinode |
| Delete AKS hybrid node pools with Remove-AksHciNodePool | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/remove-akshcinodepool |
| Restart AKS hybrid and reset clusters with Restart-AksHci | https://learn.microsoft.com/en-us/azure/aks/aksarc/reference/ps/restart-akshci |
| Verify system requirements for AKS on Windows Server | https://learn.microsoft.com/en-us/azure/aks/aksarc/system-requirements |