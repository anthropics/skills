---
name: azure-operator-nexus
description: Expert knowledge for Azure Operator Nexus development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when managing Nexus clusters, fabric ACL/BGP, secure VM connectivity, NPB TAP rules, or near‑edge storage, and other Azure Operator Nexus related development tasks. Not for Azure Network Function Manager (use azure-network-function-manager), Azure Networking (use azure-networking), Azure Virtual Network Manager (use azure-virtual-network-manager), Azure Operator Insights (use azure-operator-insights).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-05"
  generator: "docs2skills/1.0.0"
---
# Azure Operator Nexus Skill

This skill provides expert guidance for Azure Operator Nexus. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L82 | Diagnosing and fixing Nexus infrastructure issues: bare metal/VM recovery, storage and network faults, Kubernetes cluster/pod problems, runtime upgrades, and hardware/health alerts. |
| Best Practices | L83-L88 | Guidance on Nexus bare metal lifecycle ops, ETCD maintenance in Nexus AKS, and procedures for repairing and maintaining Nexus storage appliance components. |
| Decision Making | L89-L96 | Guidance on planning Nexus Kubernetes cluster placement and choosing compatible Nexus versions, VM SKUs, and platform SKUs based on workload, capacity, and storage support. |
| Architecture & Design Patterns | L97-L102 | Design patterns and reference architectures for resilient Nexus deployments, including rack-failure-tolerant control planes and near-edge storage topology and capacity planning. |
| Limits & Quotas | L103-L115 | Nexus platform limits, quotas, supported versions, upgrade cadence, storage planning, node restarts/timeouts, isolation domain requirements, and log behavior after disconnection. |
| Security | L116-L155 | Securing Nexus: identity/RBAC, ACLs, SSH and serial access, break-glass methods, key/cert/secret rotation, Defender/Policy, managed identities, and secure VM/cluster connectivity. |
| Configuration | L156-L225 | Designing, applying, and troubleshooting configuration for Nexus clusters, Kubernetes, and network fabric (ACLs, route policies, isolation domains, BGP/QoS, upgrades, drift, and commit workflows). |
| Integrations & Coding Patterns | L226-L230 | Configuring Network Packet Broker TAP rules in Azure Operator Nexus, including rule creation, traffic mirroring, filtering, and integration patterns for network observability. |
| Deployment | L231-L239 | Deploying and maintaining Nexus platform and fabric: prerequisites, image building, OS and fabric upgrades, and replacing or updating terminal servers in the network fabric. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Nexus network devices with read-only commands | https://learn.microsoft.com/en-us/azure/operator-nexus/concepts-network-fabric-read-only-commands |
| Validate Nexus Network Fabric cabling with diagnostic APIs | https://learn.microsoft.com/en-us/azure/operator-nexus/how-to-validate-cables |
| Use bare metal machine platform commands for recovery | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-baremetal-functions |
| Run emergency bare metal actions with nexusctl | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-baremetal-nexusctl |
| Use run-data-extract to troubleshoot Nexus bare-metal | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-baremetal-run-data-extract |
| Troubleshoot bare metal machines with az baremetalmachine run-read-command | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-baremetal-run-read |
| Resolve preflight check failures for Nexus runtime upgrades | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-cluster-runtime-upgrade-preflight-checks |
| Gather trace IDs for Nexus PersistentVolumeClaim failures | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-gather-pvc-trace-id |
| Collect diagnostic data for Nexus VM console issues | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-gather-vm-console-data |
| Run Nexus Kubernetes cluster log collector script | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-kubernetes-cluster-log-collector-script |
| Run read-only diagnostics on Nexus storage appliances | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-storage-run-read |
| Fix Accepted cluster hydration issues in Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-accepted-cluster-hydration |
| Diagnose and fix degraded bare metal machines in Azure Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-bare-metal-machine-degraded |
| Troubleshoot bare-metal machine provisioning in Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-bare-metal-machine-provisioning |
| Resolve warning status on bare metal machines in Azure Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-bare-metal-machine-warning |
| Fix Nexus ClusterConnectionStatus Disconnected heartbeat issues | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-cluster-heartbeat-connection-status-disconnected |
| Recover control plane quorum loss in Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-control-plane-quorum |
| Resolve CSN storage pod containers stuck in creating | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-csn-storage-pod-container-stuck-in-creating |
| Troubleshoot DNS issues in Nexus Network Fabric | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-dns-issues |
| Fix failed volume attachment alerts in Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-failed-volume-attachments |
| Fix Azure Operator Nexus hardware validation failures | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-hardware-validation-failure |
| Troubleshoot CSN-connected internet host access in AKS hybrid | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-internet-host-virtual-machine |
| Troubleshoot isolation domain provisioning failures in Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-isolation-domain |
| Troubleshoot dual-stack Nexus Kubernetes cluster configuration | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-kubernetes-cluster-dual-stack-configuration |
| Resolve Ready, SchedulingDisabled nodes after Nexus runtime upgrade | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-kubernetes-cluster-node-cordoned |
| Fix Nexus workloads stuck after node power failure | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-kubernetes-cluster-stuck-workloads-due-to-power-failure |
| Check and fix LACP bonding on Nexus physical hosts | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-lacp-bonding |
| Troubleshoot container memory limit issues in Nexus clusters | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-memory-limits |
| Resolve common issues with multiple Nexus storage appliances | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-multiple-storage-appliances |
| Fix Neighbor Group creation AuthorizationFailed errors in Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-neighbor-group-creation-error |
| Troubleshoot unhealthy NFS pods in Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-network-file-system-unhealthy |
| Fix Nexus Kubernetes pods stuck in ContainerCreating | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-nexus-kubernetes-cluster-pods |
| Troubleshoot Nexus KubernetesCluster node in NotReady | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-not-ready-kubernetes-cluster-node |
| Troubleshoot packet loss between NAKS worker nodes | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-packet-loss |
| Troubleshoot Operator Nexus bare metal server actions | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-reboot-reimage-replace |
| Interpret and act on Azure Operator Nexus resource health alerts | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-resource-health-alerts |
| Resolve storage control plane connectivity issues in Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-storage-control-plane-disconnected |
| Troubleshoot TWAMP over UDP failures with NAT in Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-twamp-udp-not-working |
| Troubleshoot unhealthy CSI storage pods in Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-unhealthy-container-storage-interface |
| Fix unhealthy or degraded storage appliances in Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-unhealthy-degraded-storage-appliance |
| Troubleshoot Azure Arc enrollment for Nexus VMs with managed identities | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-virtual-machines-arc-enroll-with-managed-identities |
| Fix VM errors after restarting Nexus bare-metal machines | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-vm-error-after-reboot |

### Best Practices
| Topic | URL |
|-------|-----|
| Best practices for bare metal machine lifecycle operations in Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-bare-metal-best-practices |
| Perform storage appliance component repairs in Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-storage-device-repair |

### Decision Making
| Topic | URL |
|-------|-----|
| Plan resource placement for Nexus Kubernetes clusters | https://learn.microsoft.com/en-us/azure/operator-nexus/concepts-nexus-kubernetes-placement |
| Map Operator Nexus versions to supported storage software | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-near-edge-storage-supported-versions |
| Select Azure Operator Nexus Kubernetes VM SKUs | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-nexus-kubernetes-cluster-sku |
| Choose appropriate Azure Operator Nexus SKUs | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-operator-nexus-skus |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design rack-resilient control plane for Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/concepts-rack-resiliency |
| Design near-edge storage architecture for Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-near-edge-storage |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Use Nexus Kubernetes persistent storage classes effectively | https://learn.microsoft.com/en-us/azure/operator-nexus/concepts-storage-kubernetes |
| Plan storage capacity with multiple Nexus appliances | https://learn.microsoft.com/en-us/azure/operator-nexus/concepts-storage-multiple-appliances |
| Restart Nexus Kubernetes nodes and handle timeouts | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-kubernetes-cluster-action-restart |
| Meet technical requirements for Nexus isolation domains | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-isolation-domain-technical-requirements |
| Review Azure Operator Nexus limits and quotas | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-limits-and-quotas |
| Supported Kubernetes versions and lifecycle in Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-nexus-kubernetes-cluster-supported-versions |
| Operator Nexus platform runtime upgrade cadence and support | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-nexus-platform-runtime-upgrades |
| Check supported software versions for Azure Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-supported-software-versions |
| Troubleshoot log disruption after 48-hour Nexus disconnection | https://learn.microsoft.com/en-us/azure/operator-nexus/troubleshoot-logs-disrupted-post-prolonged-disconnection |

### Security
| Topic | URL |
|-------|-----|
| Configure cross-subscription permissions for Nexus Network Fabric | https://learn.microsoft.com/en-us/azure/operator-nexus/concepts-cross-subscription-deployments-required-rbac-for-network-fabric |
| Automate Nexus Network Fabric operator password rotation v1 | https://learn.microsoft.com/en-us/azure/operator-nexus/concepts-password-rotation-v1 |
| Configure access and identity for Azure Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/concepts-security-access-identity |
| Configure customer Key Vault for Nexus credential rotation | https://learn.microsoft.com/en-us/azure/operator-nexus/how-to-credential-manager-key-vault |
| Apply ACLs to Azure Operator Nexus resources | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-apply-access-control-list |
| Manage emergency SSH access to BMCs with bmckeyset in Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-baremetal-bmc-ssh |
| Manage emergency SSH access to bare metal machines with baremetalmachinekeyset | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-baremetal-bmm-ssh |
| Rotate and resynchronize certificates in Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-certificate-rotation |
| Use managed identities and user resources in Operator Nexus clusters | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-cluster-managed-identity-user-provided-resources |
| Configure SSH ACLs on Nexus management VPN NNI | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-configure-acls-for-ssh-management-on-access-vpn |
| Configure Network TAP rules with UAMI-based access in Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-configure-network-tap-rules-with-user-assigned-managed-identity |
| Configure ACLs for Azure Operator Nexus networks | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-create-access-control-list |
| Manage Azure Operator Nexus credential rotation lifecycle | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-credential-rotation |
| Delete ACLs from Azure Operator Nexus resources | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-delete-access-control-list |
| Enable or disable vulnerability scanning in Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-enable-disable-vulnerability-scanning |
| Configure system-assigned managed identity for Nexus NFC | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-enable-system-assigned-managed-identity-for-network-fabric-controller |
| Enable SAMI and roles for Nexus Network Fabric | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-enable-system-assigned-managed-identity-for-network-fabric-resource |
| Configure Entra ID RBAC for Nexus Kubernetes | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-kubernetes-cluster-aad-rbac |
| Securely connect to Azure Operator Nexus clusters | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-kubernetes-cluster-connect |
| Install Defender for Containers on Nexus clusters | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-kubernetes-cluster-install-microsoft-defender |
| Configure and rotate SSH keys on Nexus cluster nodes | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-kubernetes-cluster-manage-ssh-key |
| Restrict serial port access and set timeouts on Nexus terminal servers | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-restrict-serial-port-access-and-set-timeout-on-terminal-server |
| Set up Method D v2.0 secure break-glass access in Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-set-up-break-glass-access |
| Configure in-band break-glass management for Nexus Network Fabric | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-set-up-break-glass-access-using-in-band-management |
| Configure Defender for Cloud for Azure Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-set-up-defender-for-cloud-security |
| Update ACL configurations on Azure Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-update-access-control-list |
| Update ExpressRoute authorization keys in Azure Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-update-expressroute-authorization-key |
| Configure customer-managed Key Vault for Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-usage-guide-for-customer-managed-key-vault |
| Apply Azure Policy to secure Nexus resources | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-use-azure-policy |
| Use Method D v2.0 break-glass access for Nexus fabric devices | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-use-break-glass-access |
| Use Secret Rotation v1 for Nexus network fabric credentials | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-use-password-rotation-v1 |
| Use VM Console Service for secure Nexus VM access | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-use-vm-console-service |
| Enroll Nexus VMs with Azure Arc via public relay MI | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-virtual-machines-arc-enroll-with-managed-identities |
| Create Nexus VMs with managed identities and authenticate | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-virtual-machines-authenticate-with-managed-identities |
| Configure access control list traffic policies in Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-acl-configuration |
| Use ACL configuration examples in Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-acl-examples |

### Configuration
| Topic | URL |
|-------|-----|
| Author cluster.jsonc templates for Nexus clusters | https://learn.microsoft.com/en-us/azure/operator-nexus/cluster-jsonc-example |
| Define cluster.parameters.jsonc for multi-rack Nexus clusters | https://learn.microsoft.com/en-us/azure/operator-nexus/cluster-parameters-jsonc-example |
| Use clusterManager.jsonc template for Nexus deployment | https://learn.microsoft.com/en-us/azure/operator-nexus/clustermanager-jsonc-example |
| Configure clusterManager.parameters.jsonc for Nexus clusters | https://learn.microsoft.com/en-us/azure/operator-nexus/clustermanager-parameters-jsonc-example |
| Apply A/B staged configuration updates in Nexus Fabric | https://learn.microsoft.com/en-us/azure/operator-nexus/concepts-ab-staged-commit-configuration-update-commit-workflow |
| Define and apply access control lists in Nexus Network Fabric | https://learn.microsoft.com/en-us/azure/operator-nexus/concepts-access-control-lists |
| Use commit workflow v2 for Nexus Network Fabric changes | https://learn.microsoft.com/en-us/azure/operator-nexus/concepts-commit-workflow-v2 |
| Disable BGP neighbors using Nexus read-write commands | https://learn.microsoft.com/en-us/azure/operator-nexus/concepts-disable-border-gateway-protocol-neighbors |
| Disable networks in enabled Layer 3 isolation domains safely | https://learn.microsoft.com/en-us/azure/operator-nexus/concepts-disable-internal-external-networks-enabled-layer-3-isolation-domain |
| Monitor and detect configuration drift in Nexus Network Fabric | https://learn.microsoft.com/en-us/azure/operator-nexus/concepts-network-fabric-configuration-monitoring |
| Modify Nexus Fabric devices using read-write commands | https://learn.microsoft.com/en-us/azure/operator-nexus/concepts-network-fabric-read-write-commands |
| Batch and commit Nexus Network Fabric configuration updates | https://learn.microsoft.com/en-us/azure/operator-nexus/concepts-network-fabric-resource-update-commit |
| Model terminal servers as Azure Operator Nexus ARM resources | https://learn.microsoft.com/en-us/azure/operator-nexus/concepts-terminal-server-as-resource |
| Customize CoreDNS and node-local-dns in Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/how-to-customize-kubernetes-cluster-dns |
| Create and manage IP prefixes and rules in Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/how-to-ip-prefixes |
| Create and manage route policies in Operator Nexus Network Fabric | https://learn.microsoft.com/en-us/azure/operator-nexus/how-to-route-policy |
| Append custom suffixes to Nexus interface descriptions | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-append-custom-suffix-to-interface-descriptions |
| Check runtime versions of Operator Nexus components | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-check-runtime-version |
| Manage cluster metrics configurations in Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-cluster-metrics-configuration-management |
| Use parameterized templates for Nexus cluster runtime upgrades | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-cluster-runtime-upgrade-template |
| Configure PauseAfterRack strategy for Nexus runtime upgrades | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-cluster-runtime-upgrade-with-pauseafterrack-strategy |
| Configure BGP prefix limits on CE devices in Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-configure-bgp-prefix-limit-on-customer-edge-devices |
| Configure BYO storage and UAMI for Nexus Network Fabric | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-configure-bring-your-own-storage-network-fabric |
| Configure and manage Azure Operator Nexus clusters | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-configure-cluster |
| Configure diagnostic settings and config drift monitoring in Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-configure-diagnostic-settings-monitor-configuration-differences |
| Configure L2 and L3 isolation domains in Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-configure-isolation-domain |
| Configure VRF route prefix limits for IPv4/IPv6 on AON CE devices | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-configure-virtual-routing-forwarding-route-prefix-limits-on-devices |
| Delete Layer 3 isolation domains safely in Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-delete-layer-3-isolation-domains |
| Disable cgroupsv2 on Nexus Kubernetes nodes | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-disable-cgroupsv2 |
| Disable or enable Nexus network interfaces administratively | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-disable-enable-network-interface |
| Disable internal and external networks in Nexus L3 isolation domains | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-disable-internal-external-networks-enabled-layer-3-isolation-domain |
| Enable or disable BMP log streaming for Nexus fabric resources | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-enable-log-streaming |
| Enable Micro-BFD on CE and PE devices in Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-enable-micro-bfd |
| Install Azure CLI extensions for Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-install-cli-extensions |
| Configure and manage Nexus Kubernetes agent pools | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-kubernetes-cluster-agent-pools |
| Customize Nexus worker nodes using DaemonSets | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-kubernetes-cluster-customize-workers |
| Configure dual-stack networking for Nexus Kubernetes | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-kubernetes-cluster-dual-stack |
| Manage Kubernetes cluster features in Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-kubernetes-cluster-features |
| Enable huge pages on Nexus Kubernetes node pools | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-kubernetes-cluster-huge-pages |
| Configure service load balancers in Nexus Kubernetes | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-kubernetes-service-load-balancer |
| Query supported Kubernetes versions in Azure Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-list-supported-kubernetes-versions |
| Monitor packet rates for Nexus fabric interfaces in Azure portal | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-monitor-interface-packet-rate |
| Configure monitoring for Nexus Kubernetes clusters | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-monitor-naks-cluster |
| Monitor VNF virtual machines on Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-monitor-virtualized-network-functions-virtual-machines |
| Configure QoS settings for Azure Operator Nexus network fabric | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-network-fabric-quality-of-service |
| Deploy Azure Operator Nexus instance via template | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-nexus-instance-deployment-template |
| Reboot Nexus network devices using graceful and ungraceful modes | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-reboot-network-device |
| Rotate Azure Local Operator Nexus cluster credentials | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-rotate-credential-api |
| Configure administrative lock for Nexus Network Fabric | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-set-administrative-lock-or-unlock-for-network-fabric |
| Track Nexus asynchronous operations via Azure CLI | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-track-async-operations-cli |
| Perform A/B staged configuration updates with Nexus commit workflow | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-use-ab-staged-commit-configuration-update-commit-workflow |
| Use Commit Workflow v2 to manage Nexus configuration changes | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-use-commit-workflow-v2 |
| Configure MDE runtime protection for Operator Nexus clusters | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-use-mde-runtime-protection |
| Configure placement hints for Nexus virtual machines | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-virtual-machine-placement-hints |
| Configure and interpret Azure Operator Nexus log categories | https://learn.microsoft.com/en-us/azure/operator-nexus/list-logs-available |
| Configure PE-CE connectivity for Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-customer-edge-provider-edge-connectivity |
| Configure Azure Operator Nexus isolation domains | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-isolation-domain-configuration |
| Use isolation domain configuration examples in Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-isolation-domain-configuration-examples |
| Configure Azure Operator Nexus cluster password via Key Vault URI | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-key-vault-credential |
| Assign near-edge BareMetal machine roles in Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-near-edge-baremetal-machine-roles |
| Configure neighbor groups in Azure Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-neighbor-group-configuration |
| Use Network Fabric Controller internal service metrics | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-network-fabric-controller-metrics |
| Apply route policy configuration examples in Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-nexus-route-policy-config-examples |
| Manage route policy operations in Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-nexus-route-policy-operations |
| Monitor Azure Operator Nexus Ethernet metrics | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-operator-nexus-observability-metrics |
| Configure route policies in Azure Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/reference-route-policy-configuration |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Configure Network Packet Broker TAP rules in Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-configure-network-packet-broker |

### Deployment
| Topic | URL |
|-------|-----|
| Prepare Azure Operator Nexus platform deployment prerequisites | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-platform-prerequisites |
| Replace a terminal server in Azure Operator Nexus Network Fabric | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-replace-terminal-server |
| Pre-validate and upgrade Azure Operator Nexus fabric | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-upgrade-nexus-fabric |
| Use template to upgrade Azure Operator Nexus fabric | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-upgrade-nexus-fabric-template |
| Upgrade Terminal Server OS in Azure Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-upgrade-os-of-terminal-server |
| Build VM images for Azure Operator Nexus | https://learn.microsoft.com/en-us/azure/operator-nexus/howto-virtual-machine-image |