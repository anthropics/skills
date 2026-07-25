---
name: azure-kubernetes-service
description: Expert knowledge for Azure Kubernetes Service (AKS) development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when running AI/ML or Wasm workloads, Istio/Dapr add-ons, Fleet rollouts, GPUs, or PCI-compliant clusters, and other Azure Kubernetes Service (AKS) related development tasks. Not for Azure Container Apps (use azure-container-apps), Azure Container Instances (use azure-container-instances), Azure Red Hat OpenShift (use azure-redhat-openshift).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Kubernetes Service (AKS) Skill

This skill provides expert guidance for Azure Kubernetes Service (AKS). Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L62 | Diagnosing and fixing AKS cluster/workload issues (network, DNS, GPU, encryption, upgrades, Fleet), using logs/metrics/tools (Desktop Insights, ACNS, NPD, Inspektor Gadget, KMS, kubelet) for troubleshooting. |
| Best Practices | L63-L109 | AKS operational and security best practices: performance, scaling, cost, GPU/MLOps, storage/backup, networking, pod security, upgrades/resiliency, PCI, and large-scale cluster operations. |
| Decision Making | L110-L160 | Guidance for planning AKS architectures and migrations: sizing, networking, upgrades, cost optimization, compliance, VM/node options, container OS choices, and comparisons with other platforms/services. |
| Architecture & Design Patterns | L161-L185 | Patterns and reference architectures for AKS: HA/DR (active-active/passive/cold), multi-region, PCI workloads, ingress/networking, node pools, stateful upgrades, Fleet rollout, and scaling options. |
| Limits & Quotas | L186-L211 | AKS capacity, limits, quotas, version lifecycles, performance constraints, and scaling behaviors for clusters, node pools, networking, Istio, KEDA, Fleet, and regional VM SKUs. |
| Security | L212-L293 | Securing AKS clusters: identity/RBAC, Entra auth, workload identity, network policies, encryption, CIS hardening, PCI controls, secure node access, and Azure Policy-based governance. |
| Configuration | L294-L444 | Configuring AKS clusters, networking, storage, GPUs, autoscaling, security, cost optimization, and managed add-ons (Istio, Dapr, Kueue, Kafka, MongoDB, PostgreSQL, Valkey, NetApp, Fleet). |
| Integrations & Coding Patterns | L445-L473 | Patterns for integrating AKS with AI/LLM tooling (KAITO, Ray, MCP), storage, security (Key Vault, CSI), monitoring, autoscaling, dev tools, and external services for production workloads. |
| Deployment | L474-L522 | Deploying and upgrading AKS clusters and apps, including CI/CD, service meshes, autoscaling, storage/migration, AI/ML and Wasm workloads, and production-ready infrastructure setup. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Diagnose and fix common Agentic CLI for AKS issues | https://learn.microsoft.com/en-us/azure/aks/agentic-cli-for-aks-troubleshoot |
| Diagnose AKS workloads with AKS Desktop AI assistant | https://learn.microsoft.com/en-us/azure/aks/aks-desktop-deploy-ai-assistant |
| Use AKS Desktop Insights to troubleshoot workloads | https://learn.microsoft.com/en-us/azure/aks/aks-desktop-deploy-troubleshooting |
| Support and troubleshooting options for Azure Kubernetes Service | https://learn.microsoft.com/en-us/azure/aks/aks-support-help |
| Troubleshoot AKS network issues using ACNS metrics and logs | https://learn.microsoft.com/en-us/azure/aks/container-network-observability-guide |
| Troubleshoot CoreDNS issues in AKS clusters | https://learn.microsoft.com/en-us/azure/aks/coredns-troubleshoot |
| Use Kubernetes events to troubleshoot AKS clusters | https://learn.microsoft.com/en-us/azure/aks/events |
| Diagnose GPU node health with NPD in AKS | https://learn.microsoft.com/en-us/azure/aks/gpu-health-monitoring |
| Troubleshoot Inspektor Gadget extension issues on AKS | https://learn.microsoft.com/en-us/azure/aks/inspektor-gadget-troubleshoot |
| Monitor and troubleshoot AKS KMS etcd encryption | https://learn.microsoft.com/en-us/azure/aks/kms-observability |
| Collect and view kubelet logs from AKS nodes | https://learn.microsoft.com/en-us/azure/aks/kubelet-logs |
| Diagnose and fix common Open Service Mesh add-on issues on AKS | https://learn.microsoft.com/en-us/azure/aks/open-service-mesh-troubleshoot |
| Use AKS security bulletins for vulnerability troubleshooting | https://learn.microsoft.com/en-us/azure/aks/security-bulletins/overview |
| Handle AKS upgrade blocks from deprecated Kubernetes APIs | https://learn.microsoft.com/en-us/azure/aks/stop-cluster-upgrade-api-breaking-changes |
| Troubleshoot Container Network Insights Agent issues on AKS | https://learn.microsoft.com/en-us/azure/aks/troubleshoot-container-network-insights-agent |
| Troubleshoot SNAT port exhaustion for AKS load balancers | https://learn.microsoft.com/en-us/azure/aks/troubleshoot-source-network-address-translation |
| Troubleshoot UDP packet drops in AKS clusters | https://learn.microsoft.com/en-us/azure/aks/troubleshoot-udp-packet-drops |
| Diagnose and resolve Azure AKS upgrade issues | https://learn.microsoft.com/en-us/azure/aks/upgrade-aks-faq |
| Resolve common Windows Server on AKS issues | https://learn.microsoft.com/en-us/azure/aks/windows-faq |
| Identify and migrate preview Azure Kubernetes Fleet CRDs to supported versions | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/howto-migrate-preview-to-ga-fleets |
| Interpret ClusterResourcePlacement status for Fleet Manager | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/howto-understand-placement |
| Access and use Azure Fleet agent logs | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/view-fleet-agent-logs |

### Best Practices
| Topic | URL |
|-------|-----|
| Enable Artifact Streaming in AKS to reduce image pull time | https://learn.microsoft.com/en-us/azure/aks/artifact-streaming |
| Apply AKS deployment and cluster reliability practices | https://learn.microsoft.com/en-us/azure/aks/best-practices-app-cluster-reliability |
| Optimize Azure Kubernetes Service costs effectively | https://learn.microsoft.com/en-us/azure/aks/best-practices-cost |
| Apply GPU best practices on AKS clusters | https://learn.microsoft.com/en-us/azure/aks/best-practices-gpu |
| Apply GPU observability best practices on AKS | https://learn.microsoft.com/en-us/azure/aks/best-practices-gpu-observability |
| Apply MLOps best practices on Azure Kubernetes Service | https://learn.microsoft.com/en-us/azure/aks/best-practices-ml-ops |
| Apply proactive monitoring best practices for AKS clusters | https://learn.microsoft.com/en-us/azure/aks/best-practices-monitoring-proactive |
| Optimize AKS performance and scaling for small to medium workloads | https://learn.microsoft.com/en-us/azure/aks/best-practices-performance-scale |
| Tune AKS for large-scale performance and scaling | https://learn.microsoft.com/en-us/azure/aks/best-practices-performance-scale-large |
| Best practices for AKS ephemeral NVMe disks | https://learn.microsoft.com/en-us/azure/aks/best-practices-storage-nvme |
| Plan resource and security considerations for AKS pod sandboxing | https://learn.microsoft.com/en-us/azure/aks/considerations-pod-sandboxing |
| Enforce AKS deployment safeguards and best practices | https://learn.microsoft.com/en-us/azure/aks/deployment-safeguards |
| Implement pod security best practices on AKS | https://learn.microsoft.com/en-us/azure/aks/developer-best-practices-pod-security |
| Optimize AKS workload resource management practices | https://learn.microsoft.com/en-us/azure/aks/developer-best-practices-resource-management |
| Profile and optimize GPU workloads on AKS | https://learn.microsoft.com/en-us/azure/aks/gpu-profiling |
| Use Image Cleaner to remove vulnerable AKS images | https://learn.microsoft.com/en-us/azure/aks/image-cleaner |
| Use TCP keepalive to improve AKS network resilience | https://learn.microsoft.com/en-us/azure/aks/improve-network-fault-tolerance-in-aks-using-tcp-keepalive |
| Select appropriate Inspektor Gadget tools on AKS | https://learn.microsoft.com/en-us/azure/aks/inspektor-gadget-catalog |
| Apply AKS network policy security best practices | https://learn.microsoft.com/en-us/azure/aks/network-policy-best-practices |
| Plan node image updates for NAP in AKS | https://learn.microsoft.com/en-us/azure/aks/node-auto-provisioning-upgrade-image |
| Configure and monitor AKS node auto-repair | https://learn.microsoft.com/en-us/azure/aks/node-auto-repair |
| Operate cost-optimized AKS clusters at scale | https://learn.microsoft.com/en-us/azure/aks/operate-cost-optimized-scale |
| Use advanced scheduler features effectively in AKS | https://learn.microsoft.com/en-us/azure/aks/operator-best-practices-advanced-scheduler |
| Implement cluster isolation strategies in Azure Kubernetes Service | https://learn.microsoft.com/en-us/azure/aks/operator-best-practices-cluster-isolation |
| Apply AKS cluster security operator best practices | https://learn.microsoft.com/en-us/azure/aks/operator-best-practices-cluster-security |
| Implement container image security best practices in AKS | https://learn.microsoft.com/en-us/azure/aks/operator-best-practices-container-image-management |
| Apply AKS network configuration best practices | https://learn.microsoft.com/en-us/azure/aks/operator-best-practices-network |
| Apply basic scheduler best practices in AKS | https://learn.microsoft.com/en-us/azure/aks/operator-best-practices-scheduler |
| Apply AKS storage and backup operator best practices | https://learn.microsoft.com/en-us/azure/aks/operator-best-practices-storage |
| Protect data on AKS for PCI DSS compliance | https://learn.microsoft.com/en-us/azure/aks/pci-data |
| Apply PCI risk assessment and code practices on AKS | https://learn.microsoft.com/en-us/azure/aks/pci-ra-code-assets |
| Design and validate AKS zone-resilient clusters | https://learn.microsoft.com/en-us/azure/aks/reliability-zone-resiliency-recommendations |
| Load test and validate MongoDB resiliency on AKS | https://learn.microsoft.com/en-us/azure/aks/resiliency-mongodb-cluster |
| Use AKS node pool version rollback safely | https://learn.microsoft.com/en-us/azure/aks/roll-back-node-pool-version |
| Validate MongoDB resiliency during AKS node pool upgrades | https://learn.microsoft.com/en-us/azure/aks/upgrade-mongodb-cluster |
| Handle AKS Linux node reboots using kured | https://learn.microsoft.com/en-us/azure/aks/upgrade-node-image-kured |
| Upgrade AKS node pools and control plane safely | https://learn.microsoft.com/en-us/azure/aks/upgrade-node-pools |
| Plan and execute AKS node OS upgrades safely | https://learn.microsoft.com/en-us/azure/aks/upgrade-os-version |
| Validate Valkey resiliency during AKS node pool upgrades | https://learn.microsoft.com/en-us/azure/aks/upgrade-valkey-aks-nodepool |
| Validate and operate PostgreSQL HA deployments on AKS | https://learn.microsoft.com/en-us/azure/aks/validate-postgresql-ha |
| Load test and validate Valkey cluster resiliency on AKS | https://learn.microsoft.com/en-us/azure/aks/validate-valkey-cluster |
| Apply best practices for AKS Windows containers | https://learn.microsoft.com/en-us/azure/aks/windows-best-practices |
| Control eviction and disruption budgets for Fleet Manager workloads | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/concepts-eviction-disruption |

### Decision Making
| Topic | URL |
|-------|-----|
| Plan and execute migration to Azure Kubernetes Service | https://learn.microsoft.com/en-us/azure/aks/aks-migration |
| Choose VM sizes and generations for AKS workloads | https://learn.microsoft.com/en-us/azure/aks/aks-virtual-machine-sizes |
| Migrate AKS clusters from Availability Sets to VM node pools | https://learn.microsoft.com/en-us/azure/aks/availability-sets-on-aks |
| Choose between AKS and other Azure container services | https://learn.microsoft.com/en-us/azure/aks/compare-container-options-with-aks |
| Choose and run language models on AKS | https://learn.microsoft.com/en-us/azure/aks/concepts-ai-ml-language-models |
| Plan IP address space for Azure AKS clusters | https://learn.microsoft.com/en-us/azure/aks/concepts-network-ip-address-planning |
| Choose and understand legacy CNI options in Azure Kubernetes Service | https://learn.microsoft.com/en-us/azure/aks/concepts-network-legacy-cni |
| Use Azure Advisor recommendations for AKS cost | https://learn.microsoft.com/en-us/azure/aks/cost-advisors |
| Migrate from Dapr OSS to Dapr extension on AKS | https://learn.microsoft.com/en-us/azure/aks/dapr-migration |
| Compare AWS and Azure platforms for EDW workloads | https://learn.microsoft.com/en-us/azure/aks/eks-edw-understand |
| Understand AWS vs Azure differences for web apps | https://learn.microsoft.com/en-us/azure/aks/eks-web-understand |
| Plan migration off Flatcar Container Linux on AKS | https://learn.microsoft.com/en-us/azure/aks/flatcar-container-linux-for-aks |
| Choose AKS Free, Standard, or Premium tiers | https://learn.microsoft.com/en-us/azure/aks/free-standard-pricing-tiers |
| Adopt and migrate to Gen2 VMs for AKS node pools | https://learn.microsoft.com/en-us/azure/aks/generation-2-vms |
| Select AKS Automatic or Standard for workloads | https://learn.microsoft.com/en-us/azure/aks/get-started-aks |
| Choose and plan AKS Kubernetes long-term support | https://learn.microsoft.com/en-us/azure/aks/long-term-support |
| Plan and execute migration from NPM to Cilium in AKS | https://learn.microsoft.com/en-us/azure/aks/migrate-from-npm-to-cilium-network-policy |
| Migrate from open source Istio to AKS Istio add-on using canary strategy | https://learn.microsoft.com/en-us/azure/aks/migration-from-open-source-istio-to-addon |
| Choose and configure monitoring options for AKS | https://learn.microsoft.com/en-us/azure/aks/monitor-aks |
| Choose and configure monitoring options for AKS | https://learn.microsoft.com/en-us/azure/aks/monitor-aks |
| Choose and manage AKS node images | https://learn.microsoft.com/en-us/azure/aks/node-images |
| Map AKS Open Service Mesh policies to Istio add-on | https://learn.microsoft.com/en-us/azure/aks/open-service-mesh-istio-migration-guidance |
| Choose and tune AKS options to reduce costs | https://learn.microsoft.com/en-us/azure/aks/optimize-aks-costs |
| Apply PCI customized approach controls in AKS | https://learn.microsoft.com/en-us/azure/aks/pci-customized-approach-guidance |
| Map AKS controls to PCI DSS 4.0.1 requirements | https://learn.microsoft.com/en-us/azure/aks/pci-requirement-mapping-matrix |
| Perform targeted PCI risk analysis for AKS workloads | https://learn.microsoft.com/en-us/azure/aks/pci-targeted-risk-analysis |
| Design application networking for Azure Kubernetes Service workloads | https://learn.microsoft.com/en-us/azure/aks/plan-application-networking |
| Choose control plane networking options for AKS clusters | https://learn.microsoft.com/en-us/azure/aks/plan-control-plane-networking |
| Plan networking architecture for Azure Kubernetes Service workloads | https://learn.microsoft.com/en-us/azure/aks/plan-networking |
| Select node networking models for Azure Kubernetes Service | https://learn.microsoft.com/en-us/azure/aks/plan-node-networking |
| Plan pod networking strategies for Azure Kubernetes Service | https://learn.microsoft.com/en-us/azure/aks/plan-pod-networking |
| Choose and configure AKS scale-down mode | https://learn.microsoft.com/en-us/azure/aks/scale-down-mode |
| Add and use Azure Spot node pools in AKS | https://learn.microsoft.com/en-us/azure/aks/spot-node-pool |
| Update AKS clusters to new Azure CNI IPAM and data planes | https://learn.microsoft.com/en-us/azure/aks/update-azure-cni |
| Migrate AKS from Basic to Standard Load Balancer | https://learn.microsoft.com/en-us/azure/aks/upgrade-basic-load-balancer-on-aks |
| Plan AKS upgrade capacity and cost constraints | https://learn.microsoft.com/en-us/azure/aks/upgrade-capacity-cost-planning |
| Choose AKS Automatic vs Standard upgrade options | https://learn.microsoft.com/en-us/azure/aks/upgrade-options |
| Select the right AKS upgrade scenario path | https://learn.microsoft.com/en-us/azure/aks/upgrade-scenarios-hub |
| Use Arm64 node pools in AKS for cost efficiency | https://learn.microsoft.com/en-us/azure/aks/use-arm64-vms |
| Choose and use AKS Virtual Machines node pools | https://learn.microsoft.com/en-us/azure/aks/virtual-machines-node-pools |
| Choose between AKS Automatic and Standard clusters | https://learn.microsoft.com/en-us/azure/aks/what-is-aks |
| Use and migrate from Windows Server Annual Channel on AKS | https://learn.microsoft.com/en-us/azure/aks/windows-annual-channel |
| Plan Windows vs. Linux containers on AKS | https://learn.microsoft.com/en-us/azure/aks/windows-vs-linux-containers |
| Choose a migration path to AKS Workload ID | https://learn.microsoft.com/en-us/azure/aks/workload-identity-migrate-from-pod-identity |
| Choose the right Azure Kubernetes Fleet Manager configuration | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/concepts-choosing-fleet |
| Migrate Kubernetes update workflows from Terraform to Fleet | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/howto-migrate-updates-from-terraform |
| Upgrade Azure Kubernetes Fleet Manager from hubless to hubful | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/upgrade-hub-cluster-type |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Active-active high availability pattern for AKS | https://learn.microsoft.com/en-us/azure/aks/active-active-solution |
| Active-passive disaster recovery pattern for AKS | https://learn.microsoft.com/en-us/azure/aks/active-passive-solution |
| Apply proven AKS production upgrade patterns | https://learn.microsoft.com/en-us/azure/aks/aks-production-upgrade-strategies |
| Use blue-green node pool upgrades in AKS | https://learn.microsoft.com/en-us/azure/aks/blue-green-node-pool-upgrade |
| Choose GPU partitioning strategies in AKS | https://learn.microsoft.com/en-us/azure/aks/concepts-gpu-partitioning |
| Choose ingress networking options for AKS clusters | https://learn.microsoft.com/en-us/azure/aks/concepts-network-ingress |
| Rearchitect AWS EDW workload for Azure AKS | https://learn.microsoft.com/en-us/azure/aks/eks-edw-rearchitect |
| Rearchitect AWS EKS web app and WAF for AKS | https://learn.microsoft.com/en-us/azure/aks/eks-web-rearchitect |
| Isolate AKS node pools with unique subnets | https://learn.microsoft.com/en-us/azure/aks/node-pool-unique-subnet |
| Passive-cold disaster recovery pattern for AKS | https://learn.microsoft.com/en-us/azure/aks/passive-cold-solution |
| Design AKS architecture for PCI DSS 4.0.1 workloads | https://learn.microsoft.com/en-us/azure/aks/pci-intro |
| Review summary of AKS PCI reference architecture | https://learn.microsoft.com/en-us/azure/aks/pci-summary |
| Use proximity placement groups to reduce AKS latency | https://learn.microsoft.com/en-us/azure/aks/reduce-latency-ppg |
| Multi-region AKS deployment models and trade-offs | https://learn.microsoft.com/en-us/azure/aks/reliability-multi-region-deployment-models |
| Use stateful workload upgrade patterns on AKS | https://learn.microsoft.com/en-us/azure/aks/stateful-workload-upgrades |
| Design and migrate stateful workloads on AKS | https://learn.microsoft.com/en-us/azure/aks/stateful-workloads-overview |
| Architect Valkey clusters on AKS for resilience | https://learn.microsoft.com/en-us/azure/aks/valkey-overview |
| Scale AKS workloads with virtual nodes and ACI | https://learn.microsoft.com/en-us/azure/aks/virtual-nodes |
| Manage workload drift with Fleet applyStrategy | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/concepts-placement-drift |
| Control Fleet takeover of existing workloads | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/concepts-placement-takeover |
| Design rollout strategies for Fleet resource placement | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/concepts-rollout-strategy |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Track AKS on Azure Local version and feature changes | https://learn.microsoft.com/en-us/azure/aks/aksarc/aks-whats-new-local |
| Use managed system node pools in AKS Automatic | https://learn.microsoft.com/en-us/azure/aks/automatic/aks-automatic-managed-system-node-pools-about |
| Deploy AKS Automatic clusters in custom virtual networks | https://learn.microsoft.com/en-us/azure/aks/automatic/quick-automatic-custom-network |
| Create AKS Automatic clusters with pod readiness SLA | https://learn.microsoft.com/en-us/azure/aks/automatic/quick-automatic-managed-network |
| Create private AKS Automatic clusters in custom networks | https://learn.microsoft.com/en-us/azure/aks/automatic/quick-automatic-private-custom-network |
| Understand AKS preview API lifecycle and deprecation timing | https://learn.microsoft.com/en-us/azure/aks/concepts-preview-api-life-cycle |
| Configure static block allocation for Azure CNI Pod Subnet | https://learn.microsoft.com/en-us/azure/aks/configure-azure-cni-static-block-allocation |
| Understand AKS core concepts and Azure Linux support timelines | https://learn.microsoft.com/en-us/azure/aks/core-aks-concepts |
| Understand AKS limits, quotas, and constraints | https://learn.microsoft.com/en-us/azure/aks/faq |
| Handle AKS identity binding scale and FIC limits | https://learn.microsoft.com/en-us/azure/aks/identity-bindings-concepts |
| Compare latency impact across AKS Istio add-on versions | https://learn.microsoft.com/en-us/azure/aks/istio-latency |
| Understand Istio add-on performance, capacity, and scaling limits on AKS | https://learn.microsoft.com/en-us/azure/aks/istio-scale |
| Understand KEDA limitations and autoscaling behavior in AKS | https://learn.microsoft.com/en-us/azure/aks/keda-about |
| Understand AKS node resource reservations and capacity | https://learn.microsoft.com/en-us/azure/aks/node-resource-reservations |
| Required outbound ports and FQDNs for AKS clusters | https://learn.microsoft.com/en-us/azure/aks/outbound-rules-control-egress |
| Review AKS regional quotas and VM SKU limits | https://learn.microsoft.com/en-us/azure/aks/quotas-skus-regions |
| AKS supported Kubernetes versions and lifecycle rules | https://learn.microsoft.com/en-us/azure/aks/supported-kubernetes-versions |
| Scale AKS with multiple Standard Load Balancers | https://learn.microsoft.com/en-us/azure/aks/use-multiple-standard-load-balancer |
| Configure and manage AKS system node pools | https://learn.microsoft.com/en-us/azure/aks/use-system-pools |
| Kubernetes version support policy for Azure Kubernetes Fleet Manager | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/concepts-fleet-kubernetes-version-support |
| Use Fleet placement snapshots and history limits | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/concepts-placement-snapshots |
| Understand lifecycle limits for Fleet Manager preview APIs | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/concepts-preview-api-lifecycle |

### Security
| Topic | URL |
|-------|-----|
| Apply Conditional Access to AKS clusters and nodes | https://learn.microsoft.com/en-us/azure/aks/access-control-managed-azure-ad |
| Access private AKS clusters using command invoke and Run command | https://learn.microsoft.com/en-us/azure/aks/access-private-cluster |
| Configure service account and workload identity for Agentic CLI | https://learn.microsoft.com/en-us/azure/aks/agentic-cli-for-aks-service-account-workload-identity-setup |
| Configure RBAC permissions for AKS Desktop projects | https://learn.microsoft.com/en-us/azure/aks/aks-desktop-permissions |
| Reference AKS service permissions and roles | https://learn.microsoft.com/en-us/azure/aks/aks-service-permissions |
| Secure AKS API server with authorized IP ranges | https://learn.microsoft.com/en-us/azure/aks/api-server-authorized-ip-ranges |
| Configure AKS API server authorized IP ranges with service tags | https://learn.microsoft.com/en-us/azure/aks/api-server-service-tags |
| Manually configure TLS for AKS Gateway API ingress | https://learn.microsoft.com/en-us/azure/aks/app-routing-gateway-api-tls |
| Use customer-managed keys for AKS managed disk encryption | https://learn.microsoft.com/en-us/azure/aks/azure-disk-customer-managed-keys |
| Manage AKS certificate rotation and autorotation | https://learn.microsoft.com/en-us/azure/aks/certificate-rotation |
| Harden AKS Azure Linux 2.0 nodes to CIS benchmark | https://learn.microsoft.com/en-us/azure/aks/cis-azure-linux |
| Harden AKS Azure Linux 3.0 nodes to CIS benchmark | https://learn.microsoft.com/en-us/azure/aks/cis-azure-linux-v3 |
| Apply CIS Kubernetes benchmark controls in AKS | https://learn.microsoft.com/en-us/azure/aks/cis-kubernetes |
| Apply CIS-aligned Ubuntu security settings for AKS nodes | https://learn.microsoft.com/en-us/azure/aks/cis-ubuntu |
| Align AKS Windows node image with CIS benchmark | https://learn.microsoft.com/en-us/azure/aks/cis-windows |
| Configure secure ACR authentication for AKS clusters | https://learn.microsoft.com/en-us/azure/aks/cluster-container-registry-integration |
| Understand access and identity scenarios in AKS | https://learn.microsoft.com/en-us/azure/aks/concepts-identity |
| Secure network-isolated AKS cluster connectivity requirements | https://learn.microsoft.com/en-us/azure/aks/concepts-network-isolated |
| Restrict kubeconfig access using Azure RBAC in AKS | https://learn.microsoft.com/en-us/azure/aks/control-kubeconfig-access |
| Configure identity-based AKS access to Key Vault via CSI | https://learn.microsoft.com/en-us/azure/aks/csi-secrets-store-identity-access |
| Configure FIPS-compliant node pools in Azure Kubernetes Service | https://learn.microsoft.com/en-us/azure/aks/enable-fips-nodes |
| Enable host-based encryption for AKS node data | https://learn.microsoft.com/en-us/azure/aks/enable-host-encryption |
| Configure Entra ID RBAC authorization for AKS API | https://learn.microsoft.com/en-us/azure/aks/entra-id-authorization |
| Enable Entra ID authentication for AKS control plane | https://learn.microsoft.com/en-us/azure/aks/entra-id-control-plane-authentication |
| Configure external identity providers for AKS authentication | https://learn.microsoft.com/en-us/azure/aks/external-identity-provider-authentication-configure |
| Deploy WireGuard encryption for AKS networking | https://learn.microsoft.com/en-us/azure/aks/how-to-apply-wireguard |
| Set up AKS identity bindings for workload identity | https://learn.microsoft.com/en-us/azure/aks/identity-bindings |
| Enforce signed container image validation on AKS | https://learn.microsoft.com/en-us/azure/aks/image-integrity |
| Restrict AKS pod access to IMDS endpoint | https://learn.microsoft.com/en-us/azure/aks/imds-restriction |
| Plug external CA certificates into AKS Istio add-on | https://learn.microsoft.com/en-us/azure/aks/istio-plugin-ca |
| Configure HTTPS and mTLS secure ingress gateways for AKS Istio add-on | https://learn.microsoft.com/en-us/azure/aks/istio-secure-gateway |
| Secure KEDA-based autoscaling on AKS with workload identity | https://learn.microsoft.com/en-us/azure/aks/keda-workload-identity |
| Authenticate to AKS clusters using kubelogin | https://learn.microsoft.com/en-us/azure/aks/kubelogin-authentication |
| Use Entra ID with Kubernetes RBAC in AKS clusters | https://learn.microsoft.com/en-us/azure/aks/kubernetes-rbac-entra-id |
| Configure Entra service principals for AKS clusters | https://learn.microsoft.com/en-us/azure/aks/kubernetes-service-principal |
| Disable or manage AKS local admin accounts securely | https://learn.microsoft.com/en-us/azure/aks/local-accounts |
| Configure and manage SSH access to AKS nodes | https://learn.microsoft.com/en-us/azure/aks/manage-ssh-node-access |
| Securely connect to AKS cluster nodes for maintenance | https://learn.microsoft.com/en-us/azure/aks/node-access |
| Configure networking and RBAC for NAP-enabled AKS clusters | https://learn.microsoft.com/en-us/azure/aks/node-auto-provisioning-networking |
| Configure AKS node resource group lockdown and deny assignments | https://learn.microsoft.com/en-us/azure/aks/node-resource-group-lockdown |
| Secure AKS access to Azure OpenAI with Entra | https://learn.microsoft.com/en-us/azure/aks/open-ai-secure-access-quickstart |
| Implement anti-phishing controls for AKS PCI access | https://learn.microsoft.com/en-us/azure/aks/pci-anti-phishing-social-engineering |
| Set up continuous security monitoring for AKS PCI | https://learn.microsoft.com/en-us/azure/aks/pci-continuous-security-monitoring |
| Manage cryptography and keys on AKS for PCI DSS | https://learn.microsoft.com/en-us/azure/aks/pci-cryptography-key-management |
| Implement enhanced MFA for AKS PCI environments | https://learn.microsoft.com/en-us/azure/aks/pci-enhanced-mfa-implementation |
| Configure PCI-compliant identity and access for AKS | https://learn.microsoft.com/en-us/azure/aks/pci-identity |
| Deploy malware protection for PCI workloads on AKS | https://learn.microsoft.com/en-us/azure/aks/pci-malware |
| Configure PCI-compliant monitoring and logging on AKS | https://learn.microsoft.com/en-us/azure/aks/pci-monitor |
| Implement PCI-compliant network security for AKS | https://learn.microsoft.com/en-us/azure/aks/pci-network |
| Define security policies for PCI-regulated AKS clusters | https://learn.microsoft.com/en-us/azure/aks/pci-policy |
| Plan security awareness training for AKS PCI teams | https://learn.microsoft.com/en-us/azure/aks/pci-security-awareness-training |
| Secure third-party and supply chain for AKS PCI | https://learn.microsoft.com/en-us/azure/aks/pci-third-party-supply-chain-security |
| Use built-in Azure Policy definitions for AKS | https://learn.microsoft.com/en-us/azure/aks/policy-reference |
| Use pre-created kubelet managed identity in AKS | https://learn.microsoft.com/en-us/azure/aks/pre-created-kubelet-managed-identity |
| Configure network access paths to private AKS clusters | https://learn.microsoft.com/en-us/azure/aks/private-cluster-connect |
| Use PIM for just-in-time AKS cluster access | https://learn.microsoft.com/en-us/azure/aks/privileged-identity-management |
| RDP and SSH access to AKS Windows nodes | https://learn.microsoft.com/en-us/azure/aks/rdp |
| Harden AKS containers with user namespaces, AppArmor, seccomp | https://learn.microsoft.com/en-us/azure/aks/secure-container-access |
| Use Azure Policy regulatory controls for AKS | https://learn.microsoft.com/en-us/azure/aks/security-controls-policy |
| Configure system-assigned managed identity for AKS clusters | https://learn.microsoft.com/en-us/azure/aks/system-assigned-managed-identity |
| Configure Trusted Access for secure AKS API access | https://learn.microsoft.com/en-us/azure/aks/trusted-access-feature |
| Rotate AKS service principal and Entra app credentials | https://learn.microsoft.com/en-us/azure/aks/update-credentials |
| Use Microsoft Entra pod-managed identities in AKS | https://learn.microsoft.com/en-us/azure/aks/use-azure-ad-pod-identity |
| Secure AKS clusters using Azure Policy add-on | https://learn.microsoft.com/en-us/azure/aks/use-azure-policy |
| Enable GMSA for Windows nodes in AKS clusters | https://learn.microsoft.com/en-us/azure/aks/use-group-managed-service-accounts |
| Configure legacy KMS etcd encryption for AKS | https://learn.microsoft.com/en-us/azure/aks/use-kms-etcd-encryption |
| Migrate AKS clusters from KMS v1 to KMS v2 | https://learn.microsoft.com/en-us/azure/aks/use-kms-v2 |
| Configure AKS network policies to secure pod traffic | https://learn.microsoft.com/en-us/azure/aks/use-network-policies |
| Configure OIDC issuer for secure AKS authentication | https://learn.microsoft.com/en-us/azure/aks/use-oidc-issuer |
| Deploy and use pod sandboxing in AKS | https://learn.microsoft.com/en-us/azure/aks/use-pod-sandboxing |
| Configure Pod Security Admission policies in AKS | https://learn.microsoft.com/en-us/azure/aks/use-psa |
| Enable Trusted Launch security for AKS nodes | https://learn.microsoft.com/en-us/azure/aks/use-trusted-launch |
| Enable user-assigned managed identity for AKS clusters | https://learn.microsoft.com/en-us/azure/aks/user-assigned-managed-identity |
| Configure cross-tenant workload identity for AKS | https://learn.microsoft.com/en-us/azure/aks/workload-identity-cross-tenant |
| Configure AKS cluster with Entra Workload Identity | https://learn.microsoft.com/en-us/azure/aks/workload-identity-deploy-cluster |
| Use Microsoft Entra Workload ID with AKS workloads | https://learn.microsoft.com/en-us/azure/aks/workload-identity-overview |
| Assign Azure RBAC roles for Kubernetes Fleet Manager | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/concepts-rbac |
| Use managed identities securely with Azure Kubernetes Fleet Manager | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/use-managed-identity |

### Configuration
| Topic | URL |
|-------|-----|
| Install and configure Agentic CLI for AKS clusters | https://learn.microsoft.com/en-us/azure/aks/agentic-cli-for-aks-install |
| Monitor AI inference metrics on AKS with KAITO | https://learn.microsoft.com/en-us/azure/aks/ai-toolchain-operator-monitoring |
| Create infrastructure for Apache Airflow on AKS | https://learn.microsoft.com/en-us/azure/aks/airflow-create-infrastructure |
| Configure storage and secrets to deploy Airflow on AKS with Helm | https://learn.microsoft.com/en-us/azure/aks/airflow-deploy |
| Configure AKS Communication Manager for maintenance notifications | https://learn.microsoft.com/en-us/azure/aks/aks-communication-manager |
| Manage AKS component versioning and patching strategy | https://learn.microsoft.com/en-us/azure/aks/aks-component-versioning |
| Configure AKS clusters for AKS Desktop compatibility | https://learn.microsoft.com/en-us/azure/aks/aks-desktop-install-cluster-setup |
| Configure AKS Kubernetes end-of-support notifications | https://learn.microsoft.com/en-us/azure/aks/aks-end-of-support-notifications |
| List and filter AKS-supported VM SKUs by region | https://learn.microsoft.com/en-us/azure/aks/aks-list-skus |
| Create and manage AKS-managed GPU node pools | https://learn.microsoft.com/en-us/azure/aks/aks-managed-gpu-nodes |
| Set up custom domains and SSL for AKS application routing | https://learn.microsoft.com/en-us/azure/aks/app-routing-dns-ssl |
| Configure AKS application routing with Gateway API | https://learn.microsoft.com/en-us/azure/aks/app-routing-gateway-api |
| Automate Azure DNS and TLS for AKS Gateway API | https://learn.microsoft.com/en-us/azure/aks/app-routing-gateway-api-dns-tls |
| Configure multiple NGINX ingress controllers and annotations in AKS | https://learn.microsoft.com/en-us/azure/aks/app-routing-nginx-configuration |
| Monitor AKS NGINX ingress metrics with Prometheus | https://learn.microsoft.com/en-us/azure/aks/app-routing-nginx-prometheus |
| Configure automatic upgrade channels for AKS clusters | https://learn.microsoft.com/en-us/azure/aks/auto-upgrade-cluster |
| Configure AKS node OS image autoupgrade channels | https://learn.microsoft.com/en-us/azure/aks/auto-upgrade-node-os-image |
| Install and manage Azure App Configuration extension on AKS | https://learn.microsoft.com/en-us/azure/aks/azure-app-configuration |
| Configure AKS workloads with App Configuration provider | https://learn.microsoft.com/en-us/azure/aks/azure-app-configuration-quickstart |
| Tune Azure App Configuration extension settings for AKS | https://learn.microsoft.com/en-us/azure/aks/azure-app-configuration-settings |
| Configure Azure CNI Overlay networking in AKS | https://learn.microsoft.com/en-us/azure/aks/azure-cni-overlay |
| Configure Azure CNI Powered by Cilium on AKS | https://learn.microsoft.com/en-us/azure/aks/azure-cni-powered-by-cilium |
| Configure Azure NetApp Files for AKS pods | https://learn.microsoft.com/en-us/azure/aks/azure-netapp-files |
| Provision Azure NetApp Files dual-protocol volumes | https://learn.microsoft.com/en-us/azure/aks/azure-netapp-files-dual-protocol |
| Provision Azure NetApp Files NFS volumes on AKS | https://learn.microsoft.com/en-us/azure/aks/azure-netapp-files-nfs |
| Provision Azure NetApp Files SMB volumes on AKS | https://learn.microsoft.com/en-us/azure/aks/azure-netapp-files-smb |
| Create and mount Linux NFS server volumes in AKS | https://learn.microsoft.com/en-us/azure/aks/azure-nfs-volume |
| Configure and use cluster autoscaler on AKS | https://learn.microsoft.com/en-us/azure/aks/cluster-autoscaler |
| Configure and use AKS Cluster Health Monitor checker | https://learn.microsoft.com/en-us/azure/aks/cluster-health-monitor |
| Configure scheduler profiles and plugins in AKS | https://learn.microsoft.com/en-us/azure/aks/configure-aks-scheduler |
| Configure Azure CNI networking for AKS clusters | https://learn.microsoft.com/en-us/azure/aks/configure-azure-cni |
| Configure Azure CNI Pod Subnet dynamic IP allocation | https://learn.microsoft.com/en-us/azure/aks/configure-azure-cni-dynamic-ip-allocation |
| Configure dual-stack IPv4/IPv6 networking in AKS | https://learn.microsoft.com/en-us/azure/aks/configure-dual-stack |
| Configure dual-stack IPv4/IPv6 networking in AKS | https://learn.microsoft.com/en-us/azure/aks/configure-dual-stack |
| Configure kube-proxy backends on AKS clusters | https://learn.microsoft.com/en-us/azure/aks/configure-kube-proxy |
| Configure kubenet networking for Azure Kubernetes Service clusters | https://learn.microsoft.com/en-us/azure/aks/configure-kubenet |
| Configure Standard Load Balancer settings for AKS | https://learn.microsoft.com/en-us/azure/aks/configure-load-balancer-standard |
| Configure AKS scheduler profiles for node bin packing | https://learn.microsoft.com/en-us/azure/aks/configure-node-binpack-scheduler |
| Configure Kueue queues for Ray jobs on AKS | https://learn.microsoft.com/en-us/azure/aks/configure-ray-kueue-queues |
| Configure Static Egress Gateway for AKS outbound IPs | https://learn.microsoft.com/en-us/azure/aks/configure-static-egress-gateway |
| Configure Container Network Observability for AKS monitoring | https://learn.microsoft.com/en-us/azure/aks/container-network-observability-how-to |
| Configure Cilium mTLS encryption on AKS with ACNS | https://learn.microsoft.com/en-us/azure/aks/container-network-security-cilium-mutual-tls-how-to |
| Configure CoreDNS autoscaling settings in AKS | https://learn.microsoft.com/en-us/azure/aks/coredns-autoscale |
| Customize CoreDNS behavior in AKS clusters | https://learn.microsoft.com/en-us/azure/aks/coredns-custom |
| Configure AKS cost analysis for granular allocation | https://learn.microsoft.com/en-us/azure/aks/cost-analysis |
| Monitor and reduce AKS idle costs with cost analysis | https://learn.microsoft.com/en-us/azure/aks/cost-analysis-idle-costs |
| Create Azure infrastructure for MongoDB on AKS | https://learn.microsoft.com/en-us/azure/aks/create-mongodb-infrastructure |
| Configure internal NGINX ingress with private DNS for AKS | https://learn.microsoft.com/en-us/azure/aks/create-nginx-ingress-private-controller |
| Create infrastructure for HA PostgreSQL on AKS with CloudNativePG | https://learn.microsoft.com/en-us/azure/aks/create-postgresql-ha |
| Create Azure infrastructure for Valkey clusters on AKS | https://learn.microsoft.com/en-us/azure/aks/create-valkey-infrastructure |
| Configure Azure Disk persistent volumes in AKS | https://learn.microsoft.com/en-us/azure/aks/create-volume-azure-disk |
| Tune Azure Key Vault CSI Driver configuration on AKS | https://learn.microsoft.com/en-us/azure/aks/csi-secrets-store-configuration-options |
| Configure custom certificate authorities on AKS nodes | https://learn.microsoft.com/en-us/azure/aks/custom-certificate-authority |
| Configure AKS node and kubelet settings safely | https://learn.microsoft.com/en-us/azure/aks/custom-node-configuration |
| Customize resource configuration for AKS managed add-ons | https://learn.microsoft.com/en-us/azure/aks/customize-resource-configuration |
| Configure Dapr extension settings on AKS and Arc | https://learn.microsoft.com/en-us/azure/aks/dapr-settings |
| Delete AKS node pools and understand side effects | https://learn.microsoft.com/en-us/azure/aks/delete-node-pool |
| Schedule and deploy batch jobs with Kueue on AKS | https://learn.microsoft.com/en-us/azure/aks/deploy-batch-jobs-with-kueue |
| Deploy and manage AKS cluster extensions with Azure CLI | https://learn.microsoft.com/en-us/azure/aks/deploy-extensions-az-cli |
| Configure and deploy a MongoDB cluster on AKS | https://learn.microsoft.com/en-us/azure/aks/deploy-mongodb-cluster |
| Deploy a highly available PostgreSQL database on AKS | https://learn.microsoft.com/en-us/azure/aks/deploy-postgresql-ha |
| Provision Ray and Kueue infrastructure on AKS | https://learn.microsoft.com/en-us/azure/aks/deploy-ray-infrastructure |
| Configure and deploy a Valkey cluster on AKS | https://learn.microsoft.com/en-us/azure/aks/deploy-valkey-cluster |
| Configure AKS outbound egress types and behavior | https://learn.microsoft.com/en-us/azure/aks/egress-outboundtype |
| Configure AKS egress with user-defined routes | https://learn.microsoft.com/en-us/azure/aks/egress-udr |
| Create infrastructure for highly available GitHub Actions on AKS with Azure Files | https://learn.microsoft.com/en-us/azure/aks/github-actions-azure-files-create-infrastructure |
| Configure FQDN filtering policies with ACNS on AKS | https://learn.microsoft.com/en-us/azure/aks/how-to-apply-fqdn-filtering-policies |
| Configure L7 network policies with ACNS on AKS | https://learn.microsoft.com/en-us/azure/aks/how-to-apply-l7-policies |
| Configure and use Container Network Insights Agent on AKS | https://learn.microsoft.com/en-us/azure/aks/how-to-configure-container-network-insights-agent |
| Configure AKS container network logging with ACNS | https://learn.microsoft.com/en-us/azure/aks/how-to-configure-container-network-logs |
| Configure AKS container network metrics filtering with Cilium | https://learn.microsoft.com/en-us/azure/aks/how-to-configure-container-network-metrics-filtering |
| Enable and configure eBPF Host Routing on AKS | https://learn.microsoft.com/en-us/azure/aks/how-to-enable-ebpf-host-routing |
| Configure HTTP proxy settings for AKS nodes | https://learn.microsoft.com/en-us/azure/aks/http-proxy |
| Install and configure Inspektor Gadget on AKS | https://learn.microsoft.com/en-us/azure/aks/inspektor-gadget-configure |
| Create and use internal load balancers in AKS | https://learn.microsoft.com/en-us/azure/aks/internal-lb |
| Configure Istio Gateway API ingress on AKS | https://learn.microsoft.com/en-us/azure/aks/istio-gateway-api |
| Configure MeshConfig and supported settings for Istio add-on on AKS | https://learn.microsoft.com/en-us/azure/aks/istio-meshconfig |
| Enable and configure native sidecar mode for Istio add-on on AKS | https://learn.microsoft.com/en-us/azure/aks/istio-native-sidecar |
| Configure telemetry and logging for AKS Istio-based service mesh | https://learn.microsoft.com/en-us/azure/aks/istio-telemetry |
| Configure monitoring and networking for Kafka on AKS using Strimzi | https://learn.microsoft.com/en-us/azure/aks/kafka-configure |
| Deploy Strimzi and a Kafka cluster on AKS | https://learn.microsoft.com/en-us/azure/aks/kafka-deploy |
| Prepare Azure infrastructure for Kafka on AKS with Strimzi | https://learn.microsoft.com/en-us/azure/aks/kafka-infrastructure |
| Configure KMS data encryption for AKS secrets | https://learn.microsoft.com/en-us/azure/aks/kms-data-encryption |
| Manage AKS Kubernetes resources through Azure portal UI | https://learn.microsoft.com/en-us/azure/aks/kubernetes-portal |
| Install and configure Kueue for batch on AKS | https://learn.microsoft.com/en-us/azure/aks/kueue-overview |
| Limit AKS egress traffic using Azure Firewall | https://learn.microsoft.com/en-us/azure/aks/limit-egress-traffic |
| Use public Standard Load Balancer with AKS | https://learn.microsoft.com/en-us/azure/aks/load-balancer-standard |
| Configure LocalDNS settings for Azure Kubernetes Service | https://learn.microsoft.com/en-us/azure/aks/localdns-custom |
| Abort long-running AKS cluster operations via API | https://learn.microsoft.com/en-us/azure/aks/manage-abort-operations |
| Use managed namespaces to isolate AKS workloads | https://learn.microsoft.com/en-us/azure/aks/managed-namespaces |
| Configure monitoring for MongoDB clusters on AKS with PMM | https://learn.microsoft.com/en-us/azure/aks/monitor-aks-mongodb |
| Reference for AKS monitoring data and metrics | https://learn.microsoft.com/en-us/azure/aks/monitor-aks-reference |
| Configure GPU metrics collection and monitoring in AKS | https://learn.microsoft.com/en-us/azure/aks/monitor-gpu-metrics |
| Configure NAT gateway options for Azure Kubernetes Service | https://learn.microsoft.com/en-us/azure/aks/nat-gateway |
| Create and configure network-isolated AKS clusters | https://learn.microsoft.com/en-us/azure/aks/network-isolated |
| Configure AKS pod eviction on VM freeze events | https://learn.microsoft.com/en-us/azure/aks/node-auto-drain-evict-on-freeze |
| Configure AKSNodeClass for node auto-provisioning in AKS | https://learn.microsoft.com/en-us/azure/aks/node-auto-provisioning-aksnodeclass |
| Create NAP-enabled AKS clusters in custom VNets | https://learn.microsoft.com/en-us/azure/aks/node-auto-provisioning-custom-vnet |
| Configure disruption policies for NAP nodes in AKS | https://learn.microsoft.com/en-us/azure/aks/node-auto-provisioning-disruption |
| Configure AKS Node Auto-Provisioning node pool settings | https://learn.microsoft.com/en-us/azure/aks/node-auto-provisioning-node-pools |
| Snapshot AKS node pools for repeatable environments | https://learn.microsoft.com/en-us/azure/aks/node-pool-snapshot |
| Configure NVIDIA GPU Operator on AKS clusters | https://learn.microsoft.com/en-us/azure/aks/nvidia-gpu-operator |
| Download and configure the OSM client binary for AKS | https://learn.microsoft.com/en-us/azure/aks/open-service-mesh-binary |
| Configure cost-optimized add-on scaling in AKS | https://learn.microsoft.com/en-us/azure/aks/optimized-addon-scaling |
| Configure planned maintenance windows for AKS upgrades | https://learn.microsoft.com/en-us/azure/aks/planned-maintenance |
| Configure AKS private API server access across VNets | https://learn.microsoft.com/en-us/azure/aks/private-apiserver-vnet-integration-cluster |
| Configure and deploy private AKS clusters with CLI/Terraform | https://learn.microsoft.com/en-us/azure/aks/private-clusters |
| Manually and automatically scale AKS node pools | https://learn.microsoft.com/en-us/azure/aks/scale-node-pools |
| Enable shared health probes for AKS Services | https://learn.microsoft.com/en-us/azure/aks/shared-health-probes |
| Start and stop AKS node pools to optimize costs | https://learn.microsoft.com/en-us/azure/aks/start-stop-nodepools |
| Use static public IPs with AKS load balancers | https://learn.microsoft.com/en-us/azure/aks/static-ip |
| Update Key Vault mode for AKS KMS encryption | https://learn.microsoft.com/en-us/azure/aks/update-kms-key-vault |
| Configure rolling upgrade settings for AKS node pools | https://learn.microsoft.com/en-us/azure/aks/upgrade-aks-node-pools-rolling |
| Configure Advanced Container Networking Services on AKS | https://learn.microsoft.com/en-us/azure/aks/use-advanced-container-networking-services |
| Configure AMD GPU node pools on AKS | https://learn.microsoft.com/en-us/azure/aks/use-amd-gpus |
| Run AKS node pools on Azure Dedicated Hosts | https://learn.microsoft.com/en-us/azure/aks/use-azure-dedicated-hosts |
| Configure custom CNI plugins for Azure Kubernetes Service | https://learn.microsoft.com/en-us/azure/aks/use-byo-cni |
| Use eTags for concurrency control in AKS APIs | https://learn.microsoft.com/en-us/azure/aks/use-etags |
| Use Kubernetes node pool labels effectively in AKS | https://learn.microsoft.com/en-us/azure/aks/use-labels |
| Configure Metrics Server VPA on AKS clusters | https://learn.microsoft.com/en-us/azure/aks/use-metrics-server-vertical-pod-autoscaler |
| Configure node auto-provisioning in Azure Kubernetes Service | https://learn.microsoft.com/en-us/azure/aks/use-node-auto-provisioning |
| Configure instance-level public IPs for AKS nodes | https://learn.microsoft.com/en-us/azure/aks/use-node-public-ips |
| Configure node taints for workload scheduling in AKS | https://learn.microsoft.com/en-us/azure/aks/use-node-taints |
| Configure and use NVIDIA GPUs on AKS clusters | https://learn.microsoft.com/en-us/azure/aks/use-nvidia-gpu |
| Configure Premium SSD v2 disks for AKS workloads | https://learn.microsoft.com/en-us/azure/aks/use-premium-v2-disks |
| Configure Pod Security Admission in AKS clusters | https://learn.microsoft.com/en-us/azure/aks/use-psa |
| Configure and apply Azure tags in AKS | https://learn.microsoft.com/en-us/azure/aks/use-tags |
| Enable and configure Ultra Disks on AKS | https://learn.microsoft.com/en-us/azure/aks/use-ultra-disks |
| Deploy and manage Vertical Pod Autoscaler on AKS | https://learn.microsoft.com/en-us/azure/aks/use-vertical-pod-autoscaler |
| Configure Windows GPU node pools on AKS | https://learn.microsoft.com/en-us/azure/aks/use-windows-gpu |
| Use Windows HostProcess and privileged containers on AKS | https://learn.microsoft.com/en-us/azure/aks/use-windows-hpc |
| Reference for AKS Vertical Pod Autoscaler API | https://learn.microsoft.com/en-us/azure/aks/vertical-pod-autoscaler-api-reference |
| Configure AKS virtual nodes with Azure CLI and CNI | https://learn.microsoft.com/en-us/azure/aks/virtual-nodes-cli |
| Configure AKS virtual nodes using Azure portal | https://learn.microsoft.com/en-us/azure/aks/virtual-nodes-portal |
| Create AKS Windows node pools using containerd runtime | https://learn.microsoft.com/en-us/azure/aks/windows-containerd |
| Access the Kubernetes API of an Azure Kubernetes Fleet hub cluster | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/access-fleet-hub-cluster-kubernetes-api |
| Configure cross-cluster networking in Azure Kubernetes Fleet | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/howto-configure-use-cross-cluster-networking |
| Set up DNS-based multi-cluster load balancing in Fleet | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/howto-dns-load-balancing |
| Create and configure Managed Fleet Namespaces in AKS | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/howto-managed-namespaces |
| Configure resource overrides in Azure Kubernetes Fleet | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/howto-use-overrides-customize-resources-placement |
| Configure Azure Policy to enforce AKS fleet enrollment | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/howto-use-policy-to-add-clusters-to-fleet |
| Configure intelligent cross-cluster resource placement in Fleet | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/intelligent-resource-placement |
| Configure multi-cluster L4 load balancing with Fleet | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/l4-load-balancing |
| Use envelope objects for safe Fleet resource propagation | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/quickstart-envelope-reserved-resources |
| Configure namespace-scoped resource propagation with Fleet Manager | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/quickstart-namespace-scoped-resource-propagation |
| Configure cluster resource placement to deploy workloads across Azure Kubernetes Fleet clusters | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/quickstart-resource-propagation |
| Configure taints and tolerations for Fleet resource propagation | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/use-taints-tolerations |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate MCP servers with KAITO on AKS | https://learn.microsoft.com/en-us/azure/aks/ai-toolchain-operator-mcp |
| Configure tool calling for KAITO inference on AKS | https://learn.microsoft.com/en-us/azure/aks/ai-toolchain-operator-tool-calling |
| Attach AKS extension in VS Code to Azure Container Registry | https://learn.microsoft.com/en-us/azure/aks/aks-extension-attach-azure-container-registry |
| Connect AKS clusters to AI agents via MCP server | https://learn.microsoft.com/en-us/azure/aks/aks-model-context-protocol-server |
| Autoscale AKS GPU workloads with KEDA and DCGM | https://learn.microsoft.com/en-us/azure/aks/autoscale-gpu-workloads-with-keda |
| Integrate Azure HPC Cache with AKS workloads | https://learn.microsoft.com/en-us/azure/aks/azure-hpc-cache |
| Mount Azure Blob storage in AKS using CSI | https://learn.microsoft.com/en-us/azure/aks/create-volume-azure-blob-storage |
| Use Azure Files CSI volumes with AKS pods | https://learn.microsoft.com/en-us/azure/aks/create-volume-azure-files |
| Integrate AKS with Azure Key Vault via CSI Driver | https://learn.microsoft.com/en-us/azure/aks/csi-secrets-store-driver |
| Configure Secrets Store CSI with NGINX TLS on AKS | https://learn.microsoft.com/en-us/azure/aks/csi-secrets-store-nginx-tls |
| Refactor EDW application code to use Azure services | https://learn.microsoft.com/en-us/azure/aks/eks-edw-refactor |
| Use kubectl gadget to inspect AKS workloads | https://learn.microsoft.com/en-us/azure/aks/inspektor-gadget-run-gadgets |
| Integrate AKS Istio add-on metrics with Azure Managed Prometheus | https://learn.microsoft.com/en-us/azure/aks/istio-metrics-managed-prometheus |
| Onboard custom HuggingFace models with KAITO on AKS | https://learn.microsoft.com/en-us/azure/aks/kaito-custom-inference-model |
| Use KEDA integrations with Azure and OSS services | https://learn.microsoft.com/en-us/azure/aks/keda-integrations |
| Use Azure and OSS integrations with OSM add-on on AKS | https://learn.microsoft.com/en-us/azure/aks/open-service-mesh-integrations |
| Run vLLM batch inference with Ray on AKS | https://learn.microsoft.com/en-us/azure/aks/ray-batch-inference |
| Fine-tune Aurora weather model with Ray on AKS | https://learn.microsoft.com/en-us/azure/aks/ray-finetune-aurora |
| Serve fine-tuned Aurora model with Ray Serve on AKS | https://learn.microsoft.com/en-us/azure/aks/ray-online-serving |
| Distributed LLM training with Ray on AKS | https://learn.microsoft.com/en-us/azure/aks/ray-train-llm |
| Use AKS Vulnerability Data API programmatically | https://learn.microsoft.com/en-us/azure/aks/security-vulnerability-api-reference |
| Use Telepresence with AKS for local microservice debugging | https://learn.microsoft.com/en-us/azure/aks/use-telepresence-aks |
| Deploy Mongo Express client to connect to MongoDB on AKS | https://learn.microsoft.com/en-us/azure/aks/validate-mongodb-cluster |
| Set up Automated Deployments with Fleet and GitHub Actions | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/howto-automated-deployments |
| Configure Azure Monitor alerts for Kubernetes Fleet update runs | https://learn.microsoft.com/en-us/azure/kubernetes-fleet/howto-monitor-update-runs |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy AI models on AKS using AI toolchain operator | https://learn.microsoft.com/en-us/azure/aks/ai-toolchain-operator |
| Use AI toolchain operator in Azure portal for AKS | https://learn.microsoft.com/en-us/azure/aks/ai-toolchain-operator-azure-portal |
| Fine-tune and deploy models on AKS with KAITO | https://learn.microsoft.com/en-us/azure/aks/ai-toolchain-operator-fine-tune |
| Migrate AKS app routing from NGINX to Gateway API | https://learn.microsoft.com/en-us/azure/aks/app-routing-nginx-to-gateway-api-migration |
| Set up automated deployments to AKS with CI/CD | https://learn.microsoft.com/en-us/azure/aks/automated-deployments |
| Provision production-ready AKS infrastructure on Azure | https://learn.microsoft.com/en-us/azure/aks/create-aks-infrastructure |
| Move Azure Disk PVs between AKS clusters | https://learn.microsoft.com/en-us/azure/aks/csi-disk-move-subscriptions |
| Migrate AKS in-tree storage classes to CSI drivers | https://learn.microsoft.com/en-us/azure/aks/csi-migrate-in-tree-volumes |
| Install Dapr extension on AKS and Arc-enabled clusters | https://learn.microsoft.com/en-us/azure/aks/dapr |
| Deploy Dapr Workflow applications on AKS via extension | https://learn.microsoft.com/en-us/azure/aks/dapr-workflow |
| Programmatically deploy Azure Kubernetes applications with Azure CLI | https://learn.microsoft.com/en-us/azure/aks/deploy-application-az-cli |
| Deploy Azure Kubernetes applications using ARM templates | https://learn.microsoft.com/en-us/azure/aks/deploy-application-template |
| Deploy production AKS clusters with Terraform AVM | https://learn.microsoft.com/en-us/azure/aks/deploy-cluster-terraform-verified-module |
| Deploy AKS clusters with Confidential Containers and default policy | https://learn.microsoft.com/en-us/azure/aks/deploy-confidential-containers-default-policy |
| Deploy Kubernetes applications from Azure Marketplace to AKS | https://learn.microsoft.com/en-us/azure/aks/deploy-marketplace |
| Deploy SpinKube on AKS for serverless Wasm workloads | https://learn.microsoft.com/en-us/azure/aks/deploy-spinkube |
| Configure Azure Pipelines CI/CD to deploy to AKS | https://learn.microsoft.com/en-us/azure/aks/devops-pipeline |
| Install and use Draft extension on AKS | https://learn.microsoft.com/en-us/azure/aks/draft |
| Deploy and validate AWS EDW workload on Azure AKS | https://learn.microsoft.com/en-us/azure/aks/eks-edw-deploy |
| Prepare AKS and infrastructure for EDW workload | https://learn.microsoft.com/en-us/azure/aks/eks-edw-prepare |
| Deploy AWS Yelb web application to Azure AKS | https://learn.microsoft.com/en-us/azure/aks/eks-web-deploy |
| Prepare production-ready AKS infrastructure for web apps | https://learn.microsoft.com/en-us/azure/aks/eks-web-prepare |
| Migrate Yelb web application from EKS to AKS | https://learn.microsoft.com/en-us/azure/aks/eks-web-refactor |
| Enable KEDA add-on on existing AKS clusters | https://learn.microsoft.com/en-us/azure/aks/enable-keda-existing-cluster |
| Deploy highly available GitHub Actions runners on AKS | https://learn.microsoft.com/en-us/azure/aks/github-actions-azure-files-deploy-test |
| Deploy Istio-based service mesh add-on on AKS clusters | https://learn.microsoft.com/en-us/azure/aks/istio-deploy-addon |
| Uninstall Istio-based service mesh add-on and clean AKS resources | https://learn.microsoft.com/en-us/azure/aks/istio-uninstall-addon |
| Upgrade Istio-based service mesh add-on revisions on AKS | https://learn.microsoft.com/en-us/azure/aks/istio-upgrade |
| Deploy KEDA add-on to AKS using ARM templates | https://learn.microsoft.com/en-us/azure/aks/keda-deploy-add-on-arm |
| Deploy AKS KEDA add-on using Azure CLI | https://learn.microsoft.com/en-us/azure/aks/keda-deploy-add-on-cli |
| Use GitHub Actions to build and deploy to AKS | https://learn.microsoft.com/en-us/azure/aks/kubernetes-action |
| Install and use Helm to deploy apps on AKS | https://learn.microsoft.com/en-us/azure/aks/kubernetes-helm |
| Migrate AKS from cluster autoscaler to node auto-provisioning | https://learn.microsoft.com/en-us/azure/aks/migrate-from-autoscaler-to-node-auto-provisioning |
| Migrate AKS KMS v2 to infrastructure encryption | https://learn.microsoft.com/en-us/azure/aks/migrate-key-management-service-platform-managed-key-customer-managed-key |
| Migrate AKS node pools to Azure Container Linux | https://learn.microsoft.com/en-us/azure/aks/migrate-nodes-azure-container-linux |
| Deploy OpenAI-based applications on AKS | https://learn.microsoft.com/en-us/azure/aks/open-ai-quickstart |
| Deploy Open Service Mesh add-on on AKS using Bicep templates | https://learn.microsoft.com/en-us/azure/aks/open-service-mesh-deploy-addon-bicep |
| Uninstall Open Service Mesh add-on and clean up AKS resources | https://learn.microsoft.com/en-us/azure/aks/open-service-mesh-uninstall-add-on |
| Deploy and use OpenFaaS on Azure Kubernetes Service | https://learn.microsoft.com/en-us/azure/aks/openfaas |
| Track AKS release rollout status by region | https://learn.microsoft.com/en-us/azure/aks/release-tracker |
| Migrate AKS clusters to new Azure CNI IPAM and data planes | https://learn.microsoft.com/en-us/azure/aks/update-azure-cni |
| Upgrade the AKS control plane independently | https://learn.microsoft.com/en-us/azure/aks/upgrade-aks-control-plane |
| Automate AKS node upgrades using GitHub Actions | https://learn.microsoft.com/en-us/azure/aks/upgrade-github-actions |
| Use capacity reservation groups with AKS node pools | https://learn.microsoft.com/en-us/azure/aks/use-capacity-reservation-groups |
| Run Flyte data and ML pipelines on AKS | https://learn.microsoft.com/en-us/azure/aks/use-flyte |
| Deploy wasmCloud on AKS for distributed Wasm apps | https://learn.microsoft.com/en-us/azure/aks/wasmcloud |