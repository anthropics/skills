---
name: azure-local
description: Expert knowledge for Azure Local development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when planning Azure Local racks, SDN networks, Arc VMs, AKS clusters, or Hyper-V/VMware migrations, and other Azure Local related development tasks. Not for Microsoft Foundry Local (use microsoft-foundry-local), Azure Stack Edge (use azure-stack-edge), Azure VMware Solution (use azure-vmware-solution), Azure Virtual Machines (use azure-virtual-machines).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Local Skill

This skill provides expert guidance for Azure Local. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L72 | Diagnosing and fixing Azure Local deployment, SDN, Arc VM, migration, health, and update issues, plus collecting logs, using support tools, and reviewing known problems/workarounds. |
| Best Practices | L73-L81 | Guidance on networking setup, rack-aware deployment, alert rules, and supported operations/updates for Azure Local and Arc-enabled VMs across single- and multi-rack clusters. |
| Decision Making | L82-L97 | Guidance on choosing Azure Local deployment types, VM/storage/network options, migration paths, licensing/billing, and when to use Azure Local vs Windows Server. |
| Architecture & Design Patterns | L98-L127 | Designing resilient Azure Local architectures: SDN and multisite topologies, rack-aware clusters, DR for VMs, and detailed network/storage reference patterns for various node and switch layouts |
| Limits & Quotas | L128-L141 | Limits, prerequisites, and network/system requirements for Azure Local deployments, including disaggregated, rack-aware, multi-rack scale, SLB HA ports, and Hyper-V/VMware migrations. |
| Security | L142-L184 | Identity, RBAC, certificates, NSGs, firewalls, BitLocker, Secure Boot, Defender, and security controls for Azure Local, including disconnected, multi-rack, and Trusted launch scenarios |
| Configuration | L185-L306 | Configuring Azure Local infrastructure: networking, storage, GPUs, SDN, monitoring, disconnected setups, VM images/lifecycle, migrations, multi-rack and SFF patterns, and update/Arc gateway settings. |
| Integrations & Coding Patterns | L307-L322 | VM/AKS integration patterns for Azure Local: creating Arc-enabled VMs from various image sources, using external storage/SAN, and migrating/protecting VMs via ASR, Hyper-V/VMware tools, PowerShell/CLI. |
| Deployment | L323-L358 | Planning, deploying, updating, and repairing Azure Local (rack-aware, disaggregated, virtualized) including SDN, SQL, migrations, disconnected ops, and OS/solution upgrades. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Validate rack aware cluster readiness with LLDP validator | https://learn.microsoft.com/en-us/azure/azure-local/deploy/rack-aware-cluster-readiness-check?view=azloc-2606 |
| Troubleshoot simplified machine provisioning for Azure Local (preview) | https://learn.microsoft.com/en-us/azure/azure-local/deploy/troubleshoot-simplified-machine-provisioning?view=azloc-2606 |
| Resolve known Azure Local issues and workarounds | https://learn.microsoft.com/en-us/azure/azure-local/known-issues?view=azloc-2606 |
| Collect diagnostic logs for Azure Local Arc-enabled VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/collect-log-files-arc-enabled-vms?view=azloc-2606 |
| Collect fallback logs for disconnected Azure Local Arc VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/disconnected-operations-fallback?view=azloc-2606 |
| Known issues and workarounds for disconnected operations | https://learn.microsoft.com/en-us/azure/azure-local/manage/disconnected-operations-known-issues?view=azloc-2606 |
| Collect on-demand logs for Azure Local disconnected operations | https://learn.microsoft.com/en-us/azure/azure-local/manage/disconnected-operations-on-demand-logs?view=azloc-2606 |
| Use drift detection to diagnose Azure Local configuration issues | https://learn.microsoft.com/en-us/azure/azure-local/manage/drift-detection?view=azloc-2606 |
| Track and understand Health Service automated actions | https://learn.microsoft.com/en-us/azure/azure-local/manage/health-service-actions?view=azloc-2606 |
| Interpret and resolve Health Service faults in Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/health-service-faults?view=azloc-2606 |
| Use Support.AksArc tool to remediate Azure Local infrastructure issues | https://learn.microsoft.com/en-us/azure/azure-local/manage/remediate-support-tool-infrastructure?view=azloc-2606 |
| Use Remote Support Arc extension for Azure Local diagnostics | https://learn.microsoft.com/en-us/azure/azure-local/manage/remote-support-arc-extension?view=azloc-2606 |
| Collect SDN logs for Azure Local troubleshooting | https://learn.microsoft.com/en-us/azure/azure-local/manage/sdn-log-collection?view=azloc-2606 |
| Troubleshoot Azure Local SDN deployment and connectivity issues | https://learn.microsoft.com/en-us/azure/azure-local/manage/sdn-troubleshooting?view=azloc-2606 |
| Run Azure Local Support Diagnostic Tool for issue resolution | https://learn.microsoft.com/en-us/azure/azure-local/manage/support-tools?view=azloc-2606 |
| Troubleshoot Azure Local Arc-enabled virtual machines | https://learn.microsoft.com/en-us/azure/azure-local/manage/troubleshoot-arc-enabled-vms?view=azloc-2606 |
| Collect traces and logs for common SDN issues | https://learn.microsoft.com/en-us/azure/azure-local/manage/troubleshoot-common-sdn-issues?view=azloc-2606 |
| Troubleshoot Azure Local registration via Configurator app | https://learn.microsoft.com/en-us/azure/azure-local/manage/troubleshoot-deployment-configurator-app?view=azloc-2606 |
| Troubleshoot Azure Local 23H2 deployment validation in Azure portal | https://learn.microsoft.com/en-us/azure/azure-local/manage/troubleshoot-deployment?view=azloc-2606 |
| Troubleshoot SDN deployment via Windows Admin Center | https://learn.microsoft.com/en-us/azure/azure-local/manage/troubleshoot-sdn-deployment?view=azloc-2606 |
| Troubleshoot Software Load Balancer data path issues | https://learn.microsoft.com/en-us/azure/azure-local/manage/troubleshoot-software-load-balancer?view=azloc-2606 |
| Azure Local migration FAQ for Hyper-V and VMware | https://learn.microsoft.com/en-us/azure/azure-local/migrate/migrate-faq?view=azloc-2606 |
| Troubleshoot Azure Local VM migration with Azure Migrate | https://learn.microsoft.com/en-us/azure/azure-local/migrate/migrate-troubleshoot?view=azloc-2606 |
| Resolve known Azure Local migration issues | https://learn.microsoft.com/en-us/azure/azure-local/migrate/migration-known-issues?view=azloc-2606 |
| Access Azure Local multi-rack VM serial console using Azure CLI | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-serial-console?view=azloc-2606 |
| Troubleshoot Azure Local multi-rack Arc-enabled VMs | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-troubleshoot-arc-enabled-vms?view=azloc-2606 |
| Known and fixed issues in Azure Local 23xx releases | https://learn.microsoft.com/en-us/azure/azure-local/previous-releases/known-issues-23?view=azloc-2606 |
| Known and fixed issues in Azure Local 24xx releases | https://learn.microsoft.com/en-us/azure/azure-local/previous-releases/known-issues-24?view=azloc-2606 |
| Collect support logs from Azure Local SFF devices | https://learn.microsoft.com/en-us/azure/azure-local/small-form-factor/small-form-factor-collect-system-logs?view=azloc-2606 |
| Troubleshoot Azure Local small form factor deployments | https://learn.microsoft.com/en-us/azure/azure-local/small-form-factor/small-form-factor-troubleshoot?view=azloc-2606 |
| Troubleshoot Azure Local solution update failures | https://learn.microsoft.com/en-us/azure/azure-local/update/update-troubleshooting-23h2?view=azloc-2606 |
| Troubleshoot common Azure Local upgrade issues | https://learn.microsoft.com/en-us/azure/azure-local/upgrade/troubleshoot-upgrade-to-23h2?view=azloc-2606 |

### Best Practices
| Topic | URL |
|-------|-----|
| Prepare network and hardware for rack aware cluster deployment | https://learn.microsoft.com/en-us/azure/azure-local/deploy/rack-aware-cluster-deploy-prep?view=azloc-2606 |
| Enable recommended Azure Local alert rules for core metrics | https://learn.microsoft.com/en-us/azure/azure-local/manage/set-up-recommended-alert-rules?view=azloc-2606 |
| Use supported operations for Azure Local Arc-enabled VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/virtual-machine-operations?view=azloc-2606 |
| Use supported operations for Azure Local multi-rack Arc VMs | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-virtual-machine-operations?view=azloc-2606 |
| Best practices for managing Azure Local updates | https://learn.microsoft.com/en-us/azure/azure-local/update/update-best-practices?view=azloc-2606 |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose Azure Local VM types and management model | https://learn.microsoft.com/en-us/azure/azure-local/concepts/compare-vm-management-capabilities?view=azloc-2606 |
| Decide between Azure Local and Windows Server | https://learn.microsoft.com/en-us/azure/azure-local/concepts/compare-windows-server?view=azloc-2606 |
| Plan and select external SAN storage for Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/concepts/external-storage-support?view=azloc-2606 |
| Choose SDN management methods on Azure Local with Azure Arc | https://learn.microsoft.com/en-us/azure/azure-local/concepts/sdn-overview?view=azloc-2606 |
| Understand billing and licensing for Azure Local disconnected operations | https://learn.microsoft.com/en-us/azure/azure-local/manage/disconnected-operations-billing?view=azloc-2606 |
| Plan Hyper-V VM migration to Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/migrate/migration-azure-migrate-overview?view=azloc-2606 |
| Plan VMware VM migration to Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/migrate/migration-azure-migrate-vmware-overview?view=azloc-2606 |
| Choose VM migration options to Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/migrate/migration-options-overview?view=azloc-2606 |
| Understand Azure Local disaggregated deployment scenarios | https://learn.microsoft.com/en-us/azure/azure-local/overview/disaggregated-overview?view=azloc-2606 |
| Choose a network pattern for disaggregated Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/plan/choose-network-pattern-disaggregated?view=azloc-2606 |
| Select Azure Local deployment type and scale | https://learn.microsoft.com/en-us/azure/azure-local/scalability-deployments?view=azloc-2606 |
| Choose container orchestrator for Azure Local SFF | https://learn.microsoft.com/en-us/azure/azure-local/small-form-factor/small-form-factor-container-orchestrators?view=azloc-2606 |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Plan SDN infrastructure for Azure Local 23H2 | https://learn.microsoft.com/en-us/azure/azure-local/concepts/plan-software-defined-networking-infrastructure-23h2?view=azloc-2606 |
| Distribute AKS nodes across Azure Local rack aware zones | https://learn.microsoft.com/en-us/azure/azure-local/concepts/rack-aware-cluster-aks-nodes?view=azloc-2606 |
| Apply network reference patterns for Azure Local rack aware clusters | https://learn.microsoft.com/en-us/azure/azure-local/concepts/rack-aware-cluster-reference-architecture?view=azloc-2606 |
| Design room-to-room connectivity for rack aware clusters | https://learn.microsoft.com/en-us/azure/azure-local/concepts/rack-aware-cluster-room-to-room-connectivity?view=azloc-2606 |
| Plan SDN Multisite topology and disaster recovery on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/concepts/sdn-multisite-overview?view=azloc-2606 |
| Design resilient infrastructure for Azure Local deployments | https://learn.microsoft.com/en-us/azure/azure-local/manage/disaster-recovery-infrastructure-resiliency?view=azloc-2606 |
| Plan disaster recovery strategy for Azure Local VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/disaster-recovery-overview?view=azloc-2606 |
| Design resilient virtual machines on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/disaster-recovery-vm-resiliency?view=azloc-2606 |
| Plan dedicated management clusters for disconnected Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/disconnected-operations-control-plane-appliance?view=azloc-2606 |
| Design network architecture for Azure Local disconnected operations | https://learn.microsoft.com/en-us/azure/azure-local/manage/disconnected-operations-network?view=azloc-2606 |
| Load balance multiple logical networks in Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/load-balance-multiple-networks?view=azloc-2606 |
| Understand automatic vTPM state transfer for Azure Local VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/trusted-launch-automatic-state-transfer?view=azloc-2606 |
| Choose Azure Local deployment network pattern | https://learn.microsoft.com/en-us/azure/azure-local/plan/choose-network-pattern?view=azloc-2606 |
| Design Fiber Channel disaggregated pattern without backup network | https://learn.microsoft.com/en-us/azure/azure-local/plan/fiber-channel-no-backup-disaggregated-pattern?view=azloc-2606 |
| Design Fiber Channel disaggregated pattern with backup network | https://learn.microsoft.com/en-us/azure/azure-local/plan/fiber-channel-with-backup-disaggregated-pattern?view=azloc-2606 |
| Plan four-node switchless dual-link Azure Local pattern | https://learn.microsoft.com/en-us/azure/azure-local/plan/four-node-switchless-two-switches-two-links?view=azloc-2606 |
| Network reference patterns overview for disaggregated Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/plan/network-patterns-overview-disaggregated?view=azloc-2606 |
| Review Azure Local network reference pattern options | https://learn.microsoft.com/en-us/azure/azure-local/plan/network-patterns-overview?view=azloc-2606 |
| Consider SDN design for Azure Local network patterns | https://learn.microsoft.com/en-us/azure/azure-local/plan/network-patterns-sdn-considerations?view=azloc-2606 |
| Plan single-server storage network pattern for Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/plan/single-server-deployment?view=azloc-2606 |
| Plan three-node switchless single-link Azure Local pattern | https://learn.microsoft.com/en-us/azure/azure-local/plan/three-node-switchless-two-switches-single-link?view=azloc-2606 |
| Plan three-node switchless dual-link Azure Local pattern | https://learn.microsoft.com/en-us/azure/azure-local/plan/three-node-switchless-two-switches-two-links?view=azloc-2606 |
| Plan two-node switched fully converged Azure Local pattern | https://learn.microsoft.com/en-us/azure/azure-local/plan/two-node-switched-converged?view=azloc-2606 |
| Plan two-node switched non-converged Azure Local pattern | https://learn.microsoft.com/en-us/azure/azure-local/plan/two-node-switched-non-converged?view=azloc-2606 |
| Plan two-node switchless single-switch Azure Local pattern | https://learn.microsoft.com/en-us/azure/azure-local/plan/two-node-switchless-single-switch?view=azloc-2606 |
| Plan two-node switchless dual-switch Azure Local pattern | https://learn.microsoft.com/en-us/azure/azure-local/plan/two-node-switchless-two-switches?view=azloc-2606 |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Host network requirements for Azure Local disaggregated | https://learn.microsoft.com/en-us/azure/azure-local/concepts/host-network-requirements-disaggregated?view=azloc-2606 |
| Physical network requirements for Azure Local disaggregated | https://learn.microsoft.com/en-us/azure/azure-local/concepts/physical-network-requirements-disaggregated?view=azloc-2606 |
| Review requirements and supported configs for rack aware clusters | https://learn.microsoft.com/en-us/azure/azure-local/concepts/rack-aware-cluster-requirements?view=azloc-2606 |
| System requirements for Azure Local disaggregated deployments | https://learn.microsoft.com/en-us/azure/azure-local/concepts/system-requirements-disaggregated?view=azloc-2606 |
| Configure SLB high availability ports and limitations | https://learn.microsoft.com/en-us/azure/azure-local/manage/configure-software-load-balancer?view=azloc-2606 |
| System requirements for Hyper-V to Azure Local migration | https://learn.microsoft.com/en-us/azure/azure-local/migrate/migrate-hyperv-requirements?view=azloc-2606 |
| System requirements for VMware to Azure Local migration | https://learn.microsoft.com/en-us/azure/azure-local/migrate/migrate-vmware-requirements?view=azloc-2606 |
| Check prerequisites and capacity limits for Azure Local multi-rack | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-prerequisites?view=azloc-2606 |
| Review VM prerequisites and limits for Azure Local multi-rack | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-vm-management-prerequisites?view=azloc-2606 |
| Understand Azure Local hyperconverged deployment scale | https://learn.microsoft.com/en-us/azure/azure-local/overview/hyperconverged-overview?view=azloc-2606 |

### Security
| Topic | URL |
|-------|-----|
| Configure firewall rules and endpoints for Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/concepts/firewall-requirements?view=azloc-2606 |
| Use Azure verification for VMs on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/deploy/azure-verification?view=azloc-2606 |
| Assign Azure Arc permissions for Azure Local deployment | https://learn.microsoft.com/en-us/azure/azure-local/deploy/deployment-arc-register-server-permissions?view=azloc-2606 |
| Use local identity with Azure Key Vault for Azure Local deployment | https://learn.microsoft.com/en-us/azure/azure-local/deploy/deployment-local-identity-with-key-vault?view=azloc-2606 |
| Prepare Active Directory OU and permissions for Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/deploy/deployment-prep-active-directory?view=azloc-2606 |
| Assign built-in RBAC roles for Azure Local Arc VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/assign-vm-rbac-roles?view=azloc-2606 |
| Configure Extended Security Updates for Azure Local workloads | https://learn.microsoft.com/en-us/azure/azure-local/manage/azure-benefits-esu?view=azloc-2606 |
| Configure managed identity for enhanced Azure Local management | https://learn.microsoft.com/en-us/azure/azure-local/manage/azure-enhanced-management-managed-identity?view=azloc-2606 |
| Use tags with SDN network security groups | https://learn.microsoft.com/en-us/azure/azure-local/manage/configure-network-security-groups-with-tags?view=azloc-2606 |
| Create NSGs and network security rules for Azure Local VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/create-network-security-groups?view=azloc-2606 |
| Plan identity architecture for Azure Local disconnected operations | https://learn.microsoft.com/en-us/azure/azure-local/manage/disconnected-operations-identity?view=azloc-2606 |
| Configure PKI and certificates for Azure Local disconnected operations | https://learn.microsoft.com/en-us/azure/azure-local/manage/disconnected-operations-pki?view=azloc-2606 |
| Apply security controls for Azure Local disconnected VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/disconnected-operations-security?view=azloc-2606 |
| Use Kerberos SPN authentication with Network Controller | https://learn.microsoft.com/en-us/azure/azure-local/manage/kerberos-with-spn?view=azloc-2606 |
| Manage BitLocker disk encryption on Azure Local clusters | https://learn.microsoft.com/en-us/azure/azure-local/manage/manage-bitlocker?view=azloc-2606 |
| Enable default VM network access policies on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/manage-default-network-access-policies-virtual-machines-23h2?view=azloc-2606 |
| Manage NSGs and security rules on Azure Local Arc-enabled VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/manage-network-security-groups?view=azloc-2606 |
| Rotate deployment user password and internal secrets on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/manage-secrets-rotation?view=azloc-2606 |
| Manage security defaults and drift control in Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/manage-secure-baseline?view=azloc-2606 |
| Manage Secure Boot certificate updates and CVE-2023-24932 on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/manage-secure-boot-updates?view=azloc-2606 |
| Manage security settings after upgrading Azure Local from 22H2 | https://learn.microsoft.com/en-us/azure/azure-local/manage/manage-security-post-upgrade?view=azloc-2606 |
| Secure Azure Local with Microsoft Defender for Cloud | https://learn.microsoft.com/en-us/azure/azure-local/manage/manage-security-with-defender-for-cloud?view=azloc-2606 |
| Configure syslog forwarding from Azure Local to SIEM | https://learn.microsoft.com/en-us/azure/azure-local/manage/manage-syslog-forwarding?view=azloc-2606 |
| Configure Application Control policies on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/manage-wdac?view=azloc-2606 |
| Configure Network Controller security for Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/nc-security?view=azloc-2606 |
| Manage certificates for Azure Local SDN communications | https://learn.microsoft.com/en-us/azure/azure-local/manage/sdn-manage-certs?view=azloc-2606 |
| Enable guest attestation for Trusted launch Azure Local VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/trusted-launch-guest-attestation?view=azloc-2606 |
| Back up and restore Trusted launch guest state keys | https://learn.microsoft.com/en-us/azure/azure-local/manage/trusted-launch-vm-import-key?view=azloc-2606 |
| Renew Network Controller certificates on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/update-network-controller-certificates?view=azloc-2606 |
| Renew SDN server and SLB MUX certificates | https://learn.microsoft.com/en-us/azure/azure-local/manage/update-sdn-infrastructure-certificates?view=azloc-2606 |
| Configure SDN network security groups with PowerShell | https://learn.microsoft.com/en-us/azure/azure-local/manage/use-datacenter-firewall-powershell?view=azloc-2606 |
| Configure SDN network security groups in Windows Admin Center | https://learn.microsoft.com/en-us/azure/azure-local/manage/use-datacenter-firewall-windows-admin-center?view=azloc-2606 |
| Assign RBAC roles for Azure Local multi-rack VM management | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-assign-vm-rbac-roles?view=azloc-2606 |
| Create network security groups for Azure Local multi-rack VMs | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-create-network-security-groups?view=azloc-2606 |
| Manage NSGs and security rules on Azure Local multi-rack | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-manage-network-security-groups?view=azloc-2606 |
| Configure custom Active Directory permissions for Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/plan/configure-custom-settings-active-directory?view=azloc-2606 |
| Security update details for Azure Local 23xx releases | https://learn.microsoft.com/en-us/azure/azure-local/previous-releases/security-update-23?view=azloc-2606 |
| Security update details for Azure Local 24xx releases | https://learn.microsoft.com/en-us/azure/azure-local/previous-releases/security-update-24?view=azloc-2606 |
| Secure Azure Local small form factor deployments | https://learn.microsoft.com/en-us/azure/azure-local/small-form-factor/small-form-factor-security?view=azloc-2606 |

### Configuration
| Topic | URL |
|-------|-----|
| Configure host networking for Azure Local nodes | https://learn.microsoft.com/en-us/azure/azure-local/concepts/host-network-requirements?view=azloc-2606 |
| Configure physical network for Azure Local clusters | https://learn.microsoft.com/en-us/azure/azure-local/concepts/physical-network-requirements?view=azloc-2606 |
| Provision Azure Local VMs in local availability zones | https://learn.microsoft.com/en-us/azure/azure-local/concepts/rack-aware-cluster-provision-vm-local-availability-zone?view=azloc-2606 |
| Configure supported SAN solutions for Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/concepts/san-requirements?view=azloc-2606 |
| Meet system requirements for Azure Local 23H2 | https://learn.microsoft.com/en-us/azure/azure-local/concepts/system-requirements-23h2?view=azloc-2606 |
| Plan private endpoint connectivity for Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/deploy/about-private-endpoints?view=azloc-2606 |
| Configure private endpoints for Azure Local without proxy or gateway | https://learn.microsoft.com/en-us/azure/azure-local/deploy/deploy-private-endpoints-no-proxy-no-gateway?view=azloc-2606 |
| Configure private endpoints for Azure Local with Arc gateway | https://learn.microsoft.com/en-us/azure/azure-local/deploy/deploy-private-endpoints-no-proxy-with-gateway?view=azloc-2606 |
| Configure private endpoints for Azure Local with proxy only | https://learn.microsoft.com/en-us/azure/azure-local/deploy/deploy-private-endpoints-with-proxy-no-gateway?view=azloc-2606 |
| Configure private endpoints for Azure Local with proxy and gateway | https://learn.microsoft.com/en-us/azure/azure-local/deploy/deploy-private-endpoints-with-proxy-with-gateway?view=azloc-2606 |
| Configure Azure Arc gateway for Azure Local deployments | https://learn.microsoft.com/en-us/azure/azure-local/deploy/deployment-azure-arc-gateway-overview?view=azloc-2606 |
| Configure Azure Arc gateway proxy for Azure Local registration | https://learn.microsoft.com/en-us/azure/azure-local/deploy/deployment-with-azure-arc-gateway?view=azloc-2606 |
| Register Azure Local with Arc without gateway and configure proxy | https://learn.microsoft.com/en-us/azure/azure-local/deploy/deployment-without-azure-arc-gateway?view=azloc-2606 |
| Configure external SAN storage for Azure Local clusters | https://learn.microsoft.com/en-us/azure/azure-local/deploy/enable-external-storage?view=azloc-2606 |
| Enable SDN on Azure Local using PowerShell action plan | https://learn.microsoft.com/en-us/azure/azure-local/deploy/enable-sdn-integration?view=azloc-2606 |
| Add physical NICs to Network ATC intents on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/add-network-adapters-to-network-intents?view=azloc-2606 |
| Configure and manage Azure Arc extensions on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/arc-extension-management?view=azloc-2606 |
| Assign public IP addresses to VMs on Azure Local SDN | https://learn.microsoft.com/en-us/azure/azure-local/manage/assign-public-ip-to-vm?view=azloc-2606 |
| Attach and configure GPUs for Linux VMs on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/attach-gpu-to-linux-vm?view=azloc-2606 |
| Prerequisites and requirements for Azure Local Arc-enabled VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/azure-arc-vm-management-prerequisites?view=azloc-2606 |
| Collect and upload Azure Local diagnostic logs to Microsoft | https://learn.microsoft.com/en-us/azure/azure-local/manage/collect-logs?view=azloc-2606 |
| Configure proxy settings for Azure Local 23H2 deployments | https://learn.microsoft.com/en-us/azure/azure-local/manage/configure-proxy-settings-23h2?view=azloc-2606 |
| Connect to Azure Local VMs using SSH, RDP over SSH, or VM Connect | https://learn.microsoft.com/en-us/azure/azure-local/manage/connect-arc-vm-using-ssh?view=azloc-2606 |
| Create logical networks for Azure Local Arc-enabled VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/create-logical-networks?view=azloc-2606 |
| Create network interfaces for Azure Local VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/create-network-interfaces?view=azloc-2606 |
| Create storage paths for Azure Local VM images | https://learn.microsoft.com/en-us/azure/azure-local/manage/create-storage-path?view=azloc-2606 |
| Deploy Azure Container Registry on Azure Local disconnected | https://learn.microsoft.com/en-us/azure/azure-local/manage/disconnected-operations-azure-container-registry?view=azloc-2606 |
| Configure and run backups for Azure Local disconnected environments | https://learn.microsoft.com/en-us/azure/azure-local/manage/disconnected-operations-back-up-restore?view=azloc-2606 |
| Configure Azure CLI for Azure Local disconnected operations | https://learn.microsoft.com/en-us/azure/azure-local/manage/disconnected-operations-cli?view=azloc-2606 |
| Integrate monitoring for Azure Local disconnected operations | https://learn.microsoft.com/en-us/azure/azure-local/manage/disconnected-operations-monitoring?view=azloc-2606 |
| Use Azure Policy in disconnected Azure Local environments | https://learn.microsoft.com/en-us/azure/azure-local/manage/disconnected-operations-policy?view=azloc-2606 |
| Configure Azure PowerShell for Azure Local disconnected operations | https://learn.microsoft.com/en-us/azure/azure-local/manage/disconnected-operations-powershell?view=azloc-2606 |
| Prepare Azure Local nodes for disconnected deployments | https://learn.microsoft.com/en-us/azure/azure-local/manage/disconnected-operations-prepare?view=azloc-2606 |
| Register Azure Local disconnected operations for compliance | https://learn.microsoft.com/en-us/azure/azure-local/manage/disconnected-operations-registration?view=azloc-2606 |
| Configure and execute restore for Azure Local disconnected environments | https://learn.microsoft.com/en-us/azure/azure-local/manage/disconnected-operations-restore?view=azloc-2606 |
| Enable nested virtualization on Azure Local hosts | https://learn.microsoft.com/en-us/azure/azure-local/manage/enable-nested-virtualization?view=azloc-2606 |
| Manage SDN gateway connections in Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/gateway-connections?view=azloc-2606 |
| Enable and manage remote support for Azure Local OS | https://learn.microsoft.com/en-us/azure/azure-local/manage/get-remote-support?view=azloc-2606 |
| Configure GPU Discrete Device Assignment on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/gpu-manage-via-device?view=azloc-2606 |
| Configure GPU partitioning (GPU-P) for Azure Local VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/gpu-manage-via-partitioning?view=azloc-2606 |
| Prepare GPUs for Azure Local Arc-enabled workloads | https://learn.microsoft.com/en-us/azure/azure-local/manage/gpu-preparation?view=azloc-2606 |
| Use Azure Monitor alerts for Azure Local health issues | https://learn.microsoft.com/en-us/azure/azure-local/manage/health-alerts-via-azure-monitor-alerts?view=azloc-2606 |
| Access cluster performance history via Health Service | https://learn.microsoft.com/en-us/azure/azure-local/manage/health-service-cluster-performance-history?view=azloc-2606 |
| Use Health Service to monitor Azure Local clusters | https://learn.microsoft.com/en-us/azure/azure-local/manage/health-service-overview?view=azloc-2606 |
| Modify Health Service settings for Azure Local clusters | https://learn.microsoft.com/en-us/azure/azure-local/manage/health-service-settings?view=azloc-2606 |
| Configure Software Load Balancer policies in Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/load-balancers?view=azloc-2606 |
| Manage disks and NIC resources for Azure Local Arc-enabled VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/manage-arc-virtual-machine-resources?view=azloc-2606 |
| Manage lifecycle of Azure Local Arc-enabled VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/manage-arc-virtual-machines?view=azloc-2606 |
| Monitor Azure Local at scale using portal dashboards | https://learn.microsoft.com/en-us/azure/azure-local/manage/manage-at-scale-dashboard?view=azloc-2606 |
| Manage logical networks for Azure Local Arc-enabled VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/manage-logical-networks?view=azloc-2606 |
| Manage SDN Multisite deployments for Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/manage-sdn-multisite?view=azloc-2606 |
| Configure storage thin provisioning on Azure Local 23H2 | https://learn.microsoft.com/en-us/azure/azure-local/manage/manage-thin-provisioning-23h2?view=azloc-2606 |
| Monitor Azure Local with Azure Monitor Metrics and dashboards | https://learn.microsoft.com/en-us/azure/azure-local/manage/monitor-cluster-with-metrics?view=azloc-2606 |
| Monitor Azure Local features like ReFS with Insights | https://learn.microsoft.com/en-us/azure/azure-local/manage/monitor-features?view=azloc-2606 |
| Configure Insights to monitor multiple Azure Local systems | https://learn.microsoft.com/en-us/azure/azure-local/manage/monitor-multi-23h2?view=azloc-2606 |
| Enable Azure Local Insights at scale using Azure Policy | https://learn.microsoft.com/en-us/azure/azure-local/manage/monitor-multi-azure-policies?view=azloc-2606 |
| Configure Insights to monitor a single Azure Local system | https://learn.microsoft.com/en-us/azure/azure-local/manage/monitor-single-23h2?view=azloc-2606 |
| Enable and tune ReFS deduplication on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/refs-deduplication-and-compression?view=azloc-2606 |
| Replace failed NICs in Network ATC intents on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/replace-network-adapter-to-network-intents?view=azloc-2606 |
| Configure metric alerts for Azure Local resources | https://learn.microsoft.com/en-us/azure/azure-local/manage/setup-metric-alerts?view=azloc-2606 |
| Set up log alerts for Azure Local using Insights queries | https://learn.microsoft.com/en-us/azure/azure-local/manage/setup-system-alerts?view=azloc-2606 |
| Manage SDN tenant logical networks in Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/tenant-logical-networks?view=azloc-2606 |
| Manage SDN tenant virtual networks with HNV | https://learn.microsoft.com/en-us/azure/azure-local/manage/tenant-virtual-networks?view=azloc-2606 |
| Unregister and re-register Azure Local machines via PowerShell | https://learn.microsoft.com/en-us/azure/azure-local/manage/unregister-register-machine?view=azloc-2606 |
| Update SDN infrastructure components on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/update-sdn?view=azloc-2606 |
| Use Azure Local Environment Checker for readiness validation | https://learn.microsoft.com/en-us/azure/azure-local/manage/use-environment-checker?view=azloc-2606 |
| Prepare RHEL Azure Marketplace images for Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/virtual-machine-azure-marketplace-red-hat?view=azloc-2606 |
| Prepare Ubuntu Azure Marketplace images for Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/virtual-machine-azure-marketplace-ubuntu?view=azloc-2606 |
| Prepare CentOS images for Azure Local Arc-enabled VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/virtual-machine-image-centos?view=azloc-2606 |
| Create Azure Local VM images from existing Arc-enabled VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/virtual-machine-image-existing-arc-vm?view=azloc-2606 |
| Prepare Ubuntu images for Azure Local Arc-enabled VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/virtual-machine-image-linux-sysprep?view=azloc-2606 |
| Create Azure Local VM images from local share | https://learn.microsoft.com/en-us/azure/azure-local/manage/virtual-machine-image-local-share?view=azloc-2606 |
| Prepare RHEL images for Azure Local Arc-enabled VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/virtual-machine-image-red-hat-enterprise?view=azloc-2606 |
| Prepare SUSE images for Azure Local Arc-enabled VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/virtual-machine-image-suse?view=azloc-2606 |
| Install and manage VM extensions on Azure Local Arc-enabled VMs | https://learn.microsoft.com/en-us/azure/azure-local/manage/virtual-machine-manage-extension?view=azloc-2606 |
| Manage Azure Local VM images via CLI and portal | https://learn.microsoft.com/en-us/azure/azure-local/manage/virtual-machine-manage-image?view=azloc-2606 |
| Configure Windows Server VM activation on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/vm-activate?view=azloc-2606 |
| Configure VM affinity and anti-affinity rules on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/vm-affinity?view=azloc-2606 |
| Configure virtual machine load balancing on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/vm-load-balancing?view=azloc-2606 |
| Enable guest management for Azure Local migrated VMs | https://learn.microsoft.com/en-us/azure/azure-local/migrate/migrate-enable-guest-management?view=azloc-2606 |
| Prepare environment for Hyper-V to Azure Local migration | https://learn.microsoft.com/en-us/azure/azure-local/migrate/migrate-hyperv-prerequisites?view=azloc-2606 |
| Preserve static IPs during Azure Local VM migration | https://learn.microsoft.com/en-us/azure/azure-local/migrate/migrate-maintain-ip-addresses?view=azloc-2606 |
| Prepare environment for VMware to Azure Local migration | https://learn.microsoft.com/en-us/azure/azure-local/migrate/migrate-vmware-prerequisites?view=azloc-2606 |
| Configure diagnostic settings for Azure Local migrations | https://learn.microsoft.com/en-us/azure/azure-local/migrate/monitor-migration?view=azloc-2606 |
| Install Azure Local multi-rack CLI extensions | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-cli-extensions?view=azloc-2606 |
| Configure Layer 3 isolation domains for Azure Local multi-rack | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-configure-layer-3-isolation-domain?view=azloc-2606 |
| Connect to Azure Local multi-rack VMs via SSH and RDP over SSH | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-connect-arc-vm-using-ssh?view=azloc-2606 |
| Provision Azure Local multi-rack VMs enabled by Azure Arc | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-create-arc-virtual-machines?view=azloc-2606 |
| Create internal load balancers for Azure Local multi-rack | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-create-internal-load-balancer-virtual-networks?view=azloc-2606 |
| Create load balancers on Azure Local logical networks via CLI | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-create-load-balancer-logical-network?view=azloc-2606 |
| Configure logical networks for Azure Local multi-rack VMs | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-create-logical-networks?view=azloc-2606 |
| Create network interfaces for Azure Local multi-rack VMs | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-create-network-interfaces?view=azloc-2606 |
| Create public IP resources on Azure Local multi-rack | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-create-public-ip?view=azloc-2606 |
| Configure public load balancers on Azure Local multi-rack VNets | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-create-public-load-balancer-virtual-networks?view=azloc-2606 |
| Configure virtual networks for Azure Local multi-rack | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-create-virtual-networks?view=azloc-2606 |
| Create and restore Azure Local multi-rack data disk snapshots | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-disk-snapshot?view=azloc-2606 |
| Configure GPU DDA for Azure Local multi-rack VMs | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-gpu-manage-via-device?view=azloc-2606 |
| Prepare and configure GPUs for Azure Local multi-rack | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-gpu-preparation?view=azloc-2606 |
| Manage disks and NIC resources for Azure Local multi-rack VMs | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-manage-arc-virtual-machine-resources?view=azloc-2606 |
| Manage lifecycle of Azure Local multi-rack Arc VMs | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-manage-arc-virtual-machines?view=azloc-2606 |
| Manage logical networks for Azure Local multi-rack Arc VMs | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-manage-logical-networks?view=azloc-2606 |
| Monitor Azure Local multi-rack with Azure Monitor Metrics | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-monitor-cluster-with-metrics?view=azloc-2606 |
| Install and manage VM extensions on Azure Local multi-rack VMs | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-virtual-machine-manage-extension?view=azloc-2606 |
| Manage VM images on Azure Local multi-rack deployments | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-virtual-machine-manage-image?view=azloc-2606 |
| Review components of single-server Azure Local pattern | https://learn.microsoft.com/en-us/azure/azure-local/plan/single-server-components?view=azloc-2606 |
| Apply IP addressing requirements for single-server Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/plan/single-server-ip-requirements?view=azloc-2606 |
| Review components of three-node Azure Local patterns | https://learn.microsoft.com/en-us/azure/azure-local/plan/three-node-components?view=azloc-2606 |
| Apply IP addressing for three-node Azure Local patterns | https://learn.microsoft.com/en-us/azure/azure-local/plan/three-node-ip-requirements?view=azloc-2606 |
| Review components of two-node Azure Local patterns | https://learn.microsoft.com/en-us/azure/azure-local/plan/two-node-components?view=azloc-2606 |
| Apply IP addressing for two-node Azure Local patterns | https://learn.microsoft.com/en-us/azure/azure-local/plan/two-node-ip-requirements?view=azloc-2606 |
| Use Configurator App for Azure Local SFF management | https://learn.microsoft.com/en-us/azure/azure-local/small-form-factor/small-form-factor-configurator-app?view=azloc-2606 |
| Configure GPU-enabled workloads on Azure Local SFF | https://learn.microsoft.com/en-us/azure/azure-local/small-form-factor/small-form-factor-deploy-gpu-workloads?view=azloc-2606 |
| Configure firewall FQDN allowlist for Azure Local SFF | https://learn.microsoft.com/en-us/azure/azure-local/small-form-factor/small-form-factor-firewall-requirements?view=azloc-2606 |
| Prepare Azure subscription for Azure Local SFF | https://learn.microsoft.com/en-us/azure/azure-local/small-form-factor/small-form-factor-subscription-setup?view=azloc-2606 |
| Import Azure Local update packages offline via PowerShell | https://learn.microsoft.com/en-us/azure/azure-local/update/import-discover-updates-offline-23h2?view=azloc-2606 |
| Manage Solution Builder Extension updates on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/update/solution-builder-extension?view=azloc-2606 |
| Configure Azure Local update settings and behavior | https://learn.microsoft.com/en-us/azure/azure-local/update/update-settings?view=azloc-2606 |
| Configure Network ATC on existing Azure Local clusters | https://learn.microsoft.com/en-us/azure/azure-local/upgrade/install-enable-network-atc?view=azloc-2606 |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Protect Azure Local Hyper-V VMs with Azure Site Recovery | https://learn.microsoft.com/en-us/azure/azure-local/manage/azure-site-recovery?view=azloc-2606 |
| Create Azure Local VMs enabled by Azure Arc | https://learn.microsoft.com/en-us/azure/azure-local/manage/create-arc-virtual-machines?view=azloc-2606 |
| Download Azure managed disks to Azure Local for VM use | https://learn.microsoft.com/en-us/azure/azure-local/manage/manage-data-disks?view=azloc-2606 |
| Use AKS storage classes to consume external SAN on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/use-external-storage-for-containerized-workloads?view=azloc-2606 |
| Create Azure Local Arc-enabled VMs from Azure Compute Gallery | https://learn.microsoft.com/en-us/azure/azure-local/manage/virtual-machine-image-azure-compute-gallery?view=azloc-2606 |
| Create Azure Local VM images from Azure Marketplace | https://learn.microsoft.com/en-us/azure/azure-local/manage/virtual-machine-image-azure-marketplace?view=azloc-2606 |
| Create Azure Local Arc-enabled VMs from Azure Storage images | https://learn.microsoft.com/en-us/azure/azure-local/manage/virtual-machine-image-storage-account?view=azloc-2606 |
| Configure discovery and replication for Hyper-V migration | https://learn.microsoft.com/en-us/azure/azure-local/migrate/migrate-hyperv-replicate?view=azloc-2606 |
| Automate Azure Local VM migration with PowerShell and CLI | https://learn.microsoft.com/en-us/azure/azure-local/migrate/migrate-via-powershell?view=azloc-2606 |
| Configure discovery and replication for VMware migration | https://learn.microsoft.com/en-us/azure/azure-local/migrate/migrate-vmware-replicate?view=azloc-2606 |
| Download Azure managed disks to Azure Local multi-rack | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-manage-data-disks?view=azloc-2606 |
| Create Azure Local multi-rack VM images from Azure Storage | https://learn.microsoft.com/en-us/azure/azure-local/multi-rack/multi-rack-virtual-machine-image-storage-account?view=azloc-2606 |

### Deployment
| Topic | URL |
|-------|-----|
| Plan Network Controller deployment on Azure Local 23H2 | https://learn.microsoft.com/en-us/azure/azure-local/concepts/plan-network-controller-deployment?view=azloc-2606 |
| Add or repair nodes in Azure Local rack aware clusters | https://learn.microsoft.com/en-us/azure/azure-local/concepts/rack-aware-cluster-add-server?view=azloc-2606 |
| Deploy disaggregated Azure Local via Azure portal | https://learn.microsoft.com/en-us/azure/azure-local/deploy/deploy-via-portal-disaggregated?view=azloc-2606 |
| Deploy an Azure Local instance using Azure portal | https://learn.microsoft.com/en-us/azure/azure-local/deploy/deploy-via-portal?view=azloc-2606 |
| Deploy disaggregated Azure Local using ARM templates | https://learn.microsoft.com/en-us/azure/azure-local/deploy/deployment-azure-resource-manager-template-disaggregated?view=azloc-2606 |
| Deploy Azure Local with ARM template at scale | https://learn.microsoft.com/en-us/azure/azure-local/deploy/deployment-azure-resource-manager-template?view=azloc-2606 |
| Install Azure Local OS for disaggregated deployments | https://learn.microsoft.com/en-us/azure/azure-local/deploy/deployment-install-os-disaggregated?view=azloc-2606 |
| Deploy Azure Local with local identity and Key Vault via ARM template | https://learn.microsoft.com/en-us/azure/azure-local/deploy/deployment-local-identity-with-key-vault-template?view=azloc-2606 |
| Review Azure Local deployment prerequisites and checklist | https://learn.microsoft.com/en-us/azure/azure-local/deploy/deployment-prerequisites?view=azloc-2606 |
| Deploy virtualized Azure Local instances on Hyper-V | https://learn.microsoft.com/en-us/azure/azure-local/deploy/deployment-virtual?view=azloc-2606 |
| Deploy Azure Local rack aware clusters via Azure portal | https://learn.microsoft.com/en-us/azure/azure-local/deploy/rack-aware-cluster-deploy-portal?view=azloc-2606 |
| Deploy rack aware clusters using ARM templates | https://learn.microsoft.com/en-us/azure/azure-local/deploy/rack-aware-cluster-deployment-via-template?view=azloc-2606 |
| Perform post-deployment tasks for rack aware clusters | https://learn.microsoft.com/en-us/azure/azure-local/deploy/rack-aware-cluster-post-deployment?view=azloc-2606 |
| Deploy SDN infrastructure with SDN Express scripts | https://learn.microsoft.com/en-us/azure/azure-local/deploy/sdn-express-23h2?view=azloc-2606 |
| Deploy SDN via Windows Admin Center on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/deploy/sdn-wizard-23h2?view=azloc-2606 |
| Deploy SQL Server workloads on Azure Local 23H2 | https://learn.microsoft.com/en-us/azure/azure-local/deploy/sql-server-23h2?view=azloc-2606 |
| Deploy Azure Local disconnected operations in your datacenter | https://learn.microsoft.com/en-us/azure/azure-local/manage/disconnected-operations-deploy?view=azloc-2606 |
| Update Azure Local disconnected operations appliances | https://learn.microsoft.com/en-us/azure/azure-local/manage/disconnected-operations-update?view=azloc-2606 |
| Repair Azure Local nodes in version 23H2 clusters | https://learn.microsoft.com/en-us/azure/azure-local/manage/repair-server?view=azloc-2606 |
| Suspend and resume Azure Local machines for maintenance | https://learn.microsoft.com/en-us/azure/azure-local/manage/suspend-resume-cluster-maintenance?view=azloc-2606 |
| Upgrade SDN gateway VMs with minimal disruption | https://learn.microsoft.com/en-us/azure/azure-local/manage/upgrade-sdn-gateways?view=azloc-2606 |
| Upgrade SDN infrastructure managed by on-prem tools | https://learn.microsoft.com/en-us/azure/azure-local/manage/upgrade-sdn?view=azloc-2606 |
| Deploy and hotpatch Windows Server Azure Edition VMs on Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/manage/windows-server-azure-edition-23h2?view=azloc-2606 |
| Execute Hyper-V VM migration to Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/migrate/migrate-azure-migrate?view=azloc-2606 |
| Execute VMware VM migration to Azure Local | https://learn.microsoft.com/en-us/azure/azure-local/migrate/migrate-vmware-migrate?view=azloc-2606 |
| Track Azure Local release and update paths | https://learn.microsoft.com/en-us/azure/azure-local/release-information-23h2?view=azloc-2606 |
| Use Azure Update Manager for Azure Local updates | https://learn.microsoft.com/en-us/azure/azure-local/update/azure-update-manager-23h2?view=azloc-2606 |
| Import and discover Azure Local updates offline | https://learn.microsoft.com/en-us/azure/azure-local/update/import-discover-updates-offline-23h2?view=azloc-2606 |
| Apply Azure Local solution updates via PowerShell | https://learn.microsoft.com/en-us/azure/azure-local/update/update-via-powershell-23h2?view=azloc-2606 |
| Deploy Azure Local solution upgrade using ARM templates | https://learn.microsoft.com/en-us/azure/azure-local/upgrade/install-solution-upgrade-azure-resource-manager-template?view=azloc-2606 |
| Install Azure Local solution upgrade after OS upgrade | https://learn.microsoft.com/en-us/azure/azure-local/upgrade/install-solution-upgrade?view=azloc-2606 |
| Perform post-upgrade tasks for Azure Local via PowerShell | https://learn.microsoft.com/en-us/azure/azure-local/upgrade/post-upgrade-steps?view=azloc-2606 |
| Upgrade Azure Stack HCI OS to 24H2 via PowerShell | https://learn.microsoft.com/en-us/azure/azure-local/upgrade/upgrade-22h2-to-23h2-powershell?view=azloc-2606 |