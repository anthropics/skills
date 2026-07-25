---
name: azure-site-recovery
description: Expert knowledge for Azure Site Recovery development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when planning or automating ASR for Azure VMs, VMware/Hyper-V, physical servers, ExpressRoute, or SQL workloads, and other Azure Site Recovery related development tasks. Not for Azure Backup (use azure-backup), Azure Migrate (use azure-migrate), Azure Virtual Machines (use azure-virtual-machines), Azure Virtual Machine Scale Sets (use azure-vm-scalesets).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-05"
  generator: "docs2skills/1.0.0"
---
# Azure Site Recovery Skill

This skill provides expert guidance for Azure Site Recovery. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L64 | Diagnosing and fixing Azure Site Recovery replication, failover, agent/extension, network, and appliance issues for Azure VMs, Hyper-V, VMware, and physical servers. |
| Best Practices | L65-L70 | Guidance on tuning Azure Site Recovery performance: analyzing high data churn on VMs, and monitoring/troubleshooting process server health, capacity, and throughput. |
| Decision Making | L71-L88 | Planning and sizing Azure Site Recovery: choosing tools vs Azure Migrate, VMware/Hyper-V DR capacity and cost estimation, managed disk pricing, failover/failback options, and classic-to-modern migration. |
| Architecture & Design Patterns | L89-L98 | Designing Azure Site Recovery architectures for specific workloads (AD/DNS, SAP, Dynamics AX, SharePoint, IIS, SQL, VMware, file servers) and multi-tier app DR patterns. |
| Limits & Quotas | L99-L109 | Limits, capacity planning, and compatibility for Azure Site Recovery: churn limits, safe use with Backup, planner limitations, VMware/physical support, scaling, and Mobility service resource usage. |
| Security | L110-L120 | Securing Azure Site Recovery: NSGs, TLS, encryption changes, RBAC, managed identities, and hardening replication appliances/VMware replication traffic. |
| Configuration | L121-L179 | Configuring Azure Site Recovery for Azure VMs, VMware, Hyper-V, and physical servers, including networking, encryption, policies, appliances, monitoring, and replication/failback setup. |
| Integrations & Coding Patterns | L180-L193 | Automating and integrating Azure Site Recovery with scripts and infrastructure tools (PowerShell, ARM/Bicep, Terraform) plus networking/traffic (ExpressRoute, Traffic Manager) and Hyper-V/VMware DR planning. |
| Deployment | L194-L201 | Support and compatibility details for Azure Site Recovery deployments: DR support matrices for VMware/Hyper-V/replication appliances/shared disks and guidance on migrating from classic to modern VMware DR. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Resolve common Azure-to-Azure Site Recovery issues | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-common-questions |
| Resolve protection errors in Azure-to-Azure VM replication | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-protection-errors |
| Troubleshoot other Azure Site Recovery replication issues | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-troubleshoot-errors |
| Diagnose network connectivity issues for Azure-to-Azure Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-troubleshoot-network-connectivity |
| Troubleshoot common Azure VM replication problems in Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-troubleshoot-replication |
| Fix VM-level errors in Azure Site Recovery replication | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-virtual-machine-errors |
| Resolve common Hyper-V to Azure Site Recovery issues | https://learn.microsoft.com/en-us/azure/site-recovery/hyper-v-azure-common-questions |
| Resolve Hyper-V to Azure replication issues in Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/hyper-v-azure-troubleshoot |
| Troubleshoot and configure Azure Site Recovery monitoring | https://learn.microsoft.com/en-us/azure/site-recovery/monitoring-common-questions |
| Fix Azure Site Recovery VM agent and extension issues | https://learn.microsoft.com/en-us/azure/site-recovery/site-recovery-extension-troubleshoot |
| Troubleshoot failover to Azure errors in Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/site-recovery-failover-to-azure-troubleshoot |
| Use Site Recovery dashboard and alerts to diagnose replication issues | https://learn.microsoft.com/en-us/azure/site-recovery/site-recovery-monitor-and-troubleshoot |
| Run VMM cleanup script to unregister disconnected Site Recovery servers | https://learn.microsoft.com/en-us/azure/site-recovery/unregister-vmm-server-script |
| Resolve common VMware to Azure Site Recovery issues | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-azure-common-questions |
| Troubleshoot Azure Site Recovery configuration server deployment issues | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-azure-troubleshoot-configuration-server |
| Troubleshoot VMware failback and reprotection with Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-azure-troubleshoot-failback-reprotect |
| Troubleshoot Mobility Service push installation failures | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-azure-troubleshoot-push-install |
| Resolve replication issues for VMware and physical servers to Azure | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-azure-troubleshoot-replication |
| Fix Azure Site Recovery error 78144 for missing app-consistent points | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-azure-troubleshoot-replication-vss-installation-failure-behaviors |
| Troubleshoot Azure Site Recovery Provider upgrade failures | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-azure-troubleshoot-upgrade-failures |
| Diagnose VMware vCenter discovery failures in Azure Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-azure-troubleshoot-vcenter-discovery-failures |
| Troubleshoot Azure Site Recovery process server issues | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-physical-azure-troubleshoot-process-server |
| Troubleshoot VMware replication appliance health in Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-troubleshoot-appliance-health-issue |
| Resolve VMware mobility agent health errors in Azure Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-troubleshoot-mobility-agent-health |

### Best Practices
| Topic | URL |
|-------|-----|
| Analyze and mitigate high churn patterns on Site Recovery VMs | https://learn.microsoft.com/en-us/azure/site-recovery/monitoring-high-churn |
| Monitor Azure Site Recovery process server health and performance | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-physical-azure-monitor-process-server |

### Decision Making
| Topic | URL |
|-------|-----|
| Use alternative VM size recommendations during failover | https://learn.microsoft.com/en-us/azure/site-recovery/alternative-vm-size-failover-flow |
| Plan migration from classic to modernized VMware DR | https://learn.microsoft.com/en-us/azure/site-recovery/classic-to-modernized-common-questions |
| Choose and plan failback type with Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/concepts-types-of-failback |
| Use Site Recovery deployment planner for capacity and cost | https://learn.microsoft.com/en-us/azure/site-recovery/deployment-planner-cost-estimation |
| Analyze Hyper-V Deployment Planner capacity report | https://learn.microsoft.com/en-us/azure/site-recovery/hyper-v-deployment-planner-analyze-report |
| Review Hyper-V DR cost estimation from Planner | https://learn.microsoft.com/en-us/azure/site-recovery/hyper-v-deployment-planner-cost-estimation |
| Plan Hyper-V to Azure disaster recovery capacity | https://learn.microsoft.com/en-us/azure/site-recovery/hyper-v-deployment-planner-overview |
| Choose between Azure Migrate and Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/migrate-overview |
| Evaluate Site Recovery for Citrix XenDesktop/XenApp DR | https://learn.microsoft.com/en-us/azure/site-recovery/site-recovery-citrix-xenapp-and-xendesktop |
| Estimate and understand Azure Site Recovery managed disk costs | https://learn.microsoft.com/en-us/azure/site-recovery/site-recovery-cost |
| Use Deployment Planner for VMware-to-Azure DR sizing | https://learn.microsoft.com/en-us/azure/site-recovery/site-recovery-deployment-planner |
| Interpret Deployment Planner reports for VMware DR | https://learn.microsoft.com/en-us/azure/site-recovery/site-recovery-vmware-deployment-planner-analyze-report |
| Interpret cost estimations from Site Recovery Deployment Planner | https://learn.microsoft.com/en-us/azure/site-recovery/site-recovery-vmware-deployment-planner-cost-estimation |
| Plan for deprecation of classic VMware/physical DR | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-physical-azure-classic-deprecation |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Protect on-premises file servers with Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/file-server-disaster-recovery |
| Design Dynamics AX disaster recovery using Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/site-recovery-dynamicsax |
| Configure IIS web app disaster recovery with Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/site-recovery-iis |
| Set up SAP NetWeaver disaster recovery on Azure | https://learn.microsoft.com/en-us/azure/site-recovery/site-recovery-sap |
| Implement DR for multi-tier SharePoint with Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/site-recovery-sharepoint |
| Combine SQL Server BCDR with Azure Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/site-recovery-sql |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Use Azure Site Recovery high churn limits for VMs | https://learn.microsoft.com/en-us/azure/site-recovery/concepts-azure-to-azure-high-churn-support |
| Use Azure Site Recovery with Azure Backup safely | https://learn.microsoft.com/en-us/azure/site-recovery/site-recovery-backup-interoperability |
| Review version history and limitations of Site Recovery Deployment Planner | https://learn.microsoft.com/en-us/azure/site-recovery/site-recovery-deployment-planner-history |
| Plan capacity for VMware disaster recovery with Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/site-recovery-plan-capacity-vmware |
| Check VMware and physical server support for Azure Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-physical-azure-support-matrix |
| Scale Site Recovery for large VMware deployments | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-physical-large-deployment |
| Understand Mobility service resource usage for VMware DR | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-physical-mobility-service-overview |

### Security
| Topic | URL |
|-------|-----|
| Configure Network Security Groups for Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/concepts-network-security-group-with-site-recovery |
| Deploy secure Azure Site Recovery replication appliance | https://learn.microsoft.com/en-us/azure/site-recovery/deploy-vmware-azure-replication-appliance-modernized |
| Remediate deprecated Site Recovery data encryption feature | https://learn.microsoft.com/en-us/azure/site-recovery/encryption-feature-deprecation |
| Migrate Site Recovery automation from Run As accounts to managed identities | https://learn.microsoft.com/en-us/azure/site-recovery/how-to-migrate-run-as-accounts-managed-identity |
| Apply Azure RBAC roles for Site Recovery access control | https://learn.microsoft.com/en-us/azure/site-recovery/site-recovery-role-based-linked-access-control |
| Configure TLS security for Azure Site Recovery traffic | https://learn.microsoft.com/en-us/azure/site-recovery/transport-layer-security |
| Configure secure VMware VM replication to Azure | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-azure-set-up-replication-tutorial-modernized |

### Configuration
| Topic | URL |
|-------|-----|
| Fail back Azure VMware Solution workloads from Azure | https://learn.microsoft.com/en-us/azure/site-recovery/avs-tutorial-failback |
| Configure Azure VMware Solution environment for Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/avs-tutorial-prepare-avs |
| Prepare Azure resources for Azure VMware Solution disaster recovery | https://learn.microsoft.com/en-us/azure/site-recovery/avs-tutorial-prepare-azure |
| Enable replication for Azure VMware Solution VMs to Azure | https://learn.microsoft.com/en-us/azure/site-recovery/avs-tutorial-replication |
| Manage automatic Mobility service updates in Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-autoupdate |
| Customize failover VM networking settings in Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-customize-networking |
| Enable global Azure-to-Azure disaster recovery with Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-enable-global-disaster-recovery |
| Enable replication for newly added Azure VM data disks | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-enable-replication-added-disk |
| Exclude Azure VM disks from Site Recovery using PowerShell | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-exclude-disks |
| Enable Site Recovery protection using Azure Policy assignments | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-how-to-enable-policy |
| Configure Site Recovery for ADE-encrypted Azure virtual machines | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-how-to-enable-replication-ade-vms |
| Enable Site Recovery for VMs using CMK-encrypted managed disks | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-how-to-enable-replication-cmk-disks |
| Configure private endpoint-based replication for Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-how-to-enable-replication-private-endpoints |
| Configure Site Recovery for Storage Spaces Direct guest clusters | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-how-to-enable-replication-s2d-vms |
| Enable zone-to-zone disaster recovery for Azure virtual machines | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-how-to-enable-zone-to-zone-disaster-recovery |
| Reprotect Azure VMs back to primary region after failover | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-how-to-reprotect |
| Configure virtual network mapping for Azure Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-network-mapping |
| Prepare migrated Azure VMs for cross-region disaster recovery | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-replicate-after-migration |
| Enable accelerated networking for Site Recovery VMs | https://learn.microsoft.com/en-us/azure/site-recovery/azure-vm-disaster-recovery-with-accelerated-networking |
| Configure multiple IP address failover in Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/concepts-multiple-ip-address-failover |
| Configure connectivity to Azure VMs after Site Recovery failover | https://learn.microsoft.com/en-us/azure/site-recovery/concepts-on-premises-to-azure-networking |
| Assign public IP addresses after Site Recovery failover | https://learn.microsoft.com/en-us/azure/site-recovery/concepts-public-ip-address-with-site-recovery |
| Configure trusted launch VMs with Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/concepts-trusted-vm |
| Set Mobility Service proxy settings for Azure DR | https://learn.microsoft.com/en-us/azure/site-recovery/configure-mobility-service-proxy-settings |
| Remove an Azure Site Recovery replication appliance | https://learn.microsoft.com/en-us/azure/site-recovery/delete-appliance |
| Delete a Recovery Services vault configured for Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/delete-vault |
| Enable Extended Zones VM disaster recovery during VM creation | https://learn.microsoft.com/en-us/azure/site-recovery/disaster-recovery-for-edge-zone-via-vm-flow-tutorial |
| Configure disaster recovery for VMs on Azure Extended Zones via vault flow | https://learn.microsoft.com/en-us/azure/site-recovery/disaster-recovery-for-edge-zone-vm-tutorial |
| Configure Azure Site Recovery with private endpoints | https://learn.microsoft.com/en-us/azure/site-recovery/hybrid-how-to-enable-replication-private-endpoints |
| Configure on-premises Hyper-V infrastructure for Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/hyper-v-prepare-on-premises-tutorial |
| Configure Hyper-V network mapping with Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/hyper-v-vmm-network-mapping |
| Configure Azure Monitor Logs for Azure Site Recovery monitoring | https://learn.microsoft.com/en-us/azure/site-recovery/monitor-log-analytics |
| Reference for Azure Site Recovery monitoring metrics and logs | https://learn.microsoft.com/en-us/azure/site-recovery/monitor-site-recovery-reference |
| Manage configuration server for physical server DR to Azure | https://learn.microsoft.com/en-us/azure/site-recovery/physical-manage-configuration-server |
| Enable replication for on-premises physical servers with modernized Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/physical-server-enable-replication |
| Set up Azure Site Recovery reporting with Monitor logs and workbooks | https://learn.microsoft.com/en-us/azure/site-recovery/report-site-recovery |
| Migrate from deprecated IPConfig parameters in Site Recovery cmdlets | https://learn.microsoft.com/en-us/azure/site-recovery/site-recovery-ipconfig-cmdlet-parameter-deprecation |
| Manage multi-NIC network adapters for on-premises to Azure failover | https://learn.microsoft.com/en-us/azure/site-recovery/site-recovery-manage-network-interfaces-on-premises-to-azure |
| Retain Azure VM IP addresses during Site Recovery failover | https://learn.microsoft.com/en-us/azure/site-recovery/site-recovery-retain-ip-azure-vm-failover |
| Run Azure Site Recovery Deployment Planner for VMware environments | https://learn.microsoft.com/en-us/azure/site-recovery/site-recovery-vmware-deployment-planner-run |
| Switch between replication appliances in modernized Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/switch-replication-appliance-modernized |
| Prepare Azure resources for on-premises Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/tutorial-prepare-azure |
| Protect shared disk Windows clusters with Azure Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/tutorial-shared-disk |
| Upgrade modernized Mobility Service and appliance components | https://learn.microsoft.com/en-us/azure/site-recovery/upgrade-mobility-service-modernized |
| Enable VMware virtual machine replication to Azure (Modernized) | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-azure-enable-replication |
| Enable replication for newly added VMware VM disks in Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-azure-enable-replication-added-disk |
| Prepare source machines for Mobility Service push install | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-azure-install-mobility-service |
| Manage Azure Site Recovery VMware configuration server | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-azure-manage-configuration-server |
| Manage Site Recovery process server for VMware/physical | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-azure-manage-process-server |
| Automate Mobility Service installation and updates | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-azure-mobility-install-configuration-mgr |
| Set up Azure process server for VMware/physical failback | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-azure-set-up-process-server-azure |
| Set up replication policies for VMware disaster recovery to Azure | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-azure-set-up-replication |
| Prepare Azure target environment for VMware replication | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-azure-set-up-target |
| Configure on-premises VMware environment for Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-azure-tutorial-prepare-on-premises |
| Manage Mobility agent for VMware and physical servers | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-physical-manage-mobility-service |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Configure shared disk disaster recovery using PowerShell | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-tutorial-enable-replication-shared-disk |
| Integrate Azure ExpressRoute with Site Recovery DR | https://learn.microsoft.com/en-us/azure/site-recovery/azure-vm-disaster-recovery-with-expressroute |
| Use ExpressRoute with Site Recovery for DR | https://learn.microsoft.com/en-us/azure/site-recovery/concepts-expressroute-with-site-recovery |
| Integrate Azure Traffic Manager with Site Recovery | https://learn.microsoft.com/en-us/azure/site-recovery/concepts-traffic-manager-with-site-recovery |
| Automate Hyper-V disaster recovery with PowerShell | https://learn.microsoft.com/en-us/azure/site-recovery/hyper-v-azure-powershell-resource-manager |
| Run Hyper-V Deployment Planner and generate reports | https://learn.microsoft.com/en-us/azure/site-recovery/hyper-v-deployment-planner-run |
| Provision Recovery Services vault using Bicep templates | https://learn.microsoft.com/en-us/azure/site-recovery/quickstart-create-vault-bicep |
| Create Recovery Services vault with ARM templates | https://learn.microsoft.com/en-us/azure/site-recovery/quickstart-create-vault-template |
| Automate Recovery Services vault setup using Terraform | https://learn.microsoft.com/en-us/azure/site-recovery/quickstart-create-vault-terraform |
| Automate VMware to Azure DR with PowerShell | https://learn.microsoft.com/en-us/azure/site-recovery/vmware-azure-disaster-recovery-powershell |

### Deployment
| Topic | URL |
|-------|-----|
| Check Azure Site Recovery support for VM DR | https://learn.microsoft.com/en-us/azure/site-recovery/azure-to-azure-support-matrix |
| Migrate VMware disaster recovery from classic to modernized | https://learn.microsoft.com/en-us/azure/site-recovery/how-to-move-from-classic-to-modernized-vmware-disaster-recovery |
| Verify Hyper-V to Azure Site Recovery support matrix | https://learn.microsoft.com/en-us/azure/site-recovery/hyper-v-azure-support-matrix |
| Support matrix for Azure Site Recovery replication appliance | https://learn.microsoft.com/en-us/azure/site-recovery/replication-appliance-support-matrix |
| Validate shared disk support in Azure VM DR | https://learn.microsoft.com/en-us/azure/site-recovery/shared-disk-support-matrix |