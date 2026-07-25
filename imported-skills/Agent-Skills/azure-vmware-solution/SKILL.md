---
name: azure-vmware-solution
description: Expert knowledge for Azure VMware Solution development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when designing AVS private clouds, NSX/HCX networking, Horizon VDI, SQL migrations, or JetStream DR, and other Azure VMware Solution related development tasks. Not for Azure Virtual Machines (use azure-virtual-machines), Azure Large Instances (use azure-large-instances), Azure Stack Edge (use azure-stack-edge), Azure Migrate (use azure-migrate).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure VMware Solution Skill

This skill provides expert guidance for Azure VMware Solution. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L43 | Diagnosing and fixing Azure VMware Solution issues, including deployment failures, known platform problems, and disaster recovery errors for Azure VMware VMs. |
| Best Practices | L44-L50 | Guidance on securing and safely operating AVS private clouds, plus tuning NSX/HCX scale and performance for efficient, reliable VMware workload migrations. |
| Decision Making | L51-L63 | Guidance for planning AVS workloads: choosing APIs, backup and storage, migration/region moves, SQL/Windows licensing, and reserved instance purchasing decisions. |
| Architecture & Design Patterns | L64-L76 | Network, storage, and private cloud design for AVS: hub-spoke patterns, vSAN/stretched clusters, Horizon and GitHub Enterprise sizing, Cloud Director networking, and Gen 2 architecture. |
| Limits & Quotas | L77-L88 | AVS capacity, host/cluster/vSAN limits, routing constraints, required ports, and how to plan, request quota, deploy, and scale private clouds within platform limits. |
| Security | L89-L105 | Securing AVS: identity/access control, Defender for Cloud, vSAN CMK encryption, LDAP/vCenter identity, Trusted Launch/vTPM, NSX Edge internet, ESU, app protection, credential rotation, and best practices. |
| Configuration | L106-L143 | Configuring AVS infrastructure: networking, DNS/DHCP, storage/datastores, backup, monitoring/metrics, Arc/Run Command, HCX, Cloud Director, and high availability/placement settings. |
| Integrations & Coding Patterns | L144-L155 | Patterns for connecting AVS to Azure services: storage, backups, monitoring, syslog, NetApp Files, VPN/Virtual WAN, HCX internet, and VMware Tools repo configuration. |
| Deployment | L156-L166 | Guides for planning and deploying AVS for production, including Horizon/Citrix VDI, JetStream DR, VMware Cloud Director, and migrating SQL (Always On, FCI, standalone) to Azure VMware Solution. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Resolve Azure VMware Solution known issues and workarounds | https://learn.microsoft.com/en-us/azure/azure-vmware/azure-vmware-solution-known-issues |
| Resolve disaster recovery issues for Azure VMware VMs | https://learn.microsoft.com/en-us/azure/azure-vmware/ecosystem-disaster-recovery-vms |
| Troubleshoot Azure VMware Solution deployment failures | https://learn.microsoft.com/en-us/azure/azure-vmware/fix-deployment-failures |

### Best Practices
| Topic | URL |
|-------|-----|
| Optimize NSX performance for HCX migrations in Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/azure-vmware-solution-nsx-scale-and-performance-recommendations-for-vmware-hcx |
| Maintain Azure VMware Solution private clouds safely | https://learn.microsoft.com/en-us/azure/azure-vmware/azure-vmware-solution-private-cloud-maintenance |
| Optimize NSX scale and performance for HCX migrations in Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/vmware-hcx-mon-guidance |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose API Management SKUs for Azure VMware workloads | https://learn.microsoft.com/en-us/azure/azure-vmware/architecture-identity |
| Select backup solutions for Azure VMware Solution VMs | https://learn.microsoft.com/en-us/azure/azure-vmware/ecosystem-back-up-vms |
| Choose external storage options for Azure VMware | https://learn.microsoft.com/en-us/azure/azure-vmware/ecosystem-external-storage-solutions |
| Evaluate migration solutions for AVS virtual machines | https://learn.microsoft.com/en-us/azure/azure-vmware/ecosystem-migration-vms |
| Use Azure VMware Solution: FAQs and guidance | https://learn.microsoft.com/en-us/azure/azure-vmware/faq |
| Choose and Apply Licensing for SQL and Windows on AVS | https://learn.microsoft.com/en-us/azure/azure-vmware/license-sql-windows-in-avs |
| Plan and execute workload migration between AVS private clouds | https://learn.microsoft.com/en-us/azure/azure-vmware/migrate-between-private-clouds |
| Plan and migrate Azure VMware Solution across regions | https://learn.microsoft.com/en-us/azure/azure-vmware/move-azure-vmware-solution-across-regions |
| Decide and purchase Azure VMware reserved instances | https://learn.microsoft.com/en-us/azure/azure-vmware/reserved-instance |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Integrate Azure VMware Solution into hub-spoke networks | https://learn.microsoft.com/en-us/azure/azure-vmware/architecture-api-management |
| Apply network design patterns for Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/architecture-design-public-internet-access |
| Design hub-and-spoke integration for Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/architecture-hub-and-spoke |
| Plan storage architecture for Azure VMware Solution private clouds | https://learn.microsoft.com/en-us/azure/azure-vmware/architecture-networking |
| Design Azure VMware Solution vSAN stretched clusters | https://learn.microsoft.com/en-us/azure/azure-vmware/architecture-private-clouds |
| Design storage architecture for Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/architecture-storage |
| Size and configure GitHub Enterprise Server on AVS | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-github-enterprise-server |
| Design networking for VMware Cloud Director on AVS | https://learn.microsoft.com/en-us/azure/azure-vmware/enable-vmware-vcd-with-azure-network |
| Design Azure VMware Solution Gen 2 private clouds | https://learn.microsoft.com/en-us/azure/azure-vmware/native-network-design-consideration |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Use Azure VMware Solution network planning checklist and port requirements | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-site-to-site-vpn-gateway |
| Configure vSAN ESA host and cluster settings in AVS | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-vsan-esa |
| Understand Azure VMware Solution host and cluster limits | https://learn.microsoft.com/en-us/azure/azure-vmware/introduction |
| Understand AVS Gen 2 routing architecture and limits | https://learn.microsoft.com/en-us/azure/azure-vmware/native-network-routing-architecture |
| Request and manage Azure VMware host quota | https://learn.microsoft.com/en-us/azure/azure-vmware/request-host-quota-azure-vmware-solution |
| Capacity limits for Azure VMware private cloud deployment | https://learn.microsoft.com/en-us/azure/azure-vmware/tutorial-create-private-cloud |
| Deploy an Azure VMware Solution private cloud with host and cluster limits | https://learn.microsoft.com/en-us/azure/azure-vmware/tutorial-network-checklist |
| Scale Azure VMware Solution private cloud within platform limits | https://learn.microsoft.com/en-us/azure/azure-vmware/tutorial-scale-private-cloud |

### Security
| Topic | URL |
|-------|-----|
| Configure identity and access for Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/architecture-stretched-clusters |
| Integrate Microsoft Defender for Cloud with Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/azure-security-integration |
| Configure customer-managed key encryption for AVS vSAN | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-customer-managed-keys |
| Configure external LDAP identity source for NSX on AVS | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-external-identity-source-nsx-t |
| Configure external identity sources for Azure VMware vCenter | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-identity-source-vcenter |
| Configure Trusted Launch and vTPM for Azure VMware VMs | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-virtual-trusted-platform-module |
| Enable NSX Edge public IPs and internet access in AVS | https://learn.microsoft.com/en-us/azure/azure-vmware/enable-public-ip-nsx-edge |
| Configure Extended Security Updates in Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/extended-security-updates-windows-sql-server |
| Re-enable Azure VMware Solution Gen2 service principal | https://learn.microsoft.com/en-us/azure/azure-vmware/native-first-party-principle-security |
| Manually configure AVS Gen 2 role assignments | https://learn.microsoft.com/en-us/azure/azure-vmware/native-role-assignment |
| Protect AVS web apps with Azure Application Gateway | https://learn.microsoft.com/en-us/azure/azure-vmware/protect-azure-vmware-solution-with-application-gateway |
| Rotate vCenter and NSX cloud admin credentials securely | https://learn.microsoft.com/en-us/azure/azure-vmware/rotate-cloudadmin-credentials |
| Apply security best practices to Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/security-recommendations |

### Configuration
| Topic | URL |
|-------|-----|
| Configure guest management and extensions on Arc-enabled VMs | https://learn.microsoft.com/en-us/azure/azure-vmware/arc-enable-guest-management |
| Enable and configure Managed SNAT for Azure VMware workloads | https://learn.microsoft.com/en-us/azure/azure-vmware/architecture-migrate |
| Configure networking and interconnectivity for Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/architecture-network-design-considerations |
| Configure Azure NetApp Files NFS datastores for AVS hosts | https://learn.microsoft.com/en-us/azure/azure-vmware/attach-azure-netapp-files-to-azure-vmware-solution-hosts |
| Configure Cloud Backup policies for AVS datastores and VMs | https://learn.microsoft.com/en-us/azure/azure-vmware/backup-azure-netapp-files-datastores-vms |
| Back up AVS VMware virtual machines with Azure Backup Server | https://learn.microsoft.com/en-us/azure/azure-vmware/backup-azure-vmware-solution-virtual-machines |
| Configure alerts and metrics monitoring for Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-alerts-for-azure-vmware-solution |
| Use Azure Elastic SAN as AVS iSCSI datastore | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-azure-elastic-san |
| Create Azure Monitor resource health alerts for AVS | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-azure-monitor-for-resource-health-for-azure-vmware-solution |
| Configure Azure VMware Solution performance and health metrics | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-azure-vmware-solution-metrics |
| Manage AVS datastores and VMDKs with Cloud Backup | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-cloud-backup-virtual-machine |
| Configure DHCP options for Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-dhcp-azure-vmware-solution |
| Configure HCX network extension high availability for AVS | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-hcx-network-extension-high-availability |
| Configure DNS forwarders and private DNS for Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-l2-stretched-vmware-hcx-networks |
| Set up port mirroring for Azure VMware Solution network traffic | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-nsx-network-components-azure-portal |
| Configure Pure Cloud Block Store with Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-pure-cloud-block-store |
| Configure vSAN storage policies for AVS virtual machines | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-storage-policy |
| Configure VMware Cloud Director Service on Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-vmware-cloud-director-service-azure-vmware-solution |
| Configure diagnostic settings to collect VMware syslogs from AVS | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-vmware-syslogs |
| Configure VMware vSAN settings in Azure VMware Solution clusters | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-vsan |
| Configure Windows Server Failover Cluster on Azure VMware vSAN | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-windows-server-failover-cluster |
| Configure VM placement policies in Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/create-placement-policy |
| Configure VMware Cloud Director Availability on Azure VMware | https://learn.microsoft.com/en-us/azure/azure-vmware/deploy-vmware-cloud-director-availability-in-azure-vmware-solution |
| Configure Managed SNAT for Azure VMware workloads | https://learn.microsoft.com/en-us/azure/azure-vmware/enable-managed-snat-for-workloads |
| Configure Azure Hybrid Benefit Unlimited Virtualization for SQL on AVS | https://learn.microsoft.com/en-us/azure/azure-vmware/enable-sql-azure-hybrid-benefit |
| Enable VMware Cloud Director on Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/enable-vmware-vcd-with-azure |
| Manage Arc resource bridge and credentials for Azure VMware | https://learn.microsoft.com/en-us/azure/azure-vmware/manage-arc-enabled-azure-vmware-solution |
| Configure automatic peering sync for AVS Gen 2 networks | https://learn.microsoft.com/en-us/azure/azure-vmware/native-auto-peering-sync |
| Configure networking between Azure VMware Gen1 and Gen2 clouds | https://learn.microsoft.com/en-us/azure/azure-vmware/native-connect-private-cloud-previous-edition |
| Configure DNS forward lookup zones for Azure VMware Gen2 | https://learn.microsoft.com/en-us/azure/azure-vmware/native-dns-forward-lookup-zone |
| Execute VMware HCX Run Commands in AVS | https://learn.microsoft.com/en-us/azure/azure-vmware/use-hcx-run-commands |
| Configure vCenter login banner via AVS Run Command | https://learn.microsoft.com/en-us/azure/azure-vmware/use-vcenter-login-banner-run-command |
| Use Run Commands and CloudAdmin in Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/using-run-command |
| Configure VMware Aria Operations for Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/vrealize-operations-for-azure-vmware-solution |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate Azure Native Pure Storage Cloud with AVS | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-azure-native-pure-storage-cloud |
| Configure site-to-site VPN with Azure Virtual WAN for Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/configure-port-mirroring-azure-vmware-solution |
| Enable HCX internet access for Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/enable-hcx-access-over-internet |
| Install Cloud Backup plug-in for Azure VMware VMs | https://learn.microsoft.com/en-us/azure/azure-vmware/install-cloud-backup-virtual-machines |
| Integrate Azure Native Monitoring and Protection with AVS VMs | https://learn.microsoft.com/en-us/azure/azure-vmware/integrate-azure-native-services |
| Send AVS VMware syslogs via Azure Logic Apps | https://learn.microsoft.com/en-us/azure/azure-vmware/logs-via-logic-app |
| Use Azure NetApp Files shares with AVS virtual machines | https://learn.microsoft.com/en-us/azure/azure-vmware/netapp-files-with-azure-vmware-solution |
| Configure Set-ToolsRepo run command for VMware Tools in AVS | https://learn.microsoft.com/en-us/azure/azure-vmware/use-set-toolsrepo-run-command |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy Citrix Virtual Apps and Desktops on Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/azure-vmware-solution-citrix |
| Deploy VMware Horizon on Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/azure-vmware-solution-horizon |
| Deploy JetStream DR for Azure VMware Solution and on-premises workloads | https://learn.microsoft.com/en-us/azure/azure-vmware/deploy-disaster-recovery-using-jetstream |
| Enable VMware Cloud Director service with Azure VMware Solution | https://learn.microsoft.com/en-us/azure/azure-vmware/enable-vmware-cds-with-azure |
| Migrate SQL Always On groups to Azure VMware | https://learn.microsoft.com/en-us/azure/azure-vmware/migrate-sql-server-always-on-availability-group |
| Migrate SQL Server failover cluster to Azure VMware | https://learn.microsoft.com/en-us/azure/azure-vmware/migrate-sql-server-failover-cluster |
| Migrate standalone SQL Server to Azure VMware | https://learn.microsoft.com/en-us/azure/azure-vmware/migrate-sql-server-standalone-cluster |
| Plan production-ready Azure VMware Solution deployment | https://learn.microsoft.com/en-us/azure/azure-vmware/plan-private-cloud-deployment |