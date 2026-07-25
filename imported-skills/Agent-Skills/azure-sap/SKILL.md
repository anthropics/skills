---
name: azure-sap
description: Expert knowledge for SAP HANA on Azure Large Instances development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when deploying SAP HANA LI with Terraform/SDAF, Azure DevOps pipelines, Entra ID/RBAC, Azure Monitor, or SAP RISE, and other SAP HANA on Azure Large Instances related development tasks. Not for Azure Large Instances (use azure-large-instances), Azure Virtual Machines (use azure-virtual-machines), Azure Virtual Machine Scale Sets (use azure-vm-scalesets), Azure Baremetal Infrastructure (use azure-baremetal-infrastructure).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# SAP HANA on Azure Large Instances Skill

This skill provides expert guidance for SAP HANA on Azure Large Instances. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L51 | Diagnosing and fixing SAP on Azure issues: deployment automation, data extraction pipelines, SAP BPS artifacts, SAP Insights/AMS, Azure Monitor, VM scale sets, and SAP VM extensions. |
| Best Practices | L52-L62 | Best practices for testing SAP on Azure (HA/DR, config validation, Quality Insights), and optimizing infrastructure (DFS-N SAPMNT, Azure Files NFS/SMB, VM scale sets) for reliable SAP HANA LI workloads. |
| Decision Making | L63-L76 | Planning SAP HANA/SAP app architectures on Azure: supported VM/storage configs, software versions, DR and data tiering, connectivity, data extraction, and deployment automation choices. |
| Architecture & Design Patterns | L77-L112 | Architecting SAP on Azure: HA/DR, multi-region HANA, DB choices, NetWeaver HA, latency/availability zones, SAP RISE connectivity, and Copilot/SAP integration patterns. |
| Limits & Quotas | L113-L117 | SAP on Azure limits: supported platforms/features for SAP testing automation, Azure Monitor for SAP quotas/behavior, and sizing/HA deployment constraints using Azure Files SMB. |
| Security | L118-L133 | Security, identity, and access design for SAP on Azure: RBAC, Entra ID/SPNs, TLS, private endpoints, encrypted storage, and secure monitoring providers (Azure Monitor, Db2, SQL Server, RISE). |
| Configuration | L134-L210 | Configuring and customizing SAP on Azure: automation (Terraform/SDAF), networking, storage, HA/DR clusters, monitoring providers, data integration, and Azure Center for SAP registration. |
| Integrations & Coding Patterns | L211-L224 | Patterns and scripts for integrating SAP HANA on Azure with Azure Monitor, VIS (CLI/PowerShell/REST), Salesforce/BPS, RISE, Exchange, Universal Print, and ABAP/Principal Propagation. |
| Deployment | L225-L249 | Deploying and tearing down SAP landscapes on Azure, including automated control planes, pipelines (Azure DevOps/CLI), HA architectures, and workload-specific setups like S/4HANA, B1, BO, and NetWeaver. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot SAP Deployment Automation Framework issues on Azure | https://learn.microsoft.com/en-us/azure/sap/automation/troubleshooting |
| Monitor and troubleshoot Azure Data Factory extraction | https://learn.microsoft.com/en-us/azure/sap/business-process-solutions/monitor-data-extraction |
| Monitor and troubleshoot Fabric data extraction pipelines | https://learn.microsoft.com/en-us/azure/sap/business-process-solutions/monitor-fabric-data-extraction-processing |
| Troubleshoot Azure SAP Business Process Solutions issues | https://learn.microsoft.com/en-us/azure/sap/business-process-solutions/troubleshooting |
| Upgrade SAP Business Process Solutions artifacts safely | https://learn.microsoft.com/en-us/azure/sap/business-process-solutions/update-artifacts |
| Resolve common Azure Center for SAP solutions issues | https://learn.microsoft.com/en-us/azure/sap/center-sap-solutions/faq |
| Set up and troubleshoot SAP Joule–Microsoft 365 Copilot integration | https://learn.microsoft.com/en-us/azure/sap/microsoft-ai/joule/joule-copilot-overview |
| Enable SAP Insights for workload troubleshooting in AMS | https://learn.microsoft.com/en-us/azure/sap/monitor/enable-sap-insights |
| Resolve common issues in Azure Monitor for SAP | https://learn.microsoft.com/en-us/azure/sap/monitor/faq |
| Resolve common issues with SAP VM scale sets | https://learn.microsoft.com/en-us/azure/sap/workloads/virtual-machine-scale-set-sap-faq |
| Diagnose and fix Azure VM Extension for SAP issues | https://learn.microsoft.com/en-us/azure/sap/workloads/vm-extension-for-sap-troubleshooting |

### Best Practices
| Topic | URL |
|-------|-----|
| Validate SAP on Azure configuration with testing framework checks | https://learn.microsoft.com/en-us/azure/sap/automation/testing-framework-configuration-checks |
| Run high availability tests with SAP Testing Automation Framework | https://learn.microsoft.com/en-us/azure/sap/automation/testing-framework-high-availability |
| Use Quality Insights checks for SAP on Azure | https://learn.microsoft.com/en-us/azure/sap/center-sap-solutions/get-quality-checks-insights |
| Apply DR recommendations for each SAP workload layer | https://learn.microsoft.com/en-us/azure/sap/workloads/disaster-recovery-sap-guide |
| Use Windows DFS-N for SAPMNT naming with SMB shares | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-guide-windows-dfs |
| Optimize Azure Files SSD NFS/SMB for SAP workloads | https://learn.microsoft.com/en-us/azure/sap/workloads/planning-guide-storage-azure-files |
| Apply VM scale set deployment guidelines for SAP | https://learn.microsoft.com/en-us/azure/sap/workloads/virtual-machine-scale-set-sap-deployment-guide |

### Decision Making
| Topic | URL |
|-------|-----|
| Plan SAP Deployment Automation Framework usage on Azure | https://learn.microsoft.com/en-us/azure/sap/automation/plan-deployment |
| Plan and configure DR for Azure Center for SAP solutions | https://learn.microsoft.com/en-us/azure/sap/center-sap-solutions/compliance-cedr |
| Select certified SAP configurations on Azure | https://learn.microsoft.com/en-us/azure/sap/workloads/certifications |
| Choose methods to extract SAP data into Microsoft Fabric | https://learn.microsoft.com/en-us/azure/sap/workloads/extract-sap-data |
| Design SAP HANA data tiering and archiving on Azure | https://learn.microsoft.com/en-us/azure/sap/workloads/hana-tiering-guidance |
| Choose outbound connectivity options for SAP VMs on Azure | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-guide-standard-load-balancer-outbound-connections |
| Plan SAP application architecture on Azure VMs | https://learn.microsoft.com/en-us/azure/sap/workloads/planning-guide |
| Select Azure storage types for SAP workloads | https://learn.microsoft.com/en-us/azure/sap/workloads/planning-guide-storage |
| Select supported SAP on Azure VM configurations | https://learn.microsoft.com/en-us/azure/sap/workloads/planning-supported-configurations |
| Determine SAP software versions supported on Azure | https://learn.microsoft.com/en-us/azure/sap/workloads/supported-product-on-azure |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design SAP workload zones in the automation framework | https://learn.microsoft.com/en-us/azure/sap/automation/configure-workload-zone |
| Understand resiliency patterns in Azure Center for SAP solutions | https://learn.microsoft.com/en-us/azure/sap/center-sap-solutions/compliance-bcdr-reliabilty |
| Design Copilot–SAP integration via Azure API Management and VNet peering | https://learn.microsoft.com/en-us/azure/sap/microsoft-ai/copilot-studio/architecture-apim-virtual-network |
| Architect Copilot–SAP integration via SAP BTP and Cloud Connector | https://learn.microsoft.com/en-us/azure/sap/microsoft-ai/copilot-studio/architecture-business-technology-platform-api |
| Implement demo architecture for Copilot Studio with public SAP system | https://learn.microsoft.com/en-us/azure/sap/microsoft-ai/copilot-studio/architecture-demo |
| Architect Copilot–SAP integration using On-Premises Data Gateway | https://learn.microsoft.com/en-us/azure/sap/microsoft-ai/copilot-studio/architecture-on-premises-data-gateway |
| Plan SAP BusinessObjects BI architecture on Azure | https://learn.microsoft.com/en-us/azure/sap/workloads/businessobjects-deployment-guide |
| Architect DBMS deployments for SAP on Azure VMs | https://learn.microsoft.com/en-us/azure/sap/workloads/dbms-guide-general |
| Run SAP on IBM Db2 LUW in Azure VMs | https://learn.microsoft.com/en-us/azure/sap/workloads/dbms-guide-ibm |
| Deploy SAP MaxDB, liveCache, and Content Server on Azure | https://learn.microsoft.com/en-us/azure/sap/workloads/dbms-guide-maxdb |
| Deploy Oracle Database for SAP workloads on Azure | https://learn.microsoft.com/en-us/azure/sap/workloads/dbms-guide-oracle |
| Deploy SAP ASE DBMS for SAP on Azure VMs | https://learn.microsoft.com/en-us/azure/sap/workloads/dbms-guide-sapase |
| Design SAP BW NLS with SAP IQ on Azure | https://learn.microsoft.com/en-us/azure/sap/workloads/dbms-guide-sapiq |
| Deploy SQL Server DBMS for SAP on Azure VMs | https://learn.microsoft.com/en-us/azure/sap/workloads/dbms-guide-sqlserver |
| Plan SAP disaster recovery architecture on Azure | https://learn.microsoft.com/en-us/azure/sap/workloads/disaster-recovery-overview-guide |
| Design secure Azure PaaS exposure for SAP Process Orchestration | https://learn.microsoft.com/en-us/azure/sap/workloads/expose-sap-process-orchestration-on-azure |
| Design HA SAP NetWeaver on Azure VMs with RHEL and NFS | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-guide-rhel-nfs-simple-mount |
| Implement multi-SID HA SAP NetWeaver on SLES | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-guide-suse-multi-sid |
| Design HA SAP NetWeaver on SLES with NFS | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-guide-suse-nfs-simple-mount |
| Design HA SAP NetWeaver on Azure Files SMB | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-guide-windows-azure-files-smb |
| Architect SAP workloads with Azure Availability Zones | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-zones |
| Minimize SAP application latency with proximity placement | https://learn.microsoft.com/en-us/azure/sap/workloads/proximity-placement-scenarios |
| Architect Azure integration with SAP RISE landscapes | https://learn.microsoft.com/en-us/azure/sap/workloads/rise-integration |
| Select network connectivity options for SAP RISE on Azure | https://learn.microsoft.com/en-us/azure/sap/workloads/rise-integration-network |
| Design SAP HANA availability across Azure regions | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-hana-availability-across-regions |
| Choose SAP HANA availability options in one Azure region | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-hana-availability-one-region |
| Design SAP HANA availability architectures on Azure VMs | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-hana-availability-overview |
| Design SAP HANA high availability on Azure VMs (RHEL) | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-hana-high-availability-rhel |
| Implement SAP HANA scale-out HSR with Pacemaker on RHEL | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-hana-high-availability-scale-out-hsr-rhel |
| Design high-availability VM architectures for SAP NetWeaver | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-high-availability-architecture-scenarios |
| Design high availability for SAP NetWeaver on Azure VMs | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-high-availability-guide-start |
| Use Azure VM restart for higher SAP availability | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-higher-availability-architecture-scenarios |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Supported platforms and features for SAP Testing Automation Framework | https://learn.microsoft.com/en-us/azure/sap/automation/testing-framework-supportability |

### Security
| Topic | URL |
|-------|-----|
| Set SAP deployment SPN secrets in Azure Key Vault | https://learn.microsoft.com/en-us/azure/sap/automation/bash/set-secrets |
| Understand Business Process Solutions compliance attestation | https://learn.microsoft.com/en-us/azure/sap/business-process-solutions/attestation |
| Configure Azure RBAC for Azure Center for SAP solutions | https://learn.microsoft.com/en-us/azure/sap/center-sap-solutions/manage-with-azure-rbac |
| Configure TLS 1.2 security for Azure Monitor for SAP | https://learn.microsoft.com/en-us/azure/sap/monitor/enable-tls-azure-monitor-sap-solutions |
| Enable Trusted Access and private endpoints for Azure Monitor for SAP solutions | https://learn.microsoft.com/en-us/azure/sap/monitor/enable-trusted-access |
| Create secure IBM Db2 provider for Azure Monitor for SAP | https://learn.microsoft.com/en-us/azure/sap/monitor/provider-ibm-db2 |
| Configure secure SQL Server provider for AMS | https://learn.microsoft.com/en-us/azure/sap/monitor/provider-sql-server |
| Integrate Azure security and identity with SAP RISE | https://learn.microsoft.com/en-us/azure/sap/workloads/rise-integration-security |
| Configure Azure Files NFS encryption in transit for SAP | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-azure-files-nfs-encryption-in-transit-guide |
| Design secure identity and access for SAP on Azure | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-security-identity |
| Secure Azure infrastructure foundation for SAP applications | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-security-infrastructure |
| Design Entra ID-based access for SAP platforms | https://learn.microsoft.com/en-us/azure/sap/workloads/scenario-azure-first-sap-identity-integration |

### Configuration
| Topic | URL |
|-------|-----|
| Manage SAP Terraform state with advanced_state_management script | https://learn.microsoft.com/en-us/azure/sap/automation/bash/advanced-state-management |
| Update SAP Library SAS token in Azure Key Vault | https://learn.microsoft.com/en-us/azure/sap/automation/bash/update-sas-token |
| Prepare SAP Bill of Materials for Azure automation | https://learn.microsoft.com/en-us/azure/sap/automation/bom-prepare |
| Generate SAP application installation templates for SDAF BOM | https://learn.microsoft.com/en-us/azure/sap/automation/bom-templates-db |
| Configure control plane parameters for SAP automation | https://learn.microsoft.com/en-us/azure/sap/automation/configure-control-plane |
| Customize disk configurations for SAP Deployment Automation Framework | https://learn.microsoft.com/en-us/azure/sap/automation/configure-extra-disks |
| Configure SAP installation parameters for SDAF Ansible playbooks | https://learn.microsoft.com/en-us/azure/sap/automation/configure-sap-parameters |
| Define SAP system tfvars parameters for automation | https://learn.microsoft.com/en-us/azure/sap/automation/configure-system |
| Configure SDAF control plane web application | https://learn.microsoft.com/en-us/azure/sap/automation/configure-webapp |
| Extend SAP Deployment Automation Framework configuration | https://learn.microsoft.com/en-us/azure/sap/automation/extensibility |
| Customize Azure resource naming in SAP automation | https://learn.microsoft.com/en-us/azure/sap/automation/naming-module |
| Use shell script reference for SAP deployment automation | https://learn.microsoft.com/en-us/azure/sap/automation/reference-bash |
| Configure insights templates and connections in Business Process Solutions | https://learn.microsoft.com/en-us/azure/sap/business-process-solutions/configure-insights |
| Configure SAP source systems with Azure Data Factory | https://learn.microsoft.com/en-us/azure/sap/business-process-solutions/configure-source-system-with-data-factory |
| Configure SAP S/4HANA sources with SAP Datasphere | https://learn.microsoft.com/en-us/azure/sap/business-process-solutions/configure-source-system-with-datasphere |
| Configure SAP S/4HANA and ECC open mirroring sources | https://learn.microsoft.com/en-us/azure/sap/business-process-solutions/configure-source-system-with-open-mirroring |
| Configure datasets and tables in Business Process Solutions | https://learn.microsoft.com/en-us/azure/sap/business-process-solutions/manage-datasets |
| Configure performance settings for SAP BPS on Fabric | https://learn.microsoft.com/en-us/azure/sap/business-process-solutions/performance-optimization |
| Configure post-processing for SAP Business Process Solutions | https://learn.microsoft.com/en-us/azure/sap/business-process-solutions/post-processing |
| Prepare SAP installation media for Azure Center for SAP | https://learn.microsoft.com/en-us/azure/sap/center-sap-solutions/get-sap-installation-media |
| Monitor SAP systems with Azure Center for SAP | https://learn.microsoft.com/en-us/azure/sap/center-sap-solutions/monitor-portal |
| Configure virtual network for S/4HANA on Azure | https://learn.microsoft.com/en-us/azure/sap/center-sap-solutions/prepare-network |
| Register existing SAP systems in Azure Center using Azure CLI | https://learn.microsoft.com/en-us/azure/sap/center-sap-solutions/quickstart-register-system-cli |
| Register existing SAP systems in Azure Center using PowerShell | https://learn.microsoft.com/en-us/azure/sap/center-sap-solutions/quickstart-register-system-powershell |
| Register existing SAP systems in Azure Center | https://learn.microsoft.com/en-us/azure/sap/center-sap-solutions/register-existing-system |
| Control SAP system lifecycle via Azure VIS | https://learn.microsoft.com/en-us/azure/sap/center-sap-solutions/start-stop-sap-systems |
| Reference of logs and metrics for Azure Monitor for SAP solutions | https://learn.microsoft.com/en-us/azure/sap/monitor/data-reference |
| Configure HA Pacemaker provider for Azure Monitor for SAP | https://learn.microsoft.com/en-us/azure/sap/monitor/provider-ha-pacemaker-cluster |
| Configure SAP HANA provider in Azure Monitor for SAP | https://learn.microsoft.com/en-us/azure/sap/monitor/provider-hana |
| Configure Linux OS provider for Azure Monitor for SAP | https://learn.microsoft.com/en-us/azure/sap/monitor/provider-linux |
| Configure SAP NetWeaver provider for Azure Monitor for SAP solutions | https://learn.microsoft.com/en-us/azure/sap/monitor/provider-netweaver |
| Configure virtual network for Azure Monitor for SAP | https://learn.microsoft.com/en-us/azure/sap/monitor/set-up-network |
| Deploy and configure IBM Db2 HADR for SAP on Azure VMs | https://learn.microsoft.com/en-us/azure/sap/workloads/dbms-guide-ha-ibm |
| Add disaster recovery sites to SAP HANA Pacemaker clusters | https://learn.microsoft.com/en-us/azure/sap/workloads/disaster-recovery-sap-hana |
| Configure and operate SAP HANA infrastructure on Azure VMs | https://learn.microsoft.com/en-us/azure/sap/workloads/hana-vm-operations |
| Configure Azure NetApp Files for SAP HANA storage | https://learn.microsoft.com/en-us/azure/sap/workloads/hana-vm-operations-netapp |
| Configure Azure VM storage for SAP HANA | https://learn.microsoft.com/en-us/azure/sap/workloads/hana-vm-operations-storage |
| Configure Premium SSD storage for SAP HANA VMs | https://learn.microsoft.com/en-us/azure/sap/workloads/hana-vm-premium-ssd-v1 |
| Configure Premium SSD v2 for SAP HANA workloads | https://learn.microsoft.com/en-us/azure/sap/workloads/hana-vm-premium-ssd-v2 |
| Configure Azure Ultra Disk for SAP HANA VMs | https://learn.microsoft.com/en-us/azure/sap/workloads/hana-vm-ultra-disk |
| Configure HA SAP NetWeaver on RHEL in Azure VMs | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-guide-rhel |
| Configure GlusterFS on Azure VMs for SAP HA | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-guide-rhel-glusterfs |
| Set up IBM Db2 HADR on RHEL Azure VMs | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-guide-rhel-ibm-db2-luw |
| Configure multi-SID HA SAP NetWeaver cluster on RHEL | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-guide-rhel-multi-sid |
| Configure HA SAP NetWeaver on RHEL with Azure NetApp Files | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-guide-rhel-netapp-files |
| Configure HA SAP NetWeaver on RHEL with Azure Files NFS | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-guide-rhel-nfs-azure-files |
| Configure Pacemaker clusters on RHEL in Azure | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-guide-rhel-pacemaker |
| Configure SAP PAS and AAS on RHEL HA VMs | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-guide-rhel-with-dialog-instance |
| Configure SAP HANA ASCS/ERS high availability on RHEL VMs | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-guide-rhel-with-hana-ascs-ers-dialog-instance |
| Configure HA SAP NetWeaver on Azure VMs with SLES | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-guide-suse |
| Configure HA SAP NetWeaver on SLES with Azure NetApp Files | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-guide-suse-netapp-files |
| Configure HA NFS server on SLES Azure VMs for SAP | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-guide-suse-nfs |
| Configure HA SAP NetWeaver on SLES using NFS on Azure Files | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-guide-suse-nfs-azure-files |
| Configure Pacemaker clustering on SLES in Azure | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-guide-suse-pacemaker |
| Configure SAP LaMa connector integration with Azure | https://learn.microsoft.com/en-us/azure/sap/workloads/lama-installation |
| Configure SAP ASCS/SCS multi-SID HA with WSFC and Azure shared disk | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-ascs-ha-multi-sid-wsfc-azure-shared-disk |
| Configure SAP ASCS/SCS multi-SID HA with WSFC file shares | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-ascs-ha-multi-sid-wsfc-file-share |
| Implement SAP ASCS/SCS multi-SID HA on WSFC with shared disk | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-ascs-ha-multi-sid-wsfc-shared-disk |
| Configure SAP HANA high availability on SLES Azure VMs | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-hana-high-availability |
| Configure SAP HANA high availability with Azure NetApp Files on RHEL | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-hana-high-availability-netapp-files-red-hat |
| Set up SAP HANA scale-up HA with Azure NetApp Files on SLES | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-hana-high-availability-netapp-files-suse |
| Configure SAP HANA scale-out HSR with Pacemaker | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-hana-high-availability-scale-out-hsr-suse |
| Deploy SAP HANA scale-out with standby using Azure NetApp Files on RHEL | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-hana-scale-out-standby-netapp-files-rhel |
| Deploy SAP HANA scale-out with standby using Azure NetApp Files on SLES | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-hana-scale-out-standby-netapp-files-suse |
| Configure SAP ASCS/SCS clustering with Azure file share | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-high-availability-guide-wsfc-file-share |
| Cluster SAP ASCS/SCS on WSFC with shared disk | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-high-availability-guide-wsfc-shared-disk |
| Prepare Azure infrastructure for SAP ASCS/SCS HA with WSFC | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-high-availability-infrastructure-wsfc-file-share |
| Prepare Azure infrastructure for SAP ASCS/SCS WSFC with shared disk | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-high-availability-infrastructure-wsfc-shared-disk |
| Configure SAP NetWeaver HA on WSFC with shared disks | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-high-availability-installation-wsfc-shared-disk |
| Configure SAP ILM Store with Azure Blob Storage | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-information-lifecycle-management |
| Deploy and configure Azure VM extension for SAP | https://learn.microsoft.com/en-us/azure/sap/workloads/vm-extension-for-sap |
| Configure new Azure VM extension for SAP solutions | https://learn.microsoft.com/en-us/azure/sap/workloads/vm-extension-for-sap-new |
| Configure standard Azure VM extension for SAP solutions | https://learn.microsoft.com/en-us/azure/sap/workloads/vm-extension-for-sap-standard |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate Azure Monitor for SAP with automation | https://learn.microsoft.com/en-us/azure/sap/automation/integration-azure-monitor-sap |
| Run SDAF Ansible playbooks to install SAP | https://learn.microsoft.com/en-us/azure/sap/automation/run-ansible |
| Set up Salesforce as a Business Process Solutions source | https://learn.microsoft.com/en-us/azure/sap/business-process-solutions/configure-salesforce-source-system |
| Control SAP systems with Azure CLI VIS | https://learn.microsoft.com/en-us/azure/sap/center-sap-solutions/quick-stop-start-sap-cli |
| Control SAP systems with Azure PowerShell VIS | https://learn.microsoft.com/en-us/azure/sap/center-sap-solutions/quick-stop-start-sap-powershell |
| Control SAP and VM lifecycle via VIS REST APIs | https://learn.microsoft.com/en-us/azure/sap/center-sap-solutions/stop-start-sap-and-underlying-vm |
| Integrate SAP ABAP outbound email with Exchange Online | https://learn.microsoft.com/en-us/azure/sap/workloads/exchange-online-integration-sap-email-outbound |
| Configure SAP Principal Propagation for live OData with Power Query | https://learn.microsoft.com/en-us/azure/sap/workloads/expose-sap-odata-to-power-query |
| Integrate Azure services with SAP RISE workloads | https://learn.microsoft.com/en-us/azure/sap/workloads/rise-integration-services |
| Integrate SAP front-end printing with Universal Print | https://learn.microsoft.com/en-us/azure/sap/workloads/universal-print-sap-frontend |

### Deployment
| Topic | URL |
|-------|-----|
| Bash script to deploy SAP automation control plane | https://learn.microsoft.com/en-us/azure/sap/automation/bash/deploy-controlplane |
| Bootstrap SAP deployer control plane with install_deployer.sh | https://learn.microsoft.com/en-us/azure/sap/automation/bash/install-deployer |
| Bootstrap SAP Library control plane with install_library.sh | https://learn.microsoft.com/en-us/azure/sap/automation/bash/install-library |
| Bash script to deploy a new SAP workload zone | https://learn.microsoft.com/en-us/azure/sap/automation/bash/install-workloadzone |
| Deploy SAP systems on Azure with installer.sh | https://learn.microsoft.com/en-us/azure/sap/automation/bash/installer |
| Remove SAP deployment control plane with remove_controlplane.sh | https://learn.microsoft.com/en-us/azure/sap/automation/bash/remove-controlplane |
| Tear down SAP systems using remover.sh | https://learn.microsoft.com/en-us/azure/sap/automation/bash/remover |
| Configure Azure DevOps for SAP automation pipelines | https://learn.microsoft.com/en-us/azure/sap/automation/configure-devops |
| Deploy control plane for SAP automation framework | https://learn.microsoft.com/en-us/azure/sap/automation/deploy-control-plane |
| Deploy SAP infrastructure with SDAF and Azure DevOps | https://learn.microsoft.com/en-us/azure/sap/automation/devops-tutorial |
| Check SAP Deployment Automation support matrix | https://learn.microsoft.com/en-us/azure/sap/automation/supportability |
| Deploy S/4HANA infrastructure with Azure Center | https://learn.microsoft.com/en-us/azure/sap/center-sap-solutions/deploy-s4hana |
| Install SAP software on ACSS-managed systems | https://learn.microsoft.com/en-us/azure/sap/center-sap-solutions/install-software |
| Deploy distributed HA SAP infrastructure via Azure CLI | https://learn.microsoft.com/en-us/azure/sap/center-sap-solutions/quickstart-create-high-availability-namecustom |
| Deploy SAP Business One on Azure Virtual Machines | https://learn.microsoft.com/en-us/azure/sap/workloads/business-one-azure |
| Deploy SAP BusinessObjects BI on Azure for Linux | https://learn.microsoft.com/en-us/azure/sap/workloads/businessobjects-deployment-guide-linux |
| Deploy SAP BusinessObjects BI on Azure for Windows | https://learn.microsoft.com/en-us/azure/sap/workloads/businessobjects-deployment-guide-windows |
| Use SAP on Azure planning and deployment checklist | https://learn.microsoft.com/en-us/azure/sap/workloads/deployment-checklist |
| Deploy SAP NetWeaver on Azure Linux VMs | https://learn.microsoft.com/en-us/azure/sap/workloads/deployment-guide |
| Prepare and deploy SAP HANA on Azure VMs | https://learn.microsoft.com/en-us/azure/sap/workloads/hana-get-started |
| Deploy HA SAP NetWeaver on Azure NetApp Files SMB | https://learn.microsoft.com/en-us/azure/sap/workloads/high-availability-guide-windows-netapp-files-smb |
| Install SAP NetWeaver HA on WSFC with file share | https://learn.microsoft.com/en-us/azure/sap/workloads/sap-high-availability-installation-wsfc-file-share |