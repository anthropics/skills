---
name: azure-backup
description: Expert knowledge for Azure Backup development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when protecting Azure VMs, AKS, SQL/SAP HANA, Files/Blobs/Disks, or automating backups via CLI/PowerShell, and other Azure Backup related development tasks. Not for Azure Site Recovery (use azure-site-recovery), Azure Virtual Machines (use azure-virtual-machines).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Backup Skill

This skill provides expert guidance for Azure Backup. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L70 | Diagnosing and fixing backup/restore errors, performance issues, and agent/extension problems across Azure Backup workloads (VMs, disks, databases, Kubernetes, Files, Blobs, SAP, MARS, DPM). |
| Best Practices | L71-L81 | Best practices for securing Azure Backup data and configuring reliable backups/restores for Azure VMs, Hyper-V, SQL Always On, DPM/MABS workloads, and vault-registered servers. |
| Decision Making | L82-L89 | Guidance on planning Azure Backup costs, checking supported VM SKUs, choosing reserved capacity for savings, and migrating classic backup alerts to Azure Monitor. |
| Architecture & Design Patterns | L90-L94 | Azure Backup’s architecture for protecting SAP HANA: components, data flow, backup/restore process, scalability, security, and integration with Azure storage and recovery services. |
| Limits & Quotas | L95-L131 | Limits, support matrices, regions, retention, and quotas for Azure Backup across VMs, databases (SQL, PostgreSQL, MySQL, Cosmos DB, SAP), files, disks, blobs, AKS, and monitoring. |
| Security | L132-L170 | Securing Azure Backup: encryption, RBAC/MIs, private endpoints, soft delete, ransomware protection, Azure Policy/MUA/Resource Guard, and secure restore of encrypted/Confidential/hybrid workloads. |
| Configuration | L171-L253 | Configuring and operating Azure Backup: setup, policies, automation, diagnostics, monitoring, vaults, and workload-specific backups/restores (VMs, AKS, SQL, SAP, Files, Disks, Blobs, AD, Exchange). |
| Integrations & Coding Patterns | L254-L310 | Automating Azure Backup via CLI, PowerShell, REST, and scripts for VMs, SQL, PostgreSQL, Files, Blobs, Disks, MARS/on-prem, plus policies, vaults, jobs, restores, and security/reporting integrations. |
| Deployment | L311-L319 | Guides for deploying and managing Azure Backup Server (MABS): backup of local VMs, supported workload matrices for v3/v4, automating silent installs, and stopping protection for workloads. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Diagnose and fix Azure Data Lake Storage backup errors | https://learn.microsoft.com/en-us/azure/backup/azure-data-lake-storage-backup-troubleshoot |
| Troubleshoot Azure Kubernetes Service backups with Azure Backup | https://learn.microsoft.com/en-us/azure/backup/azure-kubernetes-service-backup-troubleshoot |
| Troubleshoot data recovery from Microsoft Azure Backup Server | https://learn.microsoft.com/en-us/azure/backup/backup-azure-alternate-dpm-server-troubleshoot |
| Resolve Azure Backup Vault management errors | https://learn.microsoft.com/en-us/azure/backup/backup-azure-backup-vault-troubleshoot |
| Resolve Azure PostgreSQL Flexible Server backup and restore issues | https://learn.microsoft.com/en-us/azure/backup/backup-azure-database-postgresql-flex-troubleshoot |
| Troubleshoot Azure Database for PostgreSQL backups with Azure Backup | https://learn.microsoft.com/en-us/azure/backup/backup-azure-database-postgresql-troubleshoot |
| Diagnose and fix encrypted Azure VM backup errors | https://learn.microsoft.com/en-us/azure/backup/backup-azure-encrypted-vm-troubleshoot |
| Troubleshoot Azure Backup Server installation and workload protection | https://learn.microsoft.com/en-us/azure/backup/backup-azure-mabs-troubleshoot |
| Resolve Azure Backup (MARS) agent installation and backup issues | https://learn.microsoft.com/en-us/azure/backup/backup-azure-mars-troubleshoot |
| Resolve Azure Backup monitoring and reporting issues | https://learn.microsoft.com/en-us/azure/backup/backup-azure-monitor-alert-faq |
| Fix Azure Backup monitoring and protection status issues | https://learn.microsoft.com/en-us/azure/backup/backup-azure-monitor-troubleshoot |
| Troubleshoot Azure MySQL Flexible Server backups using Azure Backup | https://learn.microsoft.com/en-us/azure/backup/backup-azure-mysql-flexible-server-troubleshoot |
| Fix SAP HANA database backup errors on Azure VMs | https://learn.microsoft.com/en-us/azure/backup/backup-azure-sap-hana-database-troubleshoot |
| Troubleshoot System Center DPM with Azure Backup integration | https://learn.microsoft.com/en-us/azure/backup/backup-azure-scdpm-troubleshooting |
| Resolve System State Backup issues with Azure Backup | https://learn.microsoft.com/en-us/azure/backup/backup-azure-system-state-troubleshoot |
| Troubleshoot Azure Blob backup and restore failures | https://learn.microsoft.com/en-us/azure/backup/backup-azure-troubleshoot-blob-backup |
| Diagnose slow file and folder backups with Azure Backup | https://learn.microsoft.com/en-us/azure/backup/backup-azure-troubleshoot-slow-backup-performance-issue |
| Resolve Azure Backup agent and extension failures | https://learn.microsoft.com/en-us/azure/backup/backup-azure-troubleshoot-vm-backup-fails-snapshot-timeout |
| Troubleshoot Azure VM file-level recovery issues | https://learn.microsoft.com/en-us/azure/backup/backup-azure-vm-file-recovery-troubleshoot |
| Fix Azure VM backup and restore errors | https://learn.microsoft.com/en-us/azure/backup/backup-azure-vms-troubleshoot |
| Troubleshoot Azure Backup Server v3 known issues | https://learn.microsoft.com/en-us/azure/backup/backup-mabs-release-notes-v3 |
| Troubleshoot SQL Server backups on Azure VMs using Azure Backup | https://learn.microsoft.com/en-us/azure/backup/backup-sql-server-azure-troubleshoot |
| Troubleshoot Backup vault management errors | https://learn.microsoft.com/en-us/azure/backup/backup-vault-troubleshoot |
| Resolve common issues with Azure Blob Backup | https://learn.microsoft.com/en-us/azure/backup/blob-backup-faq |
| Resolve common issues with Azure Disk Backup | https://learn.microsoft.com/en-us/azure/backup/disk-backup-faq |
| Fix backup and restore failures in Azure Disk Backup | https://learn.microsoft.com/en-us/azure/backup/disk-backup-troubleshoot |
| Troubleshoot SAP HANA database instance backups on Azure VMs | https://learn.microsoft.com/en-us/azure/backup/sap-hana-database-instance-troubleshoot |
| Troubleshoot Azure Backup archive tier recovery point errors | https://learn.microsoft.com/en-us/azure/backup/troubleshoot-archive-tier |
| Troubleshoot Azure Files backup and restore with Azure Backup | https://learn.microsoft.com/en-us/azure/backup/troubleshoot-azure-files |
| Troubleshoot SAP ASE (Sybase) database backups using Azure Backup | https://learn.microsoft.com/en-us/azure/backup/troubleshoot-sap-ase-sybase-database-backup |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply Azure Backup security best practices for data | https://learn.microsoft.com/en-us/azure/backup/azure-backup-data-protection-best-practices |
| Back up and restore Hyper-V VMs with MABS | https://learn.microsoft.com/en-us/azure/backup/back-up-hyper-v-virtual-machines-mabs |
| Recover Azure Backup Server data from any vault-registered server | https://learn.microsoft.com/en-us/azure/backup/backup-azure-alternate-dpm-server |
| Prepare DPM server for Azure backups with TRIM considerations | https://learn.microsoft.com/en-us/azure/backup/backup-azure-dpm-introduction |
| Apply Azure VM backup best practices with Azure Backup | https://learn.microsoft.com/en-us/azure/backup/backup-azure-vms-introduction |
| Back up SQL Server Always On availability groups with Azure Backup | https://learn.microsoft.com/en-us/azure/backup/backup-sql-server-on-availability-groups |
| Apply Azure Backup best practices for workloads | https://learn.microsoft.com/en-us/azure/backup/guidance-best-practices |

### Decision Making
| Topic | URL |
|-------|-----|
| Estimate and plan Azure Backup costs for different workloads | https://learn.microsoft.com/en-us/azure/backup/azure-backup-pricing |
| Check VM image SKUs supported by Azure Backup policies | https://learn.microsoft.com/en-us/azure/backup/backup-azure-policy-supported-skus |
| Choose Azure Backup reserved capacity to reduce storage costs | https://learn.microsoft.com/en-us/azure/backup/backup-azure-reserved-pricing-optimize-cost |
| Migrate Azure Backup classic alerts to Azure Monitor alerts | https://learn.microsoft.com/en-us/azure/backup/move-to-azure-monitor-alerts |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Understand Azure Backup architecture for SAP HANA | https://learn.microsoft.com/en-us/azure/backup/azure-backup-architecture-for-sap-hana-backup |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Azure Backup for AKS FAQs and constraints | https://learn.microsoft.com/en-us/azure/backup/aks-backup-faq |
| Understand Azure Data Lake Storage backup support matrix | https://learn.microsoft.com/en-us/azure/backup/azure-data-lake-storage-backup-support-matrix |
| Elastic SAN backup regional support and limitations | https://learn.microsoft.com/en-us/azure/backup/azure-elastic-san-backup-support-matrix |
| Review Azure Files backup support limits and settings | https://learn.microsoft.com/en-us/azure/backup/azure-file-share-support-matrix |
| Check AKS backup region support and limitations | https://learn.microsoft.com/en-us/azure/backup/azure-kubernetes-service-cluster-backup-support-matrix |
| Azure Backup service limits, behaviors, and constraints | https://learn.microsoft.com/en-us/azure/backup/backup-azure-backup-faq |
| Review Azure Cosmos DB backup support limits | https://learn.microsoft.com/en-us/azure/backup/backup-azure-cosmos-db-support-matrix |
| PostgreSQL Flexible Server backup capabilities and retention | https://learn.microsoft.com/en-us/azure/backup/backup-azure-database-postgresql-flex-overview |
| Support matrix for PostgreSQL Flexible Server backup | https://learn.microsoft.com/en-us/azure/backup/backup-azure-database-postgresql-flex-support-matrix |
| Overview and retention limits for Azure PostgreSQL backups | https://learn.microsoft.com/en-us/azure/backup/backup-azure-database-postgresql-overview |
| Azure Backup limits for PostgreSQL server backups | https://learn.microsoft.com/en-us/azure/backup/backup-azure-database-postgresql-server-faq |
| Support matrix for PostgreSQL single server backup | https://learn.microsoft.com/en-us/azure/backup/backup-azure-database-postgresql-support-matrix |
| Review Azure Backup Server and DPM protection limits | https://learn.microsoft.com/en-us/azure/backup/backup-azure-dpm-azure-server-faq |
| Understand MARS agent backup limits and behavior | https://learn.microsoft.com/en-us/azure/backup/backup-azure-file-folder-backup-faq |
| Azure Files backup FAQs with limits and constraints | https://learn.microsoft.com/en-us/azure/backup/backup-azure-files-faq |
| Support matrix for MySQL Flexible Server long-term backup | https://learn.microsoft.com/en-us/azure/backup/backup-azure-mysql-flexible-server-support-matrix |
| Understand Azure VM Backup limits and behaviors | https://learn.microsoft.com/en-us/azure/backup/backup-azure-vm-backup-faq |
| Check Backup center workload support and limitations | https://learn.microsoft.com/en-us/azure/backup/backup-center-support-matrix |
| Instant Restore limits and behavior for Azure VM backups | https://learn.microsoft.com/en-us/azure/backup/backup-instant-restore-capability |
| Review Azure Backup support settings and limits | https://learn.microsoft.com/en-us/azure/backup/backup-support-matrix |
| Support matrix and limits for Azure VM backups | https://learn.microsoft.com/en-us/azure/backup/backup-support-matrix-iaas |
| MABS and DPM Azure Backup support and limits matrix | https://learn.microsoft.com/en-us/azure/backup/backup-support-matrix-mabs-dpm |
| Check MARS agent backup support and limitations | https://learn.microsoft.com/en-us/azure/backup/backup-support-matrix-mars-agent |
| Understand Azure Blob backup support limits and matrix | https://learn.microsoft.com/en-us/azure/backup/blob-backup-support-matrix |
| Check Azure Disk Backup support and limitations | https://learn.microsoft.com/en-us/azure/backup/disk-backup-support-matrix |
| Azure Backup limits for SQL Server on Azure VMs | https://learn.microsoft.com/en-us/azure/backup/faq-backup-sql-server |
| Use Azure Backup metrics and thresholds to monitor backup health | https://learn.microsoft.com/en-us/azure/backup/metrics-overview |
| Review SAP ASE backup support limits on Azure VMs | https://learn.microsoft.com/en-us/azure/backup/sap-ase-backup-support-matrix |
| Review Azure Backup support limits for SAP HANA | https://learn.microsoft.com/en-us/azure/backup/sap-hana-backup-support-matrix |
| Azure Backup limits for SAP HANA on Azure VMs | https://learn.microsoft.com/en-us/azure/backup/sap-hana-faq-backup-azure-vm |
| Protect Azure file shares with soft delete | https://learn.microsoft.com/en-us/azure/backup/soft-delete-azure-file-share |
| Azure Backup support limits for SQL Server on VMs | https://learn.microsoft.com/en-us/azure/backup/sql-support-matrix |
| View Azure Backup reports and workspace limits | https://learn.microsoft.com/en-us/azure/backup/view-reports |

### Security
| Topic | URL |
|-------|-----|
| Enforce AKS backup compliance using Azure Policy | https://learn.microsoft.com/en-us/azure/backup/azure-kubernetes-service-cluster-backup-policy |
| Configure and manage Azure Backup soft delete protection | https://learn.microsoft.com/en-us/azure/backup/backup-azure-enhanced-soft-delete-configure-manage |
| Use private endpoints (v2) to secure Azure Backup | https://learn.microsoft.com/en-us/azure/backup/backup-azure-private-endpoints-concept |
| Configure and manage Azure Backup private endpoints | https://learn.microsoft.com/en-us/azure/backup/backup-azure-private-endpoints-configure-manage |
| Restore Key Vault keys and secrets for encrypted Azure VMs via Azure Backup | https://learn.microsoft.com/en-us/azure/backup/backup-azure-restore-key-secret |
| Secure hybrid backups with Azure Backup features | https://learn.microsoft.com/en-us/azure/backup/backup-azure-security-feature |
| Back up and restore encrypted Azure VMs with Azure Backup | https://learn.microsoft.com/en-us/azure/backup/backup-azure-vms-encryption |
| Understand encryption behavior in Azure Backup | https://learn.microsoft.com/en-us/azure/backup/backup-encryption |
| Configure Azure RBAC roles for Recovery Services backups | https://learn.microsoft.com/en-us/azure/backup/backup-rbac-rs-vault |
| Restore Confidential VMs with PMK or CMK using Azure Backup | https://learn.microsoft.com/en-us/azure/backup/confidential-vm-restore |
| Configure managed identities and RBAC for Backup vault | https://learn.microsoft.com/en-us/azure/backup/enable-managed-identity-backup-vault |
| Configure managed identities and RBAC for Recovery Services vault | https://learn.microsoft.com/en-us/azure/backup/enable-managed-identity-recovery-services-vault |
| Enable multi-user authorization for Azure Backup vaults | https://learn.microsoft.com/en-us/azure/backup/enable-multi-user-authorization-quickstart |
| Encrypt Azure Backup data with customer-managed keys | https://learn.microsoft.com/en-us/azure/backup/encryption-at-rest-with-cmk |
| Use CMKs to encrypt Backup vault data | https://learn.microsoft.com/en-us/azure/backup/encryption-at-rest-with-cmk-for-backup-vault |
| Configure multi-user authorization with Resource Guard | https://learn.microsoft.com/en-us/azure/backup/multi-user-authorization |
| Configure Resource Guard and MUA on Azure Backup vaults | https://learn.microsoft.com/en-us/azure/backup/multi-user-authorization-tutorial |
| Use built-in Azure Policy definitions to govern Azure Backup | https://learn.microsoft.com/en-us/azure/backup/policy-reference |
| Secure MABS backups with Azure Backup private endpoints | https://learn.microsoft.com/en-us/azure/backup/private-endpoint-configure-vault-backup-server |
| Create and use private endpoints for Azure Backup | https://learn.microsoft.com/en-us/azure/backup/private-endpoints |
| Understand private endpoints (v1) for Azure Backup | https://learn.microsoft.com/en-us/azure/backup/private-endpoints-overview |
| Secure Azure Backup against ransomware and threats | https://learn.microsoft.com/en-us/azure/backup/protect-backups-from-ransomware-faq |
| Re-register MABS vault access after removing private endpoints | https://learn.microsoft.com/en-us/azure/backup/register-public-access-vault-backup-server |
| Restore Azure PostgreSQL backups with cross-subscription access | https://learn.microsoft.com/en-us/azure/backup/restore-azure-database-postgresql |
| Restore Azure VMs encrypted with Azure Disk Encryption | https://learn.microsoft.com/en-us/azure/backup/restore-azure-encrypted-virtual-machines |
| Configure permissions to restore Azure Managed Disks | https://learn.microsoft.com/en-us/azure/backup/restore-managed-disks |
| Store MARS backup passphrases securely in Key Vault | https://learn.microsoft.com/en-us/azure/backup/save-backup-passphrase-securely-in-azure-key-vault |
| Configure secure-by-default soft delete in Azure Backup | https://learn.microsoft.com/en-us/azure/backup/secure-by-default |
| Use Azure Policy compliance controls for Azure Backup | https://learn.microsoft.com/en-us/azure/backup/security-controls-policy |
| Understand Azure Backup security capabilities | https://learn.microsoft.com/en-us/azure/backup/security-overview |
| Use Azure Backup soft delete for secure recovery | https://learn.microsoft.com/en-us/azure/backup/soft-delete-azure-backup-faq |
| Protect SQL and SAP HANA VM backups with soft delete | https://learn.microsoft.com/en-us/azure/backup/soft-delete-sql-saphana-in-azure-vm |
| Use soft delete to protect Azure VM backups | https://learn.microsoft.com/en-us/azure/backup/soft-delete-virtual-machines |
| Configure threat detection and health monitoring for VM backups | https://learn.microsoft.com/en-us/azure/backup/threat-detection-configure-monitor-tutorial |
| Enable TLS 1.2 encryption for Azure Backup traffic | https://learn.microsoft.com/en-us/azure/backup/transport-layer-security |

### Configuration
| Topic | URL |
|-------|-----|
| Configure Azure Backup for Active Directory domain controllers | https://learn.microsoft.com/en-us/azure/backup/active-directory-backup-restore |
| Automate Azure Backup operations with scripts and APIs | https://learn.microsoft.com/en-us/azure/backup/automation-backup |
| Manage backup protection for Azure Data Lake Storage | https://learn.microsoft.com/en-us/azure/backup/azure-data-lake-storage-backup-manage |
| Configure vaulted backups for Azure Data Lake Storage | https://learn.microsoft.com/en-us/azure/backup/azure-data-lake-storage-configure-backup |
| Configure and run AKS backups with Azure Backup | https://learn.microsoft.com/en-us/azure/backup/azure-kubernetes-service-cluster-backup |
| Meet prerequisites and configure access for AKS backup | https://learn.microsoft.com/en-us/azure/backup/azure-kubernetes-service-cluster-backup-concept |
| Configure AKS backups with Azure Backup via CLI | https://learn.microsoft.com/en-us/azure/backup/azure-kubernetes-service-cluster-backup-using-cli |
| Configure AKS backup extension and trusted access | https://learn.microsoft.com/en-us/azure/backup/azure-kubernetes-service-cluster-manage-backups |
| Restore AKS clusters and volumes using Azure Backup | https://learn.microsoft.com/en-us/azure/backup/azure-kubernetes-service-cluster-restore |
| Configure Azure Backup vault diagnostics via Azure Policy | https://learn.microsoft.com/en-us/azure/backup/azure-policy-configure-diagnostics |
| Configure SQL Server instance snapshot backups on Azure VMs | https://learn.microsoft.com/en-us/azure/backup/back-up-sql-server-instance-snapshot |
| Auto-enable VM backups using Azure Policy | https://learn.microsoft.com/en-us/azure/backup/backup-azure-auto-enable-backup |
| Configure DPM to back up Exchange databases | https://learn.microsoft.com/en-us/azure/backup/backup-azure-backup-exchange-server |
| Configure MARS offline seeding with Azure Import/Export | https://learn.microsoft.com/en-us/azure/backup/backup-azure-backup-import-export |
| Configure DPM and MABS offline seeding with Import/Export | https://learn.microsoft.com/en-us/azure/backup/backup-azure-backup-server-import-export |
| Configure Azure Backup DPM policies for SQL Server | https://learn.microsoft.com/en-us/azure/backup/backup-azure-backup-sql |
| Define PostgreSQL backup policies via Data Protection REST API | https://learn.microsoft.com/en-us/azure/backup/backup-azure-data-protection-use-rest-api-create-update-postgresql-policy |
| Create PostgreSQL Flexible Server backup policies via REST API | https://learn.microsoft.com/en-us/azure/backup/backup-azure-database-postgresql-flex-use-rest-api-create-update-policy |
| Create blob backup policies via Data Protection REST API | https://learn.microsoft.com/en-us/azure/backup/backup-azure-dataprotection-use-rest-api-create-update-blob-policy |
| Define disk backup policies via Data Protection REST API | https://learn.microsoft.com/en-us/azure/backup/backup-azure-dataprotection-use-rest-api-create-update-disk-policy |
| Remove dependencies and delete Azure Recovery Services vaults | https://learn.microsoft.com/en-us/azure/backup/backup-azure-delete-vault |
| Configure diagnostic events for Azure Backup vaults | https://learn.microsoft.com/en-us/azure/backup/backup-azure-diagnostic-events |
| Use legacy Azure Backup diagnostics data model in Log Analytics | https://learn.microsoft.com/en-us/azure/backup/backup-azure-diagnostics-mode-data-model |
| Configure Azure Backup Server for Exchange | https://learn.microsoft.com/en-us/azure/backup/backup-azure-exchange-mabs |
| Configure Azure Files backups in Recovery Services vault | https://learn.microsoft.com/en-us/azure/backup/backup-azure-files |
| Audit and enforce Azure Files backup using Azure Policy | https://learn.microsoft.com/en-us/azure/backup/backup-azure-files-policy-automation |
| Configure and manage Azure Backup immutable vaults | https://learn.microsoft.com/en-us/azure/backup/backup-azure-immutable-vault-how-to-manage |
| Configure application-consistent backups for Azure Linux VMs | https://learn.microsoft.com/en-us/azure/backup/backup-azure-linux-app-consistent |
| Use enhanced prescript framework for database-consistent Linux VM backups | https://learn.microsoft.com/en-us/azure/backup/backup-azure-linux-database-consistent-enhanced-pre-post |
| Manage and monitor MARS agent backup configurations | https://learn.microsoft.com/en-us/azure/backup/backup-azure-manage-mars |
| Manage and monitor Azure VM backups using Recovery Services vault | https://learn.microsoft.com/en-us/azure/backup/backup-azure-manage-vms |
| Monitor and manage Recovery Services vaults via Overview dashboard | https://learn.microsoft.com/en-us/azure/backup/backup-azure-manage-windows-server |
| Configure Azure Monitor alerts for Azure Backup | https://learn.microsoft.com/en-us/azure/backup/backup-azure-monitoring-alerts |
| Configure built-in monitoring for Azure Backup workloads | https://learn.microsoft.com/en-us/azure/backup/backup-azure-monitoring-built-in-monitor |
| Configure Azure Monitor Logs and custom alerts for Azure Backup | https://learn.microsoft.com/en-us/azure/backup/backup-azure-monitoring-use-azuremonitor |
| Use resource-specific diagnostic data model for Azure Backup | https://learn.microsoft.com/en-us/azure/backup/backup-azure-reports-data-model |
| Configure Azure Backup for SQL Server on VMs | https://learn.microsoft.com/en-us/azure/backup/backup-azure-sql-database |
| Configure agentless multidisk crash-consistent backups for Azure VMs | https://learn.microsoft.com/en-us/azure/backup/backup-azure-vms-agentless-multi-disk-crash-consistent |
| Configure agentless crash-consistent backups for Azure VMs | https://learn.microsoft.com/en-us/azure/backup/backup-azure-vms-agentless-multi-disk-crash-consistent-overview |
| Configure Enhanced backup policy for Azure VMs | https://learn.microsoft.com/en-us/azure/backup/backup-azure-vms-enhanced-policy |
| Back up Azure VMs using Azure Extended Zones | https://learn.microsoft.com/en-us/azure/backup/backup-azure-vms-extended-zones |
| Back up Azure VMs from VM settings using Azure Backup | https://learn.microsoft.com/en-us/azure/backup/backup-azure-vms-first-look-arm |
| Perform backup and restore actions via Backup Center | https://learn.microsoft.com/en-us/azure/backup/backup-center-actions |
| Govern Azure backup compliance using Backup Center | https://learn.microsoft.com/en-us/azure/backup/backup-center-govern-environment |
| Monitor and operate backups at scale using Backup Center | https://learn.microsoft.com/en-us/azure/backup/backup-center-monitor-operate |
| Analyze Azure Backup trends and insights with Backup Center | https://learn.microsoft.com/en-us/azure/backup/backup-center-obtain-insights |
| Create and configure Azure Recovery Services vaults with CRR | https://learn.microsoft.com/en-us/azure/backup/backup-create-recovery-services-vault |
| Enable Azure VM backup during VM creation | https://learn.microsoft.com/en-us/azure/backup/backup-during-vm-creation |
| Configure Modern Backup Storage for Azure Backup Server | https://learn.microsoft.com/en-us/azure/backup/backup-mabs-add-storage |
| Configure Azure Managed Disk backups in the portal | https://learn.microsoft.com/en-us/azure/backup/backup-managed-disks |
| Audit and enforce Managed Disks backup with Azure Policy | https://learn.microsoft.com/en-us/azure/backup/backup-managed-disks-policy |
| Query Azure Backup logs using system functions | https://learn.microsoft.com/en-us/azure/backup/backup-reports-system-functions |
| Use ARM and Bicep templates for Azure Backup | https://learn.microsoft.com/en-us/azure/backup/backup-rm-template-samples |
| Configure operational and vaulted backups for Azure Blobs | https://learn.microsoft.com/en-us/azure/backup/blob-backup-configure-manage |
| Configure Azure Backup for Confidential VMs with DES keys | https://learn.microsoft.com/en-us/azure/backup/confidential-vm-backup |
| Configure Azure Backup reporting with Log Analytics and workbooks | https://learn.microsoft.com/en-us/azure/backup/configure-reports |
| Create and delete Azure Backup vaults for newer workloads | https://learn.microsoft.com/en-us/azure/backup/create-manage-backup-vault |
| Install and configure the MARS backup agent | https://learn.microsoft.com/en-us/azure/backup/install-mars-agent |
| Manage and monitor Azure Files backups in Azure Backup | https://learn.microsoft.com/en-us/azure/backup/manage-afs-backup |
| Manage backup lifecycle for Azure Managed Disks | https://learn.microsoft.com/en-us/azure/backup/manage-azure-managed-disks |
| Manage Azure Backup vault settings and operations | https://learn.microsoft.com/en-us/azure/backup/manage-backup-vault |
| Manage and monitor Azure Backup for SQL on VMs | https://learn.microsoft.com/en-us/azure/backup/manage-monitor-sql-database-backup |
| Configure telemetry and diagnostics for Azure Backup Server | https://learn.microsoft.com/en-us/azure/backup/manage-telemetry |
| Modify Azure VM backup policies using CLI JSON | https://learn.microsoft.com/en-us/azure/backup/modify-vm-policy-cli |
| Monitor Azure Backup estate using Backup Explorer workbook | https://learn.microsoft.com/en-us/azure/backup/monitor-azure-backup-with-backup-explorer |
| Configure Azure Monitor collection for Azure Backup | https://learn.microsoft.com/en-us/azure/backup/monitor-backup |
| Reference Azure Backup monitoring metrics and logs | https://learn.microsoft.com/en-us/azure/backup/monitor-backup-reference |
| Set up Azure Data Box offline backup for DPM and MABS | https://learn.microsoft.com/en-us/azure/backup/offline-backup-azure-data-box-dpm-mabs |
| Offline backup workflow for legacy DPM and MABS versions | https://learn.microsoft.com/en-us/azure/backup/offline-backup-server-previous-versions |
| Configure pre-backup and post-backup scripts in MABS | https://learn.microsoft.com/en-us/azure/backup/pre-backup-post-backup-scripts |
| Restore Azure VM SQL Server databases with Azure Backup | https://learn.microsoft.com/en-us/azure/backup/restore-sql-database-azure-vm |
| Configure Azure Backup for SAP HANA System Replication on VMs | https://learn.microsoft.com/en-us/azure/backup/sap-hana-database-with-hana-system-replication-backup |
| Use selective disk backup and restore for Azure VMs | https://learn.microsoft.com/en-us/azure/backup/selective-disk-backup-restore |
| Recover Windows Server files from Azure using MARS | https://learn.microsoft.com/en-us/azure/backup/tutorial-backup-restore-files-windows-server |
| Configure MARS agent backups for Windows Server to Azure | https://learn.microsoft.com/en-us/azure/backup/tutorial-backup-windows-server-to-azure |
| Configure AKS item-level backups with Azure Backup | https://learn.microsoft.com/en-us/azure/backup/tutorial-configure-backup-aks |
| Configure SAP HANA instance snapshot backups with Azure CLI | https://learn.microsoft.com/en-us/azure/backup/tutorial-configure-sap-hana-database-instance-snapshot-backup |
| Enable AKS Vault Tier protection and cross-region restore | https://learn.microsoft.com/en-us/azure/backup/tutorial-restore-aks-backups-across-regions |
| Upgrade configuration for the MARS backup agent | https://learn.microsoft.com/en-us/azure/backup/upgrade-mars-agent |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Back up PostgreSQL Flexible Server using Azure CLI | https://learn.microsoft.com/en-us/azure/backup/back-up-azure-database-postgresql-flex-backup-cli |
| Back up PostgreSQL Flexible Server using PowerShell | https://learn.microsoft.com/en-us/azure/backup/back-up-azure-database-postgresql-flex-backup-powershell |
| Configure and run VM backups via REST API | https://learn.microsoft.com/en-us/azure/backup/backup-azure-arm-userestapi-backupazurevms |
| Create Azure Backup policies using REST API | https://learn.microsoft.com/en-us/azure/backup/backup-azure-arm-userestapi-createorupdatepolicy |
| Create Recovery Services vaults using Backup REST API | https://learn.microsoft.com/en-us/azure/backup/backup-azure-arm-userestapi-createorupdatevault |
| Track Azure Backup jobs using REST API | https://learn.microsoft.com/en-us/azure/backup/backup-azure-arm-userestapi-managejobs |
| Restore Azure VMs and disks using REST API | https://learn.microsoft.com/en-us/azure/backup/backup-azure-arm-userestapi-restoreazurevms |
| Configure PostgreSQL backups using Data Protection REST API | https://learn.microsoft.com/en-us/azure/backup/backup-azure-data-protection-use-rest-api-backup-postgresql |
| Restore PostgreSQL Flexible Server using Azure CLI | https://learn.microsoft.com/en-us/azure/backup/backup-azure-database-postgresql-flex-restore-cli |
| Restore PostgreSQL Flexible Server using PowerShell | https://learn.microsoft.com/en-us/azure/backup/backup-azure-database-postgresql-flex-restore-powershell |
| Back up PostgreSQL Flexible Server using REST API | https://learn.microsoft.com/en-us/azure/backup/backup-azure-database-postgresql-flex-use-rest-api |
| Restore PostgreSQL Flexible Server using REST API | https://learn.microsoft.com/en-us/azure/backup/backup-azure-database-postgresql-flex-use-rest-api-restore |
| Configure blob backups using Data Protection REST API | https://learn.microsoft.com/en-us/azure/backup/backup-azure-dataprotection-use-rest-api-backup-blobs |
| Manage Azure Disk backups using Data Protection REST API | https://learn.microsoft.com/en-us/azure/backup/backup-azure-dataprotection-use-rest-api-backup-disks |
| Create Backup vault and blob policies via REST API | https://learn.microsoft.com/en-us/azure/backup/backup-azure-dataprotection-use-rest-api-create-update-backup-vault |
| Restore blobs using Data Protection REST API | https://learn.microsoft.com/en-us/azure/backup/backup-azure-dataprotection-use-rest-api-restore-blobs |
| Restore Azure Disks using Data Protection REST API | https://learn.microsoft.com/en-us/azure/backup/backup-azure-dataprotection-use-rest-api-restore-disks |
| Configure Azure Files backup via Azure Backup REST API | https://learn.microsoft.com/en-us/azure/backup/backup-azure-file-share-rest-api |
| Integrate Defender ransomware alerts with Azure Backup | https://learn.microsoft.com/en-us/azure/backup/backup-azure-integrate-microsoft-defender-using-logic-apps |
| Automate Azure VM SQL backup with PowerShell | https://learn.microsoft.com/en-us/azure/backup/backup-azure-sql-automation |
| Back up SQL Server in Azure VMs using Azure CLI | https://learn.microsoft.com/en-us/azure/backup/backup-azure-sql-backup-cli |
| Manage Azure Backup for SQL Server VMs using CLI | https://learn.microsoft.com/en-us/azure/backup/backup-azure-sql-manage-cli |
| Restore SQL Server databases in Azure VMs via CLI | https://learn.microsoft.com/en-us/azure/backup/backup-azure-sql-restore-cli |
| Back up SQL Server databases in Azure VMs via REST API | https://learn.microsoft.com/en-us/azure/backup/backup-azure-sql-vm-rest-api |
| Back up Azure Blobs using Azure CLI commands | https://learn.microsoft.com/en-us/azure/backup/backup-blobs-storage-account-cli |
| Back up Azure Blobs using PowerShell commands | https://learn.microsoft.com/en-us/azure/backup/backup-blobs-storage-account-ps |
| Back up Azure Managed Disks using Azure CLI | https://learn.microsoft.com/en-us/azure/backup/backup-managed-disks-cli |
| Back up Azure Managed Disks using PowerShell APIs | https://learn.microsoft.com/en-us/azure/backup/backup-managed-disks-ps |
| Back up PostgreSQL in Azure VMs using Azure CLI | https://learn.microsoft.com/en-us/azure/backup/backup-postgresql-cli |
| Back up Azure PostgreSQL using Azure PowerShell | https://learn.microsoft.com/en-us/azure/backup/backup-postgresql-ps |
| Automate and email Azure Backup reports using Logic Apps | https://learn.microsoft.com/en-us/azure/backup/backup-reports-email |
| Manage Azure Backup resources with Azure CLI | https://learn.microsoft.com/en-us/azure/backup/create-manage-azure-services-using-azure-command-line-interface |
| Manage Azure Files backups with Azure Backup REST API | https://learn.microsoft.com/en-us/azure/backup/manage-azure-file-share-rest-api |
| Manage Azure Backup for SQL Server VMs via REST API | https://learn.microsoft.com/en-us/azure/backup/manage-azure-sql-vm-rest-api |
| Use Azure Backup PowerShell script samples | https://learn.microsoft.com/en-us/azure/backup/powershell-backup-samples |
| Query Azure Backup state using Azure Resource Graph | https://learn.microsoft.com/en-us/azure/backup/query-backups-using-azure-resource-graph |
| Restore Azure Files using Azure Backup REST API | https://learn.microsoft.com/en-us/azure/backup/restore-azure-file-share-rest-api |
| Restore SQL Server databases in Azure VMs using REST API | https://learn.microsoft.com/en-us/azure/backup/restore-azure-sql-vm-rest-api |
| Restore Azure Blobs to a point in time using CLI | https://learn.microsoft.com/en-us/azure/backup/restore-blobs-storage-account-cli |
| Restore Azure Blobs using PowerShell and Azure Backup | https://learn.microsoft.com/en-us/azure/backup/restore-blobs-storage-account-ps |
| Restore Azure Managed Disks using Azure CLI | https://learn.microsoft.com/en-us/azure/backup/restore-managed-disks-cli |
| Restore Azure Managed Disks using PowerShell commands | https://learn.microsoft.com/en-us/azure/backup/restore-managed-disks-ps |
| Restore Azure PostgreSQL databases using Azure CLI | https://learn.microsoft.com/en-us/azure/backup/restore-postgresql-database-cli |
| Restore Azure PostgreSQL databases using PowerShell | https://learn.microsoft.com/en-us/azure/backup/restore-postgresql-database-ps |
| Restore PostgreSQL databases using Data Protection REST API | https://learn.microsoft.com/en-us/azure/backup/restore-postgresql-database-use-rest-api |
| Use PowerShell to find the Recovery Services vault for a storage account | https://learn.microsoft.com/en-us/azure/backup/scripts/backup-powershell-script-find-recovery-services-vault |
| Disable Azure Files soft delete via ARM API script | https://learn.microsoft.com/en-us/azure/backup/scripts/disable-soft-delete-for-file-shares |
| Scripted installation of the latest MARS agent on Windows servers | https://learn.microsoft.com/en-us/azure/backup/scripts/install-latest-microsoft-azure-recovery-services-agent |
| Automate Azure Backup configuration for on-premises Windows servers | https://learn.microsoft.com/en-us/azure/backup/scripts/microsoft-azure-recovery-services-powershell-all |
| Register on-premises Windows machines with a Recovery Services vault via script | https://learn.microsoft.com/en-us/azure/backup/scripts/register-microsoft-azure-recovery-services-agent |
| Script to create or modify MARS file and folder backup policies | https://learn.microsoft.com/en-us/azure/backup/scripts/set-file-folder-backup-policy |
| Script to create or modify system state backup policies with MARS | https://learn.microsoft.com/en-us/azure/backup/scripts/set-system-state-backup-policy |
| Update Recovery Services vault settings via REST API | https://learn.microsoft.com/en-us/azure/backup/use-restapi-update-vault-properties |

### Deployment
| Topic | URL |
|-------|-----|
| Back up Azure Local VMs with MABS | https://learn.microsoft.com/en-us/azure/backup/back-up-azure-stack-hyperconverged-infrastructure-virtual-machines |
| Use MABS v4 protection support matrix | https://learn.microsoft.com/en-us/azure/backup/backup-mabs-protection-matrix |
| Automate silent installation of Azure Backup Server v4 | https://learn.microsoft.com/en-us/azure/backup/backup-mabs-unattended-install |
| Stop protection for workloads in MABS | https://learn.microsoft.com/en-us/azure/backup/backup-server-stop-protection |
| Use MABS v3 RTM protection matrix for supported workloads | https://learn.microsoft.com/en-us/azure/backup/microsoft-azure-backup-server-protection-v3 |
| Use MABS v3 UR1 protection matrix for supported workloads | https://learn.microsoft.com/en-us/azure/backup/microsoft-azure-backup-server-protection-v3-ur1 |