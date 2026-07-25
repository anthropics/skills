---
name: azure-sql-virtual-machines
description: Expert knowledge for SQL Server on Azure Virtual Machines development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when choosing SQL VM vs Managed Instance, configuring Always On/FCI, HA/DR, storage, backups, or Blob-based backups, and other SQL Server on Azure Virtual Machines related development tasks. Not for Azure SQL Database (use azure-sql-database), Azure SQL Managed Instance (use azure-sql-managed-instance), Azure Virtual Machines (use azure-virtual-machines), SAP HANA on Azure Large Instances (use azure-sap).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# SQL Server on Azure Virtual Machines Skill

This skill provides expert guidance for SQL Server on Azure Virtual Machines. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L53 | Diagnosing and fixing performance, connectivity, capacity, memory, log, replication, and I/O issues for Azure SQL Database, Managed Instance, and SQL Server on Azure VMs |
| Best Practices | L54-L67 | Best practices for SQL Server on Azure VMs: HA/DR clustering, DNN listeners, backup/restore, performance tuning, storage and VM sizing, baselines, and best practices assessments. |
| Decision Making | L68-L80 | Guidance for choosing Azure SQL options and pricing, comparing SQL VMs vs Managed Instance, planning migrations (including Db2), HADR choices, regional feature support, and SQL VM licensing/AHB. |
| Architecture & Design Patterns | L81-L89 | High-level designs and patterns for SQL Server on Azure VMs: connectivity, Always On availability groups, failover cluster instances, and Windows Server Failover Clustering setup. |
| Limits & Quotas | L90-L94 | Info on Azure SQL capacity limits, DTU benchmark behavior, regional feature availability, and how to request quota increases for databases and managed instances |
| Security | L95-L105 | Securing SQL Server on Azure VMs: policies, TLS cert rotation, Key Vault/EKM, managed identities, Entra auth, Extended Security Updates, hardening guidance, and confidential VM deployment. |
| Configuration | L106-L147 | Configuring SQL Server on Azure VMs: HA/DR (AGs, FCIs, load balancers, clustering), storage/layout, tempdb, vCores, connectivity, backups, and SQL IaaS Agent setup/management. |
| Integrations & Coding Patterns | L148-L153 | Backing up SQL Server on Azure VMs directly to Azure Blob Storage, including configurations that use managed identities instead of stored credentials. |
| Deployment | L154-L169 | Deploying and configuring SQL Server Always On availability groups and FCI on Azure VMs, including single/multi-subnet, cross-region, prerequisites, and migration of VMs and disks. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Resolve capacity errors when deploying Azure SQL resources | https://learn.microsoft.com/en-us/azure/azure-sql/capacity-errors-troubleshoot?view=azuresql |
| Fix slow database import and export in Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/database-import-export-hang?view=azuresql |
| Troubleshoot and mitigate transient connectivity errors in Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/troubleshoot-common-connectivity-issues?view=azuresql |
| Troubleshoot Azure SQL and Fabric SQL connectivity errors | https://learn.microsoft.com/en-us/azure/azure-sql/database/troubleshoot-common-errors-issues?view=azuresql |
| Troubleshoot geo-replication and redo lag in Azure SQL Database | https://learn.microsoft.com/en-us/azure/azure-sql/database/troubleshoot-geo-replication-redo?view=azuresql |
| Investigate and fix memory issues in Azure SQL Database | https://learn.microsoft.com/en-us/azure/azure-sql/database/troubleshoot-memory-errors-issues?view=azuresql |
| Diagnose and fix Azure SQL DB transaction log full errors | https://learn.microsoft.com/en-us/azure/azure-sql/database/troubleshoot-transaction-log-errors-issues?view=azuresql-db |
| Resolve known issues in Azure SQL Managed Instance | https://learn.microsoft.com/en-us/azure/azure-sql/managed-instance/doc-changes-updates-known-issues?view=azuresql |
| Resolve transaction log full errors in Azure SQL Managed Instance | https://learn.microsoft.com/en-us/azure/azure-sql/managed-instance/troubleshoot-transaction-log-errors-issues?view=azuresql-mi |
| Resolve common SQL Server on Linux Azure VM issues | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/linux/frequently-asked-questions-faq?view=azuresql |
| Resolve common SQL Server on Azure VM issues | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/frequently-asked-questions-faq?view=azuresql |
| Troubleshoot SQL Server IaaS Agent extension issues on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/sql-agent-extension-troubleshoot-known-issues?view=azuresql |
| Diagnose I/O throttling for SQL Server on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/storage-performance-analysis?view=azuresql |

### Best Practices
| Topic | URL |
|-------|-----|
| Prepare for planned maintenance in Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/planned-maintenance?view=azuresql |
| Use SQL features with DNN listeners on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/availability-group-dnn-interoperability?view=azuresql |
| Apply backup and restore strategies for SQL Server on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/backup-restore?view=azuresql |
| Use SQL Server features with FCI DNN on Azure | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/failover-cluster-instance-dnn-interoperability?view=azuresql |
| Configure HADR clusters for SQL Server on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/hadr-cluster-best-practices?view=azuresql |
| Apply performance best-practice checklist for SQL Server on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/performance-guidelines-best-practices-checklist?view=azuresql |
| Collect performance baselines for SQL Server on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/performance-guidelines-best-practices-collect-baseline?view=azuresql |
| Optimize Azure SQL VM storage performance configuration | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/performance-guidelines-best-practices-storage?view=azuresql |
| Apply VM sizing performance best practices for SQL Server on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/performance-guidelines-best-practices-vm-size?view=azuresql |
| Run SQL best practices assessment for Azure SQL VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/sql-assessment-for-sql-vm?view=azuresql |

### Decision Making
| Topic | URL |
|-------|-----|
| Use Azure SQL decision tree to choose service | https://learn.microsoft.com/en-us/azure/azure-sql/azure-sql-decision-tree?view=azuresql |
| Check Azure SQL Database feature availability by region | https://learn.microsoft.com/en-us/azure/azure-sql/database/region-availability?view=azuresql |
| Check Azure SQL Managed Instance feature availability by region | https://learn.microsoft.com/en-us/azure/azure-sql/managed-instance/region-availability?view=azuresql |
| Plan and modernize SQL Server workloads to Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/migration-guides/modernization?view=azuresql |
| Plan and execute Db2 to SQL on Azure VM migration | https://learn.microsoft.com/en-us/azure/azure-sql/migration-guides/virtual-machines/db2-to-sql-on-azure-vm-guide?view=azuresql |
| Use Modernization Advisor to compare SQL VM vs Managed Instance | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/modernization-advisor?view=azuresql |
| Choose HADR options for SQL Server on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/business-continuity-high-availability-disaster-recovery-hadr-overview?view=azuresql |
| Switch SQL Server VM licensing to Azure Hybrid Benefit | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/licensing-model-azure-hybrid-benefit-ahb-change?view=azuresql |
| Choose cost‑effective pricing for SQL Server on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/pricing-guidance?view=azuresql |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Understand connectivity architecture for Azure SQL Database | https://learn.microsoft.com/en-us/azure/azure-sql/database/connectivity-architecture?view=azuresql |
| Apply SQL Server application patterns on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/application-patterns-development-strategies?view=azuresql |
| Design Always On availability groups for SQL Server on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/availability-group-overview?view=azuresql |
| Understand failover cluster instances for SQL Server on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/failover-cluster-instance-overview?view=azuresql |
| Use Windows Server Failover Clustering with SQL Server on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/hadr-windows-server-failover-cluster-overview?view=azuresql |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Understand DTU benchmark characteristics for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/dtu-benchmark?view=azuresql |

### Security
| Topic | URL |
|-------|-----|
| Use built-in Azure Policy definitions for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/policy-reference?view=azuresql |
| Prepare for Azure SQL TLS root certificate rotation | https://learn.microsoft.com/en-us/azure/azure-sql/updates/ssl-root-certificate-expiring?view=azuresql |
| Configure Azure Key Vault integration for SQL Server VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/azure-key-vault-integration-configure?view=azuresql |
| Enable Microsoft Entra authentication for SQL Server VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/configure-azure-ad-authentication-for-sql-vm?view=azuresql |
| Configure Extended Security Updates for SQL Server on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/extended-security-updates-sql-vm?view=azuresql |
| Harden SQL Server on Azure VMs with security best practices | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/security-considerations-best-practices?view=azuresql |
| Deploy SQL Server to Azure confidential VMs securely | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/sql-vm-create-confidential-vm-how-to?view=azuresql |

### Configuration
| Topic | URL |
|-------|-----|
| Reference for Azure SQL Database monitoring metrics and logs | https://learn.microsoft.com/en-us/azure/azure-sql/database/monitoring-sql-database-azure-monitor-reference?view=azuresql |
| Reference monitoring metrics for Azure SQL Managed Instance | https://learn.microsoft.com/en-us/azure/azure-sql/managed-instance/monitoring-sql-managed-instance-azure-monitor-reference?view=azuresql |
| Set up Always On AG with DH2i DxEnterprise on Azure | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/linux/dh2i-high-availability-tutorial?view=azuresql |
| Configure availability group listener for Linux SQL VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/linux/high-availability-listener-tutorial?view=azuresql |
| Configure RHEL cluster and fencing for SQL AG on Azure | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/linux/rhel-high-availability-fencing-tutorial?view=azuresql |
| Configure SLES cluster and STONITH for SQL AG on Azure | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/linux/sles-high-availability-fencing-tutorial?view=azuresql |
| Register Linux SQL Server VM with IaaS Agent extension | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/linux/sql-iaas-agent-extension-register-vm-linux?view=azuresql |
| Configure SQL IaaS Agent extension on Linux VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/linux/sql-server-iaas-agent-extension-linux?view=azuresql |
| Configure Ubuntu availability group for SQL on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/linux/ubuntu-high-availability-fencing-tutorial?view=azuresql |
| Create SQL Server on Azure VM with PowerShell | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/scripts/create-sql-vm-powershell?view=azuresql |
| Configure automated backups for SQL Server 2014 VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/automated-backup-sql-2014?view=azuresql |
| Configure automated backups for SQL Server 2016+ VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/automated-backup?view=azuresql |
| Configure DNN listener for SQL availability groups on VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/availability-group-distributed-network-name-dnn-listener-configure?view=azuresql |
| Configure AG listeners and load balancer via PowerShell | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/availability-group-listener-powershell-configure?view=azuresql |
| Configure load balancer and AG listener in Azure portal | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/availability-group-load-balancer-portal-configure?view=azuresql |
| Configure Azure Load Balancer for SQL AG VNN listener | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/availability-group-vnn-azure-load-balancer-configure?view=azuresql |
| Change SQL Server edition in-place on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/change-sql-server-edition?view=azuresql |
| Upgrade or downgrade SQL Server version in-place on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/change-sql-server-version?view=azuresql |
| Configure SQL Server on Azure VM deployment options | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/create-sql-vm-portal?view=azuresql |
| Provision SQL Server on Azure VMs with advanced PowerShell options | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/create-sql-vm-powershell?view=azuresql |
| Configure SQL Server on Azure Dedicated Host | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/dedicated-host?view=azuresql |
| Manually configure SQL FCI with Azure Elastic SAN | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/failover-cluster-instance-azure-elastic-san-manually-configure?view=azuresql |
| Manually configure SQL FCI with Azure shared disks | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/failover-cluster-instance-azure-shared-disks-manually-configure?view=azuresql |
| Configure distributed network name for SQL FCI on Azure | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/failover-cluster-instance-distributed-network-name-dnn-configure?view=azuresql |
| Create SQL failover cluster instance using premium file shares | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/failover-cluster-instance-premium-file-share-manually-configure?view=azuresql |
| Prepare Azure VMs for SQL failover cluster instances | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/failover-cluster-instance-prepare-vm?view=azuresql |
| Configure SQL FCI using Storage Spaces Direct on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/failover-cluster-instance-storage-spaces-direct-manually-configure?view=azuresql |
| Configure Azure Load Balancer for SQL FCI VNN | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/failover-cluster-instance-vnn-azure-load-balancer-configure?view=azuresql |
| Configure cluster quorum for SQL Server VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/hadr-cluster-quorum-configure-how-to?view=azuresql |
| Manage SQL Server on Azure VMs using the SQL virtual machines resource | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/manage-sql-vm-portal?view=azuresql |
| Enable automatic SQL IaaS Agent extension registration for all SQL VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/sql-agent-extension-automatic-registration-all-vms?view=azuresql |
| Manually register a SQL Server VM with the SQL IaaS Agent extension | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/sql-agent-extension-manually-register-single-vm?view=azuresql |
| Bulk register SQL Server VMs with the SQL IaaS Agent extension | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/sql-agent-extension-manually-register-vms-bulk?view=azuresql |
| Configure Azure Elastic SAN for SQL Server VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/storage-configuration-azure-elastic-san?view=azuresql |
| Configure storage layout for SQL Server on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/storage-configuration?view=azuresql |
| Configure tempdb on ephemeral storage for SQL Server VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/tempdb-ephemeral-storage?view=azuresql |
| Configure vCore customization for SQL Server on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/vm-vcore-customization-for-sql?view=azuresql |
| Configure connectivity options for SQL Server on Azure VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/ways-to-connect-to-sql?view=azuresql |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Back up SQL Server on Azure VMs to Azure Blob Storage | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/azure-storage-sql-server-backup-restore-use?view=azuresql |
| Back up SQL Server VM databases to Blob using managed identity | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/backup-restore-to-url-using-managed-identities?view=azuresql |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy multi-subnet availability group using PowerShell/CLI | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/availability-group-az-commandline-configure-multi-subnet?view=azuresql |
| Deploy single-subnet availability group via PowerShell/CLI | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/availability-group-az-commandline-configure?view=azuresql |
| Configure domain-independent workgroup availability group | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/availability-group-clusterless-workgroup-configure?view=azuresql |
| Configure cross-region multi-subnet availability group | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/availability-group-manually-configure-multi-subnet-multiple-regions?view=azuresql |
| Configure cross-region availability group for SQL VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/availability-group-manually-configure-multiple-regions?view=azuresql |
| Prepare prerequisites for single-subnet availability groups | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/availability-group-manually-configure-prerequisites-tutorial-single-subnet?view=azuresql |
| Configure multi-subnet availability group on SQL VMs | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/availability-group-manually-configure-tutorial-multi-subnet?view=azuresql |
| Configure single-subnet Always On availability group | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/availability-group-manually-configure-tutorial-single-subnet?view=azuresql |
| Migrate availability group from single to multi-subnet | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/availability-group-manually-migrate-multi-subnet?view=azuresql |
| Deploy availability group using Azure quickstart templates | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/availability-group-quickstart-template-configure?view=azuresql |
| Migrate SQL Server VMs to another Azure region | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/move-sql-vm-different-region?view=azuresql |
| Migrate SQL Server VM log disk to Azure Ultra Disk | https://learn.microsoft.com/en-us/azure/azure-sql/virtual-machines/windows/storage-migrate-to-ultradisk?view=azuresql |
| Migrate SQL FCI to Azure VMs with Azure Migrate | https://learn.microsoft.com/en-us/data-migration/sql-server/virtual-machines/failover-cluster-instance-migrate |