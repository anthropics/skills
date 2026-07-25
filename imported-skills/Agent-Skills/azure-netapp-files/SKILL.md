---
name: azure-netapp-files
description: Expert knowledge for Azure NetApp Files development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when deploying ANF for SAP HANA/Oracle, AVS datastores, NFS/SMB volumes, azacsnap/REST APIs, or cross-region replication, and other Azure NetApp Files related development tasks. Not for Azure Files (use azure-files), Azure Blob Storage (use azure-blob-storage), Azure Elastic SAN (use azure-elastic-san), Azure Managed Lustre (use azure-managed-lustre).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure NetApp Files Skill

This skill provides expert guidance for Azure NetApp Files. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L57 | Diagnosing and fixing Azure NetApp Files issues: networking, NFS/SMB auth and locks, capacity pools, snapshots, CMK encryption, volume CRUD/AVGs, cross-region replication, and AzAcSnap. |
| Best Practices | L58-L80 | Performance and reliability best practices for Azure NetApp Files: sizing, VM/AVD/AVS choices, NFS/SMB/Linux tuning, cloning, quotas, AD/DNS, Oracle dNFS, AzAcSnap, and Terraform-safe changes. |
| Decision Making | L81-L95 | Cost, performance, and protection design for Azure NetApp Files: choosing service levels, volume types, replication and backup options, reservations, SMB CA, cool access, and SQL Server TCO. |
| Architecture & Design Patterns | L96-L104 | Designing and deploying Azure NetApp Files for SAP HANA/Oracle, AVS datastores, VNet and AD topology, and high‑performance, multi-volume application architectures. |
| Limits & Quotas | L105-L129 | Limits, quotas, and performance caps for Azure NetApp Files volumes: size/maxfiles/inodes, user/group quotas, large-volume and cache limits, regional capacity, benchmarks, and protocol/path constraints. |
| Security | L130-L167 | Security, encryption, identity, and access control for Azure NetApp Files: Kerberos/LDAP/AD, ACLs/permissions, CMK/HSM keys, ransomware protection, and secure API/data plane configuration. |
| Configuration | L168-L209 | Configuring Azure NetApp Files: accounts, pools, volumes (NFS/SMB/dual-protocol), backups, caching, networking/AD/LDAP, SAP/Oracle AzAcSnap, logging, QoS, and zone-redundant setups. |
| Integrations & Coding Patterns | L210-L224 | Using azacsnap with Azure NetApp Files, REST API and PowerShell operations, and integrating ANF with SAP HANA/Oracle AVGs, S3 clients, Databricks, and OneLake via object REST API. |
| Deployment | L225-L238 | Deploying and configuring Azure NetApp Files for SAP HANA and Oracle (AVGs, HSR, DR, backups), managing cross-region replication, zone changes, ONTAP migration, and regional access. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot common AzAcSnap tool issues | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azacsnap-troubleshoot |
| Diagnose Azure NetApp Files Resource Provider errors and workarounds | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azure-netapp-files-troubleshoot-resource-provider-errors |
| Resolve stale file locks on ANF cache volumes | https://learn.microsoft.com/en-us/azure/azure-netapp-files/break-file-locks-cache-volume |
| Resolve Azure NetApp Files networking issues | https://learn.microsoft.com/en-us/azure/azure-netapp-files/faq-networking |
| Resolve Azure NetApp Files NFS protocol issues | https://learn.microsoft.com/en-us/azure/azure-netapp-files/faq-nfs |
| Address common SMB issues and behaviors in Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/faq-smb |
| Reset SMB computer account password for NetApp cache volumes | https://learn.microsoft.com/en-us/azure/azure-netapp-files/reset-password-cache-volumes |
| Diagnose and fix Azure NetApp Files application volume group errors | https://learn.microsoft.com/en-us/azure/azure-netapp-files/troubleshoot-application-volume-groups |
| Resolve SMB authentication and CIFS password reset failures in Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/troubleshoot-authentication-password-reset-failure |
| Resolve Azure NetApp Files capacity pool errors | https://learn.microsoft.com/en-us/azure/azure-netapp-files/troubleshoot-capacity-pools |
| Troubleshoot Azure NetApp Files cross-region replication issues | https://learn.microsoft.com/en-us/azure/azure-netapp-files/troubleshoot-cross-region-replication |
| Fix customer-managed key encryption issues in Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/troubleshoot-customer-managed-keys |
| Troubleshoot Azure NetApp Files with Diagnose and Solve | https://learn.microsoft.com/en-us/azure/azure-netapp-files/troubleshoot-diagnose-solve-problems |
| Clear stale file locks on Azure NetApp Files NFS and SMB volumes | https://learn.microsoft.com/en-us/azure/azure-netapp-files/troubleshoot-file-locks |
| Resolve Azure NetApp Files snapshot policy management errors | https://learn.microsoft.com/en-us/azure/azure-netapp-files/troubleshoot-snapshot-policies |
| Troubleshoot LDAP user access issues on Azure NetApp Files volumes | https://learn.microsoft.com/en-us/azure/azure-netapp-files/troubleshoot-user-access-ldap |
| Troubleshoot Azure NetApp Files volume CRUD errors | https://learn.microsoft.com/en-us/azure/azure-netapp-files/troubleshoot-volumes |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply practical tips for using AzAcSnap | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azacsnap-tips |
| Apply Azure NetApp Files performance planning guidelines | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azure-netapp-files-performance-considerations |
| Run performance benchmark tests on Azure NetApp Files volumes | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azure-netapp-files-performance-metrics-volumes |
| Apply SMB performance best practices for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azure-netapp-files-smb-performance |
| Design reliable DNS for Azure NetApp Files access | https://learn.microsoft.com/en-us/azure/azure-netapp-files/domain-name-system-concept |
| Use Azure NetApp Files cloning safely and effectively | https://learn.microsoft.com/en-us/azure/azure-netapp-files/faq-clone |
| Optimize Azure NetApp Files datastores for AVS performance | https://learn.microsoft.com/en-us/azure/azure-netapp-files/performance-azure-vmware-solution-datastore |
| Tune NFS session slots and concurrency for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/performance-linux-concurrency-session-slots |
| Tune Linux direct I/O for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/performance-linux-direct-io |
| Optimize Linux filesystem cache for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/performance-linux-filesystem-cache |
| Configure Linux NFS mount options for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/performance-linux-mount-options |
| Adjust Linux NFS read-ahead for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/performance-linux-nfs-read-ahead |
| Select Azure VM SKUs for Azure NetApp Files performance | https://learn.microsoft.com/en-us/azure/azure-netapp-files/performance-virtual-machine-sku |
| Optimize Oracle dNFS with Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/solutions-benefits-azure-netapp-files-oracle-database |
| Deploy Azure Virtual Desktop with NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/solutions-windows-virtual-desktop |
| Safely update Terraform-managed Azure NetApp Files resources | https://learn.microsoft.com/en-us/azure/azure-netapp-files/terraform-manage-volume |
| Apply Azure NetApp Files performance testing methodology | https://learn.microsoft.com/en-us/azure/azure-netapp-files/testing-methodology |
| Plan Active Directory Domain Services for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/understand-guidelines-active-directory-domain-service-site |
| Plan and manage Azure NetApp Files volume hard quotas | https://learn.microsoft.com/en-us/azure/azure-netapp-files/volume-hard-quota-guidelines |

### Decision Making
| Topic | URL |
|-------|-----|
| Optimize Azure NetApp Files costs and billing | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azure-netapp-files-cost-model |
| Choose Azure NetApp Files service levels by throughput | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azure-netapp-files-service-levels |
| Understand Azure NetApp Files backup capabilities and cost model | https://learn.microsoft.com/en-us/azure/azure-netapp-files/backup-introduction |
| Choose Azure NetApp Files data protection options | https://learn.microsoft.com/en-us/azure/azure-netapp-files/data-protection-disaster-recovery-options |
| Change Azure NetApp Files volume service level dynamically | https://learn.microsoft.com/en-us/azure/azure-netapp-files/dynamic-change-volume-service-level |
| Enable SMB Continuous Availability on Azure NetApp Files volumes | https://learn.microsoft.com/en-us/azure/azure-netapp-files/enable-continuous-availability-existing-smb |
| Evaluate performance trade-offs of Azure NetApp Files cool access | https://learn.microsoft.com/en-us/azure/azure-netapp-files/performance-considerations-cool-access |
| Choose Azure NetApp Files replication model | https://learn.microsoft.com/en-us/azure/azure-netapp-files/replication |
| Optimize Azure NetApp Files costs with reservations | https://learn.microsoft.com/en-us/azure/azure-netapp-files/reservations |
| Assess SQL Server TCO with Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/solutions-benefits-azure-netapp-files-sql-server |
| Choose Azure NetApp Files volume types by workload | https://learn.microsoft.com/en-us/azure/azure-netapp-files/workload-types |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Use Azure NetApp Files application volume groups for workload deployment | https://learn.microsoft.com/en-us/azure/azure-netapp-files/application-volume-group-concept |
| Deploy SAP HANA using Azure NetApp Files application volume groups | https://learn.microsoft.com/en-us/azure/azure-netapp-files/application-volume-group-introduction |
| Deploy Oracle using Azure NetApp Files application volume groups | https://learn.microsoft.com/en-us/azure/azure-netapp-files/application-volume-group-oracle-introduction |
| Plan Azure NetApp Files virtual network topologies | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azure-netapp-files-network-topologies |
| Architect high-performance Oracle on multiple Azure NetApp Files volumes | https://learn.microsoft.com/en-us/azure/azure-netapp-files/performance-oracle-multiple-volumes |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Add SAP HANA hosts using Azure NetApp Files application volume group | https://learn.microsoft.com/en-us/azure/azure-netapp-files/application-volume-group-add-hosts |
| Configure auxiliary NFS groups and limits in Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/auxiliary-groups |
| Manage Azure NetApp Files resource limits and quotas | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azure-netapp-files-resource-limits |
| Apply resize limits for ANF cache volumes | https://learn.microsoft.com/en-us/azure/azure-netapp-files/cache-volumes-resize-guidelines |
| Enable LDAP extended groups for Azure NetApp Files NFS volumes | https://learn.microsoft.com/en-us/azure/azure-netapp-files/configure-ldap-extended-groups |
| Configure user and group quotas on Azure NetApp Files volumes | https://learn.microsoft.com/en-us/azure/azure-netapp-files/default-individual-user-group-quotas-introduction |
| Understand directory size growth and metadata overhead in Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/directory-sizes-concept |
| Review Azure NetApp Files large volume limits | https://learn.microsoft.com/en-us/azure/azure-netapp-files/large-volumes |
| Apply size and feature limits for Azure NetApp Files large volumes | https://learn.microsoft.com/en-us/azure/azure-netapp-files/large-volumes-requirements-considerations |
| Manage user and group quotas on Azure NetApp Files volumes | https://learn.microsoft.com/en-us/azure/azure-netapp-files/manage-default-individual-user-group-quotas |
| Manage maxfiles limits and inode quotas in Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/maxfiles-concept |
| Use Azure NetApp Files AVS datastore performance benchmarks | https://learn.microsoft.com/en-us/azure/azure-netapp-files/performance-benchmarks-azure-vmware-solution |
| Review Azure NetApp Files Linux performance benchmarks | https://learn.microsoft.com/en-us/azure/azure-netapp-files/performance-benchmarks-linux |
| Review breakthrough mode performance limits for Azure NetApp Files large volumes | https://learn.microsoft.com/en-us/azure/azure-netapp-files/performance-large-volume-breakthrough-mode-linux |
| Understand large volume performance limits on Azure NetApp Files for Linux | https://learn.microsoft.com/en-us/azure/azure-netapp-files/performance-large-volumes-linux |
| Assess Oracle performance on a single Azure NetApp Files volume | https://learn.microsoft.com/en-us/azure/azure-netapp-files/performance-oracle-single-volumes |
| Understand Azure NetApp Files regional capacity quotas | https://learn.microsoft.com/en-us/azure/azure-netapp-files/regional-capacity-quota |
| Check Azure NetApp Files replication requirements and limits | https://learn.microsoft.com/en-us/azure/azure-netapp-files/replication-requirements |
| Restore individual Azure NetApp Files from backup | https://learn.microsoft.com/en-us/azure/azure-netapp-files/restore-single-file-backup |
| Understand file and path length limits in Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/understand-path-lengths |
| Configure volume language and character set limits in Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/understand-volume-languages |

### Security
| Topic | URL |
|-------|-----|
| Use Azure Policy definitions with Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azure-policy-definitions |
| Configure NFSv4.1 access control lists in Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/configure-access-control-lists |
| Configure customer-managed encryption keys for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/configure-customer-managed-keys |
| Secure Azure NetApp Files with HSM-backed customer-managed keys | https://learn.microsoft.com/en-us/azure/azure-netapp-files/configure-customer-managed-keys-hardware |
| Configure NFSv4.1 Kerberos encryption for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/configure-kerberos-encryption |
| Configure AD DS LDAP over TLS for NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/configure-ldap-over-tls |
| Manage Azure NetApp Files control plane security and access | https://learn.microsoft.com/en-us/azure/azure-netapp-files/control-plane-security |
| Configure cross-tenant customer-managed keys for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/customer-managed-keys-cross-tenant |
| Configure Azure NetApp Files data plane security options | https://learn.microsoft.com/en-us/azure/azure-netapp-files/data-plane-security |
| Disable NFS showmount for Azure NetApp Files security | https://learn.microsoft.com/en-us/azure/azure-netapp-files/disable-showmount |
| Choose dual-protocol security styles and permissions in Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/dual-protocol-permission-behaviors |
| Configure AD connection for Elastic SMB volumes | https://learn.microsoft.com/en-us/azure/azure-netapp-files/elastic-active-directory |
| Configure CMK encryption for Elastic NetApp volumes | https://learn.microsoft.com/en-us/azure/azure-netapp-files/elastic-customer-managed-keys |
| Understand AES encryption behavior in Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/faq-advanced-encryption-standard |
| Join Linux VM to Microsoft Entra Domain | https://learn.microsoft.com/en-us/azure/azure-netapp-files/join-active-directory-domain |
| Use Kerberos authentication with Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/kerberos |
| Understand LDAP usage and directory access for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/lightweight-directory-access-protocol |
| Use local NFS users with LDAP in Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/lightweight-directory-access-protocol-local-users |
| Configure LDAP name mapping rules for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/lightweight-directory-access-protocol-name-mapping |
| Configure LDAP schemas for Azure NetApp Files directory lookups | https://learn.microsoft.com/en-us/azure/azure-netapp-files/lightweight-directory-access-protocol-schemas |
| Manage SMB share ACLs for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/manage-smb-share-access-control-lists |
| Modify Azure NetApp Files Active Directory settings | https://learn.microsoft.com/en-us/azure/azure-netapp-files/modify-active-directory-connections |
| Manage NAS file and folder permissions in Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/network-attached-file-permissions |
| Configure NFS mode-bit file permissions in Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/network-attached-file-permissions-nfs |
| Configure SMB NTFS file permissions in Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/network-attached-file-permissions-smb |
| Configure NAS share permissions for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/network-attached-storage-permissions |
| Manage NFS group memberships and supplemental groups for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/network-file-system-group-memberships |
| Use NFSv4.x ACLs for access control in Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/nfs-access-control-lists |
| Configure Azure NetApp Files object REST API securely | https://learn.microsoft.com/en-us/azure/azure-netapp-files/object-rest-api-access-configure |
| Understand Kerberos security and performance impact on Azure NetApp Files NFSv4.1 | https://learn.microsoft.com/en-us/azure/azure-netapp-files/performance-impact-kerberos |
| Configure advanced ransomware protection for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/ransomware-configure |
| Meet requirements for Azure NetApp Files ransomware protection | https://learn.microsoft.com/en-us/azure/azure-netapp-files/ransomware-protection-requirements |
| Configure AES-based Kerberos encryption for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/understand-advanced-encryption-standard |
| Configure data encryption for Azure NetApp Files at rest and in transit | https://learn.microsoft.com/en-us/azure/azure-netapp-files/understand-data-encryption |

### Configuration
| Topic | URL |
|-------|-----|
| Meet requirements for SAP HANA application volume groups on Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/application-volume-group-considerations |
| Meet requirements for Oracle application volume groups on Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/application-volume-group-oracle-considerations |
| Use AzAcSnap backup command for snapshots | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azacsnap-cmd-ref-backup |
| Run AzAcSnap configure command correctly | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azacsnap-cmd-ref-configure |
| Run AzAcSnap test command and validate setup | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azacsnap-cmd-ref-test |
| Configure databases for AzAcSnap snapshots | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azacsnap-configure-database |
| Configure Azure storage for AzAcSnap usage | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azacsnap-configure-storage |
| Configure AzAcSnap 11 preview features for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azacsnap-preview |
| Use Azure NetApp Files in Azure Government regions | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azure-government |
| Configure NFS export policies for Azure NetApp Files volumes | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azure-netapp-files-configure-export-policy |
| Configure NFSv4.1 ID domain for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azure-netapp-files-configure-nfsv41-domain |
| Create NetApp account for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azure-netapp-files-create-netapp-account |
| Configure NFS volumes in Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azure-netapp-files-create-volumes |
| Configure SMB volumes and AD for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azure-netapp-files-create-volumes-smb |
| Delegate a subnet to Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azure-netapp-files-delegate-subnet |
| Register NetApp Resource Provider in Azure | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azure-netapp-files-register |
| Create capacity pool for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azure-netapp-files-set-up-capacity-pool |
| Configure policy-based backups for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/backup-configure-policy-based |
| Meet requirements for using Azure NetApp Files backup | https://learn.microsoft.com/en-us/azure/azure-netapp-files/backup-requirements-considerations |
| Configure Azure NetApp Files cache volume requirements | https://learn.microsoft.com/en-us/azure/azure-netapp-files/cache-requirements |
| Change service level of Azure NetApp Files cache volumes | https://learn.microsoft.com/en-us/azure/azure-netapp-files/change-cache-volume-service-level |
| Configure Azure NetApp Files cache volumes | https://learn.microsoft.com/en-us/azure/azure-netapp-files/configure-cache-volumes |
| Configure Azure NetApp Files volume network features | https://learn.microsoft.com/en-us/azure/azure-netapp-files/configure-network-features |
| Configure Linux NFS clients for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/configure-nfs-clients |
| Configure Unix permissions and ownership for Azure NetApp Files volumes | https://learn.microsoft.com/en-us/azure/azure-netapp-files/configure-unix-permissions-change-ownership-mode |
| Configure Azure Virtual WAN connectivity for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/configure-virtual-wan |
| Configure Active Directory connections for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/create-active-directory-connections |
| Configure dual-protocol NFS/SMB volumes with LDAP | https://learn.microsoft.com/en-us/azure/azure-netapp-files/create-volumes-dual-protocol |
| View and monitor Azure NetApp Files replication health | https://learn.microsoft.com/en-us/azure/azure-netapp-files/cross-region-replication-display-health-status |
| Create NetApp Elastic account for zone-redundant pools | https://learn.microsoft.com/en-us/azure/azure-netapp-files/elastic-account |
| Create Elastic zone-redundant capacity pool | https://learn.microsoft.com/en-us/azure/azure-netapp-files/elastic-capacity-pool-task |
| Monitor Elastic zone-redundant Azure NetApp Files with metrics | https://learn.microsoft.com/en-us/azure/azure-netapp-files/elastic-metrics |
| Create NFS volume on Elastic zone-redundant storage | https://learn.microsoft.com/en-us/azure/azure-netapp-files/elastic-volume |
| Create SMB volume on Elastic zone-redundant storage | https://learn.microsoft.com/en-us/azure/azure-netapp-files/elastic-volume-server-message-block |
| Configure and interpret Azure NetApp Files access logs | https://learn.microsoft.com/en-us/azure/azure-netapp-files/manage-file-access-logs |
| Manage manual QoS capacity pools in NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/manage-manual-qos-capacity-pool |
| Configure SMB features and constants in Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/sever-message-block-support |
| Configure DFS Namespaces and root consolidation with Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/use-dfs-n-and-dfs-root-consolidation-with-azure-netapp-files |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use azacsnap delete command for Azure NetApp Files snapshots | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azacsnap-cmd-ref-delete |
| Use azacsnap details command with Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azacsnap-cmd-ref-details |
| Restore data using azacsnap with Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azacsnap-cmd-ref-restore |
| Configure azacsnap runbefore and runafter hooks for Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azacsnap-cmd-ref-runbefore-runafter |
| Use Azure NetApp Files REST API for storage operations | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azure-netapp-files-develop-with-rest-api |
| Configure SAP HANA AVGs on Azure NetApp Files via REST | https://learn.microsoft.com/en-us/azure/azure-netapp-files/configure-application-volume-group-sap-hana-api |
| Configure Oracle AVGs on Azure NetApp Files via REST | https://learn.microsoft.com/en-us/azure/azure-netapp-files/configure-application-volume-oracle-api |
| Call Azure NetApp Files REST API using PowerShell | https://learn.microsoft.com/en-us/azure/azure-netapp-files/develop-rest-api-powershell |
| Access Azure NetApp Files object REST API volumes with S3 clients | https://learn.microsoft.com/en-us/azure/azure-netapp-files/object-rest-api-browser |
| Connect Azure Databricks to Azure NetApp Files via object REST API | https://learn.microsoft.com/en-us/azure/azure-netapp-files/object-rest-api-databricks |
| Connect OneLake to Azure NetApp Files using object REST API | https://learn.microsoft.com/en-us/azure/azure-netapp-files/object-rest-api-onelake |

### Deployment
| Topic | URL |
|-------|-----|
| Add SAP HANA secondary system for HSR with Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/application-volume-group-add-volume-secondary |
| Deploy first SAP HANA host with Azure NetApp Files application volume group | https://learn.microsoft.com/en-us/azure/azure-netapp-files/application-volume-group-deploy-first-host |
| Configure SAP HANA disaster recovery with Azure NetApp Files cross-region replication | https://learn.microsoft.com/en-us/azure/azure-netapp-files/application-volume-group-disaster-recovery |
| Perform disaster recovery with AzAcSnap on ALI | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azacsnap-disaster-recovery |
| Install AzAcSnap for Azure NetApp Files backups | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azacsnap-get-started |
| Install AzAcSnap on Azure and Large Instances | https://learn.microsoft.com/en-us/azure/azure-netapp-files/azacsnap-installation |
| Deploy Oracle AVGs on Azure NetApp Files with ARM | https://learn.microsoft.com/en-us/azure/azure-netapp-files/configure-application-volume-oracle-azure-resource-manager |
| Manage disaster recovery with Azure NetApp Files replication | https://learn.microsoft.com/en-us/azure/azure-netapp-files/cross-region-replication-manage-disaster-recovery |
| Change availability zones for Elastic capacity pools | https://learn.microsoft.com/en-us/azure/azure-netapp-files/elastic-change-zones |
| Migrate ONTAP volumes to Azure NetApp Files | https://learn.microsoft.com/en-us/azure/azure-netapp-files/migrate-volumes |
| Request Azure NetApp Files regional access | https://learn.microsoft.com/en-us/azure/azure-netapp-files/request-region-access |