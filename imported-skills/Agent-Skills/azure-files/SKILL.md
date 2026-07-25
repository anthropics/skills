---
name: azure-files
description: Expert knowledge for Azure Files development including best practices, decision making, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when using Azure Files/File Sync, SMB/NFS shares, AD/Entra auth, FSLogix/VDI, or RAG over file data, and other Azure Files related development tasks. Not for Azure Blob Storage (use azure-blob-storage), Azure Queue Storage (use azure-queue-storage), Azure Table Storage (use azure-table-storage), Azure NetApp Files (use azure-netapp-files).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Files Skill

This skill provides expert guidance for Azure Files. Covers best practices, decision making, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Best Practices | L35-L50 | Best practices for Azure Files and Azure File Sync: DR/failover planning, server/drive replacement and recovery, safe deprovisioning, and performance tuning for SMB/NFS and VDI/FSLogix workloads. |
| Decision Making | L51-L70 | Guidance on planning Azure Files and File Sync deployments, choosing tiers, redundancy, billing/cost models, and migration approaches (Windows, Linux, SMB, NFS, NetApp) for optimal design. |
| Limits & Quotas | L71-L78 | Scalability, performance, and quota limits for Azure Files and File Sync, including tiers, API throttling behavior, and FAQs on supported sizes, IOPS, and throughput. |
| Security | L79-L107 | Securing Azure Files access and data: identity-based SMB/NFS auth (AD DS, Entra ID, Kerberos, managed identities), encryption (TLS, CMK), permissions/ACLs, and network/firewall/proxy configuration. |
| Configuration | L108-L134 | Configuring Azure Files and Azure File Sync: networking, VPN and endpoints, performance and redundancy, cloud tiering, DFS integration, monitoring/metrics, and backup/soft delete settings. |
| Integrations & Coding Patterns | L135-L157 | Patterns and code to build RAG apps over Azure Files using Haystack, LangChain, LlamaIndex, and vector DBs (Pinecone/Qdrant/Weaviate), plus .NET/Java/Python integration and auth. |
| Deployment | L158-L169 | Guides for migrating and syncing data to Azure Files/Azure File Sync from NAS, Linux, GlusterFS, SMB/NFS shares, and moving File Sync resources safely across scopes. |

### Best Practices
| Topic | URL |
|-------|-----|
| Implement disaster recovery best practices for Azure File Sync | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-disaster-recovery-best-practices |
| Modify Azure File Sync topology without data loss | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-modify-sync-topology |
| Replace drives on Azure File Sync servers correctly | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-replace-drive |
| Replace Azure File Sync servers during lifecycle events | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-replace-server |
| Deprovision Azure File Sync server endpoints safely | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-server-endpoint-delete |
| Recover Azure File Sync servers after failures | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-server-recovery |
| Plan Azure Files disaster recovery and failover | https://learn.microsoft.com/en-us/azure/storage/files/files-disaster-recovery |
| Handle large directories on NFS Azure file shares | https://learn.microsoft.com/en-us/azure/storage/files/nfs-large-directories |
| Tune NFS Azure file share performance at scale | https://learn.microsoft.com/en-us/azure/storage/files/nfs-performance |
| Improve performance of premium SMB Azure file shares | https://learn.microsoft.com/en-us/azure/storage/files/smb-performance |
| Optimize Azure Files performance for your workloads | https://learn.microsoft.com/en-us/azure/storage/files/understand-performance |
| Use Azure Files for virtual desktop and FSLogix profiles | https://learn.microsoft.com/en-us/azure/storage/files/virtual-desktop-workloads |

### Decision Making
| Topic | URL |
|-------|-----|
| Select optimal Azure File Sync cloud tiering policies | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-choose-cloud-tiering-policies |
| Plan and choose an Azure File Sync deployment | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-planning |
| Choose and configure Azure File Sync server endpoints | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-server-endpoint-create |
| Choose and create Azure classic file shares by tier | https://learn.microsoft.com/en-us/azure/storage/files/create-classic-file-share |
| Decide when to use Microsoft.FileShares file shares | https://learn.microsoft.com/en-us/azure/storage/files/create-file-share |
| Estimate Azure Files costs across billing models | https://learn.microsoft.com/en-us/azure/storage/files/file-estimate-cost |
| Choose Azure Files redundancy options for durability | https://learn.microsoft.com/en-us/azure/storage/files/files-redundancy |
| Reduce Azure Files costs using reservations | https://learn.microsoft.com/en-us/azure/storage/files/files-reserve-capacity |
| Choose redundancy options for SSD Azure file shares | https://learn.microsoft.com/en-us/azure/storage/files/redundancy-premium-file-shares |
| Choose development approaches for Azure Files applications | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-developer-overview |
| Migrate Linux servers to NFS Azure file shares | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-migration-nfs |
| Choose migration approaches for SMB Azure file shares | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-migration-overview |
| Choose between Azure Files and Azure NetApp Files | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-netapp-comparison |
| Choose Azure Files billing model and manage costs | https://learn.microsoft.com/en-us/azure/storage/files/understanding-billing |
| Plan migration from Windows file servers to Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/windows-server-to-azure-files |
| Use zonal placement for SSD Azure file shares | https://learn.microsoft.com/en-us/azure/storage/files/zonal-placement |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Understand Azure File Sync scalability and performance targets | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-scale-targets |
| Review Azure File Sync API throttling limits and behavior | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-throttling |
| Azure Files and File Sync FAQ with limits and behaviors | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-faq |
| Azure Files scalability and performance limits by tier | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-scale-targets |

### Security
| Topic | URL |
|-------|-----|
| Configure on-premises firewall and proxy for Azure File Sync | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-firewall-and-proxy |
| Use managed identities to secure Azure File Sync access | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-managed-identities |
| Authorize Azure Files data access in portal | https://learn.microsoft.com/en-us/azure/storage/files/authorize-data-operations-portal |
| Enable OAuth-based REST access to Azure file shares | https://learn.microsoft.com/en-us/azure/storage/files/authorize-oauth-rest |
| Change identity source for Azure Files SMB authentication | https://learn.microsoft.com/en-us/azure/storage/files/change-identity-source |
| Configure customer-managed encryption keys for Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/customer-managed-keys |
| Enable TLS encryption in transit for NFS Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/encryption-in-transit-for-nfs-shares |
| Authenticate Azure Files SMB access with managed identities | https://learn.microsoft.com/en-us/azure/storage/files/files-managed-identities |
| Configure network security perimeter for Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/files-network-security-perimeter |
| Configure and secure NFS file shares in Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/files-nfs-protocol |
| Disable insecure SMB1 on Linux for Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/files-remove-smb1-linux |
| Configure Entra Kerberos auth for Azure Files on macOS | https://learn.microsoft.com/en-us/azure/storage/files/identity-kerberos-authentication-macos |
| Configure NFS root squash for Azure file shares | https://learn.microsoft.com/en-us/azure/storage/files/nfs-root-squash |
| Configure identity-based authentication for Azure Files over SMB | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-active-directory-overview |
| Configure AD DS authentication for Azure file shares | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-identity-ad-ds-enable |
| Configure on-prem AD DS authentication for Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-identity-ad-ds-overview |
| Rotate AD DS storage account identity password | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-identity-ad-ds-update-password |
| Assign share-level permissions for Azure Files SMB | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-identity-assign-share-level-permissions |
| Use Entra Domain Services auth with Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-identity-auth-domain-services-enable |
| Configure cloud trust between AD DS and Entra ID for Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-identity-auth-hybrid-cloud-trust |
| Enable Microsoft Entra Kerberos for Azure Files SMB | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-identity-auth-hybrid-identities-enable |
| Configure Kerberos auth for Linux Azure Files clients | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-identity-auth-linux-kerberos-enable |
| Configure NTFS ACL permissions for Azure file shares | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-identity-configure-file-level-permissions |
| Configure Azure Files SMB auth across AD forests | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-identity-multiple-forests |
| Mount Azure SMB file shares securely on Linux | https://learn.microsoft.com/en-us/azure/storage/files/storage-how-to-use-files-linux |

### Configuration
| Topic | URL |
|-------|-----|
| Silently install Azure File Sync agent with custom settings | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-agent-silent-installation |
| Configure Azure File Sync cloud tiering date and space policies | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-cloud-tiering-policy |
| Install and manage Azure File Sync agent on Arc servers | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-extension |
| Manage Azure File Sync cloud tiered files via PowerShell | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-how-to-manage-tiered-files |
| Monitor Azure File Sync cloud tiering metrics and cache | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-monitor-cloud-tiering |
| Configure and monitor Azure File Sync with Azure Monitor | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-monitoring |
| Configure public and private endpoints for Azure File Sync | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-networking-endpoints |
| Configure networking for Azure File Sync caching servers | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-networking-overview |
| Reference metrics and logs for monitoring Azure File Sync | https://learn.microsoft.com/en-us/azure/storage/file-sync/monitor-file-sync-reference |
| Analyze Azure Files performance metrics with Azure Monitor | https://learn.microsoft.com/en-us/azure/storage/files/analyze-files-metrics |
| Change redundancy configuration for Azure Files accounts | https://learn.microsoft.com/en-us/azure/storage/files/files-change-redundancy-configuration |
| Integrate DFS Namespaces with Azure file shares | https://learn.microsoft.com/en-us/azure/storage/files/files-manage-namespaces |
| Copy files between Azure file shares with tools | https://learn.microsoft.com/en-us/azure/storage/files/migrate-files-between-shares |
| Configure size and performance of Azure file shares | https://learn.microsoft.com/en-us/azure/storage/files/modify-file-share |
| Configure Linux point-to-site VPN for Azure Files access | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-configure-p2s-vpn-linux |
| Configure Windows P2S VPN access to Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-configure-p2s-vpn-windows |
| Set up site-to-site VPN connectivity for Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-configure-s2s-vpn |
| Configure and mount NFS Azure file shares on Linux | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-how-to-mount-nfs-shares |
| Configure Azure Monitor metrics and logs for Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-monitoring |
| Reference monitoring metrics and logs for Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-monitoring-reference |
| Configure DNS forwarding to Azure Files private endpoints | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-networking-dns |
| Configure public and private endpoints for Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-networking-endpoints |
| Configure and use soft delete for Azure file shares | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-prevent-file-share-deletion |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate Haystack RAG pipelines with Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/artificial-intelligence/retrieval-augmented-generation/open-source-frameworks/orchestrations/haystack |
| Integrate LangChain RAG pipelines with Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/artificial-intelligence/retrieval-augmented-generation/open-source-frameworks/orchestrations/langchain |
| Integrate LlamaIndex RAG pipelines with Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/artificial-intelligence/retrieval-augmented-generation/open-source-frameworks/orchestrations/llamaindex |
| Authenticate and download Azure Files data for RAG | https://learn.microsoft.com/en-us/azure/storage/files/artificial-intelligence/retrieval-augmented-generation/open-source-frameworks/setup |
| Implement Haystack + Pinecone RAG over Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/artificial-intelligence/retrieval-augmented-generation/open-source-frameworks/tutorials/haystack-pinecone/tutorial-haystack-pinecone |
| Implement Haystack + Qdrant RAG over Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/artificial-intelligence/retrieval-augmented-generation/open-source-frameworks/tutorials/haystack-qdrant/tutorial-haystack-qdrant |
| Implement Haystack + Weaviate RAG over Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/artificial-intelligence/retrieval-augmented-generation/open-source-frameworks/tutorials/haystack-weaviate/tutorial-haystack-weaviate |
| Implement Azure Files RAG with LangChain and Pinecone | https://learn.microsoft.com/en-us/azure/storage/files/artificial-intelligence/retrieval-augmented-generation/open-source-frameworks/tutorials/langchain-pinecone/tutorial-langchain-pinecone |
| Implement Azure Files RAG with LangChain and Qdrant | https://learn.microsoft.com/en-us/azure/storage/files/artificial-intelligence/retrieval-augmented-generation/open-source-frameworks/tutorials/langchain-qdrant/tutorial-langchain-qdrant |
| Implement Azure Files RAG with LangChain and Weaviate | https://learn.microsoft.com/en-us/azure/storage/files/artificial-intelligence/retrieval-augmented-generation/open-source-frameworks/tutorials/langchain-weaviate/tutorial-langchain-weaviate |
| Implement Azure Files RAG with LlamaIndex and Pinecone | https://learn.microsoft.com/en-us/azure/storage/files/artificial-intelligence/retrieval-augmented-generation/open-source-frameworks/tutorials/llamaindex-pinecone/tutorial-llamaindex-pinecone |
| Implement Azure Files RAG with LlamaIndex and Qdrant | https://learn.microsoft.com/en-us/azure/storage/files/artificial-intelligence/retrieval-augmented-generation/open-source-frameworks/tutorials/llamaindex-qdrant/tutorial-llamaindex-qdrant |
| Implement Azure Files RAG with LlamaIndex and Weaviate | https://learn.microsoft.com/en-us/azure/storage/files/artificial-intelligence/retrieval-augmented-generation/open-source-frameworks/tutorials/llamaindex-weaviate/tutorial-llamaindex-weaviate |
| Use Pinecone vector database with Azure Files RAG | https://learn.microsoft.com/en-us/azure/storage/files/artificial-intelligence/retrieval-augmented-generation/open-source-frameworks/vector-databases/pinecone |
| Use Qdrant vector database with Azure Files RAG | https://learn.microsoft.com/en-us/azure/storage/files/artificial-intelligence/retrieval-augmented-generation/open-source-frameworks/vector-databases/qdrant |
| Use Weaviate vector database with Azure Files RAG | https://learn.microsoft.com/en-us/azure/storage/files/artificial-intelligence/retrieval-augmented-generation/open-source-frameworks/vector-databases/weaviate |
| Develop .NET applications that use Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/storage-dotnet-how-to-use-files |
| Develop Java applications that use Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/storage-java-how-to-use-file-storage |
| Develop Python applications using Azure Files SDKs | https://learn.microsoft.com/en-us/azure/storage/files/storage-python-how-to-use-file-storage |

### Deployment
| Topic | URL |
|-------|-----|
| Move Azure File Sync resources across scopes safely | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-resource-move |
| Migrate data between Azure file shares with File Sync | https://learn.microsoft.com/en-us/azure/storage/file-sync/file-sync-share-to-share-migration |
| Migrate GlusterFS volumes to Azure Files | https://learn.microsoft.com/en-us/azure/storage/files/glusterfs-migration-guide |
| Migrate SMB/NFS shares to Azure Files via Storage Mover | https://learn.microsoft.com/en-us/azure/storage/files/migrate-files-storage-mover |
| Migrate Linux servers to Azure File Sync hybrid | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-migration-linux-hybrid |
| Migrate on-prem NAS to Azure Files with Data Box | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-migration-nas-cloud-databox |
| Migrate NAS SMB shares to Azure File Sync hybrid | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-migration-nas-hybrid |
| Migrate on-premises NAS to Azure File Sync using Data Box | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-migration-nas-hybrid-databox |
| Migrate to SMB Azure file shares using Robocopy | https://learn.microsoft.com/en-us/azure/storage/files/storage-files-migration-robocopy |