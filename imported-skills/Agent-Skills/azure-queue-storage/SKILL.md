---
name: azure-queue-storage
description: Expert knowledge for Azure Queue Storage development including best practices, limits & quotas, security, configuration, and integrations & coding patterns. Use when using queue client SDKs, Entra ID auth, client-side encryption, monitoring metrics/logs, or scaling queues, and other Azure Queue Storage related development tasks. Not for Azure Blob Storage (use azure-blob-storage), Azure Table Storage (use azure-table-storage), Azure Service Bus (use azure-service-bus), Azure Event Hubs (use azure-event-hubs).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-05-24"
  generator: "docs2skills/1.0.0"
---
# Azure Queue Storage Skill

This skill provides expert guidance for Azure Queue Storage. Covers best practices, limits & quotas, security, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Best Practices | L33-L39 | Monitoring, securing, and tuning Azure Queue Storage: metrics/logging, alerts, encryption, access control, and performance/scalability patterns and checklists. |
| Limits & Quotas | L40-L45 | Scalability and size limits for Azure Queue Storage, including max queues/messages, throughput, message size, and total storage constraints. |
| Security | L46-L59 | Using Entra ID/RBAC/ABAC for queue data access, configuring auth in CLI/Portal/PowerShell, client-side encryption, and migrating Queue apps to passwordless authentication |
| Configuration | L60-L65 | Configuring and interpreting monitoring for Azure Queue Storage, including metrics, logs, diagnostic settings, and detailed reference for all queue monitoring data fields. |
| Integrations & Coding Patterns | L66-L74 | Client library how-tos for using Azure Queue Storage with .NET, Java, JavaScript, Python, and PowerShell, including setup, auth, CRUD operations, and common coding patterns. |

### Best Practices
| Topic | URL |
|-------|-----|
| Best practices for monitoring Queue Storage | https://learn.microsoft.com/en-us/azure/storage/queues/queues-storage-monitoring-scenarios |
| Apply security best practices to Queue Storage | https://learn.microsoft.com/en-us/azure/storage/queues/security-recommendations |
| Performance and scalability checklist for queues | https://learn.microsoft.com/en-us/azure/storage/queues/storage-performance-checklist |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Understand Azure Queue Storage scalability limits | https://learn.microsoft.com/en-us/azure/storage/queues/scalability-targets |
| Understand Azure Queue Storage size limits | https://learn.microsoft.com/en-us/azure/storage/queues/storage-queues-introduction |

### Security
| Topic | URL |
|-------|-----|
| Assign Azure RBAC roles for queue data access | https://learn.microsoft.com/en-us/azure/storage/queues/assign-azure-role-data-access |
| Authorize Azure Queue Storage with Entra ID and RBAC | https://learn.microsoft.com/en-us/azure/storage/queues/authorize-access-azure-active-directory |
| Authorize queue data operations with Azure CLI | https://learn.microsoft.com/en-us/azure/storage/queues/authorize-data-operations-cli |
| Authorize queue data access in Azure portal | https://learn.microsoft.com/en-us/azure/storage/queues/authorize-data-operations-portal |
| Use Entra credentials with PowerShell for queues | https://learn.microsoft.com/en-us/azure/storage/queues/authorize-data-operations-powershell |
| Configure client-side encryption for Queue Storage | https://learn.microsoft.com/en-us/azure/storage/queues/client-side-encryption |
| Migrate Queue Storage apps to passwordless auth | https://learn.microsoft.com/en-us/azure/storage/queues/passwordless-migrate-queues |
| Use ABAC role assignment conditions for queues | https://learn.microsoft.com/en-us/azure/storage/queues/queues-auth-abac |
| Actions and attributes for Queue Storage ABAC | https://learn.microsoft.com/en-us/azure/storage/queues/queues-auth-abac-attributes |
| Example ABAC role conditions for Queue Storage | https://learn.microsoft.com/en-us/azure/storage/queues/queues-auth-abac-examples |

### Configuration
| Topic | URL |
|-------|-----|
| Configure monitoring for Azure Queue Storage | https://learn.microsoft.com/en-us/azure/storage/queues/monitor-queue-storage |
| Reference for Queue Storage monitoring data | https://learn.microsoft.com/en-us/azure/storage/queues/monitor-queue-storage-reference |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Manage Azure Queue Storage with PowerShell | https://learn.microsoft.com/en-us/azure/storage/queues/storage-powershell-how-to-use-queues |
| Use Azure Queue Storage .NET client library | https://learn.microsoft.com/en-us/azure/storage/queues/storage-quickstart-queues-dotnet |
| Use Azure Queue Storage Java client library | https://learn.microsoft.com/en-us/azure/storage/queues/storage-quickstart-queues-java |
| Use Azure Queue Storage JavaScript client library | https://learn.microsoft.com/en-us/azure/storage/queues/storage-quickstart-queues-nodejs |
| Use Azure Queue Storage Python client library | https://learn.microsoft.com/en-us/azure/storage/queues/storage-quickstart-queues-python |
| Work with Azure Queue Storage in .NET | https://learn.microsoft.com/en-us/azure/storage/queues/storage-tutorial-queues |