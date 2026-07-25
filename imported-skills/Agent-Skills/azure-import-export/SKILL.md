---
name: azure-import-export
description: Expert knowledge for Azure Import Export development including troubleshooting, limits & quotas, and security. Use when setting CMK via Key Vault, checking drive limits, validating prerequisites, or debugging Import/Export job failures, and other Azure Import Export related development tasks. Not for Azure Data Box (use azure-data-box-family), Azure Blob Storage (use azure-blob-storage), Azure Files (use azure-files).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-05-17"
  generator: "docs2skills/1.0.0"
---
# Azure Import Export Skill

This skill provides expert guidance for Azure Import Export. Covers troubleshooting, limits & quotas, and security. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L31-L38 | Diagnosing and fixing Azure Import/Export job failures, reading Import/Export logs, and repairing failed v1 import/export jobs and copy issues. |
| Limits & Quotas | L39-L44 | Hardware/software prerequisites for Import/Export jobs and FAQs on service limits, supported drive counts/sizes, behaviors, and constraints when importing or exporting data. |
| Security | L45-L48 | Configuring customer-managed encryption keys (CMK) for Azure Import/Export jobs, including key setup, permissions, and using Azure Key Vault for data-at-rest security. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Handle and repair failed Azure Export jobs (v1 tool) | https://learn.microsoft.com/en-us/azure/import-export/storage-import-export-tool-repairing-an-export-job-v1 |
| Handle and repair failed Azure Import jobs (v1 tool) | https://learn.microsoft.com/en-us/azure/import-export/storage-import-export-tool-repairing-an-import-job-v1 |
| Use Import/Export logs to diagnose copy issues | https://learn.microsoft.com/en-us/azure/import-export/storage-import-export-tool-reviewing-job-status-v1 |
| Troubleshoot common Azure Import/Export job failures | https://learn.microsoft.com/en-us/azure/import-export/storage-import-export-tool-troubleshooting-v1 |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Check Azure Import/Export hardware and software requirements | https://learn.microsoft.com/en-us/azure/import-export/storage-import-export-requirements |
| Azure Import/Export service limits and behaviors FAQ | https://learn.microsoft.com/en-us/azure/import-export/storage-import-export-service-faq |

### Security
| Topic | URL |
|-------|-----|
| Configure customer-managed encryption keys for Azure Import/Export | https://learn.microsoft.com/en-us/azure/import-export/storage-import-export-encryption-key-portal |