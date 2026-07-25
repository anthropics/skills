---
name: azure-quotas
description: Expert knowledge for Azure Quotas development including limits & quotas. Use when requesting per-region Storage account quota increases, checking limits, or filing Azure support requests, and other Azure Quotas related development tasks. Not for Azure Cost Management (use azure-cost-management), Azure Monitor (use azure-monitor), Azure Policy (use azure-policy), Azure Resource Manager (use azure-resource-manager).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-21"
  generator: "docs2skills/1.0.0"
---
# Azure Quotas Skill

This skill provides expert guidance for Azure Quotas. Covers limits & quotas. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Limits & Quotas | L29-L32 | How to request and manage per-region Azure Storage account quota increases, including limits, prerequisites, and support request steps. |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Increase Azure Storage account quota per region | https://learn.microsoft.com/en-us/azure/quotas/storage-account-quota-requests |