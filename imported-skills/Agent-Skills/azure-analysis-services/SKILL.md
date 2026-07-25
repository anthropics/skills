---
name: azure-analysis-services
description: Expert knowledge for Azure Analysis Services development including troubleshooting. Use when configuring firewalls/VNets, gateways, DNS, or client connections to Azure Analysis Services, and other Azure Analysis Services related development tasks. Not for Azure Synapse Analytics (use azure-synapse-analytics), Azure SQL Database (use azure-sql-database), Azure SQL Managed Instance (use azure-sql-managed-instance), SQL Server on Azure Virtual Machines (use azure-sql-virtual-machines).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-28"
  generator: "docs2skills/1.0.0"
---
# Azure Analysis Services Skill

This skill provides expert guidance for Azure Analysis Services. Covers troubleshooting. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L29-L32 | Diagnosing and fixing Azure Analysis Services connectivity issues, including firewall/VNet settings, gateway configuration, DNS, and common client connection failures. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Azure Analysis Services network connectivity | https://learn.microsoft.com/en-us/analysis-services/azure-analysis-services/analysis-services-network-faq?view=sql-analysis-services-2025 |