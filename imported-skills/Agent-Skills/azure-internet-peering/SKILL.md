---
name: azure-internet-peering
description: Expert knowledge for Azure Internet Peering development including troubleshooting. Use when validating Peering Service prefixes, checking prefix registration, verifying routing, or fixing reachability issues, and other Azure Internet Peering related development tasks. Not for Azure ExpressRoute (use azure-expressroute), Azure Virtual Network (use azure-virtual-network), Azure Virtual WAN (use azure-virtual-wan), Azure VPN Gateway (use azure-vpn-gateway).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-02-28"
  generator: "docs2skills/1.0.0"
---
# Azure Internet Peering Skill

This skill provides expert guidance for Azure Internet Peering. Covers troubleshooting. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L29-L32 | Diagnosing and validating Azure Peering Service prefixes, including prefix registration checks, routing verification, and troubleshooting connectivity or reachability issues. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Validate and troubleshoot Azure Peering Service prefixes | https://learn.microsoft.com/en-us/azure/internet-peering/peering-registered-prefix-requirements |