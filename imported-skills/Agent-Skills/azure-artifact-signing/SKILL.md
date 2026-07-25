---
name: azure-artifact-signing
description: Expert knowledge for Azure Artifact Signing development including best practices, decision making, security, configuration, and integrations & coding patterns. Use when managing signing cert lifecycle, RBAC roles, DGSSv2 migration, diagnostic logs, or CI/CD signing integrations, and other Azure Artifact Signing related development tasks. Not for Azure Key Vault (use azure-key-vault), Azure Artifacts (use azure-artifacts), Azure Information Protection (use azure-information-protection).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-28"
  generator: "docs2skills/1.0.0"
---
# Azure Artifact Signing Skill

This skill provides expert guidance for Azure Artifact Signing. Covers best practices, decision making, security, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Best Practices | L33-L37 | Guidance on managing signing certificates end-to-end: rotation, renewal, expiration handling, key protection, and lifecycle policies for Azure Artifact Signing. |
| Decision Making | L38-L43 | Pricing and SKU selection for Azure Artifact Signing and guidance to migrate from DGSSv2, including plan changes and transition steps. |
| Security | L44-L51 | RBAC roles, identities, and validations for secure Artifact Signing, plus how to sign Windows code integrity policies and assign access permissions. |
| Configuration | L52-L56 | Configuring diagnostic settings for Artifact Signing, enabling and routing logs to destinations like Log Analytics, Storage, and Event Hubs for monitoring and analysis. |
| Integrations & Coding Patterns | L57-L60 | Configuring Artifact Signing with supported tools and workflows (e.g., CI/CD systems, package managers), including setup steps and patterns for integrating signing into build and release pipelines. |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply certificate lifecycle practices in Artifact Signing | https://learn.microsoft.com/en-us/azure/artifact-signing/concept-certificate-management |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose and change Artifact Signing pricing SKUs | https://learn.microsoft.com/en-us/azure/artifact-signing/how-to-change-sku |
| Migrate from DGSSv2 to Azure Artifact Signing | https://learn.microsoft.com/en-us/azure/artifact-signing/how-to-device-guard-signing-service-migration |

### Security
| Topic | URL |
|-------|-----|
| Understand Artifact Signing resources and RBAC roles | https://learn.microsoft.com/en-us/azure/artifact-signing/concept-resources-roles |
| Manage Artifact Signing identity validations securely | https://learn.microsoft.com/en-us/azure/artifact-signing/how-to-renew-identity-validation |
| Sign Windows code integrity policies with Artifact Signing | https://learn.microsoft.com/en-us/azure/artifact-signing/how-to-sign-ci-policy |
| Assign Azure RBAC roles for Artifact Signing access | https://learn.microsoft.com/en-us/azure/artifact-signing/tutorial-assign-roles |

### Configuration
| Topic | URL |
|-------|-----|
| Configure diagnostic settings and log routing for Artifact Signing | https://learn.microsoft.com/en-us/azure/artifact-signing/how-to-sign-history |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Configure supported signing integrations for Artifact Signing | https://learn.microsoft.com/en-us/azure/artifact-signing/how-to-signing-integrations |