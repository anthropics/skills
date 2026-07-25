---
name: azure-information-protection
description: Expert knowledge for Azure Information Protection development including best practices, decision making, configuration, and deployment. Use when choosing Azure RMS vs AD RMS, deploying RMS connectors, migrating keys/policies, or configuring MSIPC clients, and other Azure Information Protection related development tasks. Not for Azure Key Vault (use azure-key-vault), Azure Security (use azure-security), Azure Defender For Cloud (use azure-defender-for-cloud).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-28"
  generator: "docs2skills/1.0.0"
---
# Azure Information Protection Skill

This skill provides expert guidance for Azure Information Protection. Covers best practices, decision making, configuration, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Best Practices | L32-L36 | Monitoring and troubleshooting Azure RMS connector health, tracking Azure Rights Management usage, and interpreting logs/metrics for ongoing protection service reliability. |
| Decision Making | L37-L41 | Guidance on choosing between Azure Rights Management and on-premises AD RMS, including feature, deployment, security, and migration considerations. |
| Configuration | L42-L46 | Configuring and deploying the Windows RMS (MSIPC) client and setting required registry values for RMS connectors on servers for Azure Information Protection. |
| Deployment | L47-L61 | Deploying the RMS connector on-prem servers and step-by-step guidance for migrating AD RMS (keys and policies) to Azure Information Protection, including HSM and software key paths |

### Best Practices
| Topic | URL |
|-------|-----|
| Monitor RMS connector health and Azure RMS usage | https://learn.microsoft.com/en-us/azure/information-protection/monitor-rms-connector |

### Decision Making
| Topic | URL |
|-------|-----|
| Decide between Azure Rights Management and AD RMS | https://learn.microsoft.com/en-us/azure/information-protection/compare-on-premise |

### Configuration
| Topic | URL |
|-------|-----|
| Configure RMS connector registry settings on servers | https://learn.microsoft.com/en-us/azure/information-protection/rms-connector-registry-settings |

### Deployment
| Topic | URL |
|-------|-----|
| Configure on-premises servers to use the RMS connector | https://learn.microsoft.com/en-us/azure/information-protection/configure-servers-rms-connector |
| Deploy the Azure RMS connector for on-premises servers | https://learn.microsoft.com/en-us/azure/information-protection/deploy-rms-connector |
| Install and configure the RMS connector for AIP | https://learn.microsoft.com/en-us/azure/information-protection/install-configure-rms-connector |
| Prepare environment for Phase 1 AD RMS to AIP migration | https://learn.microsoft.com/en-us/azure/information-protection/migrate-from-ad-rms-phase1 |
| Execute Phase 2 of AD RMS to AIP migration | https://learn.microsoft.com/en-us/azure/information-protection/migrate-from-ad-rms-phase2 |
| Complete Phase 3 of AD RMS to AIP migration | https://learn.microsoft.com/en-us/azure/information-protection/migrate-from-ad-rms-phase3 |
| Run Phase 4 tasks for AD RMS to AIP migration | https://learn.microsoft.com/en-us/azure/information-protection/migrate-from-ad-rms-phase4 |
| Finalize Phase 5 of AD RMS to AIP migration | https://learn.microsoft.com/en-us/azure/information-protection/migrate-from-ad-rms-phase5 |
| Migrate AD RMS deployments to Azure Information Protection | https://learn.microsoft.com/en-us/azure/information-protection/migrate-from-ad-rms-to-azure-rms |
| Migrate HSM-protected AD RMS key to AIP HSM key | https://learn.microsoft.com/en-us/azure/information-protection/migrate-hsmkey-to-hsmkey |
| Migrate software-protected AD RMS key to AIP HSM key | https://learn.microsoft.com/en-us/azure/information-protection/migrate-softwarekey-to-hsmkey |
| Migrate software-protected AD RMS key to AIP software key | https://learn.microsoft.com/en-us/azure/information-protection/migrate-softwarekey-to-softwarekey |