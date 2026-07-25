---
name: azure-lighthouse
description: Expert knowledge for Azure Lighthouse development including decision making, security, configuration, integrations & coding patterns, and deployment. Use when configuring Lighthouse delegations, AOBO/PIM access, Arc/Sentinel integrations, policies/remediation, or Marketplace offers, and other Azure Lighthouse related development tasks. Not for Azure Arc (use azure-arc), Azure Managed Applications (use azure-managed-applications), Azure Resource Manager (use azure-resource-manager), Azure Role-based access control (use azure-rbac).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-04-12"
  generator: "docs2skills/1.0.0"
---
# Azure Lighthouse Skill

This skill provides expert guidance for Azure Lighthouse. Covers decision making, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Decision Making | L33-L39 | Guidance on when and how to use Azure Lighthouse: multi-tenant enterprise setups, ISV SaaS patterns, comparing Lighthouse vs managed apps, and designing Managed Service offers. |
| Security | L40-L47 | Managing secure access in Azure Lighthouse: roles, tenants, AOBO, PIM eligible authorizations, and recommended security controls/practices for cross-tenant management. |
| Configuration | L48-L60 | Configuring and managing Azure Lighthouse delegations: onboarding via ARM/policy, updating/removing access, deploying/using policies (incl. built-ins), remediation with managed identities, and monitoring changes. |
| Integrations & Coding Patterns | L61-L68 | Cross-tenant integration patterns for managing Arc servers, Sentinel workspaces, Migrate projects, and Monitor Logs at scale using Azure Lighthouse. |
| Deployment | L69-L72 | Guidance for packaging, publishing, and managing Azure Lighthouse managed service offers in Azure Marketplace, including requirements, steps, and configuration details. |

### Decision Making
| Topic | URL |
|-------|-----|
| Apply Azure Lighthouse in ISV SaaS scenarios | https://learn.microsoft.com/en-us/azure/lighthouse/concepts/isv-scenarios |
| Choose between Azure Lighthouse and managed applications | https://learn.microsoft.com/en-us/azure/lighthouse/concepts/managed-applications |
| Design Managed Service offers for Azure Lighthouse | https://learn.microsoft.com/en-us/azure/lighthouse/concepts/managed-services-offers |

### Security
| Topic | URL |
|-------|-----|
| Apply CSP AOBO and Lighthouse security controls | https://learn.microsoft.com/en-us/azure/lighthouse/concepts/cloud-solution-provider |
| Implement recommended security practices for Azure Lighthouse | https://learn.microsoft.com/en-us/azure/lighthouse/concepts/recommended-security-practices |
| Use tenants, users, and roles with Azure Lighthouse | https://learn.microsoft.com/en-us/azure/lighthouse/concepts/tenants-users-roles |
| Configure eligible authorizations with Azure Lighthouse and PIM | https://learn.microsoft.com/en-us/azure/lighthouse/how-to/create-eligible-authorizations |

### Configuration
| Topic | URL |
|-------|-----|
| Configure policy remediation with managed identities via Lighthouse | https://learn.microsoft.com/en-us/azure/lighthouse/how-to/deploy-policy-remediation |
| Monitor Azure Lighthouse delegation changes via activity logs | https://learn.microsoft.com/en-us/azure/lighthouse/how-to/monitor-delegation-changes |
| Onboard customers to Azure Lighthouse with ARM | https://learn.microsoft.com/en-us/azure/lighthouse/how-to/onboard-customer |
| Delegate all subscriptions in a management group with policy | https://learn.microsoft.com/en-us/azure/lighthouse/how-to/onboard-management-group |
| Deploy Azure Policy across tenants with Lighthouse | https://learn.microsoft.com/en-us/azure/lighthouse/how-to/policy-at-scale |
| Remove Azure Lighthouse delegations and access | https://learn.microsoft.com/en-us/azure/lighthouse/how-to/remove-delegation |
| Update Azure Lighthouse delegations and role assignments | https://learn.microsoft.com/en-us/azure/lighthouse/how-to/update-delegation |
| Use Azure Lighthouse ARM templates and samples | https://learn.microsoft.com/en-us/azure/lighthouse/samples/ |
| Use built-in Azure Policy definitions for Lighthouse | https://learn.microsoft.com/en-us/azure/lighthouse/samples/policy-reference |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate Azure Lighthouse with Azure Arc at scale | https://learn.microsoft.com/en-us/azure/lighthouse/how-to/manage-hybrid-infrastructure-arc |
| Manage Microsoft Sentinel workspaces at scale with Lighthouse | https://learn.microsoft.com/en-us/azure/lighthouse/how-to/manage-sentinel-workspaces |
| Manage Azure Migrate projects across tenants with Lighthouse | https://learn.microsoft.com/en-us/azure/lighthouse/how-to/migration-at-scale |
| Use Azure Monitor Logs across tenants via Lighthouse | https://learn.microsoft.com/en-us/azure/lighthouse/how-to/monitor-at-scale |

### Deployment
| Topic | URL |
|-------|-----|
| Publish Azure Lighthouse Managed Service offers | https://learn.microsoft.com/en-us/azure/lighthouse/how-to/publish-managed-services-offers |