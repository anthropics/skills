---
name: azure-blueprints
description: Expert knowledge for Azure Blueprints development including troubleshooting, decision making, security, configuration, integrations & coding patterns, and deployment. Use when migrating off Blueprints, mapping to PBMM/ISO/SWIFT, automating via CLI/PowerShell/REST, or fixing deployment errors, and other Azure Blueprints related development tasks. Not for Azure Policy (use azure-policy), Azure Resource Manager (use azure-resource-manager), Azure Resource Graph (use azure-resource-graph), Azure Portal (use azure-portal).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Blueprints Skill

This skill provides expert guidance for Azure Blueprints. Covers troubleshooting, decision making, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L34-L38 | Diagnosing and fixing common Azure Blueprints deployment and assignment errors, including policy, role assignment, and resource lock issues, with step-by-step troubleshooting guidance. |
| Decision Making | L39-L44 | Guidance on Azure Blueprints retirement timelines, planning and executing migrations, and answers to common questions about moving off Blueprints. |
| Security | L45-L60 | Security-focused deployment stages, resource locks, operator roles, and using/mapping Azure Blueprints for compliance frameworks like PBMM, ISM PROTECTED, ISO 27001, SWIFT CSP, and UK OFFICIAL/NHS. |
| Configuration | L61-L72 | Configuring and deploying Azure Blueprints (including security/ISO/CAF/SWIFT samples), using blueprint functions, and importing/exporting blueprints via PowerShell. |
| Integrations & Coding Patterns | L73-L79 | Automating Azure Blueprints as code using CLI, PowerShell, and REST: create, import/export, and manage blueprint definitions and assignments programmatically. |
| Deployment | L80-L85 | Controlling blueprint artifact deployment order, migrating blueprints to template specs/deployment stacks, and deploying the CAF Foundation blueprint with parameters. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot common Azure Blueprints errors | https://learn.microsoft.com/en-us/azure/governance/blueprints/troubleshoot/general |

### Decision Making
| Topic | URL |
|-------|-----|
| Plan migration off Azure Blueprints with timelines | https://learn.microsoft.com/en-us/azure/governance/blueprints/blueprint-retirement |
| Answer migration questions for Blueprints retirement | https://learn.microsoft.com/en-us/azure/governance/blueprints/blueprint-retirement-faq |

### Security
| Topic | URL |
|-------|-----|
| Understand security-related stages of Azure Blueprint deployment | https://learn.microsoft.com/en-us/azure/governance/blueprints/concepts/deployment-stages |
| Configure resource locking behavior in Azure Blueprints | https://learn.microsoft.com/en-us/azure/governance/blueprints/concepts/resource-locking |
| Configure Azure Blueprint Operator role environment | https://learn.microsoft.com/en-us/azure/governance/blueprints/how-to/configure-for-blueprint-operator |
| Use Canada Federal PBMM blueprint for governance controls | https://learn.microsoft.com/en-us/azure/governance/blueprints/samples/canada-federal-pbmm |
| Use ISM PROTECTED blueprint for Australian compliance | https://learn.microsoft.com/en-us/azure/governance/blueprints/samples/ism-protected/ |
| Map ISM PROTECTED controls to Azure Policy | https://learn.microsoft.com/en-us/azure/governance/blueprints/samples/ism-protected/control-mapping |
| Map ISO 27001 ASE/SQL controls to Policy and RBAC | https://learn.microsoft.com/en-us/azure/governance/blueprints/samples/iso27001-ase-sql-workload/control-mapping |
| Map ISO 27001 shared services controls to Azure Policy | https://learn.microsoft.com/en-us/azure/governance/blueprints/samples/iso27001-shared/control-mapping |
| Use SWIFT CSP-CSCF 2020 blueprint for Azure compliance | https://learn.microsoft.com/en-us/azure/governance/blueprints/samples/swift-2020/ |
| Map SWIFT CSP-CSCF 2020 controls to Azure Policy | https://learn.microsoft.com/en-us/azure/governance/blueprints/samples/swift-2020/control-mapping |
| Use UK OFFICIAL and NHS blueprint for Azure governance | https://learn.microsoft.com/en-us/azure/governance/blueprints/samples/ukofficial-uknhs |
| Protect Azure Blueprint-deployed resources with locks | https://learn.microsoft.com/en-us/azure/governance/blueprints/tutorials/protect-new-resources |

### Configuration
| Topic | URL |
|-------|-----|
| Import and export Azure Blueprints with PowerShell | https://learn.microsoft.com/en-us/azure/governance/blueprints/how-to/import-export-ps |
| Use Azure Blueprint functions in definitions and artifacts | https://learn.microsoft.com/en-us/azure/governance/blueprints/reference/blueprint-functions |
| Configure and deploy Azure Security Benchmark blueprint sample | https://learn.microsoft.com/en-us/azure/governance/blueprints/samples/azure-security-benchmark-foundation/deploy |
| Configure and deploy CAF migration landing zone blueprint | https://learn.microsoft.com/en-us/azure/governance/blueprints/samples/caf-migrate-landing-zone/deploy |
| Configure and deploy ISM PROTECTED blueprint sample | https://learn.microsoft.com/en-us/azure/governance/blueprints/samples/ism-protected/deploy |
| Configure and deploy ISO 27001 ASE/SQL workload blueprint | https://learn.microsoft.com/en-us/azure/governance/blueprints/samples/iso27001-ase-sql-workload/deploy |
| Configure and deploy ISO 27001 shared services blueprint | https://learn.microsoft.com/en-us/azure/governance/blueprints/samples/iso27001-shared/deploy |
| Configure and deploy SWIFT CSP-CSCF 2020 blueprint | https://learn.microsoft.com/en-us/azure/governance/blueprints/samples/swift-2020/deploy |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Create Azure Blueprints using Azure CLI commands | https://learn.microsoft.com/en-us/azure/governance/blueprints/create-blueprint-azurecli |
| Create Azure Blueprints via REST API requests | https://learn.microsoft.com/en-us/azure/governance/blueprints/create-blueprint-rest-api |
| Manage Azure Blueprint assignments with Az.Blueprint PowerShell | https://learn.microsoft.com/en-us/azure/governance/blueprints/how-to/manage-assignments-ps |

### Deployment
| Topic | URL |
|-------|-----|
| Control Azure Blueprint artifact deployment order | https://learn.microsoft.com/en-us/azure/governance/blueprints/concepts/sequencing-order |
| Migrate Azure Blueprints to template specs and deployment stacks | https://learn.microsoft.com/en-us/azure/governance/blueprints/migrate-to-template-specs |
| Deploy CAF Foundation blueprint with parameters | https://learn.microsoft.com/en-us/azure/governance/blueprints/samples/caf-foundation/deploy |