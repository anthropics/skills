---
name: azure-sre-agent
description: Expert knowledge for Azure Sre Agent development including troubleshooting, best practices, decision making, security, configuration, integrations & coding patterns, and deployment. Use when wiring SRE Agent to Azure DevOps/GitHub, Log Analytics/App Insights, AKS Java workloads, or Key Vault, and other Azure Sre Agent related development tasks. Not for Azure Monitor (use azure-monitor), Azure Reliability (use azure-reliability), Azure Resiliency (use azure-resiliency), Azure Service Health (use azure-service-health).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-21"
  generator: "docs2skills/1.0.0"
---
# Azure Sre Agent Skill

This skill provides expert guidance for Azure Sre Agent. Covers troubleshooting, best practices, decision making, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L35-L42 | Diagnosing and fixing SRE Agent issues: querying telemetry with KQL, filing Azure support tickets, resolving deployment/operation failures, and debugging Java performance on AKS. |
| Best Practices | L43-L47 | Best practices for integrating Azure Monitor, Application Insights, and related observability tools with SRE Agent to collect, analyze, and act on telemetry and alerts. |
| Decision Making | L48-L55 | Guidance on when to run deep investigations, choosing Log Analytics vs App Insights connectors, estimating/controlling SRE Agent costs, and selecting supported Azure regions. |
| Security | L56-L72 | Securing SRE Agent identities, permissions, RBAC, approvals, network/VNet access, firewalls, and secure connections to Key Vault, ADO, and GitHub (including BYO GitHub App). |
| Configuration | L73-L89 | Configuring SRE Agent behavior: code interpreter, tools/skills, subagents, connectors, network, governance hooks, incident plans, IDE/MCP, and GitHub/knowledge source integrations. |
| Integrations & Coding Patterns | L90-L108 | Integrating SRE Agent with Azure DevOps, GitHub, observability and incident tools, defining REST/Kusto/Python tools, cross-tenant access, and secure connector/MCP configurations |
| Deployment | L109-L112 | How to deploy Azure SRE Agent using Infrastructure-as-Code templates, including required resources, parameters, and environment configuration steps. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Query Azure SRE Agent telemetry and actions with KQL | https://learn.microsoft.com/en-us/azure/sre-agent/audit-agent-actions |
| File Azure support requests from SRE Agent troubleshooting | https://learn.microsoft.com/en-us/azure/sre-agent/create-support-request |
| Troubleshoot Azure SRE Agent deployment and operations | https://learn.microsoft.com/en-us/azure/sre-agent/faq-troubleshooting |
| Diagnose Java performance issues on AKS with SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/troubleshoot-java-aks |

### Best Practices
| Topic | URL |
|-------|-----|
| Use Azure observability tools with SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/diagnose-azure-observability |

### Decision Making
| Topic | URL |
|-------|-----|
| Decide when to use deep investigation in Azure SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/deep-investigation |
| Decide when to use Log Analytics and App Insights connectors in SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/log-analytics-app-insights |
| Estimate and control Azure SRE Agent costs | https://learn.microsoft.com/en-us/azure/sre-agent/pricing-billing |
| Select supported Azure regions for SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/supported-regions |

### Security
| Topic | URL |
|-------|-----|
| Understand Azure SRE Agent identities and authentication | https://learn.microsoft.com/en-us/azure/sre-agent/agent-identity |
| Allow-list SRE Agent outbound IPs in Key Vault firewall | https://learn.microsoft.com/en-us/azure/sre-agent/allow-list-key-vault-firewall |
| Configure secure network controls for Azure SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/configure-network-controls |
| Configure managed identity access to ADO repos in SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/connect-ado-repo-managed-identity |
| Connect GitHub Enterprise Cloud to SRE Agent securely | https://learn.microsoft.com/en-us/azure/sre-agent/connect-github-enterprise-cloud |
| Manage Azure SRE Agent permissions and resource access | https://learn.microsoft.com/en-us/azure/sre-agent/manage-permissions |
| Configure VNet network integration for Azure SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/network-integration |
| Configure Azure SRE Agent permissions and RBAC access | https://learn.microsoft.com/en-us/azure/sre-agent/permissions |
| Configure run modes and approvals in Azure SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/run-modes |
| Securely configure BYO GitHub App for SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/setup-github-byo-app |
| Understand subscription visibility and permissions in Azure SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/subscription-permission-visibility |
| Define tool access policies for Azure SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/tool-access-policies |
| Configure Azure SRE Agent roles and permissions | https://learn.microsoft.com/en-us/azure/sre-agent/user-roles |

### Configuration
| Topic | URL |
|-------|-----|
| Use SRE Agent code interpreter for Python and shell | https://learn.microsoft.com/en-us/azure/sre-agent/code-interpreter |
| Connect knowledge sources to Azure SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/connect-knowledge |
| Create and manage governance hooks in Azure SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/create-manage-hooks-ui |
| Create custom skills with tools and files in Azure SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/create-skill |
| Configure specialized subagents in Azure SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/create-subagent |
| Configure incident response plans in Azure SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/incident-response-plans |
| Configure managed connectors for Azure SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/managed-connectors |
| Configure network and firewall requirements for SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/network-requirements |
| Configure GitHub OAuth or PAT connector for SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/setup-github-connector |
| Configure managed connectors and governance in SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/setup-managed-connector |
| Configure Azure SRE Agent MCP server for IDE clients | https://learn.microsoft.com/en-us/azure/sre-agent/setup-mcp-server |
| Configure agent hooks via REST API in Azure SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/tutorial-agent-hooks |
| Enable and use Code Interpreter in Azure SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/use-code-interpreter |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Connect Azure DevOps to Azure SRE Agent for code and work items | https://learn.microsoft.com/en-us/azure/sre-agent/ado-connector |
| Use Azure SRE Agent REST APIs securely | https://learn.microsoft.com/en-us/azure/sre-agent/api-reference |
| Connect Azure DevOps wikis as knowledge sources for SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/azure-devops-wiki-knowledge |
| Connect Azure DevOps wiki as SRE Agent knowledge source | https://learn.microsoft.com/en-us/azure/sre-agent/connect-devops-wiki |
| Use connectors to extend Azure SRE Agent capabilities | https://learn.microsoft.com/en-us/azure/sre-agent/connectors |
| Build and deploy a Python SLA calculator tool in SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/create-python-tool |
| Enable cross-tenant Azure DevOps access for SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/cross-account-ado-oauth |
| Integrate external observability tools with Azure SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/diagnose-observability |
| Integrate GitHub with Azure SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/github-connector |
| Connect incident platforms to Azure SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/incident-platforms |
| Define Kusto tools to run deterministic KQL in SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/kusto-tools |
| Operate Azure SRE Agent via MCP server integrations | https://learn.microsoft.com/en-us/azure/sre-agent/mcp-server |
| Integrate PagerDuty incidents with Azure SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/pagerduty-incidents |
| Create and configure Python tools for Azure SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/python-code-execution |
| Configure ServiceNow incident indexing for Azure SRE Agent | https://learn.microsoft.com/en-us/azure/sre-agent/setup-servicenow-indexing |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy Azure SRE Agent with IaC templates | https://learn.microsoft.com/en-us/azure/sre-agent/deploy-iac |