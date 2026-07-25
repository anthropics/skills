---
name: azure-partner-solutions
description: Expert knowledge for Azure Partner Solutions development including troubleshooting, decision making, architecture & design patterns, security, configuration, and integrations & coding patterns. Use when using Service Connector to Confluent/MongoDB/Neon, Dynatrace/Datadog/Elastic/New Relic on Azure, or Palo Alto Cloud NGFW with App Gateway, and other Azure Partner Solutions related development tasks. Not for Azure Industry (use azure-industry), Azure Managed Applications (use azure-managed-applications), Azure Lighthouse (use azure-lighthouse), Azure Oracle (use azure-oracle).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Partner Solutions Skill

This skill provides expert guidance for Azure Partner Solutions. Covers troubleshooting, decision making, architecture & design patterns, security, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L34-L45 | Diagnosing and fixing setup, integration, and runtime issues for Confluent Kafka/Flink, Datadog, Dynatrace, Elastic Cloud, and New Relic (incl. log forwarding) on Azure |
| Decision Making | L46-L50 | Guidance on evaluating Dynatrace APM on Azure, starting a free trial from the portal/Marketplace, setup steps, and considerations before adopting it for monitoring. |
| Architecture & Design Patterns | L51-L55 | Architectural guidance for integrating Palo Alto Cloud NGFW with Azure Application Gateway, including network design, routing, security, and deployment patterns. |
| Security | L56-L61 | Managing security for Azure partner services, including Confluent Cloud RBAC in Azure portal and configuring SSO/access control for Informatica IDMC Azure resources. |
| Configuration | L62-L76 | Configuring and managing Azure-integrated partner resources (Datadog, Dynatrace, Elastic, MongoDB Atlas, New Relic, NGINXaaS, etc.), including prerequisites, settings, and integrations. |
| Integrations & Coding Patterns | L77-L81 | Patterns and setup guides for connecting Azure services to external data platforms (Confluent Cloud, MongoDB Atlas, Neon Postgres) using Service Connector and Foundry Agents. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Confluent Cloud Kafka and Flink on Azure | https://learn.microsoft.com/en-us/azure/partner-solutions/apache-kafka-confluent-cloud/troubleshoot |
| Diagnose and resolve Datadog on Azure issues | https://learn.microsoft.com/en-us/azure/partner-solutions/datadog/faq |
| Diagnose and fix Datadog Azure integration issues | https://learn.microsoft.com/en-us/azure/partner-solutions/datadog/troubleshoot |
| Troubleshoot Azure Native Dynatrace Service setup | https://learn.microsoft.com/en-us/azure/partner-solutions/dynatrace/faq |
| Troubleshoot Azure Native Dynatrace Service problems | https://learn.microsoft.com/en-us/azure/partner-solutions/dynatrace/troubleshoot |
| Troubleshoot Elastic Cloud integration on Azure | https://learn.microsoft.com/en-us/azure/partner-solutions/elastic/troubleshoot |
| Troubleshoot Azure Native New Relic Service issues | https://learn.microsoft.com/en-us/azure/partner-solutions/new-relic/troubleshoot |
| Diagnose New Relic log forwarding with Azure Copilot | https://learn.microsoft.com/en-us/azure/partner-solutions/new-relic/troubleshoot-logs-copilot |

### Decision Making
| Topic | URL |
|-------|-----|
| Evaluate and start Dynatrace free trial on Azure | https://learn.microsoft.com/en-us/azure/partner-solutions/dynatrace/free-trial |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Deploy Cloud NGFW behind Azure Application Gateway | https://learn.microsoft.com/en-us/azure/partner-solutions/palo-alto/application-gateway |

### Security
| Topic | URL |
|-------|-----|
| Manage Confluent Cloud access control in Azure portal | https://learn.microsoft.com/en-us/azure/partner-solutions/apache-kafka-confluent-cloud/manage-access |
| Configure SSO and manage Informatica IDMC Azure resource | https://learn.microsoft.com/en-us/azure/partner-solutions/informatica/manage |

### Configuration
| Topic | URL |
|-------|-----|
| Manage configuration settings for Dell PowerScale in Azure | https://learn.microsoft.com/en-us/azure/partner-solutions/dell/manage |
| Configure Azure and Entra prerequisites for Dynatrace | https://learn.microsoft.com/en-us/azure/partner-solutions/dynatrace/configure-prerequisites |
| Manage Dynatrace Azure resource settings and integrations | https://learn.microsoft.com/en-us/azure/partner-solutions/dynatrace/manage |
| Manage Informatica serverless runtime environments in Azure | https://learn.microsoft.com/en-us/azure/partner-solutions/informatica/manage-serverless |
| Manage LambdaTest HyperExecute resource settings in Azure | https://learn.microsoft.com/en-us/azure/partner-solutions/lambda-test/manage |
| Manage MongoDB Atlas Azure resource configuration | https://learn.microsoft.com/en-us/azure/partner-solutions/mongo-db/manage |
| Manage configuration for Azure Native New Relic Service | https://learn.microsoft.com/en-us/azure/partner-solutions/new-relic/manage |
| Configure and manage NGINXaaS resources in Azure | https://learn.microsoft.com/en-us/azure/partner-solutions/nginx/manage |
| Configure Cloud NGFW by Palo Alto Networks in Azure | https://learn.microsoft.com/en-us/azure/partner-solutions/palo-alto/manage |
| Manage Azure Native Pure Storage Cloud settings | https://learn.microsoft.com/en-us/azure/partner-solutions/pure-storage/manage |
| Configure and manage Azure Native Qumulo settings | https://learn.microsoft.com/en-us/azure/partner-solutions/qumulo/manage |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Connect Confluent Cloud to Azure compute with Service Connector | https://learn.microsoft.com/en-us/azure/partner-solutions/apache-kafka-confluent-cloud/add-connectors |
| Integrate Microsoft Foundry Agents with MongoDB Atlas | https://learn.microsoft.com/en-us/azure/partner-solutions/mongo-db/connect-foundry-agents |