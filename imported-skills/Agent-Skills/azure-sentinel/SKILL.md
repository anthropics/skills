---
name: azure-sentinel
description: Expert knowledge for Azure Sentinel development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when configuring data connectors, KQL/ASIM analytics, playbooks/Logic Apps, UEBA/Fusion, or data lake jobs, and other Azure Sentinel related development tasks. Not for Azure Defender For Cloud (use azure-defender-for-cloud), Azure Security (use azure-security), Azure Monitor (use azure-monitor), Azure Network Watcher (use azure-network-watcher).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Sentinel Skill

This skill provides expert guidance for Azure Sentinel. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L53 | Diagnosing and fixing Sentinel issues with data connectors (AWS, Azure Blob, Syslog/CEF, SAP), KQL/jobs, MCP tools, notebooks, and analytics/automation rule health and execution. |
| Best Practices | L54-L84 | Best practices for designing, tuning, and operating Microsoft Sentinel: automation, playbooks, detections, anomalies, watchlists, incident tasks, SOC processes, ML, UEBA, and Security Copilot. |
| Decision Making | L85-L123 | Guidance for SIEM/SOAR migration to Sentinel, cost/pricing decisions, data tiers and connectors, and choosing between Sentinel/Defender features and automation options. |
| Architecture & Design Patterns | L124-L135 | Designing Sentinel architectures: BCDR, multi-workspace/tenant layouts, coexisting with other SIEMs, SAP-specific patterns, and building/publishing ISV solution components. |
| Limits & Quotas | L136-L148 | Limits, quotas, and constraints for Sentinel features (NRT rules, data lake, MCP usage, watchlists, search jobs), regional availability, ASIM issues, and removal implications. |
| Security | L149-L165 | Securing Microsoft Sentinel: auth for playbooks, RBAC and roles, data encryption and residency, storage/network protections, and SAP/MSSP-specific security configurations. |
| Configuration | L166-L289 | Configuring Microsoft Sentinel: data connectors, ASIM schemas, analytics/automation rules, playbooks, UEBA/Fusion, data lake/KQL jobs, multi-tenant/SIEM solutions, and SAP/security content setup. |
| Integrations & Coding Patterns | L290-L343 | Integrating Sentinel with external services (AWS, Defender, Purview, TIPs), automating incidents via playbooks/Logic Apps, querying data lake/graphs, and using MCP/AI tools for custom connectors and analytics. |
| Deployment | L344-L360 | Deploying and publishing Sentinel solutions, rules, automation, and SAP/Dynamics/Power Platform integrations, plus CI/CD, ARM templates, and SAP connector/agent migration and updates. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot AWS S3 log ingestion connector in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/aws-s3-troubleshoot |
| Troubleshoot Microsoft Sentinel Azure Storage Blob connector issues | https://learn.microsoft.com/en-us/azure/sentinel/azure-storage-blob-connector-troubleshoot |
| Troubleshoot Syslog and CEF AMA connectors in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/cef-syslog-ama-troubleshooting |
| Troubleshoot KQL queries and jobs in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/datalake/kql-troubleshoot |
| Resolve common Jupyter notebook errors in Sentinel data lake | https://learn.microsoft.com/en-us/azure/sentinel/datalake/notebooks-troubleshooting |
| Best practices and troubleshooting Sentinel MCP tools | https://learn.microsoft.com/en-us/azure/sentinel/datalake/troubleshoot-sentinel-mcp |
| Troubleshoot Microsoft Sentinel solution ingestion and packaging | https://learn.microsoft.com/en-us/azure/sentinel/isv/troubleshoot-sentinel-solutions |
| Monitor and troubleshoot Sentinel analytics rule health | https://learn.microsoft.com/en-us/azure/sentinel/monitor-analytics-rule-integrity |
| Monitor and troubleshoot Sentinel automation health | https://learn.microsoft.com/en-us/azure/sentinel/monitor-automation-health |
| Monitor and troubleshoot Sentinel scheduled analytics rule execution | https://learn.microsoft.com/en-us/azure/sentinel/monitor-optimize-analytics-rule-execution |
| Monitor and troubleshoot Microsoft Sentinel SAP connectivity | https://learn.microsoft.com/en-us/azure/sentinel/monitor-sap-system-health |
| Troubleshoot Sentinel SAP data connector agent | https://learn.microsoft.com/en-us/azure/sentinel/sap/sap-deploy-troubleshoot |
| Troubleshoot Microsoft Sentinel analytics rule issues | https://learn.microsoft.com/en-us/azure/sentinel/troubleshoot-analytics-rules |

### Best Practices
| Topic | URL |
|-------|-----|
| Audit and track Microsoft Sentinel incident tasks | https://learn.microsoft.com/en-us/azure/sentinel/audit-track-tasks |
| Design Microsoft Sentinel automation rules for SOAR | https://learn.microsoft.com/en-us/azure/sentinel/automate-incident-handling-with-automation-rules |
| Apply recommended Microsoft Sentinel playbook templates and use cases | https://learn.microsoft.com/en-us/azure/sentinel/automation/playbook-recommendations |
| Use and customize Sentinel playbook templates | https://learn.microsoft.com/en-us/azure/sentinel/automation/use-playbook-templates |
| Apply best practices for Microsoft Sentinel workspaces | https://learn.microsoft.com/en-us/azure/sentinel/best-practices |
| Apply Sentinel-specific best practices for data collection | https://learn.microsoft.com/en-us/azure/sentinel/best-practices-data |
| Bring custom machine learning models into Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/bring-your-own-ml |
| Manage Sentinel detection lifecycle effectively | https://learn.microsoft.com/en-us/azure/sentinel/detection-lifecycle-management-recommendations |
| Apply detection tuning recommendations in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/detection-tuning |
| Use ASIM-based essential domain solutions in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/domain-based-essential-solutions |
| Handle false positives in Microsoft Sentinel detections | https://learn.microsoft.com/en-us/azure/sentinel/false-positives |
| Create custom hunting queries in Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/hunts-custom-queries |
| Standardize incident response with Sentinel tasks | https://learn.microsoft.com/en-us/azure/sentinel/incident-tasks |
| Handle data ingestion delay in Sentinel rules | https://learn.microsoft.com/en-us/azure/sentinel/ingestion-delay |
| Investigate Sentinel incidents using large dataset search | https://learn.microsoft.com/en-us/azure/sentinel/investigate-large-datasets |
| Use UEBA data to investigate Sentinel incidents | https://learn.microsoft.com/en-us/azure/sentinel/investigate-with-ueba |
| Apply quality guidelines for Sentinel solutions | https://learn.microsoft.com/en-us/azure/sentinel/isv/sentinel-solution-quality-guidance |
| Apply operational best practices for Microsoft Sentinel SOCs | https://learn.microsoft.com/en-us/azure/sentinel/ops-guide |
| Use Security Copilot effectively with Microsoft Sentinel data | https://learn.microsoft.com/en-us/azure/sentinel/sentinel-security-copilot |
| Manage deprecated Microsoft Sentinel solutions lifecycle | https://learn.microsoft.com/en-us/azure/sentinel/sentinel-solution-deprecation |
| Use customizable anomaly detection to find threats | https://learn.microsoft.com/en-us/azure/sentinel/soc-ml-anomalies |
| Apply SOC optimization recommendations in Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/soc-optimization/soc-optimization-access |
| Apply Microsoft Sentinel watchlists effectively | https://learn.microsoft.com/en-us/azure/sentinel/watchlists |
| Edit and manage Microsoft Sentinel watchlists safely | https://learn.microsoft.com/en-us/azure/sentinel/watchlists-manage |
| Build KQL queries and rules using watchlists | https://learn.microsoft.com/en-us/azure/sentinel/watchlists-queries |
| Manage and fine-tune anomaly detection rules | https://learn.microsoft.com/en-us/azure/sentinel/work-with-anomaly-rules |
| Manage incident tasks in Sentinel investigations | https://learn.microsoft.com/en-us/azure/sentinel/work-with-tasks |

### Decision Making
| Topic | URL |
|-------|-----|
| Plan and execute Sentinel migration from MMA to AMA | https://learn.microsoft.com/en-us/azure/sentinel/ama-migrate |
| Decide and migrate alert-trigger playbooks to automation rules | https://learn.microsoft.com/en-us/azure/sentinel/automation/migrate-playbooks-to-automation-rules |
| Decide when to use the Microsoft Sentinel data lake tier | https://learn.microsoft.com/en-us/azure/sentinel/basic-logs-use-cases |
| Plan and estimate Microsoft Sentinel billing costs | https://learn.microsoft.com/en-us/azure/sentinel/billing |
| Control and analyze Microsoft Sentinel billing costs | https://learn.microsoft.com/en-us/azure/sentinel/billing-monitor-costs |
| Choose and use Microsoft Sentinel prepurchase plans | https://learn.microsoft.com/en-us/azure/sentinel/billing-pre-purchase-plan |
| Reduce and optimize Microsoft Sentinel costs | https://learn.microsoft.com/en-us/azure/sentinel/billing-reduce-costs |
| Choose correct Sentinel connector for Cisco firewalls | https://learn.microsoft.com/en-us/azure/sentinel/cisco-ftd-firewall |
| Choose between Sentinel analytics rules and Defender custom detections | https://learn.microsoft.com/en-us/azure/sentinel/compare-analytics-rules-custom-detections |
| Assess Sentinel connector support across clouds | https://learn.microsoft.com/en-us/azure/sentinel/data-type-cloud-support |
| Choose between KQL jobs, summary rules, and search jobs | https://learn.microsoft.com/en-us/azure/sentinel/datalake/kql-jobs-summary-rules-search-jobs |
| Choose which logs to ingest into Sentinel data lake | https://learn.microsoft.com/en-us/azure/sentinel/datalake/sentinel-lake-log-ingestion-guidance |
| Enroll Sentinel workspaces in simplified pricing tiers | https://learn.microsoft.com/en-us/azure/sentinel/enroll-simplified-pricing-tier |
| Choose Microsoft Sentinel log retention tiers | https://learn.microsoft.com/en-us/azure/sentinel/log-plans |
| Plan Sentinel data tiers and retention for cost optimization | https://learn.microsoft.com/en-us/azure/sentinel/manage-data-overview |
| Determine Defender XDR data type support across GCC clouds in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/microsoft-365-defender-cloud-support |
| Decide how to integrate Microsoft Defender XDR with Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/microsoft-365-defender-sentinel-integration |
| Plan Microsoft Sentinel use in Microsoft Defender portal | https://learn.microsoft.com/en-us/azure/sentinel/microsoft-sentinel-defender-portal |
| Plan migration from legacy SIEM to Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/migration |
| Migrate ArcSight SOAR automation to Sentinel playbooks | https://learn.microsoft.com/en-us/azure/sentinel/migration-arcsight-automation |
| Migrate ArcSight detection rules to Sentinel analytics | https://learn.microsoft.com/en-us/azure/sentinel/migration-arcsight-detection-rules |
| Export ArcSight historical data for Sentinel migration | https://learn.microsoft.com/en-us/azure/sentinel/migration-arcsight-historical-data |
| Choose Sentinel target platform for historical data | https://learn.microsoft.com/en-us/azure/sentinel/migration-ingestion-target-platform |
| Select data ingestion tools for Sentinel migration targets | https://learn.microsoft.com/en-us/azure/sentinel/migration-ingestion-tool |
| Migrate QRadar SOAR automation to Sentinel playbooks | https://learn.microsoft.com/en-us/azure/sentinel/migration-qradar-automation |
| Migrate QRadar detection rules to Sentinel analytics | https://learn.microsoft.com/en-us/azure/sentinel/migration-qradar-detection-rules |
| Export QRadar data via REST API for Sentinel migration | https://learn.microsoft.com/en-us/azure/sentinel/migration-qradar-historical-data |
| Update SOC and analyst processes for Sentinel migration | https://learn.microsoft.com/en-us/azure/sentinel/migration-security-operations-center-processes |
| Migrate Splunk SOAR automation to Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/migration-splunk-automation |
| Migrate Splunk detection rules to Sentinel analytics | https://learn.microsoft.com/en-us/azure/sentinel/migration-splunk-detection-rules |
| Export Splunk historical data for Sentinel migration | https://learn.microsoft.com/en-us/azure/sentinel/migration-splunk-historical-data |
| Transition Sentinel operations from Azure to Defender portal | https://learn.microsoft.com/en-us/azure/sentinel/move-to-defender |
| Prioritize Microsoft Sentinel data connectors strategically | https://learn.microsoft.com/en-us/azure/sentinel/prioritize-data-connectors |
| Use Microsoft Sentinel SIEM migration recommendations | https://learn.microsoft.com/en-us/azure/sentinel/siem-migration |
| Use Sentinel SOC optimization reference recommendations | https://learn.microsoft.com/en-us/azure/sentinel/soc-optimization/soc-optimization-reference |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design BCDR architecture for Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/business-continuity-disaster-recovery |
| Deploy Sentinel alongside an existing SIEM | https://learn.microsoft.com/en-us/azure/sentinel/deploy-side-by-side |
| Design Sentinel across multiple workspaces and tenants | https://learn.microsoft.com/en-us/azure/sentinel/extend-sentinel-across-workspaces-tenants |
| Architect Microsoft Sentinel solution components and patterns | https://learn.microsoft.com/en-us/azure/sentinel/isv/partner-integrations |
| Design and publish Microsoft Sentinel ISV solutions | https://learn.microsoft.com/en-us/azure/sentinel/isv/sentinel-integration-guide |
| Plan multi-workspace and multi-tenant Sentinel layouts | https://learn.microsoft.com/en-us/azure/sentinel/prepare-multiple-workspaces |
| Choose Microsoft Sentinel workspace designs by scenario | https://learn.microsoft.com/en-us/azure/sentinel/sample-workspace-designs |
| Design multi-workspace architecture for Sentinel SAP | https://learn.microsoft.com/en-us/azure/sentinel/sap/cross-workspace |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Configure and understand Sentinel NRT rule limits | https://learn.microsoft.com/en-us/azure/sentinel/create-nrt-rules |
| Microsoft Sentinel data lake service limits reference | https://learn.microsoft.com/en-us/azure/sentinel/datalake/sentinel-lake-service-limits |
| Microsoft Sentinel MCP pricing and usage limits | https://learn.microsoft.com/en-us/azure/sentinel/datalake/sentinel-mcp-billing |
| Check Sentinel feature availability by Azure cloud | https://learn.microsoft.com/en-us/azure/sentinel/feature-availability |
| Understand ASIM known issues and limitations in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/normalization-known-issues |
| Understand implications of removing Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/offboard-implications |
| Run Sentinel search jobs across large datasets | https://learn.microsoft.com/en-us/azure/sentinel/search-jobs |
| Review Microsoft Sentinel service limits and quotas | https://learn.microsoft.com/en-us/azure/sentinel/sentinel-service-limits |
| Create Microsoft Sentinel watchlists with size limits | https://learn.microsoft.com/en-us/azure/sentinel/watchlists-create |

### Security
| Topic | URL |
|-------|-----|
| Configure secure authentication for Sentinel playbooks | https://learn.microsoft.com/en-us/azure/sentinel/automation/authenticate-playbooks-to-sentinel |
| Define access restriction policies for Sentinel playbooks | https://learn.microsoft.com/en-us/azure/sentinel/automation/define-playbook-access-restrictions |
| Configure customer-managed keys for Sentinel data encryption | https://learn.microsoft.com/en-us/azure/sentinel/customer-managed-keys |
| Configure roles and prerequisites for Sentinel data lake | https://learn.microsoft.com/en-us/azure/sentinel/datalake/sentinel-lake-onboarding |
| Secure Sentinel Azure Storage connectors with NSP | https://learn.microsoft.com/en-us/azure/sentinel/enable-storage-network-security |
| Understand Sentinel geographic availability and data residency | https://learn.microsoft.com/en-us/azure/sentinel/geographical-availability-data-residency |
| Secure access to Sentinel workbooks with RBAC | https://learn.microsoft.com/en-us/azure/sentinel/monitor-your-data |
| Protect MSSP intellectual property in Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/mssp-protect-intellectual-property |
| Configure resource-context RBAC for Sentinel data access | https://learn.microsoft.com/en-us/azure/sentinel/resource-context-rbac |
| Configure Microsoft Sentinel roles and permissions | https://learn.microsoft.com/en-us/azure/sentinel/roles |
| Prepare SAP system security for Sentinel connector | https://learn.microsoft.com/en-us/azure/sentinel/sap/preparing-sap |
| Assign required ABAP authorizations for Sentinel SAP | https://learn.microsoft.com/en-us/azure/sentinel/sap/required-abap-authorizations |
| Use Microsoft Sentinel built-in security content for SAP | https://learn.microsoft.com/en-us/azure/sentinel/sap/sap-solution-security-content |

### Configuration
| Topic | URL |
|-------|-----|
| Add advanced condition groups to Sentinel automation rules | https://learn.microsoft.com/en-us/azure/sentinel/add-advanced-conditions-to-automation-rules |
| Understand anomaly types detected by Sentinel ML engine | https://learn.microsoft.com/en-us/azure/sentinel/anomalies-reference |
| Create Data Collection Rules for Sentinel using API examples | https://learn.microsoft.com/en-us/azure/sentinel/api-dcr-reference |
| Configure and query Microsoft Sentinel audit logs | https://learn.microsoft.com/en-us/azure/sentinel/audit-sentinel-data |
| Use SentinelAudit tables for user activity auditing | https://learn.microsoft.com/en-us/azure/sentinel/audit-table-reference |
| Configure Microsoft Sentinel automation rule properties and conditions | https://learn.microsoft.com/en-us/azure/sentinel/automation-rule-reference |
| Configure Sentinel playbooks for automated threat response | https://learn.microsoft.com/en-us/azure/sentinel/automation/automate-responses-with-playbooks |
| Create and manage Microsoft Sentinel playbooks | https://learn.microsoft.com/en-us/azure/sentinel/automation/create-playbooks |
| Automate and run Sentinel playbooks on incidents | https://learn.microsoft.com/en-us/azure/sentinel/automation/run-playbooks |
| Map CEF keys to Microsoft Sentinel CommonSecurityLog fields | https://learn.microsoft.com/en-us/azure/sentinel/cef-name-mapping |
| Understand Syslog and CEF AMA connectors for Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/cef-syslog-ama-overview |
| Configure Security Events connector for anomalous RDP detection | https://learn.microsoft.com/en-us/azure/sentinel/configure-connector-login-detection |
| Configure Microsoft Sentinel security content components | https://learn.microsoft.com/en-us/azure/sentinel/configure-content |
| Install and configure Microsoft Sentinel data connectors | https://learn.microsoft.com/en-us/azure/sentinel/configure-data-connector |
| Configure data retention and archive in Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/configure-data-retention-archive |
| Configure ingestion-time data transformation for Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/configure-data-transformation |
| Configure Fusion multistage attack detection rules | https://learn.microsoft.com/en-us/azure/sentinel/configure-fusion-rules |
| Configure Sentinel connectors for Azure and Microsoft services | https://learn.microsoft.com/en-us/azure/sentinel/connect-azure-windows-microsoft-services |
| Enable Defender Threat Intelligence connector in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/connect-mdti-data-connector |
| Configure scheduled analytics rules from templates | https://learn.microsoft.com/en-us/azure/sentinel/create-analytics-rule-from-template |
| Create and tune scheduled analytics rules in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/create-analytics-rules |
| Configure incident creation from connected alerts | https://learn.microsoft.com/en-us/azure/sentinel/create-incidents-from-alerts |
| Configure Microsoft Sentinel automation rules for response | https://learn.microsoft.com/en-us/azure/sentinel/create-manage-use-automation-rules |
| Configure Sentinel automation rules for incident tasks | https://learn.microsoft.com/en-us/azure/sentinel/create-tasks-automation-rule |
| Customize Sentinel alert names, severity, and tactics | https://learn.microsoft.com/en-us/azure/sentinel/customize-alert-details |
| Add custom activities to Sentinel entity timelines | https://learn.microsoft.com/en-us/azure/sentinel/customize-entity-activities |
| Configure Azure Storage Blob Codeless Connector Framework rules | https://learn.microsoft.com/en-us/azure/sentinel/data-connection-rules-reference-azure-storage |
| Configure GCP Codeless Connector Framework data connection rules | https://learn.microsoft.com/en-us/azure/sentinel/data-connection-rules-reference-gcp |
| Configure RestApiPoller data connector and rules JSON | https://learn.microsoft.com/en-us/azure/sentinel/data-connector-connection-rules-reference |
| Define Codeless Connector Framework data connector UI JSON | https://learn.microsoft.com/en-us/azure/sentinel/data-connector-ui-definitions-reference |
| Use asset data table mappings in Sentinel data lake | https://learn.microsoft.com/en-us/azure/sentinel/datalake/asset-data-tables |
| Access and search Sentinel data lake audit logs | https://learn.microsoft.com/en-us/azure/sentinel/datalake/auditing-lake-activities |
| Build deep-link URLs for Sentinel graph queries | https://learn.microsoft.com/en-us/azure/sentinel/datalake/create-deep-links-graph-queries |
| Configure federated data connectors for Sentinel data lake | https://learn.microsoft.com/en-us/azure/sentinel/datalake/data-federation-setup |
| Create and schedule KQL jobs in Sentinel data lake | https://learn.microsoft.com/en-us/azure/sentinel/datalake/kql-jobs |
| Configure KQL jobs in Sentinel data lake | https://learn.microsoft.com/en-us/azure/sentinel/datalake/kql-jobs |
| Run and manage KQL queries in Sentinel data lake | https://learn.microsoft.com/en-us/azure/sentinel/datalake/kql-queries |
| Create and configure custom Sentinel MCP tools from KQL | https://learn.microsoft.com/en-us/azure/sentinel/datalake/sentinel-mcp-create-custom-tool |
| Configure Microsoft Sentinel MCP server for AI queries | https://learn.microsoft.com/en-us/azure/sentinel/datalake/sentinel-mcp-get-started |
| Query and use federated data sources in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/datalake/using-data-federation |
| Build Sentinel workbooks using data lake queries | https://learn.microsoft.com/en-us/azure/sentinel/datalake/workbooks-for-data-lake |
| Use DNS AMA connector fields and normalization schema in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/dns-ama-fields |
| Enable auditing and health monitoring tables in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/enable-monitoring |
| Reference Microsoft Sentinel entity types and identifiers | https://learn.microsoft.com/en-us/azure/sentinel/entities-reference |
| Understand and use Sentinel UEBA behavior layer | https://learn.microsoft.com/en-us/azure/sentinel/entity-behaviors-layer |
| Review Fusion-detected multistage attack scenarios in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/fusion-scenario-reference |
| Configure and interpret Sentinel auditing and health monitoring | https://learn.microsoft.com/en-us/azure/sentinel/health-audit |
| Use SentinelHealth table for SIEM health monitoring | https://learn.microsoft.com/en-us/azure/sentinel/health-table-reference |
| Configure push-based codeless connectors for Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/isv/create-push-codeless-connector |
| Configure and manage Sentinel platform solution components | https://learn.microsoft.com/en-us/azure/sentinel/isv/manage-platform-solutions |
| Configure analytics rules for Sentinel solutions | https://learn.microsoft.com/en-us/azure/sentinel/isv/sentinel-analytic-rules-creation |
| Create and publish Sentinel playbooks for solutions | https://learn.microsoft.com/en-us/azure/sentinel/isv/sentinel-playbook-creation |
| Set up prerequisites for Sentinel SIEM solutions | https://learn.microsoft.com/en-us/azure/sentinel/isv/solution-setup-essentials |
| Manage versions of Sentinel analytics rule templates | https://learn.microsoft.com/en-us/azure/sentinel/manage-analytics-rule-templates |
| Use incident metrics to manage SOC performance in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/manage-soc-with-incident-metrics |
| Configure Sentinel and Defender table retention and tiers | https://learn.microsoft.com/en-us/azure/sentinel/manage-table-tiers-retention |
| Map data fields to Sentinel entities in rules | https://learn.microsoft.com/en-us/azure/sentinel/map-data-fields-to-entities |
| Use Microsoft Purview Information Protection audit record types in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/microsoft-purview-record-types-activities |
| Convert SIEM dashboards to Sentinel Azure Workbooks | https://learn.microsoft.com/en-us/azure/sentinel/migration-convert-dashboards |
| Ingest historical data into selected Sentinel target platform | https://learn.microsoft.com/en-us/azure/sentinel/migration-export-ingest |
| Configure Sentinel deployment workbook to track migration | https://learn.microsoft.com/en-us/azure/sentinel/migration-track |
| Monitor Sentinel data connector health with SentinelHealth workbook | https://learn.microsoft.com/en-us/azure/sentinel/monitor-data-connector-health |
| Onboard and manage multiple tenants with Sentinel and Azure Lighthouse | https://learn.microsoft.com/en-us/azure/sentinel/multiple-tenants-service-providers |
| View and manage incidents across multiple Sentinel workspaces | https://learn.microsoft.com/en-us/azure/sentinel/multiple-workspace-view |
| Configure near-real-time analytics rules for fast detection | https://learn.microsoft.com/en-us/azure/sentinel/near-real-time-rules |
| Manage workspace-deployed ASIM parsers in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/normalization-about-workspace-parsers |
| Use ASIM common schema fields in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/normalization-common-fields |
| Develop and deploy ASIM parsers for Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/normalization-develop-parsers |
| Implement ASIM Application Entity schema in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/normalization-entity-application |
| Implement ASIM Device Entity schema in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/normalization-entity-device |
| Implement ASIM User Entity schema in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/normalization-entity-user |
| Manage ASIM parsers configuration in Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/normalization-manage-parsers |
| Convert Sentinel analytics rules to ASIM normalized data | https://learn.microsoft.com/en-us/azure/sentinel/normalization-modify-content |
| Map AI agent telemetry to Sentinel ASIM Agent schema | https://learn.microsoft.com/en-us/azure/sentinel/normalization-schema-agent |
| Use ASIM Alert Events normalization schema | https://learn.microsoft.com/en-us/azure/sentinel/normalization-schema-alert |
| Use ASIM Asset Entity schema in Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/normalization-schema-asset |
| Use ASIM Audit Events normalization schema | https://learn.microsoft.com/en-us/azure/sentinel/normalization-schema-audit |
| Use ASIM Authentication normalization schema | https://learn.microsoft.com/en-us/azure/sentinel/normalization-schema-authentication |
| Apply ASIM DHCP normalization schema in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/normalization-schema-dhcp |
| Use ASIM DNS normalization schema in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/normalization-schema-dns |
| Use ASIM File Event normalization schema | https://learn.microsoft.com/en-us/azure/sentinel/normalization-schema-file-event |
| Use Microsoft Sentinel ASIM network session schema fields | https://learn.microsoft.com/en-us/azure/sentinel/normalization-schema-network |
| Use Microsoft Sentinel ASIM process event schema fields | https://learn.microsoft.com/en-us/azure/sentinel/normalization-schema-process-event |
| Use Microsoft Sentinel ASIM registry event schema fields | https://learn.microsoft.com/en-us/azure/sentinel/normalization-schema-registry-event |
| Use Microsoft Sentinel user management normalization schema | https://learn.microsoft.com/en-us/azure/sentinel/normalization-schema-user-management |
| Use legacy Microsoft Sentinel network normalization schema v0.1 | https://learn.microsoft.com/en-us/azure/sentinel/normalization-schema-v1 |
| Use Microsoft Sentinel ASIM web session schema fields | https://learn.microsoft.com/en-us/azure/sentinel/normalization-schema-web |
| Configure Jupyter notebooks and MSTICPy for Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/notebook-get-started |
| Use advanced MSTICPy notebook configurations in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/notebooks-msticpy-advanced |
| Restore and manage archived Sentinel log data | https://learn.microsoft.com/en-us/azure/sentinel/restore |
| Configure SAP HANA audit log collection in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/sap/collect-sap-hana-audit-logs |
| Configure SAP data connector agent or agentless | https://learn.microsoft.com/en-us/azure/sentinel/sap/deploy-data-connector-agent-container |
| Configure SAP threat detection content in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/sap/deployment-solution-configuration |
| Verify prerequisites for Sentinel SAP monitoring | https://learn.microsoft.com/en-us/azure/sentinel/sap/prerequisites-for-deploying-sap-continuous-threat-monitoring |
| Reference kickstart script parameters for SAP connector | https://learn.microsoft.com/en-us/azure/sentinel/sap/reference-kickstart |
| Configure legacy systemconfig.ini for Sentinel SAP agent | https://learn.microsoft.com/en-us/azure/sentinel/sap/reference-systemconfig |
| Configure systemconfig.json for Sentinel SAP connector | https://learn.microsoft.com/en-us/azure/sentinel/sap/reference-systemconfig-json |
| Configure SAP connector agent update script options | https://learn.microsoft.com/en-us/azure/sentinel/sap/reference-update |
| Expert configuration of Sentinel SAP connector container | https://learn.microsoft.com/en-us/azure/sentinel/sap/sap-solution-deploy-alternate |
| Reference SAP logs and tables ingested by Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/sap/sap-solution-log-reference |
| Tune monitored SAP security parameters for Sentinel rules | https://learn.microsoft.com/en-us/azure/sentinel/sap/sap-suspicious-configuration-security-parameters |
| Disable and stop SAP data collection in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/sap/stop-collection |
| Configure scheduled analytics rules in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/scheduled-rules-overview |
| Use Microsoft Sentinel security alert schema fields | https://learn.microsoft.com/en-us/azure/sentinel/security-alert-schema |
| Configure Sentinel alert schemas for XDR connectors | https://learn.microsoft.com/en-us/azure/sentinel/security-alert-schema-differences |
| Understand Sentinel out-of-the-box content centralization | https://learn.microsoft.com/en-us/azure/sentinel/sentinel-content-centralize |
| Deploy and use Sentinel Zero Trust TIC 3.0 solution | https://learn.microsoft.com/en-us/azure/sentinel/sentinel-solution |
| Configure summary rules to aggregate Sentinel data | https://learn.microsoft.com/en-us/azure/sentinel/summary-rules |
| Surface custom event details in Sentinel alerts | https://learn.microsoft.com/en-us/azure/sentinel/surface-custom-details-in-alerts |
| Configure threat intelligence feed integrations in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/threat-intelligence-integration |
| Configure filter and split transformations for Sentinel data | https://learn.microsoft.com/en-us/azure/sentinel/transformation-filter-split |
| Reference for Sentinel UEBA inputs and enrichments | https://learn.microsoft.com/en-us/azure/sentinel/ueba-reference |
| Configure Custom Logs via AMA for specific applications | https://learn.microsoft.com/en-us/azure/sentinel/unified-connector-custom-device |
| Configure unified connectors for Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/unified-connector-integration |
| Use Microsoft threat intelligence in Sentinel rules | https://learn.microsoft.com/en-us/azure/sentinel/use-matching-analytics-to-detect-threats |
| Configure analytics rules using threat indicators | https://learn.microsoft.com/en-us/azure/sentinel/use-threat-indicators-in-analytics-rules |
| Use Microsoft Sentinel built-in watchlist schemas | https://learn.microsoft.com/en-us/azure/sentinel/watchlist-schemas |
| Select Windows security event sets for Sentinel ingestion | https://learn.microsoft.com/en-us/azure/sentinel/windows-security-event-id-reference |
| Configure and manage threat indicators in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/work-with-threat-indicators |
| Configure and use Sentinel workspace manager for multi-workspace operations | https://learn.microsoft.com/en-us/azure/sentinel/workspace-manager |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Add investigation entities as threat indicators in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/add-entity-to-threat-intelligence |
| Use Sentinel connector playbooks to manage incident tasks | https://learn.microsoft.com/en-us/azure/sentinel/automation/create-tasks-playbook |
| Generate Python SOAR playbooks with Sentinel AI | https://learn.microsoft.com/en-us/azure/sentinel/automation/generate-playbook |
| Use automation integrations in Microsoft Sentinel playbooks | https://learn.microsoft.com/en-us/azure/sentinel/automation/integrations |
| Leverage Azure Logic Apps workflows for Sentinel playbooks | https://learn.microsoft.com/en-us/azure/sentinel/automation/logic-apps-playbooks |
| Use Microsoft Sentinel playbook triggers and actions via Logic Apps | https://learn.microsoft.com/en-us/azure/sentinel/automation/playbook-triggers-actions |
| Integrate Microsoft Sentinel incidents with Teams collaboration | https://learn.microsoft.com/en-us/azure/sentinel/collaborate-in-microsoft-teams |
| Connect AWS service logs to Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/connect-aws |
| Ingest AWS EKS audit logs into Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/connect-aws-eks |
| Configure Logstash DCR-based streaming to Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/connect-logstash-data-connection-rules |
| Configure Microsoft Defender XDR connector for Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/connect-microsoft-365-defender |
| Connect Purview Information Protection to Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/connect-microsoft-purview |
| Integrate STIX/TAXII threat feeds with Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/connect-threat-intelligence-taxii |
| Connect external threat intelligence platforms to Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/connect-threat-intelligence-tip |
| Integrate external TIP feeds via Sentinel upload API | https://learn.microsoft.com/en-us/azure/sentinel/connect-threat-intelligence-upload-api |
| Create and manage custom graphs in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/datalake/create-custom-graphs |
| Author custom graphs with AI in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/datalake/create-graphs-with-ai |
| Query Sentinel graphs using GQL syntax and operators | https://learn.microsoft.com/en-us/azure/sentinel/datalake/gql-reference-for-sentinel-custom-graph |
| Call Sentinel custom graph REST APIs from clients | https://learn.microsoft.com/en-us/azure/sentinel/datalake/graph-rest-api |
| Call Sentinel data lake KQL APIs programmatically | https://learn.microsoft.com/en-us/azure/sentinel/datalake/kql-queries-api |
| Use sample KQL queries for Sentinel data lake | https://learn.microsoft.com/en-us/azure/sentinel/datalake/kql-sample-queries |
| Sample notebook code for Sentinel data lake queries | https://learn.microsoft.com/en-us/azure/sentinel/datalake/notebook-examples |
| Run Jupyter notebooks on Sentinel data lake | https://learn.microsoft.com/en-us/azure/sentinel/datalake/notebooks |
| Use the Sentinel graph provider API | https://learn.microsoft.com/en-us/azure/sentinel/datalake/sentinel-graph-provider-reference |
| Use Sentinel MCP agent creation tools | https://learn.microsoft.com/en-us/azure/sentinel/datalake/sentinel-mcp-agent-creation-tool |
| Enable Sentinel MCP connector in ChatGPT or Claude | https://learn.microsoft.com/en-us/azure/sentinel/datalake/sentinel-mcp-chatgpt-claude-connector |
| Use Sentinel MCP data exploration tools | https://learn.microsoft.com/en-us/azure/sentinel/datalake/sentinel-mcp-data-exploration-tool |
| Build Logic Apps with Sentinel MCP tools | https://learn.microsoft.com/en-us/azure/sentinel/datalake/sentinel-mcp-logic-apps |
| Integrate Sentinel MCP tools with AI Foundry | https://learn.microsoft.com/en-us/azure/sentinel/datalake/sentinel-mcp-use-tool-azure-ai-foundry |
| Use Sentinel MCP tools in Copilot Studio | https://learn.microsoft.com/en-us/azure/sentinel/datalake/sentinel-mcp-use-tool-copilot-studio |
| Add Sentinel MCP tools to Security Copilot | https://learn.microsoft.com/en-us/azure/sentinel/datalake/sentinel-mcp-use-tool-security-copilot |
| Use Sentinel MCP tools in Visual Studio Code | https://learn.microsoft.com/en-us/azure/sentinel/datalake/sentinel-mcp-use-tool-visual-studio-code |
| Use MicrosoftSentinelProvider class to access data lake | https://learn.microsoft.com/en-us/azure/sentinel/datalake/sentinel-provider-class-reference |
| Enrich Sentinel entities with geolocation data using REST API | https://learn.microsoft.com/en-us/azure/sentinel/geolocation-data-api |
| Manage Sentinel hunting queries via Log Analytics REST API | https://learn.microsoft.com/en-us/azure/sentinel/hunting-with-rest-api |
| Bulk import threat intelligence files into Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/indicators-bulk-file-import |
| Integrate Defender for Cloud incidents via Defender XDR | https://learn.microsoft.com/en-us/azure/sentinel/ingest-defender-for-cloud-incidents |
| Create codeless data connectors for Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/isv/create-codeless-connector |
| Build custom Sentinel connectors with AI agent | https://learn.microsoft.com/en-us/azure/sentinel/isv/create-custom-connector-builder-agent |
| Use ASIM KQL parsers for normalized Sentinel queries | https://learn.microsoft.com/en-us/azure/sentinel/normalization-about-parsers |
| Use AI agent skills to create ASIM parsers | https://learn.microsoft.com/en-us/azure/sentinel/normalization-create-parsers-ai-agent |
| Apply ASIM helper functions in KQL queries | https://learn.microsoft.com/en-us/azure/sentinel/normalization-functions |
| Build Power BI reports from Sentinel data | https://learn.microsoft.com/en-us/azure/sentinel/powerbi |
| Trigger Sentinel playbooks from entity-based investigations | https://learn.microsoft.com/en-us/azure/sentinel/respond-threats-during-investigation |
| Use Sentinel SAP solution KQL functions for analysis | https://learn.microsoft.com/en-us/azure/sentinel/sap/sap-solution-function-reference |
| Call Sentinel SOC optimization recommendations API | https://learn.microsoft.com/en-us/azure/sentinel/soc-optimization/soc-optimization-api |
| Import threat intelligence STIX objects into Sentinel via upload API | https://learn.microsoft.com/en-us/azure/sentinel/stix-objects-api |
| Extract non-native incident entities with Sentinel playbooks | https://learn.microsoft.com/en-us/azure/sentinel/tutorial-extract-incident-entities |
| Use legacy Sentinel upload indicators API for STIX IOCs | https://learn.microsoft.com/en-us/azure/sentinel/upload-indicators-api |
| Query STIX objects and indicators in Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/work-with-stix-objects-indicators |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy Sentinel solution for Power Platform and Dynamics | https://learn.microsoft.com/en-us/azure/sentinel/business-applications/deploy-power-platform-solution |
| Set up CI/CD repository deployments for Sentinel | https://learn.microsoft.com/en-us/azure/sentinel/ci-cd |
| Customize Sentinel repository deployment behavior | https://learn.microsoft.com/en-us/azure/sentinel/ci-cd-custom-deploy |
| Deploy Sentinel monitoring for Dynamics 365 Finance | https://learn.microsoft.com/en-us/azure/sentinel/dynamics-365/deploy-dynamics-365-finance-operations-solution |
| Deploy Sentinel analytics rules via ARM templates | https://learn.microsoft.com/en-us/azure/sentinel/import-export-analytics-rules |
| Deploy Sentinel automation rules via ARM templates | https://learn.microsoft.com/en-us/azure/sentinel/import-export-automation-rules |
| Package and deploy Sentinel platform solutions | https://learn.microsoft.com/en-us/azure/sentinel/isv/package-platform-solution |
| Publish Sentinel SIEM solutions to Microsoft marketplace | https://learn.microsoft.com/en-us/azure/sentinel/isv/publish-sentinel-solutions |
| Run Sentinel hunting notebooks in Azure ML workspaces | https://learn.microsoft.com/en-us/azure/sentinel/notebooks-hunt |
| Deploy SAP data connector agent container via CLI | https://learn.microsoft.com/en-us/azure/sentinel/sap/deploy-command-line |
| Deploy Sentinel solution for SAP BTP systems | https://learn.microsoft.com/en-us/azure/sentinel/sap/deploy-sap-btp-solution |
| Deploy Sentinel solution for SAP applications | https://learn.microsoft.com/en-us/azure/sentinel/sap/deployment-overview |
| Migrate Sentinel SAP container agent to agentless connector | https://learn.microsoft.com/en-us/azure/sentinel/sap/sap-agent-migrate |
| Update Microsoft Sentinel SAP data connector agent | https://learn.microsoft.com/en-us/azure/sentinel/sap/update-sap-data-connector |