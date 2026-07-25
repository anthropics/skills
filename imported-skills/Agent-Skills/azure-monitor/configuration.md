# Azure Monitor — Configuration

> This is a reference file for the main [SKILL.md](SKILL.md). This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

### Configuration
| Topic | URL |
|-------|-----|
| Configure Azure Monitor Agent settings via DCR | https://learn.microsoft.com/en-us/azure/azure-monitor/agents/agent-settings |
| Migrate MMA custom text logs to AMA DCR tables | https://learn.microsoft.com/en-us/azure/azure-monitor/agents/azure-monitor-agent-custom-text-log-migration |
| Track Azure Monitor Agent VM extension versions | https://learn.microsoft.com/en-us/azure/azure-monitor/agents/azure-monitor-agent-extension-versions |
| Configure network and isolation settings for Azure Monitor Agent | https://learn.microsoft.com/en-us/azure/azure-monitor/agents/azure-monitor-agent-network-configuration |
| Configure ARM template to send Windows VM guest OS metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/agents/collect-custom-metrics-guestos-resource-manager-vm |
| Configure ARM template for Windows VM scale set metrics collection | https://learn.microsoft.com/en-us/azure/azure-monitor/agents/collect-custom-metrics-guestos-resource-manager-vmss |
| Configure and manage Azure Diagnostics extension | https://learn.microsoft.com/en-us/azure/azure-monitor/agents/diagnostics-extension-overview |
| Configure Windows Azure Diagnostics extension schema | https://learn.microsoft.com/en-us/azure/azure-monitor/agents/diagnostics-extension-schema-windows |
| Configure Azure Diagnostics extension to stream data to Event Hubs | https://learn.microsoft.com/en-us/azure/azure-monitor/agents/diagnostics-extension-stream-event-hubs |
| Azure Diagnostics extension configuration schema version history | https://learn.microsoft.com/en-us/azure/azure-monitor/agents/diagnostics-extension-versions |
| Install and configure Azure Diagnostics extension for Windows VMs | https://learn.microsoft.com/en-us/azure/azure-monitor/agents/diagnostics-extension-windows-install |
| Configure Log Analytics gateway for offline Azure Monitor clients | https://learn.microsoft.com/en-us/azure/azure-monitor/agents/gateway |
| Configure Azure Copilot Observability Agent resource | https://learn.microsoft.com/en-us/azure/azure-monitor/aiops/observability-agent-resource |
| Deploy Observability Agents with ARM and Bicep templates | https://learn.microsoft.com/en-us/azure/azure-monitor/aiops/observability-agent-resource-create-template |
| Enable and use the Azure Monitor common alert schema | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/alerts-common-schema |
| Create activity log and health alert rules in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/alerts-create-activity-log-alert-rule |
| Configure Azure Monitor log search alert rules | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/alerts-create-log-alert-rule |
| Configure query-based metric alerts with PromQL in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/alerts-create-query-based-metric-alerts |
| Configure Azure Monitor alert rules via CLI, PowerShell, ARM | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/alerts-create-rule-cli-powershell-arm |
| Create simple log search alert rules in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/alerts-create-simple-alert |
| Configure custom email subjects for log alerts | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/alerts-customize-email-subject-how-to |
| Understand noncommon Azure Monitor alert schema definitions | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/alerts-non-common-schema-definitions |
| Configure smart detection rules via ARM templates | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/proactive-arm-config |
| Configure smart detection email notification recipients in Application Insights | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/proactive-email-notification |
| Configure Prometheus metric alert rules in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/prometheus-alerts |
| Configure Azure Monitor action groups with ARM templates | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/resource-manager-action-groups |
| Deploy Azure Monitor resource health alerts via ARM | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/resource-manager-alerts-resource-health |
| Deploy Azure Monitor service health alerts via ARM | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/resource-manager-alerts-service-health |
| Deploy simple log search alerts via ARM templates | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/resource-manager-alerts-simple-log-search-alerts |
| Configure Application Insights connection strings securely | https://learn.microsoft.com/en-us/azure/azure-monitor/app/connection-strings |
| Create and configure workspace-based Application Insights | https://learn.microsoft.com/en-us/azure/azure-monitor/app/create-workspace-resource |
| Understand Application Insights telemetry schema and fields | https://learn.microsoft.com/en-us/azure/azure-monitor/app/data-model-complete |
| Configure Grafana dashboards for Application Insights data | https://learn.microsoft.com/en-us/azure/azure-monitor/app/grafana-dashboards |
| Configure Application Insights for Java in containers | https://learn.microsoft.com/en-us/azure/azure-monitor/app/java-get-started-supplemental |
| Configure Application Insights for Spring Boot apps | https://learn.microsoft.com/en-us/azure/azure-monitor/app/java-spring-boot |
| Advanced Java configuration for Application Insights | https://learn.microsoft.com/en-us/azure/azure-monitor/app/java-standalone-config |
| Configure Application Insights Profiler for Java | https://learn.microsoft.com/en-us/azure/azure-monitor/app/java-standalone-profiler |
| Configure Application Insights JavaScript SDK options | https://learn.microsoft.com/en-us/azure/azure-monitor/app/javascript-sdk-configuration |
| Configure OpenTelemetry settings in Application Insights | https://learn.microsoft.com/en-us/azure/azure-monitor/app/opentelemetry-configuration |
| Configure OpenTelemetry ingestion for Application Insights | https://learn.microsoft.com/en-us/azure/azure-monitor/app/opentelemetry-enable |
| Configure OpenTelemetry filtering in Application Insights | https://learn.microsoft.com/en-us/azure/azure-monitor/app/opentelemetry-filter |
| Customize the Application Insights overview dashboard | https://learn.microsoft.com/en-us/azure/azure-monitor/app/overview-dashboard |
| Configure autoscale using Application Insights custom metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/autoscale/autoscale-custom-metric |
| Configure diagnostics logs and metrics for autoscale | https://learn.microsoft.com/en-us/azure/azure-monitor/autoscale/autoscale-diagnostics |
| Understand and configure Azure autoscale settings | https://learn.microsoft.com/en-us/azure/azure-monitor/autoscale/autoscale-understanding-settings |
| Configure VM scale set autoscale with PowerShell | https://learn.microsoft.com/en-us/azure/azure-monitor/autoscale/autoscale-using-powershell |
| Set up autoscale email and webhook notifications | https://learn.microsoft.com/en-us/azure/azure-monitor/autoscale/autoscale-webhook-email |
| Onboard and analyze OpenTelemetry data in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/collect-use-observability-data |
| Understand deployment and HPA metrics collected by Container insights | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/container-insights-deployment-hpa-metrics |
| Switch Container Insights visualizations to Managed Prometheus | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/container-insights-experience-v2 |
| Configure GPU monitoring for Kubernetes with Container insights | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/container-insights-gpu-monitoring |
| Configure Container Insights for hybrid and Azure Stack Kubernetes | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/container-insights-hybrid-setup |
| View real-time Kubernetes metrics with Container Insights Live Data | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/container-insights-livedata-metrics |
| Create log-based alerts for AKS CPU, memory, and disk | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/container-insights-log-alerts |
| Query Kubernetes container logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/container-insights-log-query |
| Configure ContainerLogV2 schema and migration settings | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/container-insights-logs-schema |
| Manage and upgrade the Container Insights agent | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/container-insights-manage-agent |
| Configure multitenant logging in Container Insights | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/container-insights-multitenant |
| Configure persistent volume monitoring with Container insights | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/container-insights-persistent-volumes |
| Access and analyze Syslog data from AKS nodes in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/container-insights-syslog |
| Configure throttling parameters and monitor log loss in Container Insights | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/container-insights-throttling |
| Configure DCR transformations for Kubernetes container logs | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/container-insights-transformations |
| Configure workspace transformations for AKS control plane logs | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/control-plane-transformations |
| Configure AKS autoinstrumentation for Python and .NET | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/kubernetes-codeless-python-net |
| Configure Kubernetes ConfigMap for Azure Monitor log collection | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/kubernetes-data-collection-configmap |
| Customize and filter Azure Monitor data collection for Kubernetes | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/kubernetes-data-collection-configure |
| Enable recommended metric alert rules for Kubernetes clusters | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/kubernetes-metric-alerts |
| Enable Azure Monitor features for AKS clusters | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/kubernetes-monitoring-enable |
| Configure monitoring for Arc-enabled Kubernetes with Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/kubernetes-monitoring-enable-arc |
| Configure firewall and proxy for Kubernetes monitoring agents | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/kubernetes-monitoring-firewall |
| Configure OTLP monitoring for AKS applications | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/kubernetes-open-protocol |
| Route Prometheus metrics to multiple Azure Monitor workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/prometheus-metrics-multiple-workspaces |
| Create custom Prometheus scrape jobs with ConfigMap | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/prometheus-metrics-scrape-configmap |
| Customize Prometheus metric scraping via ConfigMap | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/prometheus-metrics-scrape-configuration |
| Review default Prometheus scrape settings in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/prometheus-metrics-scrape-default |
| Configure Prometheus remote write with Entra Workload ID | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/prometheus-remote-write-azure-workload-identity |
| Configure Prometheus remote write with managed identity | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/prometheus-remote-write-managed-identity |
| Configure Azure Monitor data collection endpoints | https://learn.microsoft.com/en-us/azure/azure-monitor/data-collection/data-collection-endpoint-overview |
| Author Azure Monitor data collection rules in JSON | https://learn.microsoft.com/en-us/azure/azure-monitor/data-collection/data-collection-rule-create-edit |
| Configure Azure Monitor data collection rules in portal | https://learn.microsoft.com/en-us/azure/azure-monitor/data-collection/data-collection-rule-create-portal |
| Use sample DCR definitions for Azure Monitor scenarios | https://learn.microsoft.com/en-us/azure/azure-monitor/data-collection/data-collection-rule-samples |
| Understand and edit Azure Monitor DCR JSON structure | https://learn.microsoft.com/en-us/azure/azure-monitor/data-collection/data-collection-rule-structure |
| View and inspect data collection rule definitions in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/data-collection/data-collection-rule-view |
| Configure Azure Monitor data transformations in DCRs | https://learn.microsoft.com/en-us/azure/azure-monitor/data-collection/data-collection-transformations |
| Create and attach transformation queries in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/data-collection/data-collection-transformations-create |
| Use supported KQL features in Azure Monitor transformations | https://learn.microsoft.com/en-us/azure/azure-monitor/data-collection/data-collection-transformations-kql |
| Create DCRs to export Azure platform metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/data-collection/metrics-export-create |
| Author DCR JSON for Azure Monitor metrics export | https://learn.microsoft.com/en-us/azure/azure-monitor/data-collection/metrics-export-structure |
| Configure Azure Monitor pipeline on Arc-enabled Kubernetes | https://learn.microsoft.com/en-us/azure/azure-monitor/data-collection/pipeline-configure |
| Configure Azure Monitor pipeline with CLI and ARM | https://learn.microsoft.com/en-us/azure/azure-monitor/data-collection/pipeline-configure-cli |
| Configure Azure Monitor pipeline via Azure portal | https://learn.microsoft.com/en-us/azure/azure-monitor/data-collection/pipeline-configure-portal |
| Configure Kubernetes gateway for Azure Monitor pipeline | https://learn.microsoft.com/en-us/azure/azure-monitor/data-collection/pipeline-kubernetes-gateway |
| Configure pod placement for Azure Monitor pipeline instances | https://learn.microsoft.com/en-us/azure/azure-monitor/data-collection/pipeline-pod-placement |
| Configure Azure Monitor pipeline log transformations | https://learn.microsoft.com/en-us/azure/azure-monitor/data-collection/pipeline-transformations |
| Configure DCRs to collect Azure platform logs | https://learn.microsoft.com/en-us/azure/azure-monitor/data-collection/platform-logs-collect |
| Configure data sources and collection methods in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/fundamentals/data-sources |
| Reference monitoring data types for Azure Monitor itself | https://learn.microsoft.com/en-us/azure/azure-monitor/fundamentals/monitor-azure-monitor-reference |
| Use private endpoints for Azure Monitor workspace queries | https://learn.microsoft.com/en-us/azure/azure-monitor/fundamentals/private-link-azure-monitor-workspace |
| Configure Azure Monitor Private Link Scope and endpoints | https://learn.microsoft.com/en-us/azure/azure-monitor/fundamentals/private-link-configure |
| Enable Private Link for VM and AKS monitoring | https://learn.microsoft.com/en-us/azure/azure-monitor/fundamentals/private-link-vm-kubernetes |
| Configure service level indicators in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/fundamentals/service-level-indicators-create |
| Configure alerts for Azure Monitor health model entities | https://learn.microsoft.com/en-us/azure/azure-monitor/health-models/alerts |
| Configure Azure Monitor health models with Designer | https://learn.microsoft.com/en-us/azure/azure-monitor/health-models/designer |
| Configure discovery of entities in Azure Monitor health models | https://learn.microsoft.com/en-us/azure/azure-monitor/health-models/discoveries |
| Configure and tune signals in Azure Monitor health models | https://learn.microsoft.com/en-us/azure/azure-monitor/health-models/signals |
| Query Azure resource logs directly with Logs API | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/api/azure-resource-queries |
| Use batch queries with Azure Monitor Logs API | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/api/batch-queries |
| Configure Azure Monitor Logs API Prefer header options | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/api/prefer-options |
| Interpret Azure Monitor Log Analytics API responses | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/api/response-format |
| Change pricing tiers for Log Analytics workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/change-pricing-tier |
| Configure and use computer groups in log queries | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/computer-groups |
| Configure custom tables and columns in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/create-custom-table |
| Configure Auxiliary plan custom tables in Log Analytics | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/create-custom-table-auxiliary |
| Run cross-resource queries in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/cross-workspace-query |
| Configure data retention for Log Analytics tables | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/data-retention-configure |
| Delete and recover Azure Log Analytics workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/delete-workspace |
| Configure on-demand export jobs for Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/export-job |
| Use standard columns in Azure Monitor log records | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/log-standard-columns |
| Set up Log Analytics data export rules to storage and Event Hubs | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/logs-data-export |
| Configure customer-managed storage for Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/private-storage |
| Configure and interpret Azure Monitor log query audit logs | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/query-audit |
| Configure and use query packs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/query-packs |
| Create Azure Monitor log queries with ARM templates | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/resource-manager-log-queries |
| Restore Azure Monitor log data for high-speed queries | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/restore |
| Deploy workspace transformations using ARM templates | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/tutorial-workspace-transformations-api |
| Add workspace transformations via Azure portal for Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/tutorial-workspace-transformations-portal |
| Configure Prometheus rule groups in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/metrics/prometheus-rule-groups |
| Understand Azure Activity Log event schema fields | https://learn.microsoft.com/en-us/azure/azure-monitor/platform/activity-log-schema |
| Configure Azure Monitor diagnostic settings and destinations | https://learn.microsoft.com/en-us/azure/azure-monitor/platform/diagnostic-settings |
| Configure Azure resource logs and destinations in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/platform/resource-logs |
| Azure resource logs services and event schemas | https://learn.microsoft.com/en-us/azure/azure-monitor/platform/resource-logs-schema |
| Apply Azure Monitor diagnostic settings using ARM | https://learn.microsoft.com/en-us/azure/azure-monitor/platform/resource-manager-diagnostic-settings |
| Configure .NET Profiler for ASP.NET Core on Linux App Service | https://learn.microsoft.com/en-us/azure/azure-monitor/profiler/profiler-aspnetcore-linux |
| Enable .NET Profiler for Azure Functions apps | https://learn.microsoft.com/en-us/azure/azure-monitor/profiler/profiler-azure-functions |
| Configure Bring Your Own Storage for Profiler and Snapshot Debugger | https://learn.microsoft.com/en-us/azure/azure-monitor/profiler/profiler-bring-your-own-storage |
| Enable .NET Profiler for ASP.NET Core in Azure containers | https://learn.microsoft.com/en-us/azure/azure-monitor/profiler/profiler-containers |
| Use .NET Profiler settings pane in Application Insights | https://learn.microsoft.com/en-us/azure/azure-monitor/profiler/profiler-settings |
| Use Azure Monitor resource log categories and schemas | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/logs-index |
| Discover Azure Monitor metrics by resource type | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/metrics-index |
| Discover Azure Monitor metrics by resource type | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/metrics-index |
| Use Azure Monitor log categories for Azure AD Domain Services | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-aad-domainservices-logs |
| Use Azure Monitor log categories for FarmBeats | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-agfoodplatform-farmbeats-logs |
| Use Azure Monitor log categories for Analysis Services | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-analysisservices-servers-logs |
| Use Azure Monitor log categories for API Management services | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-apimanagement-service-logs |
| Use Azure Monitor log categories for API Management workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-apimanagement-service-workspaces-logs |
| Configure log categories for Container Apps managed environments | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-app-managedenvironments-logs |
| Azure Monitor log categories for App Configuration stores | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-appconfiguration-configurationstores-logs |
| Azure Monitor log categories for AppLink members | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-applink-applinks-applinkmembers-logs |
| Azure Monitor log categories for Azure Spring Apps | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-appplatform-spring-logs |
| Azure Monitor log categories for Attestation providers | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-attestation-attestationproviders-logs |
| Azure Monitor log categories for Automation accounts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-automation-automationaccounts-logs |
| Azure Monitor log categories for Autonomous Development Platform accounts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-autonomousdevelopmentplatform-accounts-logs |
| Azure Monitor log categories for Autonomous Development workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-autonomousdevelopmentplatform-workspaces-logs |
| Azure Monitor log categories for Azure VMware Solution private clouds | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-avs-privateclouds-logs |
| Azure Data Transfer connections flows log categories | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-azuredatatransfer-connections-flows-logs |
| Azure Monitor log categories for Azure Playwright Service accounts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-azureplaywrightservice-accounts-logs |
| Azure Monitor log categories for Azure Sphere catalogs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-azuresphere-catalogs-logs |
| Azure Monitor log categories for Batch accounts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-batch-batchaccounts-logs |
| Configure Bot Service resource log categories in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-botservice-botservices-logs |
| Azure Monitor log categories for Redis Enterprise databases | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-cache-redisenterprise-databases-logs |
| Azure Monitor log categories for CDN edge actions | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-cdn-edgeactions-logs |
| Azure Monitor log categories for CDN endpoints | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-cdn-profiles-endpoints-logs |
| Azure Monitor log categories for CDN profiles | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-cdn-profiles-logs |
| Chaos Studio experiments Azure Monitor log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-chaos-experiments-logs |
| Log categories for Microsoft.CloudHealth healthmodels in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-cloudhealth-healthmodels-logs |
| Azure Monitor log categories for Code Signing accounts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-codesigning-codesigningaccounts-logs |
| Reference log categories for Azure Cognitive Services monitoring | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-cognitiveservices-accounts-logs |
| Azure Monitor log categories for Cognitive Services projects | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-cognitiveservices-accounts-projects-logs |
| Azure Monitor log categories for Community Trainings | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-community-communitytrainings-logs |
| Azure Monitor log categories for virtual machines | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-compute-virtualmachines-logs |
| Azure Monitor log categories for Confidential Ledger ledgers | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-confidentialledger-ledgers-logs |
| Azure Monitor log categories for Confidential Ledger ManagedCCF | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-confidentialledger-managedccf-logs |
| Azure Monitor log categories for Confidential Ledger ManagedCCFs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-confidentialledger-managedccfs-logs |
| Azure Monitor log categories for Connected Cache nodes | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-connectedcache-cachenodes-logs |
| Azure Monitor log categories for enterprise MCC customers | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-connectedcache-enterprisemcccustomers-logs |
| Azure Monitor log categories for ISP customers in Connected Cache | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-connectedcache-ispcustomers-logs |
| Azure Monitor log categories for Connected Vehicle platform accounts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-connectedvehicle-platformaccounts-logs |
| Azure Monitor log categories for Container Instances | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-containerinstance-containergroups-logs |
| Azure Monitor log categories for Container Registry | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-containerregistry-registries-logs |
| Azure Monitor log categories for AKS fleets | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-containerservice-fleets-logs |
| Azure Monitor log categories for AKS managed clusters | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-containerservice-managedclusters-logs |
| Azure Monitor log categories for Custom Providers | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-customproviders-resourceproviders-logs |
| Azure Monitor log categories for D365 Customer Insights instances | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-d365customerinsights-instances-logs |
| Review Azure Monitor log categories for PostgreSQL flexible servers | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-dbforpostgresql-flexibleservers-logs |
| Understand Azure DevCenter diagnostic log categories | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-devcenter-devcenters-logs |
| Configure Azure Monitor logs for Discovery bookshelves | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-discovery-bookshelves-logs |
| Configure Azure Monitor logs for Discovery supercomputers | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-discovery-supercomputers-logs |
| Configure Azure Monitor logs for Discovery workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-discovery-workspaces-logs |
| Interpret Azure Monitor logs for Health Data AI de-id | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-healthdataaiservices-deidservices-logs |
| Interpret Azure Monitor logs for Network Virtual Appliances | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-network-networkvirtualappliances-logs |
| Review Azure Monitor log categories for Traffic Manager | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-network-trafficmanagerprofiles-logs |
| Review Azure Monitor log categories for Virtual Network Gateways | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-network-virtualnetworkgateways-logs |
| Review Azure Monitor log categories for Virtual Networks | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-network-virtualnetworks-logs |
| Review Azure Monitor log categories for VPN Gateways | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-network-vpngateways-logs |
| Review Azure Monitor log categories for Network Analytics DataProducts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-networkanalytics-dataproducts-logs |
| Configure Azure Monitor logs for NetworkCloud bareMetalMachines | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-networkcloud-baremetalmachines-logs |
| Review Azure Monitor log categories for NetworkCloud clusterManagers | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-networkcloud-clustermanagers-logs |
| Configure Azure Monitor logs for NetworkCloud clusters | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-networkcloud-clusters-logs |
| Review Azure Monitor log categories for NetworkCloud Kubernetes clusters | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-networkcloud-kubernetesclusters-logs |
| Configure Azure Monitor logs for NetworkCloud storageAppliances | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-networkcloud-storageappliances-logs |
| Configure Azure Monitor logs for Azure Traffic Collectors | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-networkfunction-azuretrafficcollectors-logs |
| Review Azure Monitor log categories for Notification Hubs namespaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-notificationhubs-namespaces-logs |
| Review Azure Monitor log categories for Notification Hubs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-notificationhubs-namespaces-notificationhubs-logs |
| Review Azure Monitor log categories for Online Experimentation workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-onlineexperimentation-workspaces-logs |
| Review Azure Monitor log categories for Open Logistics Workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-openlogisticsplatform-workspaces-logs |
| Configure Azure Monitor logs for Log Analytics workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-operationalinsights-workspaces-logs |
| Review Azure Monitor log categories for PlayFab titles | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-playfab-titles-logs |
| Review Azure Monitor log categories for Power BI tenants | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-powerbi-tenants-logs |
| Review Azure Monitor log categories for Power BI workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-powerbi-tenants-workspaces-logs |
| Review Azure Monitor log categories for Power BI Dedicated capacities | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-powerbidedicated-capacities-logs |
| Review Azure Monitor log categories for ProviderHub monitor settings | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-providerhub-providermonitorsettings-logs |
| Review Azure Monitor log categories for ProviderHub registrations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-providerhub-providerregistrations-logs |
| Configure Azure Monitor logs for Microsoft Purview accounts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-purview-accounts-logs |
| Review Azure Quantum workspace log categories in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-quantum-workspaces-logs |
| Configure Azure Monitor logs for Recovery Services vaults | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-recoveryservices-vaults-logs |
| Review Azure Monitor log categories for Relay namespaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-relay-namespaces-logs |
| Review ResourceBuilder workspace log categories in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-resourcebuilder-workspaces-logs |
| Configure Azure Monitor logs for Azure Cognitive Search services | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-search-searchservices-logs |
| Review Azure Monitor log categories for Security anti-malware settings | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-security-antimalwaresettings-logs |
| Review Azure Monitor log categories for Defender for Storage settings | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-security-defenderforstoragesettings-logs |
| Review Azure Monitor log categories for Security Insights settings | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-securityinsights-settings-logs |
| Configure Azure Monitor logs for Service Bus namespaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-servicebus-namespaces-logs |
| Configure and interpret trafficControllers Azure Monitor logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-servicenetworking-trafficcontrollers-logs |
| Configure Azure Monitor logs for Azure SignalR Service | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-signalrservice-signalr-logs |
| Configure Azure Monitor logs for SignalR replicas | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-signalrservice-signalr-replicas-logs |
| Configure Azure Monitor logs for Web PubSub | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-signalrservice-webpubsub-logs |
| Configure Azure Monitor logs for Web PubSub replicas | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-signalrservice-webpubsub-replicas-logs |
| Review Azure Monitor log categories for Singularity accounts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-singularity-accounts-logs |
| Review Synapse workspace log categories in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/microsoft-synapse-workspaces-logs |
| Understand Oracle autonomous database log categories in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/oracle-database-autonomousdatabases-logs |
| Oracle Exadata VM cluster log categories in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-logs/oracle-database-exadbvmclusters-logs |
| Metrics reference for Azure AD Domain Services | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-aad-domainservices-metrics |
| Metrics reference for Azure Analysis Services servers | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-analysisservices-servers-metrics |
| Metrics reference for API Management gateways | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-apimanagement-gateways-metrics |
| Metrics reference for API Management service | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-apimanagement-service-metrics |
| Metrics reference for Azure Container Apps | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-app-containerapps-metrics |
| Metrics reference for Azure App Jobs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-app-jobs-metrics |
| Metrics reference for Azure managed environments | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-app-managedenvironments-metrics |
| Metrics reference for Azure session pools | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-app-sessionpools-metrics |
| Metrics reference for App Configuration stores | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-appconfiguration-configurationstores-metrics |
| Metrics reference for Azure Spring Apps | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-appplatform-spring-metrics |
| Use Azure Monitor metrics for Automation Accounts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-automation-automationaccounts-metrics |
| Monitor AVS private clouds with Azure metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-avs-privateclouds-metrics |
| Metric reference for AzureDataTransfer connection flows | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-azuredatatransfer-connections-flows-metrics |
| Monitor Azure Sphere catalogs via metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-azuresphere-catalogs-metrics |
| Reference Azure Stack HCI cluster metrics in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-azurestackhci-clusters-metrics |
| Reference Azure Monitor metrics for Batch accounts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-batch-batchaccounts-metrics |
| Azure Monitor metrics for Bing accounts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-bing-accounts-metrics |
| Monitor Bot Service channels with metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-botservice-botservices-channels-metrics |
| Monitor Bot Service connections via metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-botservice-botservices-connections-metrics |
| Bot Service metrics for Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-botservice-botservices-metrics |
| Metrics for BotService name availability checks | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-botservice-checknameavailability-metrics |
| Monitor BotService host settings with metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-botservice-hostsettings-metrics |
| Metrics for BotService auth service providers | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-botservice-listauthserviceproviders-metrics |
| Metrics for BotService QnA Maker endpoint keys | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-botservice-listqnamakerendpointkeys-metrics |
| Use Azure Monitor metrics for Azure Cache for Redis | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-cache-redis-metrics |
| Use Azure Monitor metrics for Redis Enterprise caches | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-cache-redisenterprise-metrics |
| Monitor CDN WAF policies using metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-cdn-cdnwebapplicationfirewallpolicies-metrics |
| Azure CDN edge actions metrics catalog | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-cdn-edgeactions-metrics |
| Azure CDN profiles metrics reference | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-cdn-profiles-metrics |
| Use Azure Monitor metrics for CloudHealth health models | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-cloudhealth-healthmodels-metrics |
| ClusterStor node metrics for Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-clusterstor-nodes-metrics |
| Code Signing account metrics in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-codesigning-codesigningaccounts-metrics |
| Azure Monitor metrics reference for Cognitive Services accounts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-cognitiveservices-accounts-metrics |
| Azure Monitor metrics reference for Cognitive Services projects | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-cognitiveservices-accounts-projects-metrics |
| Cloud services metrics for Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-compute-cloudservices-metrics |
| Cloud service role metrics reference | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-compute-cloudservices-roles-metrics |
| Azure managed disk metrics in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-compute-disks-metrics |
| Use Azure Monitor metrics for Azure VMs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-compute-virtualmachines-metrics |
| Use Azure Monitor metrics for VM scale sets | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-compute-virtualmachinescalesets-metrics |
| Per-VM metrics in virtual machine scale sets | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-compute-virtualmachinescalesets-virtualmachines-metrics |
| Connected Cache node metrics reference | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-connectedcache-cachenodes-metrics |
| Enterprise MCC customer metrics for Connected Cache | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-connectedcache-enterprisemcccustomers-metrics |
| ISP customer metrics for Connected Cache | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-connectedcache-ispcustomers-metrics |
| Connected Vehicle platform account metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-connectedvehicle-platformaccounts-metrics |
| Container group metrics for Azure Container Instances | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-containerinstance-containergroups-metrics |
| Use Azure Monitor metrics for BackupVaults | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-dataprotection-backupvaults-metrics |
| Use Azure Monitor metrics for Device Registry namespaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-deviceregistry-namespaces-metrics |
| Reference metrics for DevOpsInfrastructure pools in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-devopsinfrastructure-pools-metrics |
| Reference metrics for Cosmos DB database accounts in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-documentdb-databaseaccounts-metrics |
| Azure Monitor metrics reference for MongoDB clusters | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-documentdb-mongoclusters-metrics |
| Use Azure Monitor metrics for Durable Task schedulers | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-durabletask-schedulers-metrics |
| Use Azure Monitor metrics for Elastic SAN resources | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-elasticsan-elasticsans-metrics |
| Use Azure Monitor metrics for Event Grid namespaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-eventgrid-namespaces-metrics |
| Azure Monitor metrics reference for Event Hubs namespaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-eventhub-namespaces-metrics |
| Azure Monitor metrics reference for Azure FileShares | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-fileshares-fileshares-metrics |
| Azure Monitor metrics reference for HDInsight clusters | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-hdinsight-clusters-metrics |
| Use Azure Monitor metrics for Healthcare APIs services | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-healthcareapis-services-metrics |
| Metrics reference for Healthcare DICOM services workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-healthcareapis-workspaces-dicomservices-metrics |
| Metrics reference for Healthcare FHIR services workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-healthcareapis-workspaces-fhirservices-metrics |
| Metrics reference for Healthcare IoT connector workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-healthcareapis-workspaces-iotconnectors-metrics |
| Metrics reference for FHIR query event batch channels | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-healthcareinterop-fhirqueryeventbatchchannels-metrics |
| Metrics reference for FHIR query flat file batch channels | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-healthcareinterop-fhirqueryflatfilebatchchannels-metrics |
| Azure Monitor metrics reference for HealthModel resources | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-healthmodel-healthmodels-metrics |
| Use HorizonDB cluster metrics in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-horizondb-clusters-metrics |
| Metrics reference for Hybrid Container Service provisioned clusters | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-hybridcontainerservice-provisionedclusters-metrics |
| Metrics reference for Hybrid Network network functions | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-hybridnetwork-networkfunctions-metrics |
| Metrics reference for Hybrid Network virtual network functions | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-hybridnetwork-virtualnetworkfunctions-metrics |
| Metrics reference for Azure autoscale settings | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-insights-autoscalesettings-metrics |
| Metrics reference for Application Insights components | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-insights-components-metrics |
| Monitor data collection rules with Azure metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-insights-datacollectionrules-metrics |
| Metrics reference for Azure IoT Central applications | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-iotcentral-iotapps-metrics |
| Metrics reference for IoT Firmware Defense workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-iotfirmwaredefense-workspaces-metrics |
| Metrics reference for Key Vault managed HSMs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-keyvault-managedhsms-metrics |
| Metrics reference for Azure Key Vault vaults | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-keyvault-vaults-metrics |
| Metrics reference for Azure Arc-enabled Kubernetes clusters | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-kubernetes-connectedclusters-metrics |
| Use Azure Monitor metrics for Kubernetes configuration extensions | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-kubernetesconfiguration-extensions-metrics |
| Metrics reference for Azure Data Explorer (Kusto) clusters | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-kusto-clusters-metrics |
| Metrics reference for Logic Apps Integration Service Environments | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-logic-integrationserviceenvironments-metrics |
| Metrics reference for Logic Apps workflows | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-logic-workflows-metrics |
| Metrics reference for Azure Machine Learning workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-machinelearningservices-workspaces-metrics |
| Metrics reference for Azure ML online endpoint deployments | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-machinelearningservices-workspaces-onlineendpoints-deployments-metrics |
| Metrics reference for Azure ML online endpoints | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-machinelearningservices-workspaces-onlineendpoints-metrics |
| Metrics reference for Managed Network Fabric internet gateways | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-managednetworkfabric-internetgateways-metrics |
| Metrics reference for Managed Network Fabric L3 isolation domains | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-managednetworkfabric-l3isolationdomains-metrics |
| Metrics reference for Managed Network Fabric network devices | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-managednetworkfabric-networkdevices-metrics |
| Reference Azure Monitor metrics for Network Fabric Controllers | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-managednetworkfabric-networkfabriccontrollers-metrics |
| Metrics reference for Managed Network Fabric fabrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-managednetworkfabric-networkfabrics-metrics |
| Metrics reference for Azure Maps accounts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-maps-accounts-metrics |
| Metrics reference for Messaging Connectors | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-messagingconnectors-connectors-metrics |
| Metrics reference for Mobile Network sites | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-mobilenetwork-mobilenetworks-sites-metrics |
| Metrics reference for Mobile Network packet core control planes | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-mobilenetwork-packetcorecontrolplanes-metrics |
| Metrics reference for Mobile Network packet core data planes | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-mobilenetwork-packetcorecontrolplanes-packetcoredataplanes-metrics |
| Metrics reference for Mobile Network radio access networks | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-mobilenetwork-radioaccessnetworks-metrics |
| Metrics reference for Azure Monitor accounts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-monitor-accounts-metrics |
| Use Azure Monitor metrics for Monitor pipeline groups | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-monitor-pipelinegroups-metrics |
| Monitor NetApp elastic volumes with Azure metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-netapp-elasticaccounts-elasticcapacitypools-elasticvolumes-metrics |
| Use Azure Monitor metrics for NetApp elastic capacity pools | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-netapp-elasticaccounts-elasticcapacitypools-metrics |
| Monitor NetApp capacity pool caches with metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-netapp-netappaccounts-capacitypools-caches-metrics |
| Azure Monitor metrics for NetApp capacity pools | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-netapp-netappaccounts-capacitypools-metrics |
| Reference Azure NetApp Files volume metrics in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-netapp-netappaccounts-capacitypools-volumes-metrics |
| Azure Monitor metrics for NetApp accounts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-netapp-netappaccounts-metrics |
| Azure Monitor metrics for NetApp scale capacity pools | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-netapp-scaleaccounts-scalecapacitypools-metrics |
| Monitor NetApp scale volumes using Azure metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-netapp-scaleaccounts-scalecapacitypools-scalevolumes-metrics |
| Azure Application Gateway metrics reference for monitoring | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-applicationgateways-metrics |
| Azure Firewall metrics reference for Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-azurefirewalls-metrics |
| Azure Monitor metrics for Bastion hosts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-bastionhosts-metrics |
| Azure Monitor metrics for network connections | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-connections-metrics |
| Monitor DNS forwarding rulesets with Azure metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-dnsforwardingrulesets-metrics |
| Azure Monitor metrics for DNS resolver domain lists | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-dnsresolverdomainlists-metrics |
| Azure Monitor metrics for DNS resolver policies | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-dnsresolverpolicies-metrics |
| Azure Monitor metrics for DNS resolvers | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-dnsresolvers-metrics |
| Azure Monitor metrics for DNS zones | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-dnszones-metrics |
| Azure Monitor metrics for ExpressRoute circuits | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-expressroutecircuits-metrics |
| Monitor ExpressRoute peerings with Azure metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-expressroutecircuits-peerings-metrics |
| Use Azure Monitor metrics for ExpressRoute gateways | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-expressroutegateways-metrics |
| Azure Monitor metrics for ExpressRoute ports | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-expressrouteports-metrics |
| Azure Monitor metrics for Front Door | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-frontdoors-metrics |
| Azure Monitor metrics for Load Balancer | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-loadbalancers-metrics |
| Azure Monitor metrics for NAT gateways | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-natgateways-metrics |
| Use Azure Monitor metrics for network interfaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-networkinterfaces-metrics |
| Monitor Network Manager IPAM pools with metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-networkmanagers-ipampools-metrics |
| Azure Monitor metrics for network security perimeters | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-networksecurityperimeters-metrics |
| Use Azure Monitor metrics for network virtual appliances | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-networkvirtualappliances-metrics |
| Azure Monitor metrics for Network Watcher connection monitors | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-networkwatchers-connectionmonitors-metrics |
| Azure Monitor metrics for P2S VPN gateways | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-p2svpngateways-metrics |
| Azure Monitor metrics for private DNS zones | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-privatednszones-metrics |
| Azure Monitor metrics for private endpoints | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-privateendpoints-metrics |
| Azure Monitor metrics for private link services | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-privatelinkservices-metrics |
| Azure Monitor metrics for public IP addresses | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-publicipaddresses-metrics |
| Use Azure Monitor metrics for public IP prefixes | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-publicipprefixes-metrics |
| Azure Monitor metrics for Traffic Manager profiles | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-trafficmanagerprofiles-metrics |
| Azure Monitor metrics for virtual hubs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-virtualhubs-metrics |
| Use Azure Monitor metrics for virtual network appliances | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-virtualnetworkappliances-metrics |
| Use Azure Monitor metrics for virtual network gateways | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-virtualnetworkgateways-metrics |
| Azure Monitor metrics for virtual networks | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-virtualnetworks-metrics |
| Azure Monitor metrics for virtual routers | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-virtualrouters-metrics |
| Use Azure Monitor metrics for VPN gateways | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-network-vpngateways-metrics |
| Use Azure Monitor metrics for bare metal machines | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-networkcloud-baremetalmachines-metrics |
| Monitor Network Cloud cluster manager metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-networkcloud-clustermanagers-metrics |
| Use Azure Monitor metrics for Network Cloud clusters | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-networkcloud-clusters-metrics |
| Monitor Network Cloud storage appliance metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-networkcloud-storageappliances-metrics |
| Monitor Azure Traffic Collector metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-networkfunction-azuretrafficcollectors-metrics |
| Monitor Notification Hubs namespaces metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-notificationhubs-namespaces-notificationhubs-metrics |
| Reference Azure Monitor metrics for EnergyServices | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-openenergyplatform-energyservices-metrics |
| Monitor Log Analytics workspaces metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-operationalinsights-workspaces-metrics |
| Monitor Azure Orbital contact profile metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-orbital-contactprofiles-metrics |
| Monitor Azure Orbital geocatalog metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-orbital-geocatalogs-metrics |
| Monitor Azure Orbital L2 connection metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-orbital-l2connections-metrics |
| Monitor Azure Orbital spacecraft metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-orbital-spacecrafts-metrics |
| Monitor Azure Orbital terminal metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-orbital-terminals-metrics |
| Monitor OrionDB cluster metrics with Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-oriondb-clusters-metrics |
| Monitor PlayFab title metrics in Azure | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-playfab-titles-metrics |
| Monitor Power BI Dedicated capacity metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-powerbidedicated-capacities-metrics |
| Reference metrics for Copilot Studio in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-powerplatformmonitoringhub-copilotstudio-metrics |
| Use Azure Monitor metrics for Power Platform Monitoring Hub apps | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-powerplatformmonitoringhub-microsoftapp-metrics |
| Reference metrics for Power Apps in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-powerplatformmonitoringhub-powerapps-metrics |
| Reference metrics for Power Automate in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-powerplatformmonitoringhub-powerautomate-metrics |
| Monitor Microsoft Purview account metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-purview-accounts-metrics |
| Use Azure Monitor metrics for Quantum provider accounts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-quantum-provideraccounts-metrics |
| Use Azure Monitor metrics for Recovery Services vaults | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-recoveryservices-vaults-metrics |
| Monitor Azure Relay namespace metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-relay-namespaces-metrics |
| Monitor Azure subscription-level metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-resources-subscriptions-metrics |
| Reference Azure Monitor metrics for SearchServices | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-search-searchservices-metrics |
| Monitor Security Detonation chamber metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-securitydetonation-chambers-metrics |
| Monitor SecurityDetonationChambers metrics in Azure | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-securitydetonation-securitydetonationchambers-metrics |
| Monitor Azure Service Bus namespace metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-servicebus-namespaces-metrics |
| Monitor Service Networking traffic controller metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-servicenetworking-trafficcontrollers-metrics |
| Monitor Azure SignalR Service metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-signalrservice-signalr-metrics |
| Monitor Azure SignalR replica-level metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-signalrservice-signalr-replicas-metrics |
| Monitor Web PubSub service metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-signalrservice-webpubsub-metrics |
| Monitor Web PubSub replica metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-signalrservice-webpubsub-replicas-metrics |
| Monitor Singularity account metrics in Azure | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-singularity-accounts-metrics |
| Monitor SQL Managed Instance metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-sql-managedinstances-metrics |
| Monitor Azure SQL database metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-sql-servers-databases-metrics |
| Monitor Azure SQL elastic pool metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-sql-servers-elasticpools-metrics |
| Monitor SQL job agent metrics in Azure | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-sql-servers-jobagents-metrics |
| Use Azure Monitor metrics for Blob services | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-storage-storageaccounts-blobservices-metrics |
| Use Azure Monitor metrics for File services | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-storage-storageaccounts-fileservices-metrics |
| Use Azure Monitor metrics for Storage accounts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-storage-storageaccounts-metrics |
| Monitor object replication policy metrics in Storage | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-storage-storageaccounts-objectreplicationpolicies-metrics |
| Use Azure Monitor metrics for Queue services | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-storage-storageaccounts-queueservices-metrics |
| Use Azure Monitor metrics for Storage account tasks | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-storage-storageaccounts-storagetasks-metrics |
| Use Azure Monitor metrics for Table services | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-storage-storageaccounts-tableservices-metrics |
| Use Azure Monitor metrics for StorageTasks resources | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-storage-storagetasks-metrics |
| Use Azure Monitor metrics for StorageActions tasks | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-storageactions-storagetasks-metrics |
| Use Azure Monitor metrics for AML filesystems cache | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-storagecache-amlfilesystems-metrics |
| Reference Azure Monitor metrics for StorageCache caches | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-storagecache-caches-metrics |
| Use Azure Monitor metrics for Storage Sync services | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-storagesync-storagesyncservices-metrics |
| Use Azure Monitor metrics for StorageTasks service | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-storagetasks-storagetasks-metrics |
| Use Azure Monitor metrics for Stream Analytics jobs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-streamanalytics-streamingjobs-metrics |
| Use Azure Monitor metrics for Synapse big data pools | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-synapse-workspaces-bigdatapools-metrics |
| Use Azure Monitor metrics for Synapse Kusto pools | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-synapse-workspaces-kustopools-metrics |
| Use Azure Monitor metrics for Synapse workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-synapse-workspaces-metrics |
| Use Azure Monitor metrics for Synapse scope pools | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-synapse-workspaces-scopepools-metrics |
| Use Azure Monitor metrics for Synapse SQL pools | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-synapse-workspaces-sqlpools-metrics |
| Use Azure Monitor metrics for Voice Services communication gateways | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-voiceservices-communicationsgateways-metrics |
| Use Azure Monitor metrics for Container Apps | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-web-containerapps-metrics |
| Use Azure Monitor metrics for App Service hosting environments | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-web-hostingenvironments-metrics |
| Use Azure Monitor metrics for multi-role pools in hosting environments | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-web-hostingenvironments-multirolepools-metrics |
| Use Azure Monitor metrics for worker pools in hosting environments | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-web-hostingenvironments-workerpools-metrics |
| Use Azure Monitor metrics for App Service plans (serverfarms) | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-web-serverfarms-metrics |
| Use Azure Monitor metrics for Web Apps (sites) | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-web-sites-metrics |
| Use Azure Monitor metrics for Web App deployment slots | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-web-sites-slots-metrics |
| Use Azure Monitor metrics for Static Web Apps | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/microsoft-web-staticsites-metrics |
| Use Azure Monitor metrics for NGINX Plus deployments | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/nginx-nginxplus-nginxdeployments-metrics |
| Use Oracle autonomous database metrics in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/oracle-database-autonomousdatabases-metrics |
| Use Azure Monitor metrics for Oracle cloud VM clusters | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/oracle-database-cloudvmclusters-metrics |
| Use Azure Monitor metrics for Oracle DB systems | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/oracle-database-dbsystems-metrics |
| Reference Oracle Exadata VM cluster Azure Monitor metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/oracle-database-exadbvmclusters-metrics |
| Use Azure Monitor metrics for Private Messaging Connectors | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/private-messagingconnectors-connectors-metrics |
| Use Azure Monitor metrics for WANdisco data transfer agents | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/wandisco-fusion-migrators-datatransferagents-metrics |
| Use Azure Monitor metrics for WANdisco live data migrations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/wandisco-fusion-migrators-livedatamigrations-metrics |
| Use Azure Monitor metrics for WANdisco metadata migrations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/wandisco-fusion-migrators-metadatamigrations-metrics |
| Use Azure Monitor metrics for WANdisco Fusion migrators | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/supported-metrics/wandisco-fusion-migrators-metrics |
| Index Azure Monitor tables by log category | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables-category |
| Azure Monitor Log Analytics table field definitions | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables-index |
| Reference Azure Monitor Log Analytics table schemas | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables-index |
| Use AACAudit Azure Monitor table for App Configuration auditing | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aacaudit |
| Analyze Azure App Configuration HTTP request logs in AACHttpRequest | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aachttprequest |
| Use AADAgentRiskEvents Azure AD risk log table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aadagentriskevents |
| Query AADB2CRequestLogs for Azure AD B2C request and throttle data | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aadb2crequestlogs |
| Use AADCustomSecurityAttributeAuditLogs for Entra custom attribute auditing | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aadcustomsecurityattributeauditlogs |
| Use AADDomainServicesDNSAuditsDynamicUpdates for DNS dynamic update tracking | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aaddomainservicesdnsauditsdynamicupdates |
| Use AADDomainServicesDNSAuditsGeneral for DNS server audit events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aaddomainservicesdnsauditsgeneral |
| Understand AADGraphActivityLogs Azure Monitor schema and fields | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aadgraphactivitylogs |
| Use AADNonInteractiveUserSignInLogs table in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aadnoninteractiveusersigninlogs |
| Use AADProvisioningLogs for Azure AD provisioning diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aadprovisioninglogs |
| Query AADRiskyAgents identity protection logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aadriskyagents |
| Query AADRiskyServicePrincipals for Entra risky service principal insights | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aadriskyserviceprincipals |
| Use AADRiskyUsers table for Entra risky user monitoring | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aadriskyusers |
| Analyze service principal risk events via AADServicePrincipalRiskEvents | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aadserviceprincipalriskevents |
| Use AADServicePrincipalSignInLogs for service principal sign-in tracking | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aadserviceprincipalsigninlogs |
| Query AADUserRiskEvents for Entra user risk event analysis | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aaduserriskevents |
| Understand Azure Monitor ABAPAuditLog table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/abapauditlog |
| Query ABAPAuthorizationDetails for SAP role authorization insights | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/abapauthorizationdetails |
| Use ABAPChangeDocsLog table in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/abapchangedocslog |
| Analyze ABAPTableDataLog entries in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/abaptabledatalog |
| Query ABAPUserDetails for SAP user role and profile information | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/abapuserdetails |
| Query ABSBotRequests table for Azure Bot Service telemetry | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/absbotrequests |
| Analyze collaborative resource approvals via ACICollaborationAudit logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acicollaborationaudit |
| Use ACLTransactionLogs table for transaction-related monitoring | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acltransactionlogs |
| Query ACLUserDefinedLogs for custom function and endpoint logging | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acluserdefinedlogs |
| Use ACRConnectedClientList to monitor Redis client connections | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acrconnectedclientlist |
| Analyze Entra authentication events for Azure Cache via ACREntraAuthenticationAuditLog | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acrentraauthenticationauditlog |
| Use ACSAdvancedMessagingOperations logs for Azure Communication Services request monitoring | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acsadvancedmessagingoperations |
| Query ACS auth incoming operations log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acsauthincomingoperations |
| Analyze ACS billing usage with log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acsbillingusage |
| Inspect Call Automation incoming operations logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acscallautomationincomingoperations |
| Use Call Automation media summary logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acscallautomationmediasummary |
| Use ACSCallAutomationStreamingUsage Azure Monitor log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acscallautomationstreamingusage |
| Interpret ACSCallClientMediaStatsTimeSeries log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acscallclientmediastatstimeseries |
| Analyze ACS call client operations log events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acscallclientoperations |
| Use ACSCallClientServiceRequestAndOutcome log table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acscallclientservicerequestandoutcome |
| Use ACS call closed captions summary logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acscallclosedcaptionssummary |
| Query ACS call diagnostics media stream logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acscalldiagnostics |
| Use ACS call diagnostics updates log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acscalldiagnosticsupdates |
| Use ACS aggregated calling metrics log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acscallingmetrics |
| Inspect Call Recording incoming operations logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acscallrecordingincomingoperations |
| Use ACSCallRecordingSummary Azure Monitor log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acscallrecordingsummary |
| Use ACS call summary logs for participants | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acscallsummary |
| Work with ACS call summary updates log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acscallsummaryupdates |
| Query ACS call survey feedback logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acscallsurvey |
| Inspect ACS chat incoming operations logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acschatincomingoperations |
| Use ACSEmailSendMailOperational Azure Monitor log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acsemailsendmailoperational |
| Use ACS email status update operational logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acsemailstatusupdateoperational |
| Inspect ACS email user engagement operational logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acsemailuserengagementoperational |
| Query ACS Job Router incoming operations logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acsjobrouterincomingoperations |
| Analyze ACSOptOutManagementOperations Azure Monitor logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acsoptoutmanagementoperations |
| Inspect ACS rooms incoming operations and summaries | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acsroomsincomingoperations |
| Analyze ACS SMS incoming operations logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/acssmsincomingoperations |
| Inspect ADF Airflow scheduler logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adfairflowschedulerlogs |
| Use ADF Airflow task logs in monitoring | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adfairflowtasklogs |
| Analyze ADF Airflow web logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adfairflowweblogs |
| Inspect ADF Airflow worker logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adfairflowworkerlogs |
| Query ADFS sign-in logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adfssigninlogs |
| Query ADF SSIS integration runtime logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adfssisintegrationruntimelogs |
| Inspect SSIS package event message context logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adfssispackageeventmessagecontext |
| Use SSIS package event messages log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adfssispackageeventmessages |
| Analyze SSIS package executable statistics logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adfssispackageexecutablestatistics |
| Inspect SSIS package execution component phase logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adfssispackageexecutioncomponentphases |
| Use SSIS package execution data statistics logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adfssispackageexecutiondatastatistics |
| Understand ADGSyslogEvent Azure Monitor log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adgsyslogevent |
| Work with ADTDataHistoryOperation Azure Monitor schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adtdatahistoryoperation |
| Query ADTDigitalTwinsOperation logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adtdigitaltwinsoperation |
| Use ADTEventRoutesOperation Azure Monitor log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adteventroutesoperation |
| Analyze ADTModelsOperation Azure Monitor Logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adtmodelsoperation |
| Query ADTQueryOperation logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adtqueryoperation |
| Use ADXCommand Azure Monitor Logs table for diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adxcommand |
| Query ADXDataOperation table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adxdataoperation |
| Use ADXIngestionBatching Azure Monitor Logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adxingestionbatching |
| Query ADXJournal metadata operations log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adxjournal |
| Analyze ADXQuery execution data in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adxquery |
| Analyze ADXTableDetails Azure Monitor log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adxtabledetails |
| Use ADXTableUsageStatistics Azure Monitor schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/adxtableusagestatistics |
| Use AegDataPlaneRequests Azure Monitor logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aegdataplanerequests |
| Inspect AegDeliveryFailureLogs for Event Grid delivery issues | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aegdeliveryfailurelogs |
| Query AegPublishFailureLogs for Event Grid publish errors | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aegpublishfailurelogs |
| Query AEWAssignmentBlobLogs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aewassignmentbloblogs |
| Use AEWAuditLogs schema for Experiment Workspace | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aewauditlogs |
| Analyze AEWComputePipelinesLogs Azure Monitor schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aewcomputepipelineslogs |
| Use AEWExperimentAssignmentSummary log table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aewexperimentassignmentsummary |
| Query AEWExperimentScorecardMetricPairs log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aewexperimentscorecardmetricpairs |
| Work with AEWExperimentScorecards Azure Monitor Logs table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aewexperimentscorecards |
| Query AFSAuditLogs for Azure Managed Lustre auditing | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/afsauditlogs |
| Use AGCAccessLogs to analyze Application Gateway for Containers traffic | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/agcaccesslogs |
| Analyze AGCFirewallLogs schema for WAF events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/agcfirewalllogs |
| Understand Azure Monitor AgentsInfo log table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/agentsinfo |
| Use AggregatedSecurityAlert table for partner security alerts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aggregatedsecurityalert |
| Query AgriFoodApplicationAuditLogs for privileged FarmBeats actions | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/agrifoodapplicationauditlogs |
| Use AgriFoodFarmManagementLogs for FarmBeats resource changes | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/agrifoodfarmmanagementlogs |
| Analyze AgriFoodFarmOperationLogs for FarmBeats operations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/agrifoodfarmoperationlogs |
| Query AgriFoodInsightLogs Azure Monitor table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/agrifoodinsightlogs |
| Use AgriFoodJobProcessedLogs to track FarmBeats job status | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/agrifoodjobprocessedlogs |
| Inspect AgriFoodModelInferenceLogs for AI/ML inference jobs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/agrifoodmodelinferencelogs |
| Query AgriFoodProviderAuthLogs for OAuth provider activity | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/agrifoodproviderauthlogs |
| Use AgriFoodSatelliteLogs for FarmBeats satellite data access | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/agrifoodsatellitelogs |
| Analyze AgriFoodSensorManagementLogs for sensor and device events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/agrifoodsensormanagementlogs |
| Query AgriFoodWeatherLogs for FarmBeats weather ingestion | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/agrifoodweatherlogs |
| Use AGSGrafanaLoginEvents Azure Monitor log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/agsgrafanaloginevents |
| Query AGSGrafanaUsageInsightsEvents log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/agsgrafanausageinsightsevents |
| Use AGSUpdateEvents schema for Grafana dashboard changes | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/agsupdateevents |
| Analyze AGWAccessLogs schema for Application Gateway | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/agwaccesslogs |
| Interpret AGWFirewallLogs schema in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/agwfirewalllogs |
| Query AGWPerformanceLogs schema for gateway instances | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/agwperformancelogs |
| Use AHCIDiagnosticLogs schema for interoperability apps | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ahcidiagnosticlogs |
| Understand AHDSDeidAuditLogs Azure Monitor schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ahdsdeidauditlogs |
| Use AHDSDicomAuditLogs schema for DICOM actions | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ahdsdicomauditlogs |
| Analyze AHDSDicomDiagnosticLogs schema for validation issues | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ahdsdicomdiagnosticlogs |
| Use AHDSMedTechDiagnosticLogs schema for MedTech apps | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ahdsmedtechdiagnosticlogs |
| Use AirflowDagProcessingLogs for ADF Airflow diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/airflowdagprocessinglogs |
| Query AKSAudit Kubernetes API audit log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aksaudit |
| Use AKSAuditAdmin schema for modifying API operations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aksauditadmin |
| Analyze AKSControlPlane diagnostic logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/akscontrolplane |
| Use ALBHealthEvent Azure Monitor load balancer schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/albhealthevent |
| Use AlertEvidence table to inspect entities in alerts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/alertevidence |
| Use AlertInfo table for Defender alert metadata | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/alertinfo |
| Use AMAHealth Azure Monitor Logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/amahealth |
| Analyze AmlComputeCpuGpuUtilization for ML resource usage | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/amlcomputecpugpuutilization |
| Query AmlComputeInstanceEvent for ML compute instance access | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/amlcomputeinstanceevent |
| Query AmlDataLabelEvent for ML data labeling activity | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/amldatalabelevent |
| Use AmlDataSetEvent for dataset access and changes | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/amldatasetevent |
| Query AmlDataStoreEvent for ML datastore operations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/amldatastoreevent |
| Use AmlDeploymentEvent to monitor ML model deployments | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/amldeploymentevent |
| Query AmlEnvironmentEvent for ML environment lifecycle | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/amlenvironmentevent |
| Analyze AmlInferencingEvent for AKS/ACI inference operations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/amlinferencingevent |
| Use AmlModelsEvent to track ML model lifecycle events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/amlmodelsevent |
| Query AmlOnlineEndpointConsoleLog for ML endpoint console output | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/amlonlineendpointconsolelog |
| Query AmlOnlineEndpointEventLog Azure Monitor schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/amlonlineendpointeventlog |
| Use AmlOnlineEndpointTrafficLog for endpoint diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/amlonlineendpointtrafficlog |
| Analyze ML pipeline events with AmlPipelineEvent | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/amlpipelineevent |
| Inspect Azure ML registry reads via AmlRegistryReadEventsLog | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/amlregistryreadeventslog |
| Inspect Azure ML registry writes via AmlRegistryWriteEventsLog | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/amlregistrywriteeventslog |
| Use AmlRunEvent to track ML experiment access | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/amlrunevent |
| Monitor ML run status via AmlRunStatusChangedEvent | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/amlrunstatuschangedevent |
| Use ANFTopClientReadIOPS Azure Monitor logs table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/anftopclientreadiops |
| Use ANFTopClientWriteIOPS Azure Monitor logs table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/anftopclientwriteiops |
| Use ANFTopFileReadIOPS Azure Monitor logs table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/anftopfilereadiops |
| Use ANFTopFileWriteIOPS Azure Monitor logs table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/anftopfilewriteiops |
| Query Sentinel anomaly results from Anomalies table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/anomalies |
| Understand AOIDatabaseQuery Azure Monitor log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/aoidatabasequery |
| Analyze LLM gateway activity with ApiManagementGatewayLlmLog | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/apimanagementgatewayllmlog |
| Monitor MCP requests via ApiManagementGatewayMCPLog | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/apimanagementgatewaymcplog |
| Track WebSocket connections with ApiManagementWebSocketConnectionLogs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/apimanagementwebsocketconnectionlogs |
| Query availability test results via AppAvailabilityResults | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appavailabilityresults |
| Analyze client performance using AppBrowserTimings table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appbrowsertimings |
| Inspect external calls via AppDependencies table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appdependencies |
| Use AppEnvSessionConsoleLogs table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appenvsessionconsolelogs |
| Use AppEnvSessionLifecycleLogs table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appenvsessionlifecyclelogs |
| Use AppEnvSessionPoolEventLogs table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appenvsessionpooleventlogs |
| Use AppEnvSpringAppConsoleLogs table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appenvspringappconsolelogs |
| Query custom events using AppEvents table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appevents |
| Investigate failures via AppExceptions table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appexceptions |
| Understand Azure Monitor AppGenAIContent log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appgenaicontent |
| Work with custom metrics in AppMetrics table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appmetrics |
| Analyze page load data via AppPageViews table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/apppageviews |
| Use AppPerformanceCounters for performance telemetry schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appperformancecounters |
| Inspect Spring build output via AppPlatformBuildLogs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appplatformbuildlogs |
| Monitor Spring containers via AppPlatformContainerEventLogs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appplatformcontainereventlogs |
| Analyze ingress traffic via AppPlatformIngressLogs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appplatformingresslogs |
| Use AppPlatformLogsforSpring for Spring app diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appplatformlogsforspring |
| Review platform behavior via AppPlatformSystemLogs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appplatformsystemlogs |
| Query HTTP requests using AppRequests table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/apprequests |
| Audit antivirus scans via AppServiceAntivirusScanAuditLogs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appserviceantivirusscanauditlogs |
| Capture application logs via AppServiceAppLogs table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appserviceapplogs |
| Audit publishing sign-ins via AppServiceAuditLogs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appserviceauditlogs |
| Monitor auth events via AppServiceAuthenticationLogs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appserviceauthenticationlogs |
| Inspect console output via AppServiceConsoleLogs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appserviceconsolelogs |
| Audit content changes via AppServiceFileAuditLogs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appservicefileauditlogs |
| Analyze HTTP traffic via AppServiceHTTPLogs table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appservicehttplogs |
| Audit IP security events via AppServiceIPSecAuditLogs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appserviceipsecauditlogs |
| Use AppServicePlatformLogs table schema in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appserviceplatformlogs |
| Query AppSystemEvents Application Insights system events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/appsystemevents |
| Work with AppTraces Application Insights trace logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/apptraces |
| Query ArcK8sControlPlane diagnostic logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/arck8scontrolplane |
| Understand ASimAgentEventLogs schema in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/asimagenteventlogs |
| Understand ASimAssetEntityLogs Azure Monitor schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/asimassetentitylogs |
| Understand AWS ALB access log table schema in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/awsalbaccesslogs |
| Understand AWS ELB flow log table schema in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/awselbflowlogs |
| Understand AWS NLB access log table schema in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/awsnlbaccesslogs |
| Understand AZKVAuditLogs schema for Key Vault monitoring | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/azkvauditlogs |
| Use AZKVPolicyEvaluationDetailsLogs for policy evaluation insights | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/azkvpolicyevaluationdetailslogs |
| Query AZMSKafkaUserErrorLogs for Event Hubs diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/azmskafkausererrorlogs |
| Use AZMSOperationalLogs for Event Hubs and Service Bus ops | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/azmsoperationallogs |
| Analyze AZMSRunTimeAuditLogs for Event Hubs and Service Bus | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/azmsruntimeauditlogs |
| Inspect AZMSVnetConnectionEvents for network filtering logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/azmsvnetconnectionevents |
| Query AzureBackupOperations backup operation details | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/azurebackupoperations |
| Monitor AzureLoadTestingOperation resource operations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/azureloadtestingoperation |
| Use AzureMetricsV2 table schema in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/azuremetricsv2 |
| Use AzureMonitorPipelineLogErrors table for pipeline error analysis | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/azuremonitorpipelinelogerrors |
| Use AzureSQLAutomaticTuning Azure Monitor logs table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/azuresqlautomatictuning |
| Analyze AzureSQLBlocks events in Log Analytics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/azuresqlblocks |
| Query AzureSQLDatabaseWaitStatistics logs effectively | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/azuresqldatabasewaitstatistics |
| Inspect AzureSQLDeadlocks data in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/azuresqldeadlocks |
| Work with AzureSQLErrors table in Log Analytics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/azuresqlerrors |
| Use AzureSQLQueryStoreRuntimeStatistics logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/azuresqlquerystoreruntimestatistics |
| Query AzureSQLQueryStoreWaitStatistics log data | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/azuresqlquerystorewaitstatistics |
| Query AzureSQLResourceUsageStats Azure Monitor log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/azuresqlresourceusagestats |
| Use AzureSQLTimeouts Azure Monitor log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/azuresqltimeouts |
| Query CassandraLogs table schema in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/cassandralogs |
| Query CCFApplicationLogs confidential consortium framework logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ccfapplicationlogs |
| Analyze CDBCassandraRequests Cosmos DB Cassandra operations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/cdbcassandrarequests |
| Use CDBControlPlaneRequests for Cosmos DB control operations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/cdbcontrolplanerequests |
| Query CDBDataPlaneRequests Cosmos DB data operations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/cdbdataplanerequests |
| Use CDBDataPlaneRequests15M aggregated Cosmos DB metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/cdbdataplanerequests15m |
| Use CDBDataPlaneRequests5M five-minute Cosmos DB aggregates | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/cdbdataplanerequests5m |
| Analyze CDBGremlinRequests Cosmos DB Graph API operations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/cdbgremlinrequests |
| Query CDBMongoRequests Cosmos DB Mongo API operations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/cdbmongorequests |
| Use CDBPartitionKeyRUConsumption to find hot partitions | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/cdbpartitionkeyruconsumption |
| Analyze CDBPartitionKeyStatistics Cosmos DB storage outliers | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/cdbpartitionkeystatistics |
| Use CDBQueryRuntimeStatistics for Cosmos DB query analysis | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/cdbqueryruntimestatistics |
| Query CDBTableApiRequests Cosmos DB Table API operations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/cdbtableapirequests |
| Use ChaosStudioExperimentEventLogs table in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/chaosstudioexperimenteventlogs |
| Use CIEventsAudit to track Customer Insights API changes | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/cieventsaudit |
| Query CIEventsOperational Customer Insights operational events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/cieventsoperational |
| Analyze CloudAppEvents table for cloud app activities | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/cloudappevents |
| Understand Azure Monitor CloudAuditEvents schema and fields | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/cloudauditevents |
| Analyze CloudDnsEvents with Azure Monitor logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/clouddnsevents |
| Use CloudHsmHardwareOperationAuditLogs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/cloudhsmhardwareoperationauditlogs |
| Use CloudHsmServiceOperationAuditLogs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/cloudhsmserviceoperationauditlogs |
| Query CloudProcessEvents for multicloud process telemetry | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/cloudprocessevents |
| Analyze storage activity via CloudStorageAggregatedEvents | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/cloudstorageaggregatedevents |
| Work with CommonSecurityLog table for security events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/commonsecuritylog |
| Use CommunicationComplianceActivity logs for policy monitoring | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/communicationcomplianceactivity |
| Query ComputerGroup table to scope Azure Monitor logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/computergroup |
| Use ConfidentialWatchlist table in Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/confidentialwatchlist |
| Query ContainerAppConsoleLogs for app container output | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/containerappconsolelogs |
| Use ContainerAppHTTPLogs table for HTTP request analytics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/containerapphttplogs |
| Use ContainerAppSystemLogs for platform diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/containerappsystemlogs |
| Query ContainerEvent table for container events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/containerevent |
| Analyze ContainerInstanceLog table for instance logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/containerinstancelog |
| Use ContainerInventory table for container metadata | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/containerinventory |
| Query ContainerLog table for container stdout/stderr | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/containerlog |
| Use ContainerLogV2 table for Kubernetes container logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/containerlogv2 |
| Use ContainerNetworkLogs table schema in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/containernetworklogs |
| Use ContainerNodeInventory table for host information | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/containernodeinventory |
| Query and interpret CopilotActivity Azure Monitor table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/copilotactivity |
| Work with CrowdStrikeAlerts logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/crowdstrikealerts |
| Query CrowdStrikeAuditEvents table in Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/crowdstrikeauditevents |
| Work with CrowdStrikeCases table in Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/crowdstrikecases |
| Use CrowdStrikeDetections table for security analytics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/crowdstrikedetections |
| Analyze CrowdStrikeHosts table for endpoint inventory | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/crowdstrikehosts |
| Use CrowdStrikeIncidents table for incident correlation | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/crowdstrikeincidents |
| Query CrowdStrikeVulnerabilities table for vulnerability data | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/crowdstrikevulnerabilities |
| Query DatabricksAccounts audit logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksaccounts |
| Analyze DatabricksApps lakehouse apps audit logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksapps |
| Use DatabricksBrickStoreHttpGateway logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksbrickstorehttpgateway |
| Query DatabricksBudgetPolicyCentral audit logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksbudgetpolicycentral |
| Use DatabricksCapsule8Dataplane Azure Monitor log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databrickscapsule8dataplane |
| Use DatabricksClamAVScan Azure Monitor log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksclamavscan |
| Query DatabricksCloudStorageMetadata logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databrickscloudstoragemetadata |
| Use DatabricksClusterLibraries Azure Monitor log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksclusterlibraries |
| Use DatabricksClusterPolicies audit logs table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksclusterpolicies |
| Query DatabricksClusters audit logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksclusters |
| Use DatabricksDashboards logs table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksdashboards |
| Use DatabricksDatabricksSQL audit logs table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksdatabrickssql |
| Analyze DatabricksDataMonitoring logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksdatamonitoring |
| Query DatabricksDataRooms audit logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksdatarooms |
| Inspect DatabricksDBFS audit logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksdbfs |
| Use DatabricksDeltaPipelines Azure Monitor log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksdeltapipelines |
| Query DatabricksFeatureStore operations audit logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksfeaturestore |
| Use DatabricksFiles service audit logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksfiles |
| Analyze DatabricksFilesystem logs table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksfilesystem |
| Query DatabricksGenie support access audit logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksgenie |
| Use DatabricksGitCredentials audit logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksgitcredentials |
| Inspect DatabricksGlobalInitScripts audit logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksglobalinitscripts |
| Query DatabricksGroups audit logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksgroups |
| Use DatabricksIAMRole ACL change audit logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksiamrole |
| Analyze DatabricksIngestion logs table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksingestion |
| Query DatabricksInstancePools audit logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksinstancepools |
| Use DatabricksJobs audit logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksjobs |
| Inspect DatabricksLakeviewConfig audit logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databrickslakeviewconfig |
| Analyze DatabricksLineageTracking logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databrickslineagetracking |
| Inspect DatabricksMarketplaceConsumer logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksmarketplaceconsumer |
| Use DatabricksMarketplaceProvider audit logs table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksmarketplaceprovider |
| Use DatabricksMLflowAcledArtifact audit logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksmlflowacledartifact |
| Query DatabricksMLflowExperiment audit logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksmlflowexperiment |
| Use DatabricksModelRegistry Azure Monitor Logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksmodelregistry |
| Query DatabricksNotebook Azure Monitor Logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksnotebook |
| Use DatabricksOnlineTables Azure Monitor log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksonlinetables |
| Use DatabricksPartnerHub Azure Monitor Logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databrickspartnerhub |
| Inspect DatabricksPredictiveOptimization log table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databrickspredictiveoptimization |
| Use DatabricksRepos Azure Monitor Logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksrepos |
| Use DatabricksServerlessRealTimeInference Logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksserverlessrealtimeinference |
| Work with DatabricksSQL endpoint audit log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databrickssql |
| Use DatabricksUnityCatalog Azure Monitor Logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksunitycatalog |
| Analyze DatabricksVectorSearch audit log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksvectorsearch |
| Inspect DatabricksWebhookNotifications log table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databrickswebhooknotifications |
| Use DatabricksWebTerminal audit logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databrickswebterminal |
| Query DatabricksWorkspace audit log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksworkspace |
| Use DatabricksWorkspaceFiles audit log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/databricksworkspacefiles |
| Understand Azure Monitor DataSetOutput log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/datasetoutput |
| Understand Azure Monitor DataSetRuns log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/datasetruns |
| Understand Azure Monitor DataTransferOperations log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/datatransferoperations |
| Query DataverseActivity audit logs schema in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/dataverseactivity |
| Use DCRLogErrors table to inspect data collection errors | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/dcrlogerrors |
| Use DefenderIoTRawEvent IoT security log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/defenderiotrawevent |
| Use DevCenterAgentHealthLogs table in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/devcenteragenthealthlogs |
| Understand DevCenterBillingEventLogs Azure Monitor schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/devcenterbillingeventlogs |
| Use DevCenterConnectionLogs table in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/devcenterconnectionlogs |
| Query DevCenterDiagnosticLogs dev box operations schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/devcenterdiagnosticlogs |
| Use DevCenterResourceOperationLogs resource health schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/devcenterresourceoperationlogs |
| Use DeviceBehaviorEntities table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/devicebehaviorentities |
| Query DeviceBehaviorInfo table for MDE behaviors | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/devicebehaviorinfo |
| Use DeviceCustomFileEvents table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/devicecustomfileevents |
| Query DeviceCustomImageLoadEvents custom DLL load schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/devicecustomimageloadevents |
| Use DeviceCustomNetworkEvents table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/devicecustomnetworkevents |
| Inspect DeviceCustomProcessEvents custom process events schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/devicecustomprocessevents |
| Query DeviceEvents schema in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/deviceevents |
| Use DeviceFileCertificateInfo schema in log queries | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/devicefilecertificateinfo |
| Analyze file activity with DeviceFileEvents schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/devicefileevents |
| Query DLL load data via DeviceImageLoadEvents | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/deviceimageloadevents |
| Use DeviceInfo table schema for machine data | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/deviceinfo |
| Query sign-in data with DeviceLogonEvents schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/devicelogonevents |
| Leverage DeviceNetworkEvents schema for network logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/devicenetworkevents |
| Use DeviceNetworkInfo schema for endpoint networking | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/devicenetworkinfo |
| Query process activity via DeviceProcessEvents schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/deviceprocessevents |
| Analyze registry changes with DeviceRegistryEvents schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/deviceregistryevents |
| Use DeviceTvmSecureConfigurationAssessment schema for TVM | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/devicetvmsecureconfigurationassessment |
| Query TVM configuration KB via DeviceTvmSecureConfigurationAssessmentKB | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/devicetvmsecureconfigurationassessmentkb |
| Use DeviceTvmSoftwareInventory schema for software lists | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/devicetvmsoftwareinventory |
| Query identity-related events with TVM vulnerabilities schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/devicetvmsoftwarevulnerabilities |
| Use DeviceTvmSoftwareVulnerabilitiesKB schema for CVE data | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/devicetvmsoftwarevulnerabilitieskb |
| Use DiscoveryBookshelfAuditLogs table for auditing | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/discoverybookshelfauditlogs |
| Query DiscoverySupercomputerAuditLogs for operations tracking | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/discoverysupercomputerauditlogs |
| Analyze DiscoveryWorkspaceAuditLogs for workspace activities | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/discoveryworkspaceauditlogs |
| Query DNS server audit logs via DnsAuditEvents schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/dnsauditevents |
| Use DNSQueryLogs table to monitor virtual network DNS | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/dnsquerylogs |
| Query DSMAzureBlobStorageLogs schema in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/dsmazureblobstoragelogs |
| Use DSMDataClassificationLogs table for Purview data | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/dsmdataclassificationlogs |
| Analyze DSMDataLabelingLogs schema in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/dsmdatalabelinglogs |
| Use DurableTaskSchedulerLogs schema for orchestration diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/durabletaskschedulerlogs |
| Query generic Windows events via DynamicEventCollection schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/dynamiceventcollection |
| Query Dynamics365Activity audit logs schema in Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/dynamics365activity |
| Use DynamicSummary schema for Sentinel aggregated findings | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/dynamicsummary |
| Use EdgeActionConsoleLog schema for action debugging | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/edgeactionconsolelog |
| Query EdgeActionServiceLog schema for platform diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/edgeactionservicelog |
| Use EGNFailedHttpDataPlaneOperations Azure Monitor table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/egnfailedhttpdataplaneoperations |
| Analyze failed MQTT connections via EGNFailedMqttConnections schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/egnfailedmqttconnections |
| Use EGNFailedMqttPublishedMessages schema for MQTT diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/egnfailedmqttpublishedmessages |
| Query failed MQTT subscriptions via EGNFailedMqttSubscriptions schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/egnfailedmqttsubscriptions |
| Use EGNMqttDisconnections schema for MQTT session tracking | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/egnmqttdisconnections |
| Use EGNSuccessfulHttpDataPlaneOperations Azure Monitor table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/egnsuccessfulhttpdataplaneoperations |
| Use EGNSuccessfulMqttConnections schema for MQTT auditing | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/egnsuccessfulmqttconnections |
| Use EmailAttachmentInfo schema for O365 attachment analysis | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/emailattachmentinfo |
| Query Office 365 email activity via EmailEvents schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/emailevents |
| Use EmailPostDeliveryEvents schema for post-delivery security | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/emailpostdeliveryevents |
| Query EmailUrlInfo table schema in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/emailurlinfo |
| Use EnrichedMicrosoft365AuditLogs table in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/enrichedmicrosoft365auditlogs |
| Work with Event table from Windows logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/event |
| Query FileMaliciousContentInfo Defender for Office 365 logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/filemaliciouscontentinfo |
| Analyze Azure FunctionAppLogs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/functionapplogs |
| Use GCPApigee audit logs in Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/gcpapigee |
| Query GCPAuditLogs from Google Cloud in Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/gcpauditlogs |
| Analyze GCPCDN audit and traffic logs in Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/gcpcdn |
| Use GCPCloudRun request logs in Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/gcpcloudrun |
| Query GCPCloudSQL audit logs in Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/gcpcloudsql |
| Use GCPComputeEngine audit logs in Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/gcpcomputeengine |
| Analyze GCPDNS query and audit logs in Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/gcpdns |
| Query GCPFirewallLogs network activity in Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/gcpfirewalllogs |
| Use GCPIDS intrusion detection logs in Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/gcpids |
| Analyze GCPLoadBalancer and WAF logs in Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/gcploadbalancer |
| Query GCPMonitoring logs from Cloud Monitoring | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/gcpmonitoring |
| Use GCPNAT audit and traffic logs in Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/gcpnat |
| Query GCPNATAudit Cloud NAT audit logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/gcpnataudit |
| Analyze GCPResourceManager admin and data access logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/gcpresourcemanager |
| Use GCPVPCFlow network flow logs in Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/gcpvpcflow |
| Query GKEAPIServer logs from GKE clusters | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/gkeapiserver |
| Analyze GKEApplication logs for containerized apps | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/gkeapplication |
| Use GKEAudit logs to monitor GKE activity | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/gkeaudit |
| Query GKEControllerManager logs in Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/gkecontrollermanager |
| Analyze GKEHPADecision autoscaling decisions | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/gkehpadecision |
| Use GKEScheduler logs to monitor scheduling | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/gkescheduler |
| Use GoogleWorkspaceReports activity logs in Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/googleworkspacereports |
| Interpret GraphNotificationsActivityLogs schema in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/graphnotificationsactivitylogs |
| Query HDInsightAmbariClusterAlerts for cluster health | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightambariclusteralerts |
| Analyze HDInsightAmbariSystemMetrics node metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightambarisystemmetrics |
| Use HDInsightHadoopAndYarnLogs for cluster troubleshooting | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsighthadoopandyarnlogs |
| Analyze HDInsightHadoopAndYarnMetrics JMX metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsighthadoopandyarnmetrics |
| Query HDInsightHBaseLogs for HBase diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsighthbaselogs |
| Analyze HDInsightHBaseMetrics JMX metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsighthbasemetrics |
| Query HDInsightHiveAndLLAPLogs for Hive diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsighthiveandllaplogs |
| Use HDInsightHiveAndLLAPMetrics Azure Monitor log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsighthiveandllapmetrics |
| Query HDInsightHiveQueryAppStats metrics schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsighthivequeryappstats |
| Use HDInsightHiveTezAppStats Azure Monitor schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsighthivetezappstats |
| Analyze HDInsightJupyterNotebookEvents Spark log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightjupyternotebookevents |
| Work with HDInsightKafkaLogs Azure Monitor schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightkafkalogs |
| Query HDInsightKafkaMetrics metrics table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightkafkametrics |
| Use HDInsightKafkaServerLog table schema in queries | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightkafkaserverlog |
| Analyze HDInsightOozieLogs Azure Monitor schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightoozielogs |
| Use HDInsightRangerAuditLogs security audit schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightrangerauditlogs |
| Query HDInsightSecurityLogs for Ambari and auth events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightsecuritylogs |
| Use HDInsightSparkApplicationEvents table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightsparkapplicationevents |
| Query HDInsightSparkBlockManagerEvents schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightsparkblockmanagerevents |
| Analyze HDInsightSparkEnvironmentEvents log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightsparkenvironmentevents |
| Use HDInsightSparkExecutorEvents Azure Monitor schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightsparkexecutorevents |
| Query HDInsightSparkExtraEvents custom event schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightsparkextraevents |
| Use HDInsightSparkJobEvents table in KQL queries | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightsparkjobevents |
| Analyze HDInsightSparkLogs including Jupyter and Livy | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightsparklogs |
| Query HDInsightSparkSQLExecutionEvents schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightsparksqlexecutionevents |
| Use HDInsightSparkStageEvents stage-level schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightsparkstageevents |
| Analyze HDInsightSparkStageTaskAccumulables metrics schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightsparkstagetaskaccumulables |
| Use HDInsightSparkTaskEvents task telemetry schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightsparktaskevents |
| Query HDInsightStormLogs cluster node log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightstormlogs |
| Use HDInsightStormMetrics cluster metrics schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightstormmetrics |
| Analyze HDInsightStormTopologyMetrics topology schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/hdinsightstormtopologymetrics |
| Use HealthStateChangeEvent workload health schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/healthstatechangeevent |
| Query Heartbeat table for agent health monitoring | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/heartbeat |
| Use IdentityAccountInfo table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/identityaccountinfo |
| Query IdentityDirectoryEvents for directory changes | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/identitydirectoryevents |
| Use IdentityEvents table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/identityevents |
| Use IdentityInfo table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/identityinfo |
| Analyze IdentityLogonEvents for on-prem AD auth | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/identitylogonevents |
| Query IdentityQueryEvents for AD object access | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/identityqueryevents |
| Use IlumioInsights Sentinel connector log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ilumioinsights |
| Use IntuneDeviceComplianceOrg specialist report schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/intunedevicecomplianceorg |
| Query IntuneDevices specialist report table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/intunedevices |
| Use KubeMonAgentEvents table for Kubernetes monitoring | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/kubemonagentevents |
| Query Kubernetes node data in KubeNodeInventory | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/kubenodeinventory |
| Use KubePodInventory for pod and container logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/kubepodinventory |
| Analyze Kubernetes persistent volumes via KubePVInventory | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/kubepvinventory |
| Query Kubernetes services using KubeServices table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/kubeservices |
| Inspect Log Analytics job executions in LAJobLogs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/lajoblogs |
| Understand LAQueryLogs schema for Azure Monitor auditing | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/laquerylogs |
| Monitor summary rule executions via LASummaryLogs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/lasummarylogs |
| Query LedgerTransactionLogs in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ledgertransactionlogs |
| Query LedgerUserDefinedLogs in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ledgeruserdefinedlogs |
| Understand LIATrackingEvents Azure Monitor log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/liatrackingevents |
| Use LogicAppWorkflowRuntime logs for workflow diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/logicappworkflowruntime |
| Use MCCEventLogs for cache performance monitoring | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/mcceventlogs |
| Audit MCVP service transactions via MCVPAuditLogs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/mcvpauditlogs |
| Monitor MCVP operations with MCVPOperationLogs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/mcvpoperationlogs |
| Query MDCDetectionDNSEvents schema in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/mdcdetectiondnsevents |
| Use MDCDetectionFimEvents table for security analytics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/mdcdetectionfimevents |
| Analyze MDCDetectionGatingValidationEvents Kubernetes logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/mdcdetectiongatingvalidationevents |
| Work with MDCDetectionK8SApiEvents in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/mdcdetectionk8sapievents |
| Use MDCDetectionProcessV2Events table in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/mdcdetectionprocessv2events |
| Use MDCFileIntegrityMonitoringEvents table in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/mdcfileintegritymonitoringevents |
| Inspect MDPResourceLog for Managed DevOps Pool events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/mdpresourcelog |
| Query MeshControlPlane Istiod logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/meshcontrolplane |
| Use MessageEvents Azure Monitor Logs table fields | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/messageevents |
| Use MessagePostDeliveryEvents Azure Monitor Logs table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/messagepostdeliveryevents |
| Use MessageUrlInfo Azure Monitor Logs table fields | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/messageurlinfo |
| Query Azure Data Transfer connection logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-azuredatatransfer-connections |
| Use Chaos Studio experiment logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-chaos-experiments |
| Analyze Azure Communication Services logs with Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-communication-communicationservices |
| Understand Azure Monitor table schema for PostgreSQL servers | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-dbforpostgresql-serversv2 |
| Use Azure Monitor tables for AVD application groups | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-desktopvirtualization-applicationgroups |
| Monitor Azure Virtual Desktop host pools with tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-desktopvirtualization-hostpools |
| Use Azure Monitor tables for AVD workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-desktopvirtualization-workspaces |
| Azure Monitor table schema for DevCenter devcenters | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-devcenter-devcenters |
| Monitor IoT Hubs using Azure Monitor tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-devices-iothubs |
| Azure Monitor tables for IoT provisioning services | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-devices-provisioningservices |
| Monitor Managed DevOps Pools with Azure tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-devopsinfrastructure-pools |
| Azure Monitor tables for Azure Digital Twins instances | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-digitaltwins-digitaltwinsinstances |
| Audit Microsoft Discovery bookshelves with Monitor tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-discovery-bookshelves |
| Track Microsoft Discovery supercomputer operations via logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-discovery-supercomputers |
| Monitor Microsoft Discovery workspaces with audit tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-discovery-workspaces |
| Azure Monitor tables for Cassandra clusters in Cosmos DB | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-documentdb-cassandraclusters |
| Monitor Cosmos DB database accounts with Azure tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-documentdb-databaseaccounts |
| Azure Monitor tables for MongoDB vCore clusters | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-documentdb-mongoclusters |
| Use Azure Monitor tables for Durable Task schedulers | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-durabletask-schedulers |
| Use Azure Monitor microsoft.edge diagnostics table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-edge-diagnostics |
| Use Azure Monitor tables for Event Grid domains | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-eventgrid-domains |
| Monitor Event Grid namespaces with diagnostic tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-eventgrid-namespaces |
| Use Azure Monitor tables for Event Grid partner namespaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-eventgrid-partnernamespaces |
| Monitor Event Grid partner topics delivery failures | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-eventgrid-partnertopics |
| Monitor Event Grid system topics with failure logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-eventgrid-systemtopics |
| Use Azure Monitor tables for Event Grid topics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-eventgrid-topics |
| Azure Monitor tables for Event Hubs namespaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-eventhub-namespaces |
| Use Azure Monitor experiment workspace table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-experimentation-experimentworkspaces |
| Use Azure Monitor tables for Cloud HSM clusters | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-hardwaresecuritymodules-cloudhsmclusters |
| Use Azure Monitor tables for HDInsight clusters | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-hdinsight-clusters |
| Monitor Healthcare Interoperability applications via logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-healthcareinterop-workspaces |
| Interpret Azure Monitor logs for Health Data AI de-id | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-healthdataaiservices-deidservices |
| Monitor hybrid Kubernetes provisioned clusters with tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-hybridcontainerservice-provisionedclusters |
| Azure Monitor tables for autoscale settings resources | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-insights-autoscalesettings |
| Understand Application Insights Azure Monitor table schemas | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-insights-components |
| Use InsightsMetrics for workload monitoring solutions | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-insights-workloadmonitoring |
| Use Azure Monitor tables for Key Vault auditing | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-keyvault-vaults |
| Use Azure Monitor tables for Azure Data Explorer clusters | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-kusto-clusters |
| Analyze Azure Load Testing logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-loadtestservice-loadtests |
| Query Azure Monitor logs for Logic Apps integration accounts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-logic-integrationaccounts |
| Monitor Logic Apps workflows using Azure Monitor tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-logic-workflows |
| Audit Azure ML registries with Azure Monitor tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-machinelearningservices-registries |
| Use Azure Monitor tables for Azure ML workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-machinelearningservices-workspaces |
| Monitor managed network fabric devices with Azure Monitor tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-managednetworkfabric-networkdevices |
| Analyze Azure Media Services diagnostics via Azure Monitor tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-media-mediaservices |
| Review Azure Monitor workspace metrics usage tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-monitor-accounts |
| Use Azure Monitor tables for NetApp capacity pool IOPS analysis | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-netapp-netappaccounts-capacitypools |
| Monitor Azure Application Gateway and WAF logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-network-applicationgateways |
| Analyze Azure Firewall application, DNS, and flow logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-network-azurefirewalls |
| Use Azure Monitor tables for Bastion host auditing and metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-network-bastionhosts |
| Monitor DNS resolver policies with Azure Monitor query logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-network-dnsresolverpolicies |
| Monitor ExpressRoute circuits with Azure Monitor tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-network-expressroutecircuits |
| Use Azure Monitor tables for Front Door activity and metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-network-frontdoors |
| Monitor Azure Load Balancer health with Azure Monitor tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-network-loadbalancers |
| Use Azure Monitor tables for network interface activity and metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-network-networkinterfaces |
| Audit Azure Virtual Network Manager configurations with log tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-network-networkmanagers |
| Monitor network security groups with Azure Monitor tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-network-networksecuritygroups |
| Audit Network Security Perimeter inbound access logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-network-networksecurityperimeters |
| Collect syslog and metrics for network virtual appliances | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-network-networkvirtualappliances |
| Use Connection Monitor tables for network diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-network-networkwatchers-connectionmonitors |
| Monitor public IP addresses with Azure Monitor tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-network-publicipaddresses |
| Use Azure Monitor tables for Traffic Manager profiles | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-network-trafficmanagerprofiles |
| Monitor virtual network gateways with Azure Monitor tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-network-virtualnetworkgateways |
| Use Azure Monitor tables for virtual network activity and metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-network-virtualnetworks |
| Monitor VPN gateways with Azure Monitor tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-network-vpngateways |
| Use Azure Monitor tables for Network Analytics data products | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-networkanalytics-dataproducts |
| Track Nexus cluster manager deployments with Azure Monitor tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-networkcloud-clustermanagers |
| Monitor Nexus clusters with Kubernetes and hardware logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-networkcloud-clusters |
| Use Azure Monitor tables for Nexus storage appliance alerts and audits | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-networkcloud-storageappliances |
| Analyze Azure Traffic Collector IPFIX flows and metadata | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-networkfunction-azuretrafficcollectors |
| Use Azure Monitor tables for Online Experiment Workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-onlineexperimentation-workspaces |
| Use Azure Monitor tables for Energy Data Services diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-openenergyplatform-energyservices |
| Monitor Open Logistics Platform workspaces and events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-openlogisticsplatform-workspaces |
| Reference Azure Monitor tables for Log Analytics workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-operationalinsights-workspaces |
| Use Azure Monitor tables for Orbital geocatalog logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-orbital-geocatalogs |
| Query Azure Monitor logs for PlayFab titles | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-playfab-titles |
| Use Azure Monitor tables for Power BI tenants | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-powerbi-tenants |
| Monitor Power BI workspaces with Azure Monitor tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-powerbi-tenants-workspaces |
| Azure Monitor table schema for Power BI Dedicated | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-powerbidedicated-capacities |
| Azure Monitor tables for Microsoft Purview accounts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-purview-accounts |
| Log schema for Azure Quantum provider accounts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-quantum-provideraccounts |
| Log schema for Azure Quantum workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-quantum-workspaces |
| Analyze Azure Site Recovery jobs via Monitor tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-recoveryservices-vaults |
| Monitor Azure Relay namespaces with log tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-relay-namespaces |
| Azure Monitor tables for SCVMM virtual machines | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-scvmm-virtualmachines |
| Azure Monitor tables for Azure Cognitive Search services | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-search-searchservices |
| Defender for Storage malware scan logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-security-defenderforstoragesettings |
| Query Defender for Cloud attack path tables in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-security-security |
| Sentinel normalized agent event logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-securityinsights-agenteventnormalized |
| Sentinel normalized alert events table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-securityinsights-alerteventnormalized |
| ASIM normalized security tables in Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-securityinsights-asimtables |
| Sentinel normalized asset entity events schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-securityinsights-assetentitynormalized |
| Sentinel normalized audit events table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-securityinsights-auditeventnormalized |
| Sentinel normalized authentication events schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-securityinsights-authenticationevent |
| CEF events collection table in Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-securityinsights-cef |
| ASIM DNS activity normalized schema in Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-securityinsights-dnsnormalized |
| Sentinel network session normalized logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-securityinsights-networksessionnormalized |
| Sentinel process event normalized logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-securityinsights-processeventnormalized |
| Purview data sensitivity logs in Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-securityinsights-purview |
| Microsoft Sentinel security insights and alerts tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-securityinsights-securityinsights |
| Threat intelligence tables and STIX schema in Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-securityinsights-threatintelligence |
| ASIM web session normalized logs schema in Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-securityinsights-websessionlogs |
| Azure Monitor tables for Service Bus and Event Hubs namespaces | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-servicebus-namespaces |
| Azure Monitor tables for Service Fabric clusters | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-servicefabric-clusters |
| Use Azure Monitor tables for traffic controllers | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-servicenetworking-trafficcontrollers |
| Azure SignalR Service diagnostics tables in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-signalrservice-signalr |
| Azure Web PubSub connectivity and HTTP logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-signalrservice-webpubsub |
| Azure Monitor tables for SQL managed instances | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-sql-managedinstances |
| Azure SQL servers diagnostic and metric tables schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-sql-servers |
| Azure Monitor tables for Azure SQL databases | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-sql-servers-databases |
| Execution and request logs for StandbyContainerGroupPools | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-standbypool-standbycontainergrouppools |
| Execution and request logs for StandbyVirtualMachinePools | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-standbypool-standbyvirtualmachinepools |
| Azure Storage accounts activity, metric, and service log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-storage-storageaccounts |
| Query Azure Managed Lustre monitoring tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-storagecache-amlfilesytems |
| Azure HPC Cache API, firmware, and warning logs schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-storagecache-caches |
| Use Azure Monitor tables for Storage Mover resources | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-storagemover-storagemovers |
| Query Azure Monitor tables for Stream Analytics jobs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-streamanalytics-streamingjobs |
| Monitor Synapse workspaces with Azure Monitor tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-synapse-workspaces |
| Analyze Time Series Insights environment logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-timeseriesinsights-environments |
| Analyze Toolchain Orchestrator diagnostics tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-toolchainorchestrator-diagnostics |
| Monitor Video Indexer accounts with Azure Monitor logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-videoindexer-accounts |
| Use Azure Monitor tables for App Service sites | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-web-sites |
| Monitor Workload Monitor resources via Azure Monitor tables | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-workloadmonitor-monitors |
| Use Azure Monitor tables for Zero Trust Segmentation | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoft-zerotrustsegmentation-segmentationmanagers |
| Use MicrosoftDataShareReceivedSnapshotLog for consumer sync | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoftdatasharereceivedsnapshotlog |
| Use MicrosoftDataShareSentSnapshotLog for provider sync | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoftdatasharesentsnapshotlog |
| Query MicrosoftDataShareShareLog for share operations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoftdatasharesharelog |
| Analyze MicrosoftGraphActivityLogs for Graph API requests | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoftgraphactivitylogs |
| Query MicrosoftGraphPolicyLogs Azure Monitor table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoftgraphpolicylogs |
| Use MicrosoftHealthcareApisAuditLogs for FHIR auditing | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsofthealthcareapisauditlogs |
| Query MicrosoftPurviewInformationProtection audit logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoftpurviewinformationprotection |
| Analyze MicrosoftServicePrincipalSignInLogs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/microsoftserviceprincipalsigninlogs |
| Analyze MNFDeviceUpdates for Nexus hardware status | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/mnfdeviceupdates |
| Use MNFSystemSessionHistoryUpdates for Nexus sessions | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/mnfsystemsessionhistoryupdates |
| Query MNFSystemStateMessageUpdates for Nexus state changes | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/mnfsystemstatemessageupdates |
| Understand MPCAuditLogs schema in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/mpcauditlogs |
| Use MPCIngestionLogs table in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/mpcingestionlogs |
| Use MySqlAuditLogs for Azure Database for MySQL auditing | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/mysqlauditlogs |
| Analyze MySqlSlowLogs for slow query diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/mysqlslowlogs |
| Use NCBMBreakGlassAuditLogs for Nexus break-glass access | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ncbmbreakglassauditlogs |
| Analyze NCBMSecurityDefenderLogs for Nexus security events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ncbmsecuritydefenderlogs |
| Use NCBMSecurityLogs for Nexus Baremetal security auditing | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ncbmsecuritylogs |
| Query NCBMSystemLogs for Nexus Baremetal syslog events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ncbmsystemlogs |
| Analyze NCCIDRACLogs for Nexus hardware failures | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/nccidraclogs |
| Understand NCCKubernetesAPIAuditLogs Azure Monitor schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ncckubernetesapiauditlogs |
| Query NCCKubernetesLogs for Nexus container workloads | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ncckuberneteslogs |
| Analyze NCCPlatformOperationsLogs for Nexus undercloud events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/nccplatformoperationslogs |
| Use NCCVMOrchestrationLogs for Nexus VM orchestration | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/nccvmorchestrationlogs |
| Query NCMClusterOperationsLogs for Nexus cluster lifecycle | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ncmclusteroperationslogs |
| Use NCSStorageAlerts for Nexus storage alert monitoring | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ncsstoragealerts |
| Analyze NCSStorageAudits for Nexus storage access auditing | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ncsstorageaudits |
| Query NCSStorageLogs for Nexus storage system events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ncsstoragelogs |
| Query NetworkAccessAlerts for network access issues | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/networkaccessalerts |
| Analyze NetworkAccessConnectionEvents in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/networkaccessconnectionevents |
| Analyze NetworkAccessGenerativeAIInsights interaction logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/networkaccessgenerativeaiinsights |
| Use NetworkAccessTraffic Azure Monitor Logs table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/networkaccesstraffic |
| Use NetworkSessions table for session analytics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/networksessions |
| Analyze NGINXaaS deployment logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/nginx-nginxplus-nginxdeployments |
| Query NginxUpstreamUpdateLogs from NGINXaaS | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/nginxupstreamupdatelogs |
| Use NGXOperationLogs for NGINXaaS access and error logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ngxoperationlogs |
| Analyze NGXSecurityLogs for NGINXaaS security events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ngxsecuritylogs |
| Use NSPAccessLogs for Network Security Perimeter access | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/nspaccesslogs |
| Use NTAInsights Azure Monitor Logs table for traffic analytics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ntainsights |
| Query NTAIpDetails Traffic Analytics WHOIS data | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ntaipdetails |
| Use NTANetAnalytics table for flow log insights | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ntanetanalytics |
| Use NTANspRuleRecommendation Azure Monitor log table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ntansprulerecommendation |
| Use NTARuleRecommendation Azure Monitor Logs table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ntarulerecommendation |
| Query NTATopologyDetails for network topology data | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ntatopologydetails |
| Analyze NWConnectionMonitorDestinationListenerResult logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/nwconnectionmonitordestinationlistenerresult |
| Query NWConnectionMonitorDNSResult logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/nwconnectionmonitordnsresult |
| Query NWConnectionMonitorPathResult for path analysis | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/nwconnectionmonitorpathresult |
| Use NWConnectionMonitorTestResult for test outcomes | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/nwconnectionmonitortestresult |
| Query OAuthAppInfo Azure Monitor log table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/oauthappinfo |
| Analyze OEPAirFlowTask diagnostic task logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/oepairflowtask |
| Query OEPAuditLogs for Energy Data Services | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/oepauditlogs |
| Use OEPDataplaneLogs for Indexer Service HTTP tracing | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/oepdataplanelogs |
| Analyze OEPElasticOperator logs for cluster operations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/oepelasticoperator |
| Query OEPElasticsearch diagnostic cluster logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/oepelasticsearch |
| Work with OEWAuditLogs table in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/oewauditlogs |
| Query OEWExperimentAssignmentSummary variant data | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/oewexperimentassignmentsummary |
| Analyze OEWExperimentScorecardMetricPairs metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/oewexperimentscorecardmetricpairs |
| Query OEWExperimentScorecards table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/oewexperimentscorecards |
| Query OfficeActivity for Microsoft 365 audit logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/officeactivity |
| Use OktaSystemLogs table in Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/oktasystemlogs |
| Use OLPSupplyChainEntityOperations for entity changes | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/olpsupplychainentityoperations |
| Query OLPSupplyChainEvents for workspace events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/olpsupplychainevents |
| Query Operation table for workspace activities | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/operation |
| Use Azure Monitor tables for Oracle cloud VM clusters | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/oracle-database-cloudvmclusters |
| Use OracleCloudDatabase table for Oracle events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/oracleclouddatabase |
| Use OTelEvents table for OpenTelemetry span events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/otelevents |
| Understand Azure Monitor OTelLogs table schema and fields | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/otellogs |
| Analyze OTelResources attributes for telemetry sources | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/otelresources |
| Use OTelSpans table for distributed tracing spans | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/otelspans |
| Query OTelTraces for OpenTelemetry trace data | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/oteltraces |
| Use OTelTracesAgent for agent-based trace logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/oteltracesagent |
| Use PerfInsightsFindings Azure Monitor Logs table fields | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/perfinsightsfindings |
| Use PerfInsightsImpactedResources Azure Monitor Logs table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/perfinsightsimpactedresources |
| Use PerfInsightsRun Azure Monitor Logs table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/perfinsightsrun |
| Query PFTitleAuditLogs for PlayFab title actions | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/pftitleauditlogs |
| Analyze PGSQLAutovacuumStats for PostgreSQL autovacuum | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/pgsqlautovacuumstats |
| Use PGSQLDbTransactionsStats for transaction limits | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/pgsqldbtransactionsstats |
| Query PGSQLPgBouncer logs for connection pooling | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/pgsqlpgbouncer |
| Use PGSQLPgStatActivitySessions Azure Monitor logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/pgsqlpgstatactivitysessions |
| Query PGSQLQueryStoreQueryText logs for PostgreSQL | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/pgsqlquerystorequerytext |
| Analyze PGSQLQueryStoreRuntime metrics in logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/pgsqlquerystoreruntime |
| Work with PGSQLQueryStoreWaits wait statistics logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/pgsqlquerystorewaits |
| Use PGSQLServerLogs table for PostgreSQL diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/pgsqlserverlogs |
| Query PowerAppsActivity audit logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/powerappsactivity |
| Use PowerAutomateActivity table for flow auditing | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/powerautomateactivity |
| Query and interpret PowerBIActivity log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/powerbiactivity |
| Monitor tenant datasets with PowerBIDatasetsTenant logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/powerbidatasetstenant |
| Monitor workspace datasets with PowerBIDatasetsWorkspace logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/powerbidatasetsworkspace |
| Query PowerPlatformAdminActivity administrative audit logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/powerplatformadminactivity |
| Use PowerPlatformConnectorActivity logs for connector auditing | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/powerplatformconnectoractivity |
| Analyze PowerPlatformDlpActivity DLP admin logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/powerplatformdlpactivity |
| Understand PreAuthenticationDiscoveryLogs table schema in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/preauthenticationdiscoverylogs |
| Query ProjectActivity audit logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/projectactivity |
| Query PurviewDataSensitivityLogs for classified data insights | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/purviewdatasensitivitylogs |
| Monitor scan progress with PurviewScanStatusLogs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/purviewscanstatuslogs |
| Audit Purview account changes with PurviewSecurityLogs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/purviewsecuritylogs |
| Query QualysKnowledgeBase vulnerabilities in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/qualysknowledgebase |
| Use QuantumProviderAccountJobAuditLogs table in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/quantumprovideraccountjobauditlogs |
| Use QuantumProviderAccountQueueAuditLogs table in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/quantumprovideraccountqueueauditlogs |
| Use QuantumProviderAccountTargetAuditLogs table in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/quantumprovideraccounttargetauditlogs |
| Use QuantumWorkspaceJobAuditLogs table in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/quantumworkspacejobauditlogs |
| Use Rapid7InsightVMCloudAssets table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/rapid7insightvmcloudassets |
| Use Rapid7InsightVMCloudVulnerabilities table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/rapid7insightvmcloudvulnerabilities |
| Analyze REDConnectionEvents for Redis Enterprise connections | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/redconnectionevents |
| Monitor remote network health with RemoteNetworkHealthLogs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/remotenetworkhealthlogs |
| Analyze ResourceManagementPublicAccessLogs for private link impact | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/resourcemanagementpublicaccesslogs |
| Use RetinaNetworkFlowLogs for container network monitoring | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/retinanetworkflowlogs |
| Use SalesforceAuditTrail table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/salesforceaudittrail |
| Query SalesforceLoginHistory data in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/salesforceloginhistory |
| Use SCGPoolExecutionLog for StandbyContainerGroupPool auditing | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/scgpoolexecutionlog |
| Analyze SCGPoolRequestLog for StandbyContainerGroupPool requests | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/scgpoolrequestlog |
| Query SecureScoreControls for control-level security posture | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/securescorecontrols |
| Use SecureScores table for subscription security scoring | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/securescores |
| Use SecurityAttackPathData log table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/securityattackpathdata |
| Use SecurityCaseEvent table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/securitycaseevent |
| Use SecurityEvent table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/securityevent |
| Work with SecurityIncident Azure Monitor log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/securityincident |
| Use SecurityIoTRawEvent table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/securityiotrawevent |
| Use SecurityNestedRecommendation table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/securitynestedrecommendation |
| Use SecurityRegulatoryCompliance table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/securityregulatorycompliance |
| Use SentinelAlibabaCloudAPIGatewayLogs table schema in KQL | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/sentinelalibabacloudapigatewaylogs |
| Query SentinelAlibabaCloudVPCFlowLogs table fields | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/sentinelalibabacloudvpcflowlogs |
| Work with SentinelAlibabaCloudWAFLogs table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/sentinelalibabacloudwaflogs |
| Use SentinelAudit table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/sentinelaudit |
| Use SentinelBehaviorEntities table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/sentinelbehaviorentities |
| Understand SentinelBehaviorInfo Azure Monitor log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/sentinelbehaviorinfo |
| Use SentinelHealth table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/sentinelhealth |
| Analyze SentinelImpervaWAFCloudV2Logs table in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/sentinelimpervawafcloudv2logs |
| Interpret Azure SignalR diagnostic log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/signalrservicediagnosticlogs |
| Use SqlAtpStatus Azure Monitor log schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/sqlatpstatus |
| Use SQLSecurityAuditEvents for Synapse SQL auditing | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/sqlsecurityauditevents |
| Use SqlVulnerabilityAssessmentScanStatus table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/sqlvulnerabilityassessmentscanstatus |
| Use StorageBlobLogs table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/storagebloblogs |
| Use StorageCacheOperationEvents table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/storagecacheoperationevents |
| Use StorageCacheUpgradeEvents table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/storagecacheupgradeevents |
| Use StorageCacheWarningEvents table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/storagecachewarningevents |
| Use StorageFileLogs table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/storagefilelogs |
| Use StorageMalwareScanningResults table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/storagemalwarescanningresults |
| Understand Azure Monitor StorageMoverAuditLogs schema and fields | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/storagemoverauditlogs |
| Interpret StorageMoverCopyLogsFailed Azure Monitor table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/storagemovercopylogsfailed |
| Interpret StorageMoverCopyLogsTransferred Azure Monitor table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/storagemovercopylogstransferred |
| Use StorageMoverJobRunLogs table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/storagemoverjobrunlogs |
| Use StorageQueueLogs table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/storagequeuelogs |
| Use StorageTableLogs table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/storagetablelogs |
| Analyze SVMPoolExecutionLog for Standby VM pool operations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/svmpoolexecutionlog |
| Use SVMPoolRequestLog for Standby VM pool request tracking | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/svmpoolrequestlog |
| Use SynapseBigDataPoolApplicationsEnded table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/synapsebigdatapoolapplicationsended |
| Use SynapseBuiltinSqlPoolRequestsEnded table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/synapsebuiltinsqlpoolrequestsended |
| Use SynapseDXCommand table in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/synapsedxcommand |
| Use SynapseDXFailedIngestion Azure Monitor logs for diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/synapsedxfailedingestion |
| Query SynapseDXIngestionBatching logs for batch statistics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/synapsedxingestionbatching |
| Analyze SynapseDXQuery execution with Azure Monitor logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/synapsedxquery |
| Use SynapseDXSucceededIngestion logs to track ingestions | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/synapsedxsucceededingestion |
| Inspect SynapseDXTableDetails logs for table metadata | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/synapsedxtabledetails |
| Monitor Synapse table usage with SynapseDXTableUsageStatistics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/synapsedxtableusagestatistics |
| Query SynapseGatewayApiRequests logs for API monitoring | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/synapsegatewayapirequests |
| Analyze Synapse integration activity runs via logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/synapseintegrationactivityruns |
| Monitor Synapse integration pipeline runs with logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/synapseintegrationpipelineruns |
| Track Synapse integration trigger runs using logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/synapseintegrationtriggerruns |
| Use SynapseLinkEvent logs to monitor Synapse Link status | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/synapselinkevent |
| Review completed SCOPE jobs with SynapseScopePoolScopeJobsEnded logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/synapsescopepoolscopejobsended |
| Track SCOPE job state changes via SynapseScopePoolScopeJobsStateChange | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/synapsescopepoolscopejobsstatechange |
| Inspect DMS worker activity in SynapseSqlPoolDmsWorkers logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/synapsesqlpooldmsworkers |
| Analyze SQL requests with SynapseSqlPoolExecRequests logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/synapsesqlpoolexecrequests |
| Examine SQL request steps via SynapseSqlPoolRequestSteps logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/synapsesqlpoolrequeststeps |
| Monitor query distributions with SynapseSqlPoolSqlRequests logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/synapsesqlpoolsqlrequests |
| Investigate wait states using SynapseSqlPoolWaits logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/synapsesqlpoolwaits |
| Query Linux Syslog events in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/syslog |
| Track Threat Intelligence export operations via logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/threatintelexportoperation |
| Query STIX indicators using ThreatIntelIndicators logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/threatintelindicators |
| Analyze ThreatIntelligenceIndicator logs for security indicators | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/threatintelligenceindicator |
| Use ThreatIntelObjects logs for generic STIX object data | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/threatintelobjects |
| Audit Toolchain orchestrator interactions with TOUserAudits logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/touseraudits |
| Monitor Time Series Insights ingress errors with TSIIngress logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/tsiingress |
| Analyze Update Compliance device data with UCClient logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ucclient |
| Check device readiness using UCClientReadinessStatus logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ucclientreadinessstatus |
| Query UCClientUpdateStatus Azure Monitor logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ucclientupdatestatus |
| Query UCDeviceAlert table for update alerts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ucdevicealert |
| Analyze UCDOAggregatedStatus delivery optimization logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ucdoaggregatedstatus |
| Understand UCDOStatus Azure Monitor log table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ucdostatus |
| Use UCServiceUpdateStatus for service-side update logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ucserviceupdatestatus |
| Query UCUpdateAlert for client and service alerts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ucupdatealert |
| Query UrlClickEvents for Defender for Office 365 | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/urlclickevents |
| Use Usage table to analyze Azure Monitor workspace usage | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/usage |
| Query UserAccessAnalytics for Azure resource access paths | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/useraccessanalytics |
| Use UserPeerAnalytics to analyze user peer relationships | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/userpeeranalytics |
| Query VCoreMongoRequests for MongoDB vCore requests | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/vcoremongorequests |
| Use VIAudit table for Video Indexer audit logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/viaudit |
| Query VIIndexing for Video Indexer indexing logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/viindexing |
| Analyze open server ports with VMBoundPort logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/vmboundport |
| Use VMComputer table for VM inventory data | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/vmcomputer |
| Query VMConnection for VM network traffic logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/vmconnection |
| Use VMProcess table for server process telemetry | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/vmprocess |
| Query W3CIISLog for IIS web server logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/w3ciislog |
| Query Watchlist table data in Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/watchlist |
| Use WebPubSubConnectivity logs for connection diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/webpubsubconnectivity |
| Inspect WebPubSubHttpRequest logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/webpubsubhttprequest |
| Leverage WebPubSubMessaging logs for message tracing | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/webpubsubmessaging |
| Work with Windows365AuditLogs table in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/windows365auditlogs |
| Query WindowsEvent table for collected Windows events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/windowsevent |
| Query WireData network telemetry in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/wiredata |
| Use WorkloadDiagnosticLogs for monitoring VM diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/workloaddiagnosticlogs |
| Use WOUserAudits Azure Monitor Logs table for auditing | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/wouseraudits |
| Use WVDAgentHealthStatus for AVD agent health monitoring | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/wvdagenthealthstatus |
| Analyze AVD autoscale evaluations with WVDAutoscaleEvaluationPooled | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/wvdautoscaleevaluationpooled |
| Query WVDCheckpoints for Windows Virtual Desktop checkpoints | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/wvdcheckpoints |
| Use WVDConnectionGraphicsDataPreview for AVD graphics telemetry | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/wvdconnectiongraphicsdatapreview |
| Query WVDConnectionNetworkData for AVD network metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/wvdconnectionnetworkdata |
| Use WVDConnections table for AVD connection activity | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/wvdconnections |
| Query WVDErrors for Azure Virtual Desktop error activity | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/wvderrors |
| Use WVDFeeds table for Windows Virtual Desktop feed activity | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/wvdfeeds |
| Query WVDHostRegistrations for AVD host registration logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/wvdhostregistrations |
| Use WVDManagement table for AVD management activity logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/wvdmanagement |
| Query WVDMultiLinkAdd for AVD MultiLink add activity | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/wvdmultilinkadd |
| Use WVDSessionHostManagement for AVD session host management logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/wvdsessionhostmanagement |
| Understand ZTSGraph Azure Monitor log table schema | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ztsgraph |
| Use ZTSJobStatus Azure Monitor log table fields | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ztsjobstatus |
| Query ZTSMetadata Azure Monitor log table columns | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ztsmetadata |
| Understand Azure Monitor ZTSRequest log schema and fields | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/tables/ztsrequest |
| Enable Snapshot Debugger for .NET apps on Azure App Service | https://learn.microsoft.com/en-us/azure/azure-monitor/snapshot-debugger/snapshot-debugger-app-service |
| Configure Snapshot Debugger for .NET in Azure Functions | https://learn.microsoft.com/en-us/azure/azure-monitor/snapshot-debugger/snapshot-debugger-function-app |
| Enable Snapshot Debugger on Service Fabric, Cloud Services, and VMs | https://learn.microsoft.com/en-us/azure/azure-monitor/snapshot-debugger/snapshot-debugger-vm |
| Create Azure Monitor workbooks using ARM templates | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/resource-manager-workbooks |
| Define Azure Monitor workbooks via ARM templates | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-automate |
| Customize chart visualizations in Azure Workbooks | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-chart-visualizations |
| Render composite bar metrics in Azure Workbooks | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-composite-bar |
| Use Copilot to build Azure Workbooks | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-copilot-overview |
| Configure Azure Workbooks data source connections | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-data-sources |
| Use dropdown parameters in Azure Workbooks | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-dropdowns |
| Create graph relationship visualizations in Workbooks | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-graph-visualizations |
| Configure grid visualizations in Azure Workbooks | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-grid-visualizations |
| Configure honeycomb visualizations in Azure Workbooks | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-honey-comb |
| Configure link actions in Azure Workbooks | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-link-actions |
| Configure map visualizations in Azure Workbooks | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-map-visualizations |
| Use multi-value parameters for filtering in Workbooks | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-multi-value |
| Configure options group parameters in Workbooks | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-options-group |
| Configure parameters for Azure Monitor workbooks | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-parameters |
| Select rendering options for Azure Workbooks visuals | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-renderers |
| Configure resource picker parameters in Workbooks | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-resources |
| Use stat visualizations for health dashboards | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-stat-visualizations |
| Use text parameters and defaults in Workbooks | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-text |
| Configure text visualizations in Azure Workbooks | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-text-visualizations |
| Design tile visualizations in Azure Workbooks | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-tile-visualizations |
| Set time parameters for Azure Workbooks reports | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-time |
| Use time brushing parameters in Azure Workbooks | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-time-brushing |
| Create visual indicators and icons in Workbooks | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-traffic-lights |
| Build tree grid visualizations in Azure Workbooks | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-tree-visualizations |
| Create Azure Monitor DCRs for VM log data sources | https://learn.microsoft.com/en-us/azure/azure-monitor/vm/data-collection |
| Configure Azure Monitor Agent for Windows Firewall logs | https://learn.microsoft.com/en-us/azure/azure-monitor/vm/data-collection-firewall-logs |
| Collect IIS logs from VMs using Azure Monitor Agent | https://learn.microsoft.com/en-us/azure/azure-monitor/vm/data-collection-iis |
| Collect JSON log files from VMs using Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/vm/data-collection-log-json |
| Collect custom text log files from VMs with DCRs | https://learn.microsoft.com/en-us/azure/azure-monitor/vm/data-collection-log-text |
| Configure performance counter collection with Azure Monitor Agent | https://learn.microsoft.com/en-us/azure/azure-monitor/vm/data-collection-performance |
| Ingest SNMP trap data into Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/vm/data-collection-snmp-data |
| Configure Linux Syslog collection with Azure Monitor Agent | https://learn.microsoft.com/en-us/azure/azure-monitor/vm/data-collection-syslog |
| Configure Windows event log collection with Azure Monitor Agent | https://learn.microsoft.com/en-us/azure/azure-monitor/vm/data-collection-windows-events |
| Reference OpenTelemetry guest OS metrics in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/vm/metrics-guest-reference |
| Customize OpenTelemetry VM metrics via data collection rules | https://learn.microsoft.com/en-us/azure/azure-monitor/vm/metrics-opentelemetry-guest-modify |
| Analyze Azure VM monitoring data using Azure Monitor features | https://learn.microsoft.com/en-us/azure/azure-monitor/vm/monitor-virtual-machine-analyze |
| Configure Azure Monitor Agent DCRs for Fabric and ADX | https://learn.microsoft.com/en-us/azure/azure-monitor/vm/send-fabric-destination |
| Disable or adjust Azure Monitor VM data collection | https://learn.microsoft.com/en-us/azure/azure-monitor/vm/vm-disable-monitoring |
| Configure Azure Monitor VM monitoring via CLI and templates | https://learn.microsoft.com/en-us/azure/azure-monitor/vm/vm-enable-monitoring |
| Uninstall VM insights Dependency Agent from Azure VMs | https://learn.microsoft.com/en-us/azure/azure-monitor/vm/vminsights-dependency-agent-uninstall |
| Enable VM Insights on intermittently connected Windows clients | https://learn.microsoft.com/en-us/azure/azure-monitor/vm/vminsights-enable-client |
| Configure VM insights using Azure Policy initiatives | https://learn.microsoft.com/en-us/azure/azure-monitor/vm/vminsights-enable-policy |
| Query VM insights map and connection data with Log Analytics | https://learn.microsoft.com/en-us/azure/azure-monitor/vm/vminsights-log-query |
| Create and customize VM insights workbooks for reporting | https://learn.microsoft.com/en-us/azure/azure-monitor/vm/vminsights-workbooks |
