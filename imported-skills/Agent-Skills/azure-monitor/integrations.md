# Azure Monitor — Integrations & Coding Patterns

> This is a reference file for the main [SKILL.md](SKILL.md). This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Send classic Windows VM guest metrics to Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/agents/collect-custom-metrics-guestos-vm-classic |
| Send classic Cloud Services metrics to Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/agents/collect-custom-metrics-guestos-vm-cloud-service-classic |
| Route Azure Diagnostics data to Application Insights | https://learn.microsoft.com/en-us/azure/azure-monitor/agents/diagnostics-extension-to-application-insights |
| Consume Azure activity log alerts via webhook payloads | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/activity-log-alerts-webhook |
| Author Kusto queries for log alert rules | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/alerts-log-alert-query-samples |
| Configure webhook payloads for log search alerts | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/alerts-log-webhook |
| Integrate Azure Monitor alerts with Logic Apps workflows | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/alerts-logic-apps |
| Use Azure Monitor alert payload schemas for integrations | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/alerts-payload-samples |
| Create Azure Monitor metric alerts using Azure CLI | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/azure-cli-metrics-alert-sample |
| Migrate ServiceNow ITSM actions to Secure Webhook | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/itsm-convert-servicenow-to-webhook |
| Connect ServiceNow to Azure Monitor ITSM Connector | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/itsmc-connections-servicenow |
| Connect BMC Helix to Azure Monitor via Secure Webhook | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/itsmc-secure-webhook-connections-bmc |
| Integrate ServiceNow with Azure Monitor Secure Webhook | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/itsmc-secure-webhook-connections-servicenow |
| Understand ITSM data synced to Log Analytics workspaces | https://learn.microsoft.com/en-us/azure/azure-monitor/alerts/itsmc-synced-data |
| Enable Click Analytics feature extension for JS SDK | https://learn.microsoft.com/en-us/azure/azure-monitor/app/javascript-feature-extensions |
| Integrate Application Insights JS SDK with React, Angular, and React Native | https://learn.microsoft.com/en-us/azure/azure-monitor/app/javascript-framework-extensions |
| Instrument web apps with Application Insights JavaScript SDK | https://learn.microsoft.com/en-us/azure/azure-monitor/app/javascript-sdk |
| Customize OpenTelemetry integration with Application Insights | https://learn.microsoft.com/en-us/azure/azure-monitor/app/opentelemetry-add-modify |
| Integrate Application Insights work items with GitHub and Azure DevOps | https://learn.microsoft.com/en-us/azure/azure-monitor/app/work-item-integration |
| Configure Container Insights to scrape and send Prometheus metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/container-insights-prometheus-logs |
| Integrate KEDA autoscaling with Prometheus metrics from Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/integrate-keda |
| Ingest OTLP telemetry into Azure Monitor using AMA | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/opentelemetry-ingest-agent |
| Send OTLP telemetry to Azure Monitor via OTel Collector | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/opentelemetry-protocol-ingestion |
| Configure Argo CD monitoring with Azure Managed Prometheus | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/prometheus-argo-cd-integration |
| Monitor NVIDIA GPU metrics via DCGM exporter in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/prometheus-dcgm-integration |
| Configure Elasticsearch monitoring with Azure Managed Prometheus | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/prometheus-elasticsearch-integration |
| Integrate common Prometheus exporters with Azure Managed Prometheus | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/prometheus-exporters |
| Collect Istio service mesh metrics with Azure Managed Prometheus | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/prometheus-istio-integration |
| Configure Kafka monitoring with Azure Managed Prometheus | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/prometheus-kafka-integration |
| Configure Prometheus scrape CRDs for Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/prometheus-metrics-scrape-crd |
| Configure Prometheus remote write with Entra auth | https://learn.microsoft.com/en-us/azure/azure-monitor/containers/prometheus-remote-write-active-directory |
| Query Azure Monitor resources with Resource Graph | https://learn.microsoft.com/en-us/azure/azure-monitor/fundamentals/resource-graph-samples |
| Authenticate and access Azure Monitor Logs API | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/api/access-api |
| Format Azure Monitor Logs query API requests | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/api/request-format |
| Correlate Azure Data Explorer and Resource Graph with logs | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/azure-monitor-data-explorer-proxy |
| Use Delete Data API to remove Log Analytics records | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/delete-log-data |
| Ingest Azure Event Hubs data into Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/ingest-logs-event-hub |
| Use KQL ML tools for anomaly detection in logs | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/kql-machine-learning-azure-monitor |
| Integrate Azure Monitor Log Analytics queries with Excel | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/log-excel |
| Connect Azure Monitor Log Analytics data to Power BI | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/log-powerbi |
| Export Log Analytics data to Storage using Logic Apps | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/logs-export-logic-app |
| Integrate notebooks with Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/notebooks-azure-monitor-logs |
| Ingest custom logs to Azure Monitor via Logs Ingestion API | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/tutorial-logs-ingestion-api |
| Sample REST and SDK code for Azure Logs Ingestion API | https://learn.microsoft.com/en-us/azure/azure-monitor/logs/tutorial-logs-ingestion-code |
| Send custom metrics to Azure Monitor via REST API | https://learn.microsoft.com/en-us/azure/azure-monitor/metrics/metrics-store-custom-rest-api |
| Query Prometheus metrics via Azure Monitor REST API with PromQL | https://learn.microsoft.com/en-us/azure/azure-monitor/metrics/prometheus-api-promql |
| Configure Grafana with Azure Monitor managed Prometheus | https://learn.microsoft.com/en-us/azure/azure-monitor/metrics/prometheus-grafana |
| Configure Prometheus remote-write to Azure Monitor managed Prometheus | https://learn.microsoft.com/en-us/azure/azure-monitor/metrics/prometheus-remote-write |
| Query Prometheus metrics using Azure Workbooks | https://learn.microsoft.com/en-us/azure/azure-monitor/metrics/prometheus-workbooks |
| Call Azure Monitor REST APIs for metrics and logs | https://learn.microsoft.com/en-us/azure/azure-monitor/platform/rest-api-walkthrough |
| Stream Azure Monitor data to Event Hubs | https://learn.microsoft.com/en-us/azure/azure-monitor/platform/stream-monitoring-data-event-hubs |
| Instrument custom requests for Profiler with Application Insights | https://learn.microsoft.com/en-us/azure/azure-monitor/profiler/profiler-trackrequests |
| Run Kusto queries on AACAudit App Config logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aacaudit |
| Query AACHttpRequest logs for throttling and errors | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aachttprequest |
| Query AAD custom security attribute audit logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aadcustomsecurityattributeauditlogs |
| Query AADDomainServicesAccountLogon sign-in logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aaddomainservicesaccountlogon |
| Query AADDomainServicesAccountManagement activity logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aaddomainservicesaccountmanagement |
| Query AADDomainServicesDirectoryServiceAccess logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aaddomainservicesdirectoryserviceaccess |
| Query AADDomainServicesLogonLogoff events in Kusto | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aaddomainserviceslogonlogoff |
| Query AADDomainServicesPolicyChange audit events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aaddomainservicespolicychange |
| Query AADDomainServicesPrivilegeUse security logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aaddomainservicesprivilegeuse |
| Query AADDomainServicesSystemSecurity events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aaddomainservicessystemsecurity |
| Analyze AADGraphActivityLogs for app and SP calls | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aadgraphactivitylogs |
| Query AADManagedIdentitySignInLogs for active identities | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aadmanagedidentitysigninlogs |
| Query AADNonInteractiveUserSignInLogs for IP and city | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aadnoninteractiveusersigninlogs |
| Analyze AADProvisioningLogs for user and group changes | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aadprovisioninglogs |
| Query AADRiskyUsers logs for high-risk accounts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aadriskyusers |
| Query AADServicePrincipalRiskEvents detections | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aadserviceprincipalriskevents |
| Query AADServicePrincipalSignInLogs for activity analysis | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aadserviceprincipalsigninlogs |
| Query AADUserRiskEvents for active risk detections | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aaduserriskevents |
| Query ABAPAuditLog for logins and file downloads | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/abapauditlog |
| Query ABSBotRequests logs for bot channel traffic | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/absbotrequests |
| Query ACICollaborationAudit for CI resource entitlements | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acicollaborationaudit |
| Query ACLTransactionLogs for latest transactions | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acltransactionlogs |
| Query ACLUserDefinedLogs for custom log entries | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acluserdefinedlogs |
| Query ACRConnectedClientList for Redis client IPs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acrconnectedclientlist |
| Query ACREntraAuthenticationAuditLog events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acrentraauthenticationauditlog |
| Query ACS advanced messaging operations in Log Analytics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acsadvancedmessagingoperations |
| Query ACS auth incoming operations in Log Analytics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acsauthincomingoperations |
| Analyze ACS billing usage with Kusto queries | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acsbillingusage |
| Query ACS call automation incoming operations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acscallautomationincomingoperations |
| Analyze ACS call automation media summary logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acscallautomationmediasummary |
| Measure ACS call automation streaming usage | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acscallautomationstreamingusage |
| Query ACS call client media stats time series | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acscallclientmediastatstimeseries |
| Analyze ACS call client operations and diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acscallclientoperations |
| Analyze ACS call diagnostics metrics with Kusto | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acscalldiagnostics |
| Query ACS call diagnostics updates for media quality | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acscalldiagnosticsupdates |
| Query ACS call recording incoming operations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acscallrecordingincomingoperations |
| Analyze ACS call recording summary metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acscallrecordingsummary |
| Query ACS call summary for participants and duration | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acscallsummary |
| Analyze ACS call summary updates with Kusto | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acscallsummaryupdates |
| Query ACS call survey ratings and issues | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acscallsurvey |
| Query ACS chat incoming operations and errors | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acschatincomingoperations |
| Summarize ACS email send mail operational logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acsemailsendmailoperational |
| Query ACS email status update operational failures | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acsemailstatusupdateoperational |
| Query ACS job router incoming operations and errors | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acsjobrouterincomingoperations |
| Analyze ACS rooms incoming operations and statistics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acsroomsincomingoperations |
| Query ACS SMS incoming operations and errors | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/acssmsincomingoperations |
| Query AD assessment recommendations by scope and status | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/adassessmentrecommendation |
| Query ADF activity run availability and status | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/adfactivityrun |
| Query ADF pipeline run availability and status | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/adfpipelinerun |
| Find top IPs by AD FS sign-in lockouts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/adfssigninlogs |
| Query ADF trigger run availability and status | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/adftriggerrun |
| Monitor ADT data history operations and latency | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/adtdatahistoryoperation |
| Query Azure Digital Twins operation errors and counts | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/adtdigitaltwinsoperation |
| Query Azure Digital Twins event routes operations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/adteventroutesoperation |
| Query Azure Digital Twins models operations and errors | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/adtmodelsoperation |
| Query Azure Digital Twins query operation errors | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/adtqueryoperation |
| Monitor ADX ingestion batching size and duration | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/adxingestionbatching |
| Analyze ADX table usage statistics with Kusto | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/adxtableusagestatistics |
| Query AEW compute pipelines logs for tasks and latency | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aewcomputepipelineslogs |
| Query AEW experiment assignment summary and scorecards | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aewexperimentassignmentsummary |
| Query AEW experiment scorecard metric pairs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aewexperimentscorecardmetricpairs |
| Query AEW experiment scorecards metadata and results | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/aewexperimentscorecards |
| Query AFS audit logs for filesystem requests | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/afsauditlogs |
| Analyze AGC access logs for request and error rates | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/agcaccesslogs |
| Query AgentsInfo log table in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/agentsinfo |
| List Azure Grafana login error events with Kusto | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/agsgrafanaloginevents |
| Query AutoscaleEvaluationsLog table in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/autoscaleevaluationslog |
| Query AutoscaleScaleActionsLog for autoscale events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/autoscalescaleactionslog |
| Use Kusto queries for AzureActivity log analysis | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/azureactivity |
| Analyze AzureAttestationDiagnostics with Kusto queries | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/azureattestationdiagnostics |
| Query AzureBackupOperations for backup events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/azurebackupoperations |
| Use Kusto queries for AzureDiagnostics log analysis | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/azurediagnostics |
| Query AzureLoadTestingOperation for test runs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/azureloadtestingoperation |
| Analyze AzureMetrics with example Kusto queries | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/azuremetrics |
| Query AzureSQLDeadlocks logs with Kusto examples | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/azuresqldeadlocks |
| Query AzureSQLErrors logs with Kusto examples | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/azuresqlerrors |
| Analyze Query Store runtime stats in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/azuresqlquerystoreruntimestatistics |
| Analyze Query Store wait stats in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/azuresqlquerystorewaitstatistics |
| Query AzureSQLResourceUsageStats in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/azuresqlresourceusagestats |
| Query AzureSQLTimeouts logs with Kusto examples | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/azuresqltimeouts |
| Query CassandraLogs for node and error events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/cassandralogs |
| Query CCFApplicationLogs for application errors | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/ccfapplicationlogs |
| Query ChaosStudioExperimentEventLogs for experiment runs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/chaosstudioexperimenteventlogs |
| Use Kusto queries on CIEventsAudit logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/cieventsaudit |
| Query CIEventsOperational for API and workflow events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/cieventsoperational |
| Query CloudAppEvents for file rename activity | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/cloudappevents |
| Analyze CloudHsmServiceOperationAuditLogs with Kusto | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/cloudhsmserviceoperationauditlogs |
| Query CommonSecurityLog for high-volume devices | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/commonsecuritylog |
| Query CommunicationComplianceActivity by organization | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/communicationcomplianceactivity |
| Use ConfidentialWatchlist in joins and lookups | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/confidentialwatchlist |
| Query ConfigurationChange for software and service changes | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/configurationchange |
| Query ConfigurationData for stopped auto-start services | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/configurationdata |
| Query ContainerAppHTTPLogs for HTTP traffic insights | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/containerapphttplogs |
| Query ContainerImageInventory for image status | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/containerimageinventory |
| Query ContainerInventory for container lifecycle data | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/containerinventory |
| Analyze ContainerLog for billable and filtered logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/containerlog |
| Search ContainerLogV2 with example Kusto queries | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/containerlogv2 |
| Query ContainerNetworkLogs for dropped flows and top IPs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/containernetworklogs |
| Search ContainerNodeInventory with Kusto queries | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/containernodeinventory |
| Query ContainerRegistryLoginEvents for login history | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/containerregistryloginevents |
| Query ContainerRegistryRepositoryEvents for registry activity | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/containerregistryrepositoryevents |
| Search ContainerServiceLog with example Kusto queries | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/containerservicelog |
| Analyze CopilotActivity logs for usage and security | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/copilotactivity |
| Query CoreAzureBackup for backup item types | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/coreazurebackup |
| Query CrowdStrikeAlerts for critical alerts by tactic | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/crowdstrikealerts |
| Query CrowdStrikeCases for new cases by status | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/crowdstrikecases |
| Query CrowdStrikeDetections for high severity events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/crowdstrikedetections |
| Query CrowdStrikeIncidents for open and in-progress cases | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/crowdstrikeincidents |
| KQL query patterns for Databricks budget policy logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/databricksbudgetpolicycentral |
| Query DataSetOutput for latest DCR conditional output | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/datasetoutput |
| Query DataSetRuns for latest successful DCR runs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/datasetruns |
| Query DataTransferOperations for discovered and completed objects | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/datatransferoperations |
| KQL examples for Dataverse activity monitoring | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/dataverseactivity |
| Query DCRLogErrors for ingestion and transform failures | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/dcrlogerrors |
| Query DevCenter agent health logs with KQL | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/devcenteragenthealthlogs |
| Analyze DevCenter billing event logs using KQL | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/devcenterbillingeventlogs |
| Summarize DevCenter diagnostic logs with KQL | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/devcenterdiagnosticlogs |
| Query DevCenter resource operation logs for hibernate checks | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/devcenterresourceoperationlogs |
| KQL examples for Surface Hub calendar diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/devicecalendar |
| Query Surface Hub cleanup failures with KQL | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/devicecleanup |
| Analyze Surface Hub hardware health logs via KQL | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/devicehardwarehealth |
| Query Surface Hub software health events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/devicehealth |
| Monitor Surface Hub Skype heartbeat errors with KQL | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/deviceskypeheartbeat |
| Identify antivirus configuration issues via DeviceTvm logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/devicetvmsecureconfigurationassessment |
| List unsupported software from DeviceTvm inventory | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/devicetvmsoftwareinventory |
| Find devices affected by software vulnerabilities | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/devicetvmsoftwarevulnerabilities |
| KQL queries for DNS events and malicious domains | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/dnsevents |
| Query DNSQueryLogs for counts by VNet and return code | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/dnsquerylogs |
| Analyze Durable Task scheduler logs with KQL | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/durabletaskschedulerlogs |
| Query Edge action console logs for top messages | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/edgeactionconsolelog |
| Query failed HTTP dataplane operations and TLS usage | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/egnfailedhttpdataplaneoperations |
| Analyze failed MQTT connections and auth errors | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/egnfailedmqttconnections |
| Monitor MQTT disconnections by reason and session | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/egnmqttdisconnections |
| Query successful HTTP dataplane operations and TLS versions | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/egnsuccessfulhttpdataplaneoperations |
| Analyze successful MQTT connections by session | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/egnsuccessfulmqttconnections |
| Investigate malicious email attachments with KQL | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/emailattachmentinfo |
| Detect phishing campaigns using EmailEvents queries | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/emailevents |
| Analyze post-delivery email actions and detections | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/emailpostdeliveryevents |
| Query email URL information by message ID | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/emailurlinfo |
| Use Kusto queries for Azure Monitor Event table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/event |
| Investigate ingestion failures with FailedIngestion queries | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/failedingestion |
| Analyze Azure Functions logs with FunctionAppLogs queries | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/functionapplogs |
| Query GCP audit logs ingested into Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/gcpauditlogs |
| Monitor agent heartbeats and latency with KQL | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/heartbeat |
| Query identity directory events for group and password changes | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/identitydirectoryevents |
| Detect cleartext LDAP logons with IdentityLogonEvents | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/identitylogonevents |
| Identify SAMR query activity with IdentityQueryEvents | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/identityqueryevents |
| Query Illumio Insights deny events in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/ilumioinsights |
| Advanced InsightsMetrics queries for IoT Edge and Kubernetes | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/insightsmetrics |
| List and search Kubernetes events with KubeEvents queries | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/kubeevents |
| Query KubeMonAgentEvents for agent diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/kubemonagentevents |
| Monitor Kubernetes node inventory and readiness with KQL | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/kubenodeinventory |
| Detect pod issues and crashes with KubePodInventory queries | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/kubepodinventory |
| KubeServices log queries for Azure Monitor analytics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/kubeservices |
| LAJobLogs Kusto query patterns for job diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/lajoblogs |
| LAQueryLogs queries for usage, throttling, and performance | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/laquerylogs |
| LASummaryLogs example queries for rule duration analysis | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/lasummarylogs |
| LogicAppWorkflowRuntime queries for failed workflow operations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/logicappworkflowruntime |
| MDCDetectionDNSEvents queries for DNS event analysis | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/mdcdetectiondnsevents |
| MDCDetectionFimEvents queries for host directory monitoring | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/mdcdetectionfimevents |
| MDCDetectionGatingValidationEvents queries for recent validations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/mdcdetectiongatingvalidationevents |
| MeshControlPlane queries for Istiod control plane logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/meshcontrolplane |
| ReceivedSnapshotLog queries for duration, failures, and errors | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/microsoftdatasharereceivedsnapshotlog |
| SentSnapshotLog queries for snapshot health and trends | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/microsoftdatasharesentsnapshotlog |
| MicrosoftGraphActivityLogs queries for app and request failures | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/microsoftgraphactivitylogs |
| Purview Information Protection queries by label and workload | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/microsoftpurviewinformationprotection |
| MNFDeviceUpdates queries for component and interface states | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/mnfdeviceupdates |
| MNFSystemSessionHistoryUpdates queries for admin session tracking | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/mnfsystemsessionhistoryupdates |
| MNFSystemStateMessageUpdates queries for Syslog error messages | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/mnfsystemstatemessageupdates |
| MySqlAuditLogs queries for GENERAL and CONNECTION events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/mysqlauditlogs |
| MySqlSlowLogs queries for top longest-running queries | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/mysqlslowlogs |
| Kusto query patterns for NCCKubernetesAPIAuditLogs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/ncckubernetesapiauditlogs |
| NetworkSessions queries for scanning and data exfiltration | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/networksessions |
| NginxUpstreamUpdateLogs queries for upstream change tracking | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/nginxupstreamupdatelogs |
| NGXOperationLogs queries for access and error log review | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/ngxoperationlogs |
| NGXSecurityLogs queries for chronological security events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/ngxsecuritylogs |
| NTARuleRecommendation queries for vNet rule suggestions | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/ntarulerecommendation |
| NWConnectionMonitorPathResult queries for hop-by-hop paths | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/nwconnectionmonitorpathresult |
| NWConnectionMonitorTestResult queries for failures and latency | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/nwconnectionmonitortestresult |
| OEPDataplaneLogs queries for HTTP codes and user activity | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/oepdataplanelogs |
| OEWExperimentAssignmentSummary queries for feature variants | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/oewexperimentassignmentsummary |
| OEWExperimentScorecardMetricPairs queries for experiment results | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/oewexperimentscorecardmetricpairs |
| OEWExperimentScorecards queries for experiment metadata and scores | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/oewexperimentscorecards |
| OfficeActivity queries for user activity and risky operations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/officeactivity |
| OktaSystemLogs queries for successful login events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/oktasystemlogs |
| OLPSupplyChainEntityOperations queries for warehouse delete success | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/olpsupplychainentityoperations |
| OTelEvents queries for exception counts by type and service | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/otelevents |
| OTelLogs queries for severity distribution by service | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/otellogs |
| OTelSpans queries for span counts and average duration | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/otelspans |
| Performance counter analysis with Perf log queries | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/perf |
| Analyze PerfInsightsImpactedResources with KQL queries | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/perfinsightsimpactedresources |
| PGSQLAutovacuumStats queries for bloat and vacuum analysis | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/pgsqlautovacuumstats |
| PGSQLDbTransactionsStats queries for remaining transaction capacity | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/pgsqldbtransactionsstats |
| PGSQLPgBouncer queries for connection pooler error logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/pgsqlpgbouncer |
| PGSQLPgStatActivitySessions queries for long-running sessions | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/pgsqlpgstatactivitysessions |
| KQL query patterns for PGSQLQueryStoreRuntime logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/pgsqlquerystoreruntime |
| KQL query patterns for PGSQLQueryStoreWaits logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/pgsqlquerystorewaits |
| KQL queries for Azure PGSQLServerLogs analysis | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/pgsqlserverlogs |
| Query PowerAppsActivity logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/powerappsactivity |
| Query PowerAutomateActivity logs with KQL | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/powerautomateactivity |
| Analyze PowerBIActivity audit logs via KQL | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/powerbiactivity |
| Query PowerPlatformAdminActivity operations in logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/powerplatformadminactivity |
| KQL queries for PowerPlatformConnectorActivity logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/powerplatformconnectoractivity |
| Analyze PowerPlatformDlpActivity events with KQL | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/powerplatformdlpactivity |
| Query ProjectActivity logs in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/projectactivity |
| KQL queries for ProtectionStatus and malware data | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/protectionstatus |
| Query PurviewSecurityLogs for collection deletes | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/purviewsecuritylogs |
| Analyze QualysKnowledgeBase vulnerabilities with KQL | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/qualysknowledgebase |
| KQL queries for REDConnectionEvents Redis diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/redconnectionevents |
| Query RetinaNetworkFlowLogs for dropped flows | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/retinanetworkflowlogs |
| KQL queries for SCGPoolExecutionLog settings updates | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/scgpoolexecutionlog |
| Query SCGPoolRequestLog for pool exhaustion events | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/scgpoolrequestlog |
| KQL queries for SecurityAttackPathData risk levels | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/securityattackpathdata |
| Query SecurityCaseEvent logs with Kusto examples | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/securitycaseevent |
| SecurityEvent log analysis with KQL examples | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/securityevent |
| Query SentinelAudit logs for failed updates | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/sentinelaudit |
| Analyze SignalRServiceDiagnosticLogs with KQL | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/signalrservicediagnosticlogs |
| SigninLogs analysis for Azure AD sign-ins | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/signinlogs |
| Analyze SQLAssessmentRecommendation results with KQL | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/sqlassessmentrecommendation |
| StorageBlobLogs KQL for errors and latency | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/storagebloblogs |
| Query StorageCacheOperationEvents for failures | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/storagecacheoperationevents |
| KQL queries for StorageCacheUpgradeEvents history | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/storagecacheupgradeevents |
| Query StorageCacheWarningEvents for active warnings | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/storagecachewarningevents |
| Analyze StorageMalwareScanningResults with KQL | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/storagemalwarescanningresults |
| Query SucceededIngestion logs for ingestion metrics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/succeededingestion |
| Query SVMPoolExecutionLog for capacity changes | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/svmpoolexecutionlog |
| Query SVMPoolRequestLog for degraded pool states | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/svmpoolrequestlog |
| KQL queries for SynapseLinkEvent failure diagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/synapselinkevent |
| Syslog analysis in Azure Monitor with KQL | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/syslog |
| Query TOUserAudits for Toolchain operations | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/touseraudits |
| Analyze TOUserDiagnostics for deployment failures | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/touserdiagnostics |
| TSIIngress KQL for event source connection issues | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/tsiingress |
| Query UCDOAggregatedStatus for content distribution | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/ucdoaggregatedstatus |
| Query UCDOStatus log table in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/ucdostatus |
| Analyze missing updates with Update log table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/update |
| Track update installation with UpdateRunProgress logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/updaterunprogress |
| Summarize update compliance via UpdateSummary logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/updatesummary |
| Investigate URL click events with UrlClickEvents logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/urlclickevents |
| Use Azure Monitor Usage table Kusto queries | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/usage |
| Analyze Mongo vCore performance with VCoreMongoRequests | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/vcoremongorequests |
| Query Video Indexer audit logs via VIAudit table | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/viaudit |
| Monitor Video Indexer indexing with VIIndexing logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/viindexing |
| Analyze IIS traffic using W3CIISLog in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/w3ciislog |
| Track Windows update deployments with WaaSDeploymentStatus | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/waasdeploymentstatus |
| Assess Windows servicing state via WaaSUpdateStatus logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/waasupdatestatus |
| Use Watchlist data in Azure Monitor Kusto queries | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/watchlist |
| Query WindowsEvent logs for security audit changes | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/windowsevent |
| Analyze network traffic with WireData in Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/wiredata |
| Query workload monitoring issues via WorkloadDiagnosticLogs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/workloaddiagnosticlogs |
| Audit workload orchestration via WOUserAudits logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/wouseraudits |
| Diagnose workload orchestration failures with WOUserDiagnostics | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/wouserdiagnostics |
| Monitor WVD agent health with WVDAgentHealthStatus logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/wvdagenthealthstatus |
| Analyze WVD resource usage via WVDCheckpoints logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/wvdcheckpoints |
| Evaluate WVD network performance with WVDConnectionNetworkData | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/wvdconnectionnetworkdata |
| Analyze WVD connection quality via WVDConnections logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/wvdconnections |
| Identify WVD deployment errors using WVDErrors logs | https://learn.microsoft.com/en-us/azure/azure-monitor/reference/queries/wvderrors |
| Convert SCOM management packs into Azure Monitor data collection rules | https://learn.microsoft.com/en-us/azure/azure-monitor/scom-manage-instance/convert-management-packs-into-data-collection-rules |
| Build Grafana dashboards using Azure Data Explorer data | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/grafana-azure-data-explorer |
| Use Grafana dashboards for Azure Kubernetes Service monitoring | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/grafana-kubernetes |
| Transform workbook JSON results using JSONPath | https://learn.microsoft.com/en-us/azure/azure-monitor/visualize/workbooks-jsonpath |
