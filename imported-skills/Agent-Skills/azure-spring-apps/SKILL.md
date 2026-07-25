---
name: azure-spring-apps
description: Expert knowledge for Azure Spring Apps development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when configuring ASA networking/security, Tanzu tools, observability/APM, CI/CD deployments, or blue‑green releases, and other Azure Spring Apps related development tasks. Not for Azure App Service (use azure-app-service), Azure Container Apps (use azure-container-apps), Azure Kubernetes Service (AKS) (use azure-kubernetes-service), Azure Functions (use azure-functions).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-02-28"
  generator: "docs2skills/1.0.0"
---
# Azure Spring Apps Skill

This skill provides expert guidance for Azure Spring Apps. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L54 | Diagnosing and fixing Azure Spring Apps issues: memory/OOM, dumps/JFR, remote debugging, VNet connectivity, logs/diagnostics, exit codes, build failures, and Spring Cloud Gateway. |
| Best Practices | L55-L60 | Guidance on production-ready monitoring and diagnostics in Azure Spring Apps, including observability setup, metrics/logs/traces, and configuring JVM diagnostic and debugging options. |
| Decision Making | L61-L81 | Guidance on choosing Azure Spring Apps plans and migrating Spring workloads, configs, gateways, and networking from ASA to Enterprise, AKS, or Container Apps, including logging and Tanzu replacements |
| Architecture & Design Patterns | L82-L89 | Deployment and resiliency patterns for Azure Spring Apps: zero-downtime and blue-green releases, load balancer integration, zone redundancy, and disaster recovery design. |
| Limits & Quotas | L90-L100 | Version/Java support, service-specific limits/quotas, storage caps, VNet requirements, and guidance for scaling Azure Spring Apps Enterprise (instances, large CPU/memory apps). |
| Security | L101-L127 | Securing Azure Spring Apps: TLS/SSL, custom domains, App Gateway, Entra ID SSO/RBAC, managed identities (Key Vault, SQL, Functions), and Azure Policy/regulatory controls. |
| Configuration | L128-L167 | Configuring Azure Spring Apps runtime: networking, ingress/egress, DNS, storage, logging/metrics, APM, health probes, scaling, gateways, Tanzu tools, and enterprise job/lifecycle settings. |
| Integrations & Coding Patterns | L168-L192 | Integrating Azure Spring Apps with databases, Redis, Key Vault, gRPC, Tanzu tools, and APM/monitoring (App Insights, AppDynamics, Dynatrace, Elastic, New Relic) and collecting metrics/logs. |
| Deployment | L193-L212 | Deploying Azure Spring Apps: CI/CD with GitHub/Azure Pipelines/Maven/CLI, container & polyglot deployments, VNet/ARM/Bicep/Terraform setup, blue‑green staging, and region moves. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Capture heap and thread dumps and use JFR in Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-capture-dumps |
| Connect to Azure Spring Apps instances for advanced troubleshooting | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-connect-to-app-instance-for-troubleshooting |
| Resolve app restarts caused by out-of-memory in Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-fix-app-restart-issues-caused-by-out-of-memory |
| Enable and use remote debugging for Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-remote-debugging-app-instance |
| Self-diagnose Azure Spring Apps issues in virtual networks | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-self-diagnose-running-in-vnet |
| Use Azure Spring Apps diagnostics to self-diagnose issues | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-self-diagnose-solve |
| Use tools to troubleshoot Java memory issues in Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/tools-to-troubleshoot-memory-issues |
| General troubleshooting guide for Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/troubleshoot |
| Troubleshoot application exit codes in Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/troubleshoot-exit-code |
| Troubleshoot Azure Spring Apps in virtual networks | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/troubleshooting-vnet |
| Stream Azure Spring Apps job logs for troubleshooting | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-job-log-streaming |
| Stream managed component logs in Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-managed-component-log-streaming |
| Troubleshoot VMware Spring Cloud Gateway on Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-troubleshoot-enterprise-spring-cloud-gateway |
| Troubleshoot Azure Spring Apps build failures | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/troubleshoot-build-exit-code |

### Best Practices
| Topic | URL |
|-------|-----|
| Optimize observability for production Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/application-observability |
| Configure JVM diagnostic options for Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-dump-jvm-options |

### Decision Making
| Topic | URL |
|-------|-----|
| Migrate Azure Spring Apps Basic/Standard to Enterprise plan | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-migrate-standard-tier-to-enterprise-tier |
| Choose the right Azure Spring Apps plan | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/plan-comparison |
| Understand Azure Spring Apps Enterprise marketplace offer | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-enterprise-marketplace-offer |
| Migrate Application Live View to Spring Boot Admin | https://learn.microsoft.com/en-us/azure/spring-apps/migration/migrate-application-live-view |
| Migrate from Application Configuration Service to Spring Cloud Config Server | https://learn.microsoft.com/en-us/azure/spring-apps/migration/migrate-enterprise-application-configuration-service |
| Plan migration off deprecated Tanzu components | https://learn.microsoft.com/en-us/azure/spring-apps/migration/migrate-off-deprecated-tanzu-components |
| Plan migration from Azure Spring Apps to Azure Kubernetes Service | https://learn.microsoft.com/en-us/azure/spring-apps/migration/migrate-to-aks-overview |
| Migrate Azure Spring Apps API Portal to Azure API Management | https://learn.microsoft.com/en-us/azure/spring-apps/migration/migrate-to-azure-container-apps-components-api-portal |
| Migrate Azure Spring Apps ACS to Config Server for Spring | https://learn.microsoft.com/en-us/azure/spring-apps/migration/migrate-to-azure-container-apps-components-application-configuration-service |
| Migrate Spring Cloud Config Server to Config Server for Spring | https://learn.microsoft.com/en-us/azure/spring-apps/migration/migrate-to-azure-container-apps-components-config-server |
| Migrate Eureka Server to Eureka Server for Spring on Container Apps | https://learn.microsoft.com/en-us/azure/spring-apps/migration/migrate-to-azure-container-apps-components-eureka |
| Migrate Spring Cloud Gateway Tanzu to Gateway for Spring on Container Apps | https://learn.microsoft.com/en-us/azure/spring-apps/migration/migrate-to-azure-container-apps-components-gateway |
| Migrate Application Live View to Managed Admin for Spring | https://learn.microsoft.com/en-us/azure/spring-apps/migration/migrate-to-azure-container-apps-components-live-view |
| Map logs and metrics from Azure Spring Apps to Container Apps | https://learn.microsoft.com/en-us/azure/spring-apps/migration/migrate-to-azure-container-apps-monitoring |
| Migrate Azure Spring Apps custom virtual network to Container Apps | https://learn.microsoft.com/en-us/azure/spring-apps/migration/migrate-to-azure-container-apps-network |
| Decide when to migrate from Azure Spring Apps to Container Apps | https://learn.microsoft.com/en-us/azure/spring-apps/migration/migrate-to-azure-container-apps-overview |
| Plan Azure Container Apps environment for Spring Apps migration | https://learn.microsoft.com/en-us/azure/spring-apps/migration/migrate-to-azure-container-apps-provision |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design zero-downtime deployments on Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/concept-zero-downtime-deployment |
| Apply blue-green deployment patterns in Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/concepts-blue-green-deployment-strategies |
| Integrate Azure Spring Apps with Azure load balancer options | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-integrate-azure-load-balancers |
| Design resilient Azure Spring Apps with zones and DR | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/reliability-spring-apps |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Version support policy for Java and Spring on Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/concept-app-customer-responsibilities |
| Azure Spring Apps FAQ with service-specific behaviors | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/faq |
| Use built-in persistent storage limits in Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-built-in-persistent-storage |
| Service plans and quotas for Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/quotas |
| VNet requirements and dependencies for Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/vnet-customer-responsibilities |
| Scale Azure Spring Apps Enterprise to 1000 instances | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-enterprise-deploy-app-at-scale |
| Deploy large CPU and memory apps on Azure Spring Apps Enterprise | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-enterprise-large-cpu-memory-applications |

### Security
| Topic | URL |
|-------|-----|
| Understand built-in security controls in Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/concept-security-controls |
| Use managed identity from Azure Spring Apps to access Azure SQL | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/connect-managed-identity-to-azure-sql |
| Expose Azure Spring Apps via Application Gateway with end-to-end TLS | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/expose-apps-gateway-end-to-end-tls |
| Authenticate Azure Spring Apps CI/CD with Key Vault in GitHub Actions | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/github-actions-key-vault |
| Secure Config Server and Service Registry with Entra RBAC | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-access-data-plane-azure-ad-rbac |
| Map and secure custom domains for Azure Spring Apps with TLS | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-custom-domain |
| Enable ingress-to-app TLS for Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-enable-ingress-to-app-tls |
| Enable system-assigned managed identity in Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-enable-system-assigned-managed-identity |
| Manage user-assigned managed identities for Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-manage-user-assigned-managed-identities |
| Create custom RBAC roles for Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-permissions |
| Use managed identities with Azure Spring Apps applications | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-use-managed-identities |
| Use TLS/SSL certificates in Azure Spring Apps applications | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-use-tls-certificate |
| Use built-in Azure Policy definitions for Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/policy-reference |
| Apply Azure Policy regulatory compliance controls to Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/security-controls-policy |
| Invoke Azure Functions from Azure Spring Apps using managed identity | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/tutorial-managed-identities-functions |
| Use managed identities to access Key Vault from Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/tutorial-managed-identities-key-vault |
| Expose Azure Spring Apps via Application Gateway TLS termination | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/expose-apps-gateway-tls-termination |
| Expose Azure Spring Apps to internet with TLS options | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-access-app-from-internet-virtual-network |
| Configure Entra ID SSO for Spring Cloud Gateway and API Portal | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-set-up-sso-with-azure-ad |
| Configure single sign-on for Azure Spring Apps Enterprise apps | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/quickstart-configure-single-sign-on-enterprise |
| Deploy Entra ID–protected REST API to Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/quickstart-deploy-restful-api-app |
| Secure Spring Boot communications end-to-end on Azure | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/secure-communications-end-to-end |
| Migrate custom domain TLS/SSL from Spring Apps to Container Apps | https://learn.microsoft.com/en-us/azure/spring-apps/migration/migrate-to-azure-container-apps-custom-domain |

### Configuration
| Topic | URL |
|-------|-----|
| Configure private endpoints to access Azure Spring Apps in a VNet | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/access-app-virtual-network |
| Understand Azure Spring Apps API breaking changes | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/breaking-changes |
| Configure Spring Boot Actuator for Azure Spring Apps monitoring | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/concept-manage-monitor-app-spring-boot-actuator |
| Customize Azure Spring Apps egress with user-defined routes | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/concept-outbound-type |
| Configure diagnostics logs and metrics for Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/diagnostic-services |
| Configure Application Insights Java agent for Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-application-insights |
| Configure managed Spring Cloud Config Server in Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-config-server |
| Configure health probes and graceful termination for Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-configure-health-probes-graceful-termination |
| Customize ingress controller settings in Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-configure-ingress |
| Configure Palo Alto firewall with Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-configure-palo-alto |
| Configure planned maintenance windows for Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-configure-planned-maintenance |
| Control Azure Spring Apps egress with user-defined routes | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-create-user-defined-route-instance |
| Configure custom persistent storage for Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-custom-persistent-storage |
| Enable real-time log streaming for Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-log-streaming |
| Map DNS names for multiple Azure Spring Apps instances | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-map-dns-virtual-network |
| Identify and configure outbound public IPs for Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-outbound-public-ip |
| Prepare Steeltoe applications for deployment to Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-prepare-app-deployment |
| Manually scale Azure Spring Apps CPU, memory, and instances | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-scale-manual |
| Register and discover Spring Boot apps with Azure Spring Apps Service Registry | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-service-registration |
| Set up autoscale rules for Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-setup-autoscale |
| Flush and update DNS settings in Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-use-flush-dns-settings |
| Configure Logback to write logs to custom storage in Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-write-log-to-custom-persistent-storage |
| Monitor Azure Spring Apps lifecycle events with Activity Log and Service Health | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/monitor-app-lifecycle-events |
| Configure Spring Cloud Config Server in Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/quickstart-setup-config-server |
| Generate and collect structured application logs in Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/structured-app-log |
| Configure alerts and action groups for Azure Spring Apps monitoring | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/tutorial-alerts-action-groups |
| Configure VMware Spring Cloud Gateway on Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-configure-enterprise-spring-cloud-gateway |
| Configure VMware Spring Cloud Gateway route filters | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-configure-enterprise-spring-cloud-gateway-filters |
| Configure Application Configuration Service for Tanzu | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-enterprise-application-configuration-service |
| Configure APM integration and CA certificates | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-enterprise-configure-apm-integration-and-ca-certificates |
| Manage job lifecycle in Azure Spring Apps Enterprise | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-manage-job |
| Use Tanzu Application Accelerator with Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-use-accelerator |
| Use Application Live View with Azure Spring Apps Enterprise | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-use-application-live-view |
| Configure Tanzu Dev Tools in Azure Spring Apps Enterprise | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-use-dev-tool-portal |
| Monitor Azure Spring Apps with Application Live View | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/monitor-apps-by-application-live-view |
| Configure Spring Cloud Gateway request rate limits | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/quickstart-set-request-rate-limits-enterprise |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Monitor Azure Spring Apps with AppDynamics Java agent | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-appdynamics-java-agent-monitor |
| Bind Azure Cosmos DB to Azure Spring Apps applications | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-bind-cosmos |
| Bind Azure Database for MySQL to Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-bind-mysql |
| Bind Azure Database for PostgreSQL to Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-bind-postgres |
| Connect Azure Cache for Redis to Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-bind-redis |
| Collect Resilience4j circuit breaker metrics with Micrometer and Application Insights | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-circuit-breaker-metrics |
| Monitor Azure Spring Apps with Dynatrace OneAgent | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-dynatrace-one-agent-monitor |
| Monitor Azure Spring Apps with Elastic APM Java agent | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-elastic-apm-java-agent-monitor |
| Analyze Azure Spring Apps logs with Elastic Cloud | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-elastic-diagnostic-settings |
| Monitor Azure Spring Apps with New Relic Java agent | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-new-relic-monitor |
| Use gRPC services in Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-use-grpc |
| Integrate Azure Spring Apps with Azure Database for MySQL | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/quickstart-integrate-azure-database-mysql |
| Use Netflix Turbine and Hystrix circuit breaker with Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/tutorial-circuit-breaker |
| Use Tanzu Build Service with Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-enterprise-build-service |
| Integrate Tanzu Service Registry with Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-enterprise-service-registry |
| Use API Portal for Tanzu with Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-use-enterprise-api-portal |
| Route app traffic using VMware Spring Cloud Gateway | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-use-enterprise-spring-cloud-gateway |
| Integrate Azure OpenAI with Azure Spring Apps Enterprise | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/quickstart-fitness-store-azure-openai |
| Integrate PostgreSQL and Redis with Azure Spring Apps Enterprise | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/quickstart-integrate-azure-database-and-redis-enterprise |
| Load Azure Spring Apps secrets from Key Vault | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/quickstart-key-vault-enterprise |
| Integrate Application Insights and APM agents into container images | https://learn.microsoft.com/en-us/azure/spring-apps/migration/migrate-to-azure-container-apps-build-application-performance-monitoring |

### Deployment
| Topic | URL |
|-------|-----|
| Use Azure Pipelines task to deploy to Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-cicd |
| Deploy Azure Spring Apps into a virtual network (VNet injection) | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-deploy-in-azure-virtual-network |
| Deploy custom container images to Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-deploy-with-custom-container-image |
| Build CI/CD for Azure Spring Apps with GitHub Actions | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-github-actions |
| Deploy Spring Boot applications from source using Azure CLI to Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-launch-from-source |
| Configure Maven plugin to deploy Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-maven-deploy-apps |
| Move Azure Spring Apps instances across regions | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-move-across-regions |
| Set up a staging environment using blue-green deployments in Azure Spring Apps | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/how-to-staging-environment |
| Deploy Azure Spring Apps into a virtual network using ARM templates | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/quickstart-deploy-infrastructure-vnet |
| Provision Azure Spring Apps in a virtual network using Azure CLI | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/quickstart-deploy-infrastructure-vnet-azure-cli |
| Deploy Azure Spring Apps into a virtual network using Bicep | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/quickstart-deploy-infrastructure-vnet-bicep |
| Provision Azure Spring Apps in a virtual network using Terraform | https://learn.microsoft.com/en-us/azure/spring-apps/basic-standard/quickstart-deploy-infrastructure-vnet-terraform |
| Deploy polyglot apps on Azure Spring Apps Enterprise | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-enterprise-deploy-polyglot-apps |
| Deploy static web files with Tanzu Web Servers buildpack | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/how-to-enterprise-deploy-static-file |
| Build and deploy apps to Azure Spring Apps Enterprise plan | https://learn.microsoft.com/en-us/azure/spring-apps/enterprise/quickstart-deploy-apps-enterprise |
| Use automation tools and CI/CD for Azure Container Apps | https://learn.microsoft.com/en-us/azure/spring-apps/migration/migrate-to-azure-container-apps-automation |
| Implement blue-green deployments with Azure Container Apps | https://learn.microsoft.com/en-us/azure/spring-apps/migration/migrate-to-azure-container-apps-blue-green |