---
name: azure-app-service
description: Expert knowledge for Azure App Service development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when choosing App Service plans/ASE, configuring VNet/custom domains/certs, CI/CD slots, or managed identity access, and other Azure App Service related development tasks. Not for Azure Functions (use azure-functions), Azure Spring Apps (use azure-spring-apps), Azure Static Web Apps (use azure-static-web-apps), Azure Service Fabric (use azure-service-fabric).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-28"
  generator: "docs2skills/1.0.0"
---
# Azure App Service Skill

This skill provides expert guidance for Azure App Service. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L44 | Diagnosing and troubleshooting App Service apps using built-in diagnostics, logs, and Azure Monitor, plus fixes for common WordPress-on-App-Service issues. |
| Best Practices | L45-L55 | Best practices for deploying and securing App Service apps, handling inbound/outbound and TLS IP changes, and using Traffic Manager for resilient, highly available endpoints |
| Decision Making | L56-L74 | Guidance on choosing App Service tiers, plans, auth and networking options, and planning migrations (Windows→Linux, .NET, Docker, VNet, ASE) plus cost and custom domain strategy. |
| Architecture & Design Patterns | L75-L79 | Architectural guidance for App Service: ASE geo-distribution, outbound traffic via NAT Gateway, and recommended Azure services/patterns for building scalable, secure apps. |
| Limits & Quotas | L80-L84 | App Service resource limits (CPU, memory, connections), quota types, how they’re measured/monitored, and how to use metrics to detect and avoid hitting plan or app quotas. |
| Security | L85-L132 | Securing App Service apps: auth (Entra, social, OIDC, MCP), managed identities, certs/TLS, IP/VNet/firewall, storage/SQL/Graph access, and policy/compliance controls. |
| Configuration | L133-L186 | Configuring App Service apps: runtime and language settings, containers, networking/VNet/ASE, domains/certs, storage, auth, health/monitoring, backups, and environment variables. |
| Integrations & Coding Patterns | L187-L196 | Patterns for integrating App Service apps with APM tools, TLS/SSL certs, Application Gateway, MCP, Azure OpenAI chatbots (Node/Flask), and event-driven jobs via WebJobs bindings. |
| Deployment | L197-L219 | Deploying and scaling App Service apps: CI/CD (GitHub Actions, Azure Pipelines), ZIP/FTP/local Git deploy, custom containers, deployment slots, ASE setup/scaling, DNS migration, and automation scripts. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Use App Service diagnostics to troubleshoot apps | https://learn.microsoft.com/en-us/azure/app-service/overview-diagnostics |
| Enable and access Azure App Service diagnostic logs | https://learn.microsoft.com/en-us/azure/app-service/troubleshoot-diagnostic-logs |
| Troubleshoot App Service apps with Azure Monitor | https://learn.microsoft.com/en-us/azure/app-service/tutorial-troubleshoot-monitor |
| Resolve common WordPress on Azure App Service issues | https://learn.microsoft.com/en-us/azure/app-service/wordpress-faq |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply best practices and troubleshooting for Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/app-service-best-practices |
| Apply deployment best practices for App Service | https://learn.microsoft.com/en-us/azure/app-service/deploy-best-practices |
| Prepare App Service apps for inbound IP address changes | https://learn.microsoft.com/en-us/azure/app-service/ip-address-change-inbound |
| Prepare App Service apps for outbound IP address changes | https://learn.microsoft.com/en-us/azure/app-service/ip-address-change-outbound |
| Handle TLS/SSL IP address changes for App Service bindings | https://learn.microsoft.com/en-us/azure/app-service/ip-address-change-ssl |
| Apply security best practices to Azure App Service deployments | https://learn.microsoft.com/en-us/azure/app-service/overview-security |
| Configure Azure Traffic Manager with App Service endpoints | https://learn.microsoft.com/en-us/azure/app-service/web-sites-traffic-manager |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose and use .NET migration tools for App Service | https://learn.microsoft.com/en-us/azure/app-service/app-service-asp-net-migration |
| Configure and evaluate App Service Premium v3 tier | https://learn.microsoft.com/en-us/azure/app-service/app-service-configure-premium-v3-tier |
| Configure and evaluate App Service Premium v4 tier | https://learn.microsoft.com/en-us/azure/app-service/app-service-configure-premium-v4-tier |
| Assess .NET web apps before App Service migration | https://learn.microsoft.com/en-us/azure/app-service/app-service-migration-assess-net |
| Plan migration of App Service apps from Windows to Linux | https://learn.microsoft.com/en-us/azure/app-service/app-service-migration-windows-linux |
| Compare App Service Environment v3 with multitenant App Service | https://learn.microsoft.com/en-us/azure/app-service/environment/ase-multi-tenant-comparison |
| Choose the right authentication option for App Service | https://learn.microsoft.com/en-us/azure/app-service/identity-scenarios |
| Migrate App Service VNet integration from gateway to regional | https://learn.microsoft.com/en-us/azure/app-service/migrate-gateway-based-vnet-integration |
| Decide and plan migration from Docker Compose to sidecars | https://learn.microsoft.com/en-us/azure/app-service/migrate-sidecar-multi-container-apps |
| Choose App Service networking features for security and access | https://learn.microsoft.com/en-us/azure/app-service/networking-features |
| Choose and configure App Gateway with App Service | https://learn.microsoft.com/en-us/azure/app-service/overview-app-gateway-integration |
| Plan and manage custom domains for App Service | https://learn.microsoft.com/en-us/azure/app-service/overview-custom-domains |
| Select and scale Azure App Service plans effectively | https://learn.microsoft.com/en-us/azure/app-service/overview-hosting-plans |
| Plan and manage Azure App Service costs | https://learn.microsoft.com/en-us/azure/app-service/overview-manage-costs |
| Choose secure connectivity methods for App Service | https://learn.microsoft.com/en-us/azure/app-service/tutorial-connect-overview |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design geo-distributed scale with App Service Environments | https://learn.microsoft.com/en-us/azure/app-service/environment/app-service-app-service-environment-geo-distributed-scale |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Understand quotas and metrics for Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/web-sites-monitor |

### Security
| Topic | URL |
|-------|-----|
| Set up IP and VNet access restrictions for App Service | https://learn.microsoft.com/en-us/azure/app-service/app-service-ip-restrictions |
| Configure Key Vault references in App Service settings | https://learn.microsoft.com/en-us/azure/app-service/app-service-key-vault-references |
| Handle App Service Managed Certificate changes and validation | https://learn.microsoft.com/en-us/azure/app-service/app-service-managed-certificate-changes-july-2025 |
| Configure TLS mutual authentication in Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/app-service-web-configure-tls-mutual-auth |
| Secure App Service OpenAPI tools for Foundry with Entra auth | https://learn.microsoft.com/en-us/azure/app-service/configure-authentication-ai-foundry-openapi-tool |
| Customize sign-in and sign-out behavior in App Service auth | https://learn.microsoft.com/en-us/azure/app-service/configure-authentication-customize-sign-in-out |
| Configure MCP server authorization in Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/configure-authentication-mcp |
| Secure MCP servers on App Service with Entra authentication | https://learn.microsoft.com/en-us/azure/app-service/configure-authentication-mcp-server-vscode |
| Manage OAuth tokens with App Service authentication | https://learn.microsoft.com/en-us/azure/app-service/configure-authentication-oauth-tokens |
| Configure Microsoft Entra authentication for App Service | https://learn.microsoft.com/en-us/azure/app-service/configure-authentication-provider-aad |
| Enable Sign in with Apple for App Service apps | https://learn.microsoft.com/en-us/azure/app-service/configure-authentication-provider-apple |
| Set up Facebook authentication for App Service apps | https://learn.microsoft.com/en-us/azure/app-service/configure-authentication-provider-facebook |
| Configure GitHub authentication for App Service apps | https://learn.microsoft.com/en-us/azure/app-service/configure-authentication-provider-github |
| Configure Google authentication for Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/configure-authentication-provider-google |
| Configure custom OpenID Connect providers for App Service | https://learn.microsoft.com/en-us/azure/app-service/configure-authentication-provider-openid-connect |
| Configure X (Twitter) authentication for App Service | https://learn.microsoft.com/en-us/azure/app-service/configure-authentication-provider-twitter |
| Access user identities with App Service authentication | https://learn.microsoft.com/en-us/azure/app-service/configure-authentication-user-identities |
| Disable basic auth for App Service deployments securely | https://learn.microsoft.com/en-us/azure/app-service/configure-basic-auth-disable |
| Encrypt Azure App Service app content at rest with CMK | https://learn.microsoft.com/en-us/azure/app-service/configure-encrypt-at-rest-using-cmk |
| Configure security settings for Java apps on Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/configure-language-java-security |
| Configure TLS/SSL bindings for Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/configure-ssl-bindings |
| Configure TLS/SSL certificates for Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/configure-ssl-certificate |
| Choose authentication methods for Azure App Service deployments | https://learn.microsoft.com/en-us/azure/app-service/deploy-authentication-types |
| Handle TLS certificate policy changes in App Service | https://learn.microsoft.com/en-us/azure/app-service/industry-wide-certificate-changes |
| Secure App Service outbound traffic with Azure Firewall | https://learn.microsoft.com/en-us/azure/app-service/network-secure-outbound-traffic-azure-firewall |
| Configure App Service access restrictions and firewall rules | https://learn.microsoft.com/en-us/azure/app-service/overview-access-restrictions |
| Use Entra agent identity with App Service and Functions | https://learn.microsoft.com/en-us/azure/app-service/overview-agent-identity |
| Configure App Service built-in authentication and authorization | https://learn.microsoft.com/en-us/azure/app-service/overview-authentication-authorization |
| Configure managed identities for Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/overview-managed-identity |
| Configure TLS/SSL security for Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/overview-tls |
| Prevent dangling subdomain takeovers in App Service | https://learn.microsoft.com/en-us/azure/app-service/reference-dangling-subdomain-prevention |
| Secure .NET App Service access to Microsoft Graph with managed identity | https://learn.microsoft.com/en-us/azure/app-service/scenario-secure-app-access-microsoft-graph-as-app |
| Grant delegated Microsoft Graph access for App Service users | https://learn.microsoft.com/en-us/azure/app-service/scenario-secure-app-access-microsoft-graph-as-user |
| Secure App Service access to Azure Storage with managed identities | https://learn.microsoft.com/en-us/azure/app-service/scenario-secure-app-access-storage |
| Enable and configure App Service authentication | https://learn.microsoft.com/en-us/azure/app-service/scenario-secure-app-authentication-app-service |
| Use Azure Policy compliance controls for App Service | https://learn.microsoft.com/en-us/azure/app-service/security-controls-policy |
| Manage minimum TLS versions for App Service and Functions | https://learn.microsoft.com/en-us/azure/app-service/tls-minimum-version |
| Secure App Service apps end-to-end with built-in auth | https://learn.microsoft.com/en-us/azure/app-service/tutorial-auth-aad |
| Connect App Service to SQL on behalf of signed-in user | https://learn.microsoft.com/en-us/azure/app-service/tutorial-connect-app-access-sql-database-as-user-dotnet |
| Secure database access from App Service with managed identity | https://learn.microsoft.com/en-us/azure/app-service/tutorial-connect-msi-azure-database |
| Secure SQL access with managed identity in App Service | https://learn.microsoft.com/en-us/azure/app-service/tutorial-connect-msi-sql-database |
| Isolate Azure App Service traffic with VNet integration | https://learn.microsoft.com/en-us/azure/app-service/tutorial-networking-isolate-vnet |
| Secure App Service apps with custom domains and certificates | https://learn.microsoft.com/en-us/azure/app-service/tutorial-secure-domain-certificate |
| Secure N-tier Azure App Service with private networking | https://learn.microsoft.com/en-us/azure/app-service/tutorial-secure-ntier-app |

### Configuration
| Topic | URL |
|-------|-----|
| Configure Azure App Service App Configuration references | https://learn.microsoft.com/en-us/azure/app-service/app-service-configuration-references |
| Configure Hybrid Connections for Azure App Service apps | https://learn.microsoft.com/en-us/azure/app-service/app-service-hybrid-connections |
| Manage App Service authentication API and runtime versions | https://learn.microsoft.com/en-us/azure/app-service/configure-authentication-api-version |
| Configure App Service authentication using file-based settings | https://learn.microsoft.com/en-us/azure/app-service/configure-authentication-file-based |
| Configure core settings for Azure App Service apps | https://learn.microsoft.com/en-us/azure/app-service/configure-common |
| Mount Azure Storage file shares in App Service | https://learn.microsoft.com/en-us/azure/app-service/configure-connect-to-azure-storage |
| Configure custom containers for Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/configure-custom-container |
| Configure Traffic Manager with App Service custom domains | https://learn.microsoft.com/en-us/azure/app-service/configure-domain-traffic-manager |
| Configure custom error pages in Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/configure-error-pages |
| Configure gateway-required VNet integration for App Service | https://learn.microsoft.com/en-us/azure/app-service/configure-gateway-required-vnet-integration |
| Configure gRPC applications on Azure App Service for Linux | https://learn.microsoft.com/en-us/azure/app-service/configure-grpc |
| Configure Aspire applications on Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/configure-language-dotnet-aspire |
| Configure ASP.NET apps on Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/configure-language-dotnet-framework |
| Configure ASP.NET Core apps on Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/configure-language-dotnetcore |
| Configure Java data sources on Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/configure-language-java-data-sources |
| Deploy and configure Java apps on Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/configure-language-java-deploy-run |
| Configure Node.js applications on Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/configure-language-nodejs |
| Configure PHP applications on Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/configure-language-php |
| Configure Python apps on Azure App Service Linux | https://learn.microsoft.com/en-us/azure/app-service/configure-language-python |
| Open SSH sessions to App Service containers | https://learn.microsoft.com/en-us/azure/app-service/configure-linux-open-ssh-session |
| Configure Azure App Service Managed Instance settings | https://learn.microsoft.com/en-us/azure/app-service/configure-managed-instance |
| Configure Azure App Service built-in MCP server | https://learn.microsoft.com/en-us/azure/app-service/configure-mcp-built-in |
| Configure sidecars for Azure App Service on Linux | https://learn.microsoft.com/en-us/azure/app-service/configure-sidecar |
| Configure and manage Azure App Service certificates | https://learn.microsoft.com/en-us/azure/app-service/configure-ssl-app-service-certificate |
| Configure VNet integration for Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/configure-vnet-integration-enable |
| Configure routing for App Service regional VNet integration | https://learn.microsoft.com/en-us/azure/app-service/configure-vnet-integration-routing |
| Configure zone redundancy for Azure App Service plans | https://learn.microsoft.com/en-us/azure/app-service/configure-zone-redundancy |
| Configure ASE-wide custom settings via ARM templates | https://learn.microsoft.com/en-us/azure/app-service/environment/app-service-app-service-environment-custom-settings |
| Configure networking for App Service Environment v3 | https://learn.microsoft.com/en-us/azure/app-service/environment/configure-network-settings |
| Enable zone redundancy for App Service Environments and Isolated plans | https://learn.microsoft.com/en-us/azure/app-service/environment/configure-zone-redundancy-environment |
| Create App Service Environment v3 with ARM template | https://learn.microsoft.com/en-us/azure/app-service/environment/how-to-create-from-template |
| Configure custom domain suffix for App Service Environment | https://learn.microsoft.com/en-us/azure/app-service/environment/how-to-custom-domain-suffix |
| Manage certificates and bindings in App Service Environment | https://learn.microsoft.com/en-us/azure/app-service/environment/overview-certificates |
| Configure and host web apps in App Service Environment | https://learn.microsoft.com/en-us/azure/app-service/environment/using |
| Back up and restore Azure App Service apps | https://learn.microsoft.com/en-us/azure/app-service/manage-backup |
| Buy and configure Azure App Service managed domains | https://learn.microsoft.com/en-us/azure/app-service/manage-custom-dns-buy-domain |
| Reference monitoring data for Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/monitor-app-service-reference |
| Configure health checks for Azure App Service instances | https://learn.microsoft.com/en-us/azure/app-service/monitor-instances-health-check |
| Understand OS-level capabilities for Windows apps on App Service | https://learn.microsoft.com/en-us/azure/app-service/operating-system-functionality |
| Manage inbound and outbound IP addresses for App Service | https://learn.microsoft.com/en-us/azure/app-service/overview-inbound-outbound-ips |
| Configure and manage App Service local cache | https://learn.microsoft.com/en-us/azure/app-service/overview-local-cache |
| Configure DNS and name resolution for Azure App Service apps | https://learn.microsoft.com/en-us/azure/app-service/overview-name-resolution |
| Configure Azure NAT Gateway integration for App Service | https://learn.microsoft.com/en-us/azure/app-service/overview-nat-gateway-integration |
| Use private endpoints with Azure App Service apps | https://learn.microsoft.com/en-us/azure/app-service/overview-private-endpoint |
| Configure App Service virtual network integration options | https://learn.microsoft.com/en-us/azure/app-service/overview-vnet-integration |
| Reference environment variables for Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/reference-app-settings |
| Reference environment variables for Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/reference-app-settings |
| Configure sidecar containers for Linux custom apps in App Service | https://learn.microsoft.com/en-us/azure/app-service/tutorial-custom-container-sidecar |
| Configure sidecar containers for Linux apps on App Service | https://learn.microsoft.com/en-us/azure/app-service/tutorial-sidecar |
| Configure WebJobs execution behavior with Kudu settings | https://learn.microsoft.com/en-us/azure/app-service/webjobs-execution |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate Java apps on App Service with APM platforms | https://learn.microsoft.com/en-us/azure/app-service/configure-language-java-apm |
| Use App Service TLS/SSL certificates in application code | https://learn.microsoft.com/en-us/azure/app-service/configure-ssl-certificate-in-code |
| Integrate App Service Environment with Azure Application Gateway | https://learn.microsoft.com/en-us/azure/app-service/environment/integrate-with-application-gateway |
| Integrate Node.js Express chatbot with Azure OpenAI via App Service | https://learn.microsoft.com/en-us/azure/app-service/tutorial-ai-openai-chatbot-node |
| Integrate Python Flask chatbot with Azure OpenAI via App Service | https://learn.microsoft.com/en-us/azure/app-service/tutorial-ai-openai-chatbot-python |
| Implement event-driven jobs with Azure WebJobs SDK bindings | https://learn.microsoft.com/en-us/azure/app-service/webjobs-sdk-how-to |

### Deployment
| Topic | URL |
|-------|-----|
| Clone Azure App Service apps using PowerShell | https://learn.microsoft.com/en-us/azure/app-service/app-service-web-app-cloning |
| Set up Azure Pipelines CI/CD for App Service | https://learn.microsoft.com/en-us/azure/app-service/deploy-azure-pipelines |
| Set up CI/CD to App Service custom containers | https://learn.microsoft.com/en-us/azure/app-service/deploy-ci-cd-custom-container |
| Manage deployment credentials for Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/deploy-configure-credentials |
| Deploy App Service custom containers using GitHub Actions | https://learn.microsoft.com/en-us/azure/app-service/deploy-container-github-action |
| Configure continuous deployment to Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/deploy-continuous-deployment |
| Deploy to Azure App Service using FTP/FTPS | https://learn.microsoft.com/en-us/azure/app-service/deploy-ftp |
| Deploy to Azure App Service using GitHub Actions | https://learn.microsoft.com/en-us/azure/app-service/deploy-github-actions |
| Deploy from a local Git repository to App Service | https://learn.microsoft.com/en-us/azure/app-service/deploy-local-git |
| Run Azure App Service apps directly from ZIP packages | https://learn.microsoft.com/en-us/azure/app-service/deploy-run-package |
| Configure deployment slots and staging for App Service | https://learn.microsoft.com/en-us/azure/app-service/deploy-staging-slots |
| Deploy ZIP and file packages to Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/deploy-zip |
| Scale Azure App Service Environment to Isolated v4 | https://learn.microsoft.com/en-us/azure/app-service/environment/app-service-configure-isolated-v4-tier |
| Create an App Service Environment in a virtual network | https://learn.microsoft.com/en-us/azure/app-service/environment/creation |
| Provision App Service Environment v3 using Terraform | https://learn.microsoft.com/en-us/azure/app-service/environment/creation-terraform |
| Migrate active DNS domains to Azure App Service | https://learn.microsoft.com/en-us/azure/app-service/manage-custom-dns-migrate-domain |
| Scale up Azure App Service plans and capacities | https://learn.microsoft.com/en-us/azure/app-service/manage-scale-up |
| Plan for App Service maintenance restarts and downtime | https://learn.microsoft.com/en-us/azure/app-service/routine-maintenance-downtime |
| Automate App Service deployment with Azure CLI scripts | https://learn.microsoft.com/en-us/azure/app-service/samples-cli |
| Automate App Service deployment using PowerShell | https://learn.microsoft.com/en-us/azure/app-service/samples-powershell |