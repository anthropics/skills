---
name: azure-front-door
description: Expert knowledge for Azure Front Door development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when configuring Front Door caching/rules, CDN streaming, TLS/Private Link, POP limits, or 4xx/5xx diagnostics, and other Azure Front Door related development tasks. Not for Azure Application Gateway (use azure-application-gateway), Azure Load Balancer (use azure-load-balancer), Azure Traffic Manager (use azure-traffic-manager), Azure Web Application Firewall (use azure-web-application-firewall).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Front Door Skill

This skill provides expert guidance for Azure Front Door. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L41 | Diagnosing and fixing Azure Front Door 4xx/5xx errors, CORS and compression issues, config/runtime problems, and performance bottlenecks using logs, reference strings, and best practices. |
| Best Practices | L42-L48 | Designing optimal Front Door configs, rules engine patterns, and CDN tuning for video-on-demand/live streaming performance, reliability, and cost efficiency. |
| Decision Making | L49-L60 | Guidance on choosing Front Door vs CDN tiers, comparing Standard/Premium/Classic pricing, understanding billing, and planning or executing migrations and upgrades between tiers. |
| Architecture & Design Patterns | L61-L69 | Architectural patterns for Azure Front Door: apex domain setup, blue/green deployments, manual failover with Traffic Manager, static blob hosting, reliable uploads, and well-architected design guidance. |
| Limits & Quotas | L70-L78 | POP codes and locations, regional POP lists, Front Door limits/quotas and behaviors, routing composite limits, and subscription-level bandwidth throttling details. |
| Security | L79-L96 | TLS, certificates, origins, and logging security for Front Door: cipher suites, HTTPS, Private Link, managed identity auth, security headers, and sensitive data/log protection. |
| Configuration | L97-L120 | Configuring Azure Front Door behavior: caching, rules/rewrite, headers/protocols, compression, Private Link backends, WebSockets, monitoring, and cache purge via portal/CLI/PowerShell. |
| Integrations & Coding Patterns | L121-L126 | Automating Azure Front Door setup with Azure CLI/PowerShell, including creating profiles, endpoints, and delivery rules via scripts and command-line workflows. |
| Deployment | L127-L137 | Automating Front Door deployment and migration using Bicep/ARM/Terraform, updating DevOps pipelines, and upgrading or migrating between Classic, Standard, and Premium tiers. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Resolve CORS issues when using Azure Front Door | https://learn.microsoft.com/en-us/azure/frontdoor/standard-premium/troubleshoot-cross-origin-resources |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply Azure Front Door configuration best practices | https://learn.microsoft.com/en-us/azure/frontdoor/best-practices |
| Implement Azure Front Door rules engine scenarios and patterns | https://learn.microsoft.com/en-us/azure/frontdoor/rules-engine-scenarios |
| Optimize VOD and Live Streaming with Azure Front Door | https://learn.microsoft.com/en-us/azure/frontdoor/video-on-demand-live-streaming |

### Decision Making
| Topic | URL |
|-------|-----|
| Understand Azure Front Door Standard/Premium billing components | https://learn.microsoft.com/en-us/azure/frontdoor/billing |
| Compare pricing of Azure CDN Standard and Front Door | https://learn.microsoft.com/en-us/azure/frontdoor/compare-cdn-front-door-price |
| Choose between Azure Front Door and Azure CDN tiers | https://learn.microsoft.com/en-us/azure/frontdoor/front-door-cdn-comparison |
| Migrate Azure Front Door Classic to Standard or Premium | https://learn.microsoft.com/en-us/azure/frontdoor/migrate-tier |
| FAQ for migrating to Front Door Standard/Premium | https://learn.microsoft.com/en-us/azure/frontdoor/migration-faq |
| Plan migration from Front Door classic to Standard/Premium | https://learn.microsoft.com/en-us/azure/frontdoor/tier-migration |
| Upgrade Front Door Standard to Premium tier | https://learn.microsoft.com/en-us/azure/frontdoor/tier-upgrade |
| Compare Azure Front Door Standard, Premium, and Classic pricing | https://learn.microsoft.com/en-us/azure/frontdoor/understanding-pricing |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design and configure apex domains with Azure Front Door | https://learn.microsoft.com/en-us/azure/frontdoor/apex-domain |
| Implement blue/green deployments using Front Door | https://learn.microsoft.com/en-us/azure/frontdoor/blue-green-deployment |
| Implement manual failover for Front Door with Traffic Manager | https://learn.microsoft.com/en-us/azure/frontdoor/high-availability |
| Architect Azure Front Door with Storage blobs for static content | https://learn.microsoft.com/en-us/azure/frontdoor/scenario-storage-blobs |
| Design reliable blob upload via Azure Front Door | https://learn.microsoft.com/en-us/azure/frontdoor/scenario-upload-storage-blobs |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Map Azure Front Door POP abbreviations to locations | https://learn.microsoft.com/en-us/azure/frontdoor/edge-locations-by-abbreviation |
| Review Azure Front Door POP locations by region | https://learn.microsoft.com/en-us/azure/frontdoor/edge-locations-by-region |
| Azure Front Door FAQs on limits and behavior | https://learn.microsoft.com/en-us/azure/frontdoor/front-door-faq |
| Understand Azure Front Door routing composite limits | https://learn.microsoft.com/en-us/azure/frontdoor/front-door-routing-limits |
| Understand Front Door Standard/Premium bandwidth throttling by subscription | https://learn.microsoft.com/en-us/azure/frontdoor/standard-premium/subscription-offers |

### Security
| Topic | URL |
|-------|-----|
| Disable weak DHE cipher suites on Front Door | https://learn.microsoft.com/en-us/azure/frontdoor/diffie-hellman-ciphers |
| End-to-end TLS and cipher support in Front Door | https://learn.microsoft.com/en-us/azure/frontdoor/end-to-end-tls |
| Add security headers with Azure Front Door Rules Engine | https://learn.microsoft.com/en-us/azure/frontdoor/front-door-security-headers |
| Use managed identity for Key Vault certificates | https://learn.microsoft.com/en-us/azure/frontdoor/managed-identity |
| Configure Front Door managed identity origin auth | https://learn.microsoft.com/en-us/azure/frontdoor/origin-authentication-with-managed-identities |
| Secure Azure Front Door origins against direct access | https://learn.microsoft.com/en-us/azure/frontdoor/origin-security |
| Secure Front Door origins with Private Link | https://learn.microsoft.com/en-us/azure/frontdoor/private-link |
| Secure Azure Front Door deployment end-to-end | https://learn.microsoft.com/en-us/azure/frontdoor/secure-front-door |
| Configure HTTPS and TLS certificates for Front Door custom domains | https://learn.microsoft.com/en-us/azure/frontdoor/standard-premium/how-to-configure-https-custom-domain |
| Secure Azure Front Door to App Service with Private Link | https://learn.microsoft.com/en-us/azure/frontdoor/standard-premium/how-to-enable-private-link-web-app |
| Use log scrubbing to protect Front Door logs | https://learn.microsoft.com/en-us/azure/frontdoor/standard-premium/how-to-protect-sensitive-data |
| Configure sensitive data protection in Front Door logs | https://learn.microsoft.com/en-us/azure/frontdoor/standard-premium/sensitive-data-protection |
| Configure Azure Front Door TLS protocol and cipher suites | https://learn.microsoft.com/en-us/azure/frontdoor/standard-premium/tls-policy |
| Set predefined or custom TLS policies in Azure Front Door | https://learn.microsoft.com/en-us/azure/frontdoor/standard-premium/tls-policy-configure |

### Configuration
| Topic | URL |
|-------|-----|
| Understand and configure Front Door caching behavior | https://learn.microsoft.com/en-us/azure/frontdoor/front-door-caching |
| Onboard root or apex domains to Azure Front Door | https://learn.microsoft.com/en-us/azure/frontdoor/front-door-how-to-onboard-apex-domain |
| Understand HTTP header protocol support in Azure Front Door | https://learn.microsoft.com/en-us/azure/frontdoor/front-door-http-headers-protocol |
| HTTP/2 protocol support in Azure Front Door | https://learn.microsoft.com/en-us/azure/frontdoor/front-door-http2 |
| Configure Azure Front Door rule set actions | https://learn.microsoft.com/en-us/azure/frontdoor/front-door-rules-engine-actions |
| Configure URL rewrite rules in Azure Front Door | https://learn.microsoft.com/en-us/azure/frontdoor/front-door-url-rewrite |
| Configure caching rules in Azure Front Door | https://learn.microsoft.com/en-us/azure/frontdoor/how-to-configure-caching |
| Configure origins and origin groups in Azure Front Door | https://learn.microsoft.com/en-us/azure/frontdoor/how-to-configure-origin |
| Configure Azure Front Door Private Link to Application Gateway | https://learn.microsoft.com/en-us/azure/frontdoor/how-to-enable-private-link-application-gateway |
| Connect Front Door to static website via Private Link | https://learn.microsoft.com/en-us/azure/frontdoor/how-to-enable-private-link-storage-static-website |
| Integrate Azure Storage with Front Door caching | https://learn.microsoft.com/en-us/azure/frontdoor/integrate-storage-account |
| Use Azure Front Door monitoring metrics and logs | https://learn.microsoft.com/en-us/azure/frontdoor/monitor-front-door-reference |
| Use server variables in Azure Front Door rule sets | https://learn.microsoft.com/en-us/azure/frontdoor/rule-set-server-variables |
| Use Azure Front Door rule set match conditions | https://learn.microsoft.com/en-us/azure/frontdoor/rules-match-conditions |
| Configure file compression in Azure Front Door | https://learn.microsoft.com/en-us/azure/frontdoor/standard-premium/how-to-compression |
| Connect Front Door Premium to API Management via Private Link | https://learn.microsoft.com/en-us/azure/frontdoor/standard-premium/how-to-enable-private-link-apim |
| Configure Private Link to internal load balancer | https://learn.microsoft.com/en-us/azure/frontdoor/standard-premium/how-to-enable-private-link-internal-load-balancer |
| Configure Front Door Private Link to Storage | https://learn.microsoft.com/en-us/azure/frontdoor/standard-premium/how-to-enable-private-link-storage-account |
| Use WebSockets with Azure Front Door | https://learn.microsoft.com/en-us/azure/frontdoor/standard-premium/websocket |
| Map Azure Front Door classic settings to Standard/Premium | https://learn.microsoft.com/en-us/azure/frontdoor/tier-mapping |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Create Azure Front Door profiles using Azure CLI | https://learn.microsoft.com/en-us/azure/frontdoor/create-front-door-cli |
| Create Azure Front Door and delivery rules with CLI | https://learn.microsoft.com/en-us/azure/frontdoor/standard-premium/front-door-add-rules-cli |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy Azure Front Door using Bicep templates | https://learn.microsoft.com/en-us/azure/frontdoor/create-front-door-bicep |
| Deploy Azure Front Door using ARM templates | https://learn.microsoft.com/en-us/azure/frontdoor/create-front-door-template |
| Provision Azure Front Door with Terraform configuration | https://learn.microsoft.com/en-us/azure/frontdoor/create-front-door-terraform |
| Deploy Azure Front Door using ARM/Bicep template samples | https://learn.microsoft.com/en-us/azure/frontdoor/front-door-quickstart-template-samples |
| Migrate Front Door classic using PowerShell | https://learn.microsoft.com/en-us/azure/frontdoor/migrate-tier-powershell |
| Update DevOps pipelines after Front Door migration | https://learn.microsoft.com/en-us/azure/frontdoor/post-migration-dev-ops-experience |
| Provision Azure Front Door with Terraform configuration samples | https://learn.microsoft.com/en-us/azure/frontdoor/terraform-samples |
| Upgrade Front Door Standard to Premium via PowerShell | https://learn.microsoft.com/en-us/azure/frontdoor/tier-upgrade-powershell |