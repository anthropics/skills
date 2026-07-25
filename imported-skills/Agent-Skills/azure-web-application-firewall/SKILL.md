---
name: azure-web-application-firewall
description: Expert knowledge for Azure Web Application Firewall development including troubleshooting, best practices, decision making, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when configuring Front Door/App Gateway WAF rules, DRS groups, geo/IP filters, rate limits, or bot/CAPTCHA, and other Azure Web Application Firewall related development tasks. Not for Azure Application Gateway (use azure-application-gateway), Azure Front Door (use azure-front-door), Azure Firewall (use azure-firewall), Azure DDos Protection (use azure-ddos-protection).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Web Application Firewall Skill

This skill provides expert guidance for Azure Web Application Firewall. Covers troubleshooting, best practices, decision making, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L36-L40 | Diagnosing and fixing Azure WAF issues on Front Door and Application Gateway, including rule matches, false positives, blocked requests, and configuration or logging problems. |
| Best Practices | L41-L49 | Best practices for configuring, tuning, and hardening WAF on Front Door and Application Gateway, including geomatch rules, exclusions, and security posture improvements. |
| Decision Making | L50-L55 | Guidance on planning and migrating from legacy WAF configs to full WAF policies, and managing the lifecycle, upgrades, and versions of Azure WAF managed rule sets. |
| Limits & Quotas | L56-L61 | Details on WAF limits like max request/body size, file upload constraints, rule engine behavior under high load, and how to configure or tune these limits on Application Gateway. |
| Security | L62-L70 | Configuring WAF security controls: IP restrictions, Front Door DRS rule groups, exclusion/exception lists, and enforcing WAF policies via Azure Policy. |
| Configuration | L71-L111 | Configuring WAF policies and rules for Front Door and Application Gateway: custom/managed rules, rate limiting, geo-filtering, bot/CAPTCHA, exclusions, logging, and sensitive data protection. |
| Integrations & Coding Patterns | L112-L122 | Using WAF with other Azure services: integrating logs with Sentinel/Log Analytics, automating incident response, investigating events, and protecting APIM/Azure OpenAI via Front Door WAF. |
| Deployment | L123-L129 | How to deploy and manage Application Gateway WAF v2 using Bicep, ARM templates, Terraform, and upgrade existing WAF configurations to WAF policies. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Azure Front Door WAF behavior and rules | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/waf-faq |

### Best Practices
| Topic | URL |
|-------|-----|
| Implement WAF best practices in Azure Front Door | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/waf-front-door-best-practices |
| Tune Azure Front Door WAF rules and exclusions | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/waf-front-door-tuning |
| Apply best practices for WAF on Application Gateway | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/best-practices |
| Apply geomatch WAF rules to strengthen web app security | https://learn.microsoft.com/en-us/azure/web-application-firewall/geomatch-custom-rules-examples |
| Secure and harden Azure Web Application Firewall deployments | https://learn.microsoft.com/en-us/azure/web-application-firewall/secure-web-application-firewall |

### Decision Making
| Topic | URL |
|-------|-----|
| Migrate Azure Application Gateway WAF configs to full policies | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/migrate-policy |
| Plan Azure WAF managed ruleset lifecycle and upgrades | https://learn.microsoft.com/en-us/azure/web-application-firewall/ruleset-support-policy |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Understand Azure Application Gateway WAF limits and behavior | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/application-gateway-waf-faq |
| Configure WAF request and file upload size limits on Application Gateway | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/application-gateway-waf-request-size-limits |

### Security
| Topic | URL |
|-------|-----|
| Configure IP restriction rules in Front Door WAF | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/waf-front-door-configure-ip-restriction |
| Understand Azure WAF Front Door DRS rule groups | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/waf-front-door-drs |
| Configure WAF exclusion lists for Azure Front Door | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/waf-front-door-exclusion |
| Configure WAF exception lists for Application Gateway | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/application-gateway-exceptions |
| Enforce WAF governance using Azure Policy | https://learn.microsoft.com/en-us/azure/web-application-firewall/shared/waf-azure-policy |

### Configuration
| Topic | URL |
|-------|-----|
| Configure CAPTCHA challenges in Azure Front Door WAF | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/captcha-challenge |
| Configure WAF exception lists for Azure Front Door | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/front-door-exceptions |
| Configure custom block responses for Front Door WAF | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/waf-front-door-configure-custom-response-code |
| Define custom WAF rules for Azure Front Door | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/waf-front-door-custom-rules |
| Configure Azure Front Door WAF custom and managed rules | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/waf-front-door-custom-rules-powershell |
| Set up WAF exclusion rules on Azure Front Door | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/waf-front-door-exclusion-configure |
| Configure geo-filtering rules in Azure Front Door WAF | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/waf-front-door-geo-filtering |
| Configure monitoring and logging for Front Door WAF | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/waf-front-door-monitor |
| Enable and configure bot protection in Front Door WAF | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/waf-front-door-policy-configure-bot-protection |
| Configure Azure Front Door WAF policy-level settings | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/waf-front-door-policy-settings |
| Configure rate limiting policies in Front Door WAF | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/waf-front-door-rate-limit |
| Create and tune WAF rate-limit rules on Front Door | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/waf-front-door-rate-limit-configure |
| Create a geo-filtering WAF policy with PowerShell | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/waf-front-door-tutorial-geo-filtering |
| Configure log scrubbing on Azure Front Door WAF | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/waf-sensitive-data-protection-configure-frontdoor |
| Enable sensitive data protection for Front Door WAF logs | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/waf-sensitive-data-protection-frontdoor |
| Reference for Application Gateway WAF CRS and DRS rules | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/application-gateway-crs-rulegroups-rules |
| Customize Application Gateway WAF rules using Azure CLI | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/application-gateway-customize-waf-rules-cli |
| Customize Application Gateway WAF rules in Azure portal | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/application-gateway-customize-waf-rules-portal |
| Customize Application Gateway WAF rules with PowerShell | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/application-gateway-customize-waf-rules-powershell |
| Configure WAF exclusion lists on Application Gateway | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/application-gateway-waf-configuration |
| Configure and analyze Application Gateway WAF metrics | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/application-gateway-waf-metrics |
| Associate WAF policies with existing Application Gateways | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/associate-waf-policy-existing-gateway |
| Configure bot protection rules for Azure Application Gateway WAF | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/bot-protection |
| Configure custom block response codes and pages for Application Gateway WAF | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/configure-custom-response-code |
| Create WAF v2 custom rules with Azure PowerShell | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/configure-waf-custom-rules |
| Create and attach WAF policies to Azure Application Gateway | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/create-waf-policy-ag |
| Configure HTTP DDoS ruleset for Application Gateway WAF | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/ddos-ruleset |
| Use Application Gateway WAF Insights dashboards | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/insights |
| Configure per-site WAF policies with PowerShell | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/per-site-policies |
| Understand and scope WAF policies on Application Gateway | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/policy-overview |
| Create rate-limiting custom rules for Application Gateway WAF v2 | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/rate-limiting-configure |
| Configure rate limiting for Azure Application Gateway WAF | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/rate-limiting-overview |
| Configure sensitive data protection in WAF logs | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/waf-sensitive-data-protection |
| Set up WAF log scrubbing on Application Gateway | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/waf-sensitive-data-protection-configure |
| Enable and manage logging for Azure WAF | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/web-application-firewall-logs |
| Manage WAF policies centrally with Azure Firewall Manager | https://learn.microsoft.com/en-us/azure/web-application-firewall/shared/manage-policies |
| Use JavaScript challenge for bot mitigation in WAF | https://learn.microsoft.com/en-us/azure/web-application-firewall/waf-javascript-challenge |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Automate WAF incident response with Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/automated-detection-response-with-sentinel |
| Protect APIM-hosted APIs with Front Door WAF | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/protect-api-hosted-apim-by-waf |
| Secure Azure OpenAI endpoints using Front Door WAF | https://learn.microsoft.com/en-us/azure/web-application-firewall/afds/protect-azure-open-ai |
| Analyze Application Gateway WAF logs with Log Analytics | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/log-analytics |
| Investigate Azure WAF events with Security Copilot | https://learn.microsoft.com/en-us/azure/web-application-firewall/waf-copilot |
| Detect new web threats using WAF and Sentinel | https://learn.microsoft.com/en-us/azure/web-application-firewall/waf-new-threat-detection |
| Integrate Azure WAF logs with Microsoft Sentinel | https://learn.microsoft.com/en-us/azure/web-application-firewall/waf-sentinel |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy Azure Application Gateway WAF v2 using Bicep | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/quick-create-bicep |
| Deploy Azure Application Gateway WAF v2 via ARM template | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/quick-create-template |
| Upgrade Azure Application Gateway WAF configuration to policy | https://learn.microsoft.com/en-us/azure/web-application-firewall/ag/upgrade-ag-waf-policy |
| Provision Application Gateway WAF v2 with Terraform | https://learn.microsoft.com/en-us/azure/web-application-firewall/quickstart-web-application-firewall-terraform |