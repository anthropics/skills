---
name: azure-playwright-workspaces
description: Expert knowledge for Playwright Workspaces development including troubleshooting, best practices, decision making, limits & quotas, security, and configuration. Use when managing Playwright Testing workspaces, tokens/RBAC, quotas, monitoring/metrics, or run/AADSTS7000112 issues, and other Playwright Workspaces related development tasks. Not for Azure App Testing (use azure-app-testing), Azure DevOps (use azure-devops), Azure Pipelines (use azure-pipelines), Azure Test Plans (use azure-test-plans).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-02-28"
  generator: "docs2skills/1.0.0"
---
# Playwright Workspaces Skill

This skill provides expert guidance for Playwright Workspaces. Covers troubleshooting, best practices, decision making, limits & quotas, security, and configuration. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L34-L39 | Diagnosing and fixing Playwright Testing run failures and resolving AADSTS7000112/Azure AD sign-in issues for accessing the Playwright portal. |
| Best Practices | L40-L49 | Optimizing Playwright Testing workspaces for speed, latency, visual regression, remote/private app access, key service features, and reporting/sharding strategies |
| Decision Making | L50-L54 | Guidance on creating, choosing, organizing, and managing Microsoft Playwright Testing workspaces for different teams, projects, and testing scenarios. |
| Limits & Quotas | L55-L60 | Details on Playwright Testing workspace limits, free trial quotas, concurrency caps, and how to configure or monitor usage against those limits. |
| Security | L61-L67 | Managing workspace access tokens, setting up authentication/authorization, and configuring RBAC roles and permissions for Microsoft Playwright Testing workspaces. |
| Configuration | L68-L73 | Configuring Playwright Testing workspaces: service config file setup, enabling monitoring, and understanding available metrics and logs for observability. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Microsoft Playwright Testing run failures | https://learn.microsoft.com/en-us/azure/playwright-testing/troubleshoot-test-run-failures |
| Fix AADSTS7000112 sign-in issues for Playwright portal | https://learn.microsoft.com/en-us/azure/playwright-testing/troubleshoot-unable-sign-into-playwright-portal |

### Best Practices
| Topic | URL |
|-------|-----|
| Optimize Playwright Testing suite configuration for speed | https://learn.microsoft.com/en-us/azure/playwright-testing/concept-determine-optimal-configuration |
| Configure Playwright visual comparison tests on cloud browsers | https://learn.microsoft.com/en-us/azure/playwright-testing/how-to-configure-visual-comparisons |
| Optimize regional latency for Playwright Testing workspaces | https://learn.microsoft.com/en-us/azure/playwright-testing/how-to-optimize-regional-latency |
| Run Playwright tests on local or private apps via remote browsers | https://learn.microsoft.com/en-us/azure/playwright-testing/how-to-test-local-applications |
| Use key Microsoft Playwright Testing service features effectively | https://learn.microsoft.com/en-us/azure/playwright-testing/how-to-use-service-features |
| Use Playwright Testing reporting with sharded test runs | https://learn.microsoft.com/en-us/azure/playwright-testing/playwright-testing-reporting-with-sharding |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose and manage Microsoft Playwright Testing workspaces | https://learn.microsoft.com/en-us/azure/playwright-testing/how-to-manage-playwright-workspace |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Understand Microsoft Playwright Testing free trial limits | https://learn.microsoft.com/en-us/azure/playwright-testing/how-to-try-playwright-testing-free |
| Review Microsoft Playwright Testing limits and configuration | https://learn.microsoft.com/en-us/azure/playwright-testing/resource-limits-quotas-capacity |

### Security
| Topic | URL |
|-------|-----|
| Manage Microsoft Playwright Testing workspace access tokens | https://learn.microsoft.com/en-us/azure/playwright-testing/how-to-manage-access-tokens |
| Configure authentication and authorization for Playwright Testing | https://learn.microsoft.com/en-us/azure/playwright-testing/how-to-manage-authentication |
| Configure RBAC access for Playwright Testing workspaces | https://learn.microsoft.com/en-us/azure/playwright-testing/how-to-manage-workspace-access |

### Configuration
| Topic | URL |
|-------|-----|
| Configure playwright.service.config.ts for Playwright Testing | https://learn.microsoft.com/en-us/azure/playwright-testing/how-to-use-service-config-file |
| Configure monitoring for Microsoft Playwright Testing workspaces | https://learn.microsoft.com/en-us/azure/playwright-testing/monitor-playwright-testing |
| Reference monitoring metrics and logs for Playwright Testing | https://learn.microsoft.com/en-us/azure/playwright-testing/monitor-playwright-testing-reference |