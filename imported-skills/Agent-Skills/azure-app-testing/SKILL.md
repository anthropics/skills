---
name: azure-app-testing
description: Expert knowledge for Azure App Testing development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when using Azure Load Testing, Playwright Workspaces, JMeter/Locust tests, VNet/private endpoints, or CI/CD pipelines, and other Azure App Testing related development tasks. Not for Azure Test Plans (use azure-test-plans), Azure DevOps (use azure-devops), Azure Pipelines (use azure-pipelines), Playwright Workspaces (use azure-playwright-workspaces).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure App Testing Skill

This skill provides expert guidance for Azure App Testing. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L47 | Diagnosing and fixing Azure Load Testing and Playwright Workspace issues, including failed tests, debug runs, browser recorder, private endpoints, and test run/reporting errors. |
| Best Practices | L48-L56 | Guidance on load testing App Service apps, tuning high-scale tests, finding performance bottlenecks, and optimizing Playwright Workspace tests for reliability and low latency. |
| Decision Making | L57-L64 | Guides for deciding load test resource moves (regions, groups, subscriptions) and tuning performance settings like Azure Functions configs and Playwright parallelism. |
| Architecture & Design Patterns | L65-L70 | Designing Azure Load Testing setups with virtual networks and private endpoints, including VNet-injected tests, network isolation, and testing services over private connectivity. |
| Limits & Quotas | L71-L78 | Configuring and understanding usage limits, quotas, and free trial constraints for Azure Load Testing and Playwright Workspaces, including monthly caps and workspace configuration options. |
| Security | L79-L91 | Securing Azure Load Testing and Playwright Workspaces: RBAC, auth for endpoints, managed identities, Key Vault, CMK encryption, certificates, access tokens, and Azure Policy controls. |
| Configuration | L92-L113 | Configuring and running Azure Load Testing and Playwright Workspaces: test definitions, HTTP/JMeter settings, secrets, monitoring, baselines, reporting/export, CI/CD YAML, scheduling, and multi-region load. |
| Integrations & Coding Patterns | L114-L124 | Authoring and running load tests with JMeter, Locust, and Playwright, using CSV data and plugins, integrating with VS Code/Copilot, and testing local or private apps via Azure Load Testing. |
| Deployment | L125-L129 | Setting up and automating CI/CD for Azure Load Testing, including manual pipeline configuration and integration with Azure Pipelines for automated test runs. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Use AI-powered actionable insights to diagnose Azure load test issues | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-analyze-test-results-using-actionable-insights |
| Diagnose and troubleshoot failing Azure load tests | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-diagnose-failing-load-test |
| Run Azure load tests in debug mode for troubleshooting | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-run-tests-in-debug-mode |
| Diagnose browser recorder issues in Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/troubleshoot-browser-extension |
| Troubleshoot private endpoint load tests in Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/troubleshoot-private-endpoint-tests |
| Troubleshoot Playwright Workspaces reporting errors | https://learn.microsoft.com/en-us/azure/app-testing/playwright-workspaces/troubleshoot-playwright-workspaces-reporting |
| Troubleshoot Playwright Workspaces test run issues | https://learn.microsoft.com/en-us/azure/app-testing/playwright-workspaces/troubleshoot-test-run-failures |

### Best Practices
| Topic | URL |
|-------|-----|
| Load test Azure App Service apps with Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/concept-load-test-app-service |
| Configure high-scale load tests and engine instances in Azure | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-high-scale-load |
| Identify performance bottlenecks using Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/tutorial-identify-bottlenecks-azure-portal |
| Configure Playwright visual comparisons in Workspaces reliably | https://learn.microsoft.com/en-us/azure/app-testing/playwright-workspaces/how-to-configure-visual-comparisons |
| Optimize regional latency for Playwright Workspaces tests | https://learn.microsoft.com/en-us/azure/app-testing/playwright-workspaces/how-to-optimize-regional-latency |

### Decision Making
| Topic | URL |
|-------|-----|
| Move Azure Load Testing resources between regions | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-move-between-regions |
| Move Azure Load Testing resources across resource groups or subscriptions | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-move-between-resource-groups-subscriptions |
| Choose optimal Azure Functions configuration with load tests | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-optimize-azure-functions |
| Determine optimal Playwright Workspaces parallelism configuration | https://learn.microsoft.com/en-us/azure/app-testing/playwright-workspaces/concept-determine-optimal-configuration |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Choose virtual network deployment scenarios for Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/concept-azure-load-testing-vnet-injection |
| Test private endpoints with virtual network–injected Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-test-private-endpoint |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Configure monthly usage limits for Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-manage-usage-limits |
| Service limits and quotas for Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/resource-limits-quotas-capacity |
| Understand Playwright Workspaces free trial limits | https://learn.microsoft.com/en-us/azure/app-testing/playwright-workspaces/how-to-try-playwright-workspaces-free |
| Review limits and configuration for Playwright Workspaces | https://learn.microsoft.com/en-us/azure/app-testing/playwright-workspaces/resource-limits-quotas-capacity |

### Security
| Topic | URL |
|-------|-----|
| Manage Azure Load Testing access with RBAC roles | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-assign-roles |
| Configure customer-managed keys for Azure Load Testing encryption | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-configure-customer-managed-keys |
| Load test authenticated endpoints with Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-test-secured-endpoints |
| Use managed identities and Key Vault with Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-use-a-managed-identity |
| Secure Azure Load Testing resources with Azure Policy | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-use-azure-policy |
| Configure multiple certificates with JKS and Key Vault in Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-use-multiple-certificates |
| Manage Playwright Workspaces access tokens securely | https://learn.microsoft.com/en-us/azure/app-testing/playwright-workspaces/how-to-manage-access-tokens |
| Configure authentication and authorization for Playwright Workspaces | https://learn.microsoft.com/en-us/azure/app-testing/playwright-workspaces/how-to-manage-authentication |
| Configure RBAC-based access control for Playwright Workspaces | https://learn.microsoft.com/en-us/azure/app-testing/playwright-workspaces/how-to-manage-workspace-access |

### Configuration
| Topic | URL |
|-------|-----|
| Configure HTTP requests in URL-based Azure load tests | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-add-requests-to-url-based-test |
| Compare multiple Azure load test runs and baselines | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-compare-multiple-test-runs |
| Configure JMeter user properties in Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-configure-user-properties |
| Create and manage Azure load test definitions | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-create-manage-test |
| Create and manage Azure load test runs in the portal | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-create-manage-test-runs |
| Configure fail and auto-stop criteria for Azure load tests | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-define-test-criteria |
| Export Azure Load Testing results for external reporting | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-export-test-results |
| Generate multi-region load with Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-generate-load-from-multiple-regions |
| Monitor server-side Azure resource metrics during load tests | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-monitor-server-side-metrics |
| Use secrets and environment variables in Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-parameterize-load-tests |
| Schedule recurring Azure load tests | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-schedule-tests |
| Use Azure Load Testing results dashboard for analysis | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-understand-test-run-results-dashboard |
| Reference for Azure Load Testing monitoring data and resources | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/monitor-load-testing-reference |
| Configure Azure Load Testing with YAML in CI/CD | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/reference-test-config-yaml |
| JMeter properties overridden by Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/resource-jmeter-property-overrides |
| Select supported Azure resources for Load Testing monitoring | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/resource-supported-azure-resource-types |
| Use Playwright Workspaces service configuration file options | https://learn.microsoft.com/en-us/azure/app-testing/playwright-workspaces/how-to-use-service-config-file |
| Configure Playwright Workspaces reporting for advanced diagnostics | https://learn.microsoft.com/en-us/azure/app-testing/playwright-workspaces/quickstart-advanced-diagnostic-with-playwright-workspaces-reporting |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Run JMeter-based load tests in Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-create-and-run-load-test-with-jmeter-script |
| Use CSV data in JMeter and Locust tests on Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-read-csv-data |
| Use JMeter plugins with Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-use-jmeter-plugins |
| Create Locust-based load tests in Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/quickstart-create-run-load-test-with-locust |
| Use VS Code extension and Copilot for Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/quickstart-create-run-load-tests-from-visual-studio-code |
| Use supported JMeter features in Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/resource-jmeter-support |
| Run Playwright Workspaces tests against local or private apps | https://learn.microsoft.com/en-us/azure/app-testing/playwright-workspaces/how-to-test-local-applications |

### Deployment
| Topic | URL |
|-------|-----|
| Manually configure CI/CD pipelines for Azure Load Testing | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/how-to-configure-load-test-cicd |
| Automate Azure Load Testing in Azure Pipelines CI/CD | https://learn.microsoft.com/en-us/azure/app-testing/load-testing/quickstart-add-load-test-cicd |