---
name: azure-cost-management
description: Expert knowledge for Azure Cost Management development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when managing budgets/alerts, cost exports, billing accounts, reservations/savings plans, or cost APIs/scripts, and other Azure Cost Management related development tasks. Not for Azure Advisor (use azure-advisor), Azure Monitor (use azure-monitor), Azure Quotas (use azure-quotas), Azure Impact Reporting (use azure-impact-reporting).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Cost Management Skill

This skill provides expert guidance for Azure Cost Management. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L66 | Diagnosing and fixing Azure billing, subscription, and reservation issues (sign-up, access, payments, utilization, and portal errors) using logs, pivot tables, and targeted troubleshooting steps. |
| Best Practices | L67-L78 | Best practices for analyzing and optimizing Azure costs, using Advisor and savings plans, managing subscriptions and agreements, and leveraging Hybrid Benefit for cost savings |
| Decision Making | L79-L159 | Guidance for cost-related decisions: billing model migrations, EA/MCA/CSP management, reservations and savings plans, discounts, chargeback, and optimizing Azure service spend. |
| Architecture & Design Patterns | L160-L164 | How Azure bills centrally assigned SQL Server licenses hourly, including license assignment, cost calculation, and optimization considerations |
| Limits & Quotas | L165-L177 | Usage, timing, and granularity limits for cost data; free account and subscription spending limits; savings plan exclusions/utilization; subscription count limits; billing account dormancy/retention. |
| Security | L178-L199 | RBAC and admin roles for cost data, billing accounts, EA/MCA/CSP, subscription transfers, reservations, savings plans, tax docs, and security/compliance for Azure purchases |
| Configuration | L200-L227 | Configuring Azure Cost Management: budgets, alerts, tags, exports, cost analysis views, reservations/savings plans, billing ownership/transfers, payment methods, and EA/MCA/partner billing settings. |
| Integrations & Coding Patterns | L228-L245 | APIs, scripts, and PowerShell patterns for automating cost analysis, billing data retrieval, and programmatic creation/management of Azure subscriptions and reservations. |
| Deployment | L246-L249 | Configuring automated, large-scale exports of Azure cost and usage data to storage (like Azure Storage), including setup, scheduling, and management for ongoing cost analysis. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot common Azure Cost Management error codes | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/cost-management-error-codes |
| Troubleshoot and reactivate disabled Azure for Students | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/azurestudents-subscription-disabled |
| Diagnose and reactivate disabled Azure subscriptions | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/subscription-disabled |
| Troubleshoot subscription access issues after MCA signup | https://learn.microsoft.com/en-us/azure/cost-management-billing/microsoft-customer-agreement/troubleshoot-subscription-access |
| Find who purchased an Azure reservation using logs | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/find-reservation-purchaser-from-logs |
| Resolve issues downloading Azure reservation usage details | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/troubleshoot-download-usage |
| Fix 'No eligible subscriptions' when buying reservations | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/troubleshoot-no-eligible-subscriptions |
| Fix Azure reservation types appearing as not available | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/troubleshoot-product-not-available |
| Troubleshoot unexpected Azure reservation recommendations | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/troubleshoot-reservation-recommendation |
| Transfer Azure reservation orders between Entra tenants | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/troubleshoot-reservation-transfers-between-tenants |
| Resolve Azure reservations showing zero or low utilization | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/troubleshoot-reservation-utilization |
| Troubleshoot Azure savings plan utilization anomalies | https://learn.microsoft.com/en-us/azure/cost-management-billing/savings-plan/troubleshoot-savings-plan-utilization |
| Troubleshoot Azure billing payment update errors | https://learn.microsoft.com/en-us/azure/cost-management-billing/troubleshoot-billing/billing-troubleshoot-azure-payment-issues |
| Fix VM creation errors for Azure EA users | https://learn.microsoft.com/en-us/azure/cost-management-billing/troubleshoot-billing/cannot-create-vm |
| Resolve missing billing account in Azure portal | https://learn.microsoft.com/en-us/azure/cost-management-billing/troubleshoot-billing/troubleshoot-account-not-found |
| Fix issues viewing Azure invoices in portal | https://learn.microsoft.com/en-us/azure/cost-management-billing/troubleshoot-billing/troubleshoot-cant-find-invoice |
| Troubleshoot CSP billing with reconciliation usage files | https://learn.microsoft.com/en-us/azure/cost-management-billing/troubleshoot-billing/troubleshoot-csp-billing-issues-usage-file-pivot-tables |
| Troubleshoot MCA billing using Azure usage pivot tables | https://learn.microsoft.com/en-us/azure/cost-management-billing/troubleshoot-billing/troubleshoot-customer-agreement-billing-issues-usage-file-pivot-tables |
| Resolve declined credit cards for Azure billing | https://learn.microsoft.com/en-us/azure/cost-management-billing/troubleshoot-billing/troubleshoot-declined-card |
| Troubleshoot Azure EA billing with usage pivot tables | https://learn.microsoft.com/en-us/azure/cost-management-billing/troubleshoot-billing/troubleshoot-ea-billing-issues-usage-file-pivot-tables |
| Diagnose and fix Azure threshold billing issues | https://learn.microsoft.com/en-us/azure/cost-management-billing/troubleshoot-billing/troubleshoot-threshold-billing |
| Resolve Azure subscription sign-up directory errors | https://learn.microsoft.com/en-us/azure/cost-management-billing/troubleshoot-subscription/cannot-sign-up-subscription |
| Resolve 'No subscriptions found' error in Azure portal | https://learn.microsoft.com/en-us/azure/cost-management-billing/troubleshoot-subscription/no-subscriptions-found |
| Troubleshoot new Azure account sign-up issues | https://learn.microsoft.com/en-us/azure/cost-management-billing/troubleshoot-subscription/troubleshoot-azure-sign-up |
| Resolve 'Not available due to conflict' for Azure reservations | https://learn.microsoft.com/en-us/azure/cost-management-billing/troubleshoot-subscription/troubleshoot-not-available-conflict |
| Troubleshoot Azure portal subscription sign-in problems | https://learn.microsoft.com/en-us/azure/cost-management-billing/troubleshoot-subscription/troubleshoot-sign-in-issue |

### Best Practices
| Topic | URL |
|-------|-----|
| Use Cost Analysis for common Azure cost questions | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/cost-analysis-common-uses |
| Apply Azure Cost Management optimization best practices | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/cost-mgt-best-practices |
| Reduce Azure costs using Advisor recommendations | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/tutorial-acm-opt-recommendations |
| Safely cancel and delete Azure subscriptions | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/cancel-azure-subscription |
| Follow best practices to onboard to Microsoft Customer Agreement | https://learn.microsoft.com/en-us/azure/cost-management-billing/microsoft-customer-agreement/onboard-microsoft-customer-agreement |
| Manually calculate EA savings plan cost savings | https://learn.microsoft.com/en-us/azure/cost-management-billing/savings-plan/calculate-ea-savings-plan-savings |
| Optimize centrally managed Azure Hybrid Benefit for SQL | https://learn.microsoft.com/en-us/azure/cost-management-billing/scope-level/tutorial-azure-hybrid-benefits-sql |
| Plan and implement Azure cost management practices | https://learn.microsoft.com/en-us/azure/cost-management-billing/understand/plan-manage-costs |

### Decision Making
| Topic | URL |
|-------|-----|
| Decide and configure Azure cost allocation rules | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/allocate-costs |
| Plan and implement Azure cost allocation strategies | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/cost-allocation-introduction |
| Choose and use built-in Cost Analysis views | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/cost-analysis-built-in-views |
| Plan migration from EA to MCA Cost Management APIs | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/migrate-cost-management-api |
| Use and manage Azure EA billing accounts | https://learn.microsoft.com/en-us/azure/cost-management-billing/enterprise-agreement-faq |
| Understand Azure data transfer fees and scenarios | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/data-transfer-fees |
| Decide on Azure EA VM reserved instances savings | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/ea-portal-vm-reservations |
| Evaluate Azure EA pricing and usage calculations | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/ea-pricing-overview |
| Transfer Azure billing ownership to MCA | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/mca-request-billing-ownership |
| Transition Enterprise Agreement billing to Microsoft Customer Agreement | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/mca-setup-account |
| Decide and understand supported Azure product transfers | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/subscription-transfer |
| Decide and execute Azure subscription offer changes | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/switch-azure-offer |
| Choose and upgrade Azure free or student accounts | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/upgrade-azure-subscription |
| Prepare subscriptions for Microsoft Customer Agreement billing migration | https://learn.microsoft.com/en-us/azure/cost-management-billing/microsoft-customer-agreement/checklist-microsoft-customer-agreement-billing-migration |
| Manage Azure billing as a partner in CSP | https://learn.microsoft.com/en-us/azure/cost-management-billing/partner-faq |
| Choose and manage Azure Reservations and Savings Plans | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations-savings-plan-faq |
| Use Microsoft Agent prepurchase plan across services | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/agent-pre-purchase |
| Choose and purchase Azure DocumentDB reservations | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/azure-documentdb |
| Decide how Azure reservation benefits are applied | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/benefit-application-order |
| Apply reservation discounts to Azure Dedicated Hosts | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/billing-understand-dedicated-hosts-reservation-charges |
| Prepay for Azure virtual machine software reservations | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/buy-vm-software-reservation |
| Use amortized reservation costs for internal chargeback | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/charge-back-usage |
| Choose and use Azure Copilot Credit P3 pre-purchase | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/copilot-credit-p3 |
| Determine which Azure reservation to purchase | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/determine-reservation-purchase |
| Apply reservation discounts to Azure SQL Edge | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/discount-sql-edge |
| Exchange or refund Azure reservations under policy rules | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/exchange-and-refund-azure-reservations |
| Choose and purchase Microsoft Fabric capacity reservations | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/fabric-capacity |
| Plan and evaluate GitHub AI Credits pre-purchase | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/github-ai-credits-pre-purchase-plan |
| Decide on GitHub pre-purchase plan for Azure billing | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/github-pre-purchase |
| Use instance size flexibility for Azure Reservations | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/instance-size-flexibility |
| Evaluate limited-time discounts for VMs in Poland Central | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/limited-time-central-poland |
| Evaluate limited-time discounts for Linux VMs in Sweden Central | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/limited-time-central-sweden |
| Evaluate limited-time discounts for select Linux VMs | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/limited-time-linux |
| Evaluate limited-time discounts for Dv3 VMs in US West | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/limited-time-us-west |
| Plan transition from retired Azure Reserved VM Instances | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/manage-legacy-vm-reservations-after-july-1-2026 |
| Choose and purchase Foundry throughput reservations | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/microsoft-foundry |
| Use reservations for Nutanix Cloud Clusters on Azure | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/nutanix-bare-metal |
| Evaluate limited-time Azure SQL reservations in Poland | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/poland-limited-time-sql-services-reservations |
| Decide how and when to buy Azure reservations | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/prepare-buy-reservation |
| Choose and use Azure App Service reserved capacity | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/prepay-app-service |
| Optimize Azure Databricks costs with reserved capacity | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/prepay-databricks-reserved-capacity |
| Plan reservations for JBoss EAP Integrated Support | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/prepay-jboss-eap-integrated-support-app-service |
| Prepay for Azure Red Hat OpenShift software usage | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/prepay-red-hat-openshift |
| Reserve Azure Synapse Dedicated SQL pool capacity | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/prepay-sql-data-warehouse-charges |
| Prepay for Azure SQL Edge reserved capacity | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/prepay-sql-edge |
| Apply reservation discounts to Azure App Service | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/reservation-discount-app-service |
| Understand how Azure reservation discounts are applied | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/reservation-discount-application |
| Apply reservation discounts to Azure Synapse Analytics DW | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/reservation-discount-azure-sql-dw |
| Use Azure Databricks prepurchased commit units effectively | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/reservation-discount-databricks |
| Understand Azure reservation exchange policy changes | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/reservation-exchange-policy-changes |
| Use Azure reservation purchase recommendations effectively | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/reserved-instance-purchase-recommendations |
| Understand software costs not covered by Azure reservations | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/reserved-instance-windows-software-costs |
| Decide when and how to use Azure Reservations | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/save-compute-costs-reservations |
| Use Azure Synapse Pre-Purchase Plan with SCUs | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/synapse-analytics-pre-purchase-plan |
| Apply reservation discounts to Azure Cache for Redis | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/understand-azure-cache-for-redis-reservation-charges |
| Apply reservation discounts to Azure Cosmos DB throughput | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/understand-cosmosdb-reservation-charges |
| Apply reservation discounts to Azure disk storage | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/understand-disk-reservations |
| Apply reservation discounts to Azure SQL Database | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/understand-reservation-charges |
| Apply reservation discounts to Azure Database for MySQL | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/understand-reservation-charges-mysql |
| Apply reservation discounts to Azure SQL Managed Instance | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/understand-reservation-charges-sql-managed-instance |
| Use Red Hat reservation plan discounts on Azure VMs | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/understand-rhel-reservation-charges |
| Apply reservation discounts to Azure storage services | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/understand-storage-charges |
| Use SUSE and Red Hat software plan discounts on Azure | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/understand-suse-reservation-charges |
| Interpret amortized reservation and savings plan costs | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/view-amortized-costs |
| Use amortized savings plan costs for chargeback | https://learn.microsoft.com/en-us/azure/cost-management-billing/savings-plan/charge-back-costs |
| Select Azure savings plan commitment amount | https://learn.microsoft.com/en-us/azure/cost-management-billing/savings-plan/choose-commitment-amount |
| Decide between Azure savings plans and reservations | https://learn.microsoft.com/en-us/azure/cost-management-billing/savings-plan/decide-between-savings-plan-reservation |
| Understand how Azure savings plan discounts are applied | https://learn.microsoft.com/en-us/azure/cost-management-billing/savings-plan/discount-application |
| Interpret and use Azure savings plan recommendations | https://learn.microsoft.com/en-us/azure/cost-management-billing/savings-plan/purchase-recommendations |
| Trade in Azure reservations for savings plans | https://learn.microsoft.com/en-us/azure/cost-management-billing/savings-plan/reservation-trade-in |
| Choose and understand Azure savings plan scopes | https://learn.microsoft.com/en-us/azure/cost-management-billing/savings-plan/scope-savings-plan |
| Use SQL Server HADR with centrally managed Azure Hybrid Benefit | https://learn.microsoft.com/en-us/azure/cost-management-billing/scope-level/sql-server-hadr-licenses |
| Transition to centrally managed Azure Hybrid Benefit | https://learn.microsoft.com/en-us/azure/cost-management-billing/scope-level/transition-existing |
| Assess impact of Azure billing meter ID updates | https://learn.microsoft.com/en-us/azure/cost-management-billing/understand/billing-meter-id-updates |
| Understand shared Azure billing meter regions | https://learn.microsoft.com/en-us/azure/cost-management-billing/understand/billing-meter-location |
| Understand billing for Azure external service charges | https://learn.microsoft.com/en-us/azure/cost-management-billing/understand/understand-azure-marketplace-charges |
| Plan migration from SAP HANA Large Instances on Azure | https://learn.microsoft.com/en-us/azure/sap/large-instances/decommission-sap-hana |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Understand how Azure applies centrally assigned SQL licenses hourly | https://learn.microsoft.com/en-us/azure/cost-management-billing/scope-level/manage-licenses-centrally |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Azure Cost Management and Billing usage limits | https://learn.microsoft.com/en-us/azure/cost-management-billing/cost-management-billing-faq |
| Understand Azure Cost Management data timing and granularity | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/understand-cost-mgt-data |
| Avoid charges by staying within Azure free account limits | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/avoid-charges-free-account |
| Understand Azure free account credits and duration limits | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/create-free-services |
| Understand and manage Azure subscription spending limits | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/spending-limit |
| Identify Azure savings plan software cost exclusions | https://learn.microsoft.com/en-us/azure/cost-management-billing/savings-plan/software-costs-not-included |
| Check Azure savings plan utilization and data latency | https://learn.microsoft.com/en-us/azure/cost-management-billing/savings-plan/view-utilization |
| Understand limits when creating multiple Azure subscriptions | https://learn.microsoft.com/en-us/azure/cost-management-billing/troubleshoot-subscription/create-subscriptions-deploy-resources |
| Manage Azure billing account dormancy and retention | https://learn.microsoft.com/en-us/azure/cost-management-billing/understand/keep-billing-accounts-active |

### Security
| Topic | URL |
|-------|-----|
| Check Azure credit balance and required roles | https://learn.microsoft.com/en-us/azure/cost-management-billing/benefits/credits/mca-check-azure-credits-balance |
| Assign RBAC access to Azure Cost Management data | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/assign-access-acm-data |
| Assign and change Azure subscription admin roles with RBAC | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/add-change-subscription-administrator |
| Migrate from Azure classic admins to RBAC roles | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/classic-administrator-retire |
| Elevate Global Administrator access to billing accounts | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/elevate-access-global-admin |
| Grant RBAC permissions to create Azure EA subscriptions | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/grant-access-to-create-subscription |
| Configure Azure subscription transfer policies between directories | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/manage-azure-subscription-policy |
| Assign Azure billing roles for account access | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/manage-billing-access |
| Understand PSD2 SCA requirements for Azure purchases | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/open-banking-strong-customer-authentication |
| Manage Azure Enterprise Agreement admin roles and permissions | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/understand-ea-roles |
| Manage billing roles for Microsoft Customer Agreements | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/understand-mca-roles |
| Manage tenants and secure billing access under MCA | https://learn.microsoft.com/en-us/azure/cost-management-billing/microsoft-customer-agreement/manage-tenants |
| View Azure reservations as a Cloud Solution Provider | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/how-to-view-csp-reservations |
| Grant RBAC access to Azure reservations with PowerShell | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/manage-reservations-rbac-powershell |
| Configure permissions to view and manage Azure reservations | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/view-reservations |
| Determine eligibility and permissions to buy Azure savings plans | https://learn.microsoft.com/en-us/azure/cost-management-billing/savings-plan/permission-buy-savings-plan |
| Configure permissions to view and manage savings plans | https://learn.microsoft.com/en-us/azure/cost-management-billing/savings-plan/permission-view-manage |
| Access and download Azure tax documents securely | https://learn.microsoft.com/en-us/azure/cost-management-billing/understand/mca-download-tax-document |

### Configuration
| Topic | URL |
|-------|-----|
| Configure and apply billing tags in Cost Management | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/billing-tags |
| Configure and use Azure Cost Management alerts | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/cost-mgt-alerts-monitor-usage-spending |
| Configure and customize Azure Cost Analysis views | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/customize-cost-analysis-views |
| Configure tag inheritance for Azure cost allocation | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/enable-tag-inheritance |
| Configure Cost Management exports using SAS keys | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/export-cost-data-storage-account-sas-key |
| Configure grouping and filtering in Cost Analysis and Budgets | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/group-filter |
| Define Cost Management budgets using Bicep | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/quick-create-budget-bicep |
| Create Cost Management budgets with ARM templates | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/quick-create-budget-template |
| Set up Azure reservation utilization alerts | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/reservation-utilization-alerts |
| Create and manage Azure Cost Management budgets | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/tutorial-acm-create-budgets |
| Transfer billing ownership of MOSP Azure subscriptions | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/billing-subscription-transfer |
| Configure Azure Marketplace and private offer purchase policies | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/enable-marketplace-purchases |
| Configure Partner Admin Link for Power Platform with Azure credentials | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/link-partner-id-power-apps-accounts |
| Configure markup rules in Azure 21Vianet Cost Management | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/markup-china |
| Move MOSP or MCA Azure subscriptions to an Enterprise Agreement | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/mosp-ea-transfer |
| Calculate Enterprise Agreement reservation savings in Excel | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/calculate-ea-reservations-savings |
| Configure and manage Azure reservation scope and settings | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/manage-reserved-vm-instance |
| Configure and manage Azure reservation scope and settings | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/manage-reserved-vm-instance |
| Configure automatic renewal for Azure reservations | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/reservation-renew |
| Interpret Azure reservation usage for single subscriptions | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/understand-reserved-instance-usage |
| Interpret Azure reservation usage for EA and MCA accounts | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/understand-reserved-instance-usage-ea |
| Configure automatic renewal for Azure savings plans | https://learn.microsoft.com/en-us/azure/cost-management-billing/savings-plan/renew-savings-plan |
| Create and scope SQL Server license assignments in Azure | https://learn.microsoft.com/en-us/azure/cost-management-billing/scope-level/create-sql-license-assignments |
| Configure SQL IaaS extension registration for cost management | https://learn.microsoft.com/en-us/azure/cost-management-billing/scope-level/sql-iaas-extension-registration |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Analyze Azure costs using the Cost Management Power BI app | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/analyze-cost-data-azure-cost-management-power-bi-template-app |
| Automate Azure cost management with APIs and scripts | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/manage-automation |
| Map Azure billing scenarios to Cost Management APIs | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/cost-management-automation-scenarios |
| Automate MCA billing role migration across tenants with PowerShell | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/mca-role-migration |
| Create MCA subscriptions across associated billing tenants | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/programmatically-create-customer-agreement-associated-billing-tenants |
| Programmatically create Azure subscriptions via REST APIs | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/programmatically-create-subscription |
| Create EA subscriptions using latest Azure APIs | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/programmatically-create-subscription-enterprise-agreement |
| Create MCA subscriptions programmatically with latest APIs | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/programmatically-create-subscription-microsoft-customer-agreement |
| Programmatically create MCA subscriptions across Entra tenants | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/programmatically-create-subscription-microsoft-customer-agreement-across-tenants |
| Programmatically create Partner Agreement Azure subscriptions | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/programmatically-create-subscription-microsoft-partner-agreement |
| Programmatically create Azure subscriptions with legacy APIs | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/programmatically-create-subscription-preview |
| Use Cost Details API for EA billing analysis | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/review-enterprise-billing |
| Retrieve subscription billing data via Cost Details API | https://learn.microsoft.com/en-us/azure/cost-management-billing/manage/review-subscription-billing |
| Use Azure reservation APIs for automation | https://learn.microsoft.com/en-us/azure/cost-management-billing/reservations/reservation-apis |

### Deployment
| Topic | URL |
|-------|-----|
| Set up recurring large-scale cost data exports | https://learn.microsoft.com/en-us/azure/cost-management-billing/costs/ingest-azure-usage-at-scale |