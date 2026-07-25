---
name: azure-well-architected
description: Expert guidance for designing, assessing, and optimizing Azure workloads using Azure Well Architected. Covers design review checklists, recommendations, design principles, tradeoffs, service guides, workload patterns, and assessment questions. Use when designing AI, HPC, SaaS, AVD, or mission-critical Azure workloads with WAF-aligned guidance, and other Azure Well Architected related development tasks.
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-28"
  generator: "docs2skills/1.0.0"
---
# Azure Well Architected Skill

This skill provides expert guidance for designing, assessing, and optimizing Azure workloads using Azure Well Architected. Covers design review checklists, recommendations, design principles, tradeoffs, service guides, workload patterns, and assessment questions. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Design Review Checklists | L35-L43 | Checklists to review Azure workloads for cost, operations, performance, reliability, and security best practices and identify gaps against Well-Architected guidance. |
| Recommendations | L44-L117 | Guidance on cost optimization, operations, performance, reliability, security, and sustainability best practices for architecting and running Azure workloads. |
| Design Principles | L118-L132 | Design patterns and best practices for cost, reliability, security, performance, operations, sustainability, and mission-critical design across AI, SaaS, AVD, HPC, and other Azure workloads. |
| Tradeoffs | L133-L142 | Guidance on weighing cost, reliability, performance, security, and operations tradeoffs in Azure architectures, including regions/AZ choices and cross-pillar design decisions. |
| Service Guides | L143-L178 | End-to-end Well-Architected (WAF) guidance for specific Azure services—covering design, networking, security/IAM, monitoring, BCDR, performance, and cost optimization patterns. |
| Workload Patterns | L179-L223 | Design patterns, reference architectures, and end-to-end guidance for AI, HPC, mission-critical, SaaS, and sustainable workloads on Azure, including platforms, data, ops, security, and governance. |
| Assessment Questions | L224-L235 | Guided assessments and maturity models to evaluate AI, SaaS, AVD, AVS, and other Azure workloads against WAF pillars: cost, reliability, security, performance, and operations. |

### Design Review Checklists
| Topic | URL |
|-------|-----|
| Use Cost Optimization design review checklist for Azure | https://learn.microsoft.com/en-us/azure/well-architected/cost-optimization/checklist |
| Use operational excellence design review checklist | https://learn.microsoft.com/en-us/azure/well-architected/operational-excellence/checklist |
| Use performance efficiency design review checklist | https://learn.microsoft.com/en-us/azure/well-architected/performance-efficiency/checklist |
| Use reliability design checklist for Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/reliability/checklist |
| Use the Security design review checklist for workloads | https://learn.microsoft.com/en-us/azure/well-architected/security/checklist |

### Recommendations
| Topic | URL |
|-------|-----|
| Align Azure resource usage with billing increments | https://learn.microsoft.com/en-us/azure/well-architected/cost-optimization/align-usage-to-billing-increments |
| Implement cost data collection and review for Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/cost-optimization/collect-review-cost-data |
| Use consolidation strategies to reduce Azure costs | https://learn.microsoft.com/en-us/azure/well-architected/cost-optimization/consolidation |
| Build and maintain a cost model for Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/cost-optimization/cost-model |
| Create a culture of financial responsibility for cloud costs | https://learn.microsoft.com/en-us/azure/well-architected/cost-optimization/create-culture-financial-responsibility |
| Negotiate and obtain best provider rates for Azure | https://learn.microsoft.com/en-us/azure/well-architected/cost-optimization/get-best-rates |
| Reduce Azure workload costs through code optimization | https://learn.microsoft.com/en-us/azure/well-architected/cost-optimization/optimize-code-costs |
| Optimize individual component costs in Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/cost-optimization/optimize-component-costs |
| Optimize Azure data storage and management costs | https://learn.microsoft.com/en-us/azure/well-architected/cost-optimization/optimize-data-costs |
| Optimize non-production and production environment costs | https://learn.microsoft.com/en-us/azure/well-architected/cost-optimization/optimize-environment-costs |
| Implement cost optimization for workload data flows | https://learn.microsoft.com/en-us/azure/well-architected/cost-optimization/optimize-flow-costs |
| Optimize personnel time for Azure workload operations | https://learn.microsoft.com/en-us/azure/well-architected/cost-optimization/optimize-personnel-time |
| Optimize scaling strategies to reduce Azure costs | https://learn.microsoft.com/en-us/azure/well-architected/cost-optimization/optimize-scaling-costs |
| Define and enforce spending guardrails for Azure costs | https://learn.microsoft.com/en-us/azure/well-architected/cost-optimization/set-spending-guardrails |
| Develop background jobs to offload application workloads | https://learn.microsoft.com/en-us/azure/well-architected/design-guides/background-jobs |
| Create a disaster recovery plan for multi-region workloads | https://learn.microsoft.com/en-us/azure/well-architected/design-guides/disaster-recovery |
| Implement transient fault handling in cloud applications | https://learn.microsoft.com/en-us/azure/well-architected/design-guides/handle-transient-faults |
| Build workload health models to improve reliability | https://learn.microsoft.com/en-us/azure/well-architected/design-guides/health-modeling |
| Design and operate an incident management practice | https://learn.microsoft.com/en-us/azure/well-architected/design-guides/incident-management |
| Design data partitioning for reliable Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/design-guides/partition-data |
| Implement continuous integration for Azure release engineering | https://learn.microsoft.com/en-us/azure/well-architected/design-guides/release-engineering-continuous-integration |
| Design and implement automation in Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/operational-excellence/enable-automation |
| Formalize development practices for Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/operational-excellence/formalize-development-practices |
| Standardize Azure operations with formalized tasks | https://learn.microsoft.com/en-us/azure/well-architected/operational-excellence/formalize-operations-tasks |
| Design and run an incident management process for Azure | https://learn.microsoft.com/en-us/azure/well-architected/operational-excellence/incident-response |
| Adopt infrastructure as code for Azure deployments | https://learn.microsoft.com/en-us/azure/well-architected/operational-excellence/infrastructure-as-code-design |
| Design an observability and monitoring system in Azure | https://learn.microsoft.com/en-us/azure/well-architected/operational-excellence/observability |
| Implement safe deployment practices for Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/operational-excellence/safe-deployments |
| Apply testing strategies for operational excellence | https://learn.microsoft.com/en-us/azure/well-architected/operational-excellence/testing |
| Standardize development tools and processes for Azure teams | https://learn.microsoft.com/en-us/azure/well-architected/operational-excellence/tools-processes |
| Implement CI/CD-based workload development supply chains | https://learn.microsoft.com/en-us/azure/well-architected/operational-excellence/workload-supply-chain |
| Implement capacity planning for Azure performance efficiency | https://learn.microsoft.com/en-us/azure/well-architected/performance-efficiency/capacity-planning |
| Continuously optimize performance efficiency in Azure | https://learn.microsoft.com/en-us/azure/well-architected/performance-efficiency/continuous-performance-optimize |
| Implement multi-layer performance monitoring for Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/performance-efficiency/monitoring |
| Optimize application code and infrastructure performance on Azure | https://learn.microsoft.com/en-us/azure/well-architected/performance-efficiency/optimize-code-infrastructure |
| Optimize data performance in Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/performance-efficiency/optimize-data-performance |
| Optimize operational tasks to protect workload performance | https://learn.microsoft.com/en-us/azure/well-architected/performance-efficiency/optimize-operational-tasks |
| Define and expose performance targets for Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/performance-efficiency/performance-targets |
| Implement performance testing strategies for Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/performance-efficiency/performance-test |
| Prioritize performance of critical flows in Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/performance-efficiency/prioritize-critical-flows |
| Respond to live performance issues in Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/performance-efficiency/respond-live-performance-issues |
| Optimize scaling and partitioning for Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/performance-efficiency/scale-partition |
| Select Azure services to meet workload performance needs | https://learn.microsoft.com/en-us/azure/well-architected/performance-efficiency/select-services |
| Plan disaster recovery strategies for Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/reliability/disaster-recovery |
| Perform failure mode analysis for Azure reliability | https://learn.microsoft.com/en-us/azure/well-architected/reliability/failure-mode-analysis |
| Identify and prioritize workload flows for reliability | https://learn.microsoft.com/en-us/azure/well-architected/reliability/identify-flows |
| Define availability and recovery targets for reliability | https://learn.microsoft.com/en-us/azure/well-architected/reliability/metrics |
| Implement monitoring strategy for workload reliability | https://learn.microsoft.com/en-us/azure/well-architected/reliability/monitoring |
| Design redundancy strategies to meet reliability targets | https://learn.microsoft.com/en-us/azure/well-architected/reliability/redundancy |
| Implement reliability testing strategy for Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/reliability/reliability-test |
| Design reliable scaling strategies for Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/reliability/scaling |
| Build self-healing and self-preservation into workloads | https://learn.microsoft.com/en-us/azure/well-architected/reliability/self-preservation |
| Implement simplicity and efficiency for reliable workloads | https://learn.microsoft.com/en-us/azure/well-architected/reliability/simplify |
| Securely manage and store application secrets in Azure | https://learn.microsoft.com/en-us/azure/well-architected/security/application-secrets |
| Implement data classification for secure workloads | https://learn.microsoft.com/en-us/azure/well-architected/security/data-classification |
| Apply encryption and secret management for Azure data | https://learn.microsoft.com/en-us/azure/well-architected/security/encryption |
| Establish and apply a security baseline in Azure | https://learn.microsoft.com/en-us/azure/well-architected/security/establish-baseline |
| Implement security hardening controls for Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/security/harden-resources |
| Design identity and access management for workloads | https://learn.microsoft.com/en-us/azure/well-architected/security/identity-access |
| Implement security incident response for Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/security/incident-response |
| Design monitoring and threat detection for Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/security/monitor-threats |
| Implement secure networking and connectivity controls | https://learn.microsoft.com/en-us/azure/well-architected/security/networking |
| Implement secure development lifecycle architecture in Azure | https://learn.microsoft.com/en-us/azure/well-architected/security/secure-development-lifecycle |
| Design segmentation strategies with perimeters and isolation | https://learn.microsoft.com/en-us/azure/well-architected/security/segmentation |
| Implement rigorous security testing for Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/security/test |
| Use cost optimization recommendations for sustainable Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/sustainability/sustainability-cost-optimization-recommendations |
| Adopt operational excellence practices for sustainable Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/sustainability/sustainability-operational-excellence-recommendations |
| Optimize performance efficiency for sustainable Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/sustainability/sustainability-performance-efficiency-recommendations |
| Implement reliability recommendations for sustainable Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/sustainability/sustainability-reliability-recommendations |
| Apply security recommendations to improve sustainable Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/sustainability/sustainability-security-recommendations |

### Design Principles
| Topic | URL |
|-------|-----|
| Apply WAF design principles to AI workloads | https://learn.microsoft.com/en-us/azure/well-architected/ai/design-principles |
| Use architecture patterns that improve cost optimization | https://learn.microsoft.com/en-us/azure/well-architected/cost-optimization/design-patterns |
| Apply Cost Optimization design principles in Azure | https://learn.microsoft.com/en-us/azure/well-architected/cost-optimization/principles |
| Use WAF design principles for Azure HPC architectures | https://learn.microsoft.com/en-us/azure/well-architected/hpc/hpc-design-principles |
| Apply mission-critical design principles on Azure | https://learn.microsoft.com/en-us/azure/well-architected/mission-critical/mission-critical-design-principles |
| Apply Operational Excellence design principles in Azure | https://learn.microsoft.com/en-us/azure/well-architected/operational-excellence/principles |
| Apply Performance Efficiency design principles in Azure | https://learn.microsoft.com/en-us/azure/well-architected/performance-efficiency/principles |
| Apply reliability design principles to Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/reliability/principles |
| Use WAF-aligned design principles for SaaS on Azure | https://learn.microsoft.com/en-us/azure/well-architected/saas/design-principles |
| Apply security design principles with zero trust | https://learn.microsoft.com/en-us/azure/well-architected/security/principles |
| Apply sustainability design methodology for Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/sustainability/sustainability-design-methodology |

### Tradeoffs
| Topic | URL |
|-------|-----|
| Analyze cost optimization tradeoffs across WAF pillars | https://learn.microsoft.com/en-us/azure/well-architected/cost-optimization/tradeoffs |
| Balance regions and availability zones for reliability and cost | https://learn.microsoft.com/en-us/azure/well-architected/design-guides/regions-availability-zones |
| Evaluate operational excellence tradeoffs in Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/operational-excellence/tradeoffs |
| Analyze performance efficiency tradeoffs across WAF pillars | https://learn.microsoft.com/en-us/azure/well-architected/performance-efficiency/tradeoffs |
| Analyze reliability tradeoffs across WAF pillars | https://learn.microsoft.com/en-us/azure/well-architected/reliability/tradeoffs |
| Evaluate security tradeoffs in Azure architectures | https://learn.microsoft.com/en-us/azure/well-architected/security/tradeoffs |

### Service Guides
| Topic | URL |
|-------|-----|
| Apply WAF best practices to Azure App Service Web Apps | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/app-service-web-apps |
| Configure Azure Monitor Application Insights using WAF guidance | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/application-insights |
| Apply WAF best practices to Azure API Management | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-api-management |
| Apply WAF best practices to Azure Application Gateway v2 | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-application-gateway |
| Design and configure Azure Blob Storage with WAF best practices | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-blob-storage |
| Apply Well-Architected best practices to Azure Container Apps | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-container-apps |
| Apply WAF best practices to Azure Database for MySQL | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-database-for-mysql |
| Use WAF-aligned architecture for Azure Databricks | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-databricks |
| Optimize Azure Disk Storage using WAF guidance | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-disk-storage |
| Design Event Grid architectures with WAF best practices | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-event-grid |
| Implement Azure Event Hubs using WAF-aligned patterns | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-event-hubs |
| Architect Azure ExpressRoute connectivity with WAF | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-expressroute |
| Apply Well-Architected best practices to Azure Files | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-files |
| Secure and scale Azure Firewall with WAF practices | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-firewall |
| Design Azure Front Door for global reliability and performance | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-front-door |
| Configure Azure Functions using WAF-aligned best practices | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-functions |
| Optimize Azure Kubernetes Service using WAF guidance | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-kubernetes-service |
| Design Azure Load Balancer deployments with WAF guidance | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-load-balancer |
| Deploy Azure Local with WAF-aligned architecture patterns | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-local |
| Apply Well-Architected practices to Azure Log Analytics | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-log-analytics |
| Apply WAF principles to Azure Machine Learning deployments | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-machine-learning |
| Optimize Azure NetApp Files with WAF-aligned configurations | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-netapp-files |
| Implement Azure Service Bus messaging with WAF guidance | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-service-bus |
| Design Azure Service Fabric clusters using WAF principles | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-service-fabric |
| Configure Azure SQL Database according to WAF best practices | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-sql-database |
| Apply WAF best practices to Azure SQL Managed Instance | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-sql-managed-instance |
| Architect Azure Traffic Manager with WAF-aligned routing | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-traffic-manager |
| Design Azure Virtual WAN architectures using WAF guidance | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/azure-virtual-wan |
| Apply WAF best practices to Azure Cosmos DB for NoSQL | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/cosmos-db |
| Apply WAF best practices to Azure Database for PostgreSQL | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/postgresql |
| Design Azure Virtual Machines and scale sets with WAF | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/virtual-machines |
| Design Azure Virtual Network with Well-Architected best practices | https://learn.microsoft.com/en-us/azure/well-architected/service-guides/virtual-network |

### Workload Patterns
| Topic | URL |
|-------|-----|
| Apply Well-Architected principles to AI workloads | https://learn.microsoft.com/en-us/azure/well-architected/ai/ |
| Design AI-enabled applications on Azure using WAF | https://learn.microsoft.com/en-us/azure/well-architected/ai/application-design |
| Select application platforms for AI workloads on Azure | https://learn.microsoft.com/en-us/azure/well-architected/ai/application-platform |
| Use reference architecture patterns for Azure AI workloads | https://learn.microsoft.com/en-us/azure/well-architected/ai/architecture-pattern |
| Select and design data platforms for Azure AI | https://learn.microsoft.com/en-us/azure/well-architected/ai/data-platform |
| Use a structured design methodology for AI workloads | https://learn.microsoft.com/en-us/azure/well-architected/ai/design-methodology |
| Apply Well-Architected principles to Azure AI workloads | https://learn.microsoft.com/en-us/azure/well-architected/ai/get-started |
| Design grounding data for Azure AI applications | https://learn.microsoft.com/en-us/azure/well-architected/ai/grounding-data-design |
| Implement MLOps and GenAIOps for Azure AI workloads | https://learn.microsoft.com/en-us/azure/well-architected/ai/mlops-genaiops |
| Operate production AI workloads on Azure | https://learn.microsoft.com/en-us/azure/well-architected/ai/operations |
| Define roles and personas for Azure AI teams | https://learn.microsoft.com/en-us/azure/well-architected/ai/personas |
| Apply responsible AI practices in Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/ai/responsible-ai |
| Test and evaluate Azure AI models and systems | https://learn.microsoft.com/en-us/azure/well-architected/ai/test |
| Design training data pipelines for Azure AI workloads | https://learn.microsoft.com/en-us/azure/well-architected/ai/training-data-design |
| Design high-performance computing workloads on Azure | https://learn.microsoft.com/en-us/azure/well-architected/hpc/ |
| Apply Well-Architected guidance to Azure HPC workloads | https://learn.microsoft.com/en-us/azure/well-architected/hpc/get-started-overview |
| Adopt a reference architecture pattern for Azure HPC | https://learn.microsoft.com/en-us/azure/well-architected/hpc/hpc-architecture-pattern |
| Design mission-critical workloads on Azure for high reliability | https://learn.microsoft.com/en-us/azure/well-architected/mission-critical/ |
| Design resilient mission-critical applications on Azure | https://learn.microsoft.com/en-us/azure/well-architected/mission-critical/mission-critical-application-design |
| Select Azure application platforms for mission-critical apps | https://learn.microsoft.com/en-us/azure/well-architected/mission-critical/mission-critical-application-platform |
| Adopt mission-critical architecture pattern on Azure | https://learn.microsoft.com/en-us/azure/well-architected/mission-critical/mission-critical-architecture-pattern |
| Choose data platforms for mission-critical Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/mission-critical/mission-critical-data-platform |
| Design deployment and testing for mission-critical workloads | https://learn.microsoft.com/en-us/azure/well-architected/mission-critical/mission-critical-deployment-testing |
| Use mission-critical design methodology on Azure | https://learn.microsoft.com/en-us/azure/well-architected/mission-critical/mission-critical-design-methodology |
| Design networking for mission-critical Azure applications | https://learn.microsoft.com/en-us/azure/well-architected/mission-critical/mission-critical-networking-connectivity |
| Operationalize mission-critical workloads with DevOps on Azure | https://learn.microsoft.com/en-us/azure/well-architected/mission-critical/mission-critical-operational-procedures |
| Apply WAF to mission-critical Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/mission-critical/mission-critical-overview |
| Implement security for mission-critical Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/mission-critical/mission-critical-security |
| Apply WAF best practices to SaaS solutions on Azure | https://learn.microsoft.com/en-us/azure/well-architected/saas/ |
| Develop an AI strategy for Azure-based SaaS products | https://learn.microsoft.com/en-us/azure/well-architected/saas/ai-strategy |
| Design billing and cost management for SaaS on Azure | https://learn.microsoft.com/en-us/azure/well-architected/saas/billing-cost-management |
| Choose and operate compute platforms for SaaS on Azure | https://learn.microsoft.com/en-us/azure/well-architected/saas/compute |
| Design data platform and tenancy for SaaS workloads on Azure | https://learn.microsoft.com/en-us/azure/well-architected/saas/data |
| Apply structured design methodology to SaaS workloads on Azure | https://learn.microsoft.com/en-us/azure/well-architected/saas/design-methodology |
| Apply DevOps practices to manage SaaS workloads on Azure | https://learn.microsoft.com/en-us/azure/well-architected/saas/devops |
| Implement governance for SaaS workloads on Azure | https://learn.microsoft.com/en-us/azure/well-architected/saas/governance |
| Design identity and access management for SaaS workloads | https://learn.microsoft.com/en-us/azure/well-architected/saas/identity-access |
| Design incident management processes for SaaS solutions on Azure | https://learn.microsoft.com/en-us/azure/well-architected/saas/incident-management |
| Design networking topology and security for SaaS on Azure | https://learn.microsoft.com/en-us/azure/well-architected/saas/networking |
| Plan region selection and resource organization for SaaS on Azure | https://learn.microsoft.com/en-us/azure/well-architected/saas/resource-organization |
| Design sustainable AI workloads on Azure | https://learn.microsoft.com/en-us/azure/well-architected/sustainability/sustainable-ai-design |

### Assessment Questions
| Topic | URL |
|-------|-----|
| Use AI workload assessment for WAF alignment | https://learn.microsoft.com/en-us/azure/well-architected/ai/assessment |
| Assess Cost Optimization maturity for Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/cost-optimization/maturity-model |
| Use Azure Well-Architected Review assessment effectively | https://learn.microsoft.com/en-us/azure/well-architected/design-guides/implementing-recommendations |
| Use mission-critical workload readiness assessment on Azure | https://learn.microsoft.com/en-us/azure/well-architected/mission-critical/mission-critical-assessment |
| Evaluate Operational Excellence maturity for workloads | https://learn.microsoft.com/en-us/azure/well-architected/operational-excellence/maturity-model |
| Assess Performance Efficiency maturity for Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/performance-efficiency/maturity-model |
| Assess reliability maturity for Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/reliability/maturity-model |
| Use SaaS workload assessment tool for Azure architectures | https://learn.microsoft.com/en-us/azure/well-architected/saas/assessment |
| Evaluate security maturity for Azure workloads | https://learn.microsoft.com/en-us/azure/well-architected/security/maturity-model |