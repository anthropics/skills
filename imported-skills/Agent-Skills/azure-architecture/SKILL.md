---
name: azure-architecture
description: Expert guidance for designing Azure solutions using Azure Architecture. Covers reference architectures, solution ideas, design patterns, technology choices, architecture styles, best practices, anti-patterns, example workloads, and migration guides. Use when designing AKS, SAP, IoT, data/AI platforms, or migrating AWS/GCP/on-prem workloads to Azure, and other Azure Architecture related development tasks.
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Architecture Skill

This skill provides expert guidance for designing Azure solutions using Azure Architecture. Covers reference architectures, solution ideas, design patterns, technology choices, architecture styles, best practices, anti-patterns, example workloads, and migration guides. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Reference Architectures | L37-L90 | End-to-end Azure solution blueprints: mission-critical, secure, and hybrid architectures for AKS, data platforms, SAP, networking, DR, MLOps, and enterprise app deployments. |
| Solution Ideas | L91-L125 | End-to-end solution patterns for AI, data, analytics, IoT, security, and mainframe/SAP migration on Azure, showing how to design, integrate, and operate complete architectures. |
| Design Patterns | L126-L174 | Patterns for resilient, scalable, and secure Azure app architectures: messaging, transactions, caching, routing, identity, global distribution, legacy migration, and workload isolation. |
| Technology Choices | L175-L209 | Guides for choosing the right Azure/Fabric services (AI/ML, data, analytics, storage, compute, networking, messaging, containers, vector/search) for specific workloads and architectures. |
| Architecture Styles | L210-L221 | Guidance on choosing and designing Azure app architectures (big compute, big data, event-driven, microservices, N-tier, web-queue-worker) with patterns, components, and best practices. |
| Best Practices | L222-L279 | Best-practice patterns for Azure apps: secure APIs/RAG/IoT/SAP, MLOps and model lifecycle, scaling, caching/CDN, DR, networking/DNS/Private Link, AKS ops, Event Hubs + Functions, and monitoring. |
| Anti-patterns | L280-L294 | Diagnosing and fixing common Azure performance and scalability anti-patterns (busy DB/front end, chatty I/O, no caching, noisy neighbors, retry storms, sync I/O, monolithic persistence). |
| Example Workloads | L295-L375 | End-to-end Azure solution blueprints: real-world workloads for data/AI, security, networking, hybrid, mainframe, SAP, IoT, AKS, Fabric, and app modernization with detailed reference architectures. |
| Migration Guides | L376-L405 | Guides for migrating from AWS/GCP/on-prem (incl. Oracle, Kafka, EKS) to Azure, mapping services, architectures, identity, networking, security, and cost/ops differences. |

### Reference Architectures
| Topic | URL |
|-------|-----|
| Deploy a baseline enterprise Foundry chat reference architecture | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/architecture/baseline-microsoft-foundry-chat |
| Implement baseline Foundry chat in an Azure landing zone | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/architecture/baseline-microsoft-foundry-landing-zone |
| Deploy MLOps v2 CI/CD and retraining architectures | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/guide/machine-learning-operations-v2 |
| Implement DR-ready Azure enterprise data platform architecture | https://learn.microsoft.com/en-us/azure/architecture/data-guide/disaster-recovery/dr-for-azure-data-platform-architecture |
| Enterprise-hardened Azure Data Factory lakehouse architecture | https://learn.microsoft.com/en-us/azure/architecture/databases/architecture/azure-data-factory-enterprise-hardened |
| Mission-critical Azure Data Factory analytics architecture | https://learn.microsoft.com/en-us/azure/architecture/databases/architecture/azure-data-factory-mission-critical |
| Baseline medallion lakehouse with Azure Data Factory | https://learn.microsoft.com/en-us/azure/architecture/databases/architecture/azure-data-factory-on-azure-landing-zones-baseline |
| Deploy MongoDB Atlas securely on Azure | https://learn.microsoft.com/en-us/azure/architecture/databases/architecture/mongodb-atlas-baseline |
| Move archive data from mainframes to Azure storage | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/mainframe/move-archive-data-mainframes |
| Deploy a hub-spoke AKS cluster with Azure Firewall | https://learn.microsoft.com/en-us/azure/architecture/guide/aks/aks-firewall |
| Architect mission-critical global content delivery on Azure | https://learn.microsoft.com/en-us/azure/architecture/guide/networking/global-web-applications/mission-critical-content-delivery |
| Implement mission-critical global HTTP ingress on Azure | https://learn.microsoft.com/en-us/azure/architecture/guide/networking/global-web-applications/mission-critical-global-http-ingress |
| Design global routing redundancy for mission-critical web apps | https://learn.microsoft.com/en-us/azure/architecture/guide/networking/global-web-applications/overview |
| Implement multiregion load balancing with Traffic Manager and Application Gateway | https://learn.microsoft.com/en-us/azure/architecture/high-availability/traffic-manager-application-gateway |
| Implement enterprise cloud file shares with Azure Files | https://learn.microsoft.com/en-us/azure/architecture/hybrid/azure-files-private |
| Design Azure Local baseline infrastructure architecture | https://learn.microsoft.com/en-us/azure/architecture/hybrid/azure-local-baseline |
| Implement Azure Local storage switchless architecture | https://learn.microsoft.com/en-us/azure/architecture/hybrid/azure-local-switchless |
| Design Azure Virtual Desktop on Azure Local | https://learn.microsoft.com/en-us/azure/architecture/hybrid/azure-local-workload-virtual-desktop |
| Implement a hub-spoke network topology in Azure | https://learn.microsoft.com/en-us/azure/architecture/networking/architecture/hub-spoke |
| Implement hub-spoke networking with Azure Virtual WAN | https://learn.microsoft.com/en-us/azure/architecture/networking/architecture/hub-spoke-virtual-wan-architecture |
| Implement TIC 3.0-compliant internet access on Azure | https://learn.microsoft.com/en-us/azure/architecture/networking/architecture/trusted-internet-connections |
| Deploy Microsoft Entra security for AWS identities | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/aws/aws-azure-ad-security |
| Host GPU-based ML and HPC workloads on AKS | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/containers/aks-gpu/gpu-aks |
| Deploy microservices architecture on AKS with DevOps | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/containers/aks-microservices/aks-microservices |
| Deploy advanced AKS microservices with secure networking | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/containers/aks-microservices/aks-microservices-advanced |
| Apply application design patterns for mission-critical Azure apps | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/containers/aks-mission-critical/mission-critical-app-design |
| Choose application platform for mission-critical workloads | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/containers/aks-mission-critical/mission-critical-app-platform |
| Design data platforms for mission-critical Azure solutions | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/containers/aks-mission-critical/mission-critical-data-platform |
| Implement deployment and testing for mission-critical workloads | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/containers/aks-mission-critical/mission-critical-deploy-test |
| Implement health modeling for mission-critical Azure workloads | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/containers/aks-mission-critical/mission-critical-health-modeling |
| Design mission-critical architectures on Azure AKS | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/containers/aks-mission-critical/mission-critical-intro |
| Design networking for mission-critical AKS workloads | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/containers/aks-mission-critical/mission-critical-networking |
| Operate and maintain mission-critical workloads on Azure | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/containers/aks-mission-critical/mission-critical-operations |
| Apply security controls to mission-critical Azure workloads | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/containers/aks-mission-critical/mission-critical-security |
| Deploy a multiregion AKS baseline architecture | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/containers/aks-multi-region/aks-multi-cluster |
| Use baseline reference architecture for secure AKS clusters | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/containers/aks/baseline-aks |
| Build Azure Red Hat OpenShift landing zone for financial services | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/containers/aro/azure-redhat-openshift-financial-services-workloads |
| Deploy a Databricks-based stream processing pipeline | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/data/stream-processing-databricks |
| Implement stream processing with Azure Stream Analytics | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/data/stream-processing-stream-analytics |
| Implement secure hybrid DMZ network in Azure | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/dmz/secure-vnet-dmz |
| Implement basic enterprise integration with Logic Apps and API Management | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/enterprise-integration/basic-enterprise-integration |
| Deploy ExpressRoute with VPN failover for hybrid connectivity | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/hybrid-networking/expressroute-vpn-failover |
| Replicate and sync mainframe data to Azure during migration | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/migration/sync-mainframe-data-with-azure |
| Deploy and secure Linux VMs with full Azure stack | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/n-tier/linux-vm |
| Deploy and secure Windows VMs with full Azure stack | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/n-tier/windows-vm |
| Deploy SAP BW/4HANA on Azure Linux VMs for HA | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/sap/run-sap-bw4hana-with-linux-virtual-machines |
| Deploy SAP HANA scale-up systems on Azure Linux VMs | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/sap/run-sap-hana-for-linux-virtual-machines |
| High-availability multi-zone App Service Environment deployment | https://learn.microsoft.com/en-us/azure/architecture/web-apps/app-service-environment/architectures/app-service-environment-high-availability-deployment |
| Enterprise App Service Environment v3 deployment architecture | https://learn.microsoft.com/en-us/azure/architecture/web-apps/app-service-environment/architectures/app-service-environment-standard-deployment |
| Baseline zone-redundant App Service web app architecture | https://learn.microsoft.com/en-us/azure/architecture/web-apps/app-service/architectures/baseline-zone-redundant |

### Solution Ideas
| Topic | URL |
|-------|-----|
| Generate AI-assisted documents from enterprise data | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/idea/generate-documents-from-your-data |
| Design image classification apps using Azure services | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/idea/intelligent-apps-image-processing |
| Scale many-models machine learning on Azure | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/idea/many-models-machine-learning-azure-machine-learning |
| Process multimodal content with Azure AI services | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/idea/multi-modal-content-processing |
| Design multi-agent workflow automation on Azure | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/idea/multiple-agent-workflow-automation |
| Forecast customer orders with Azure AI | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/idea/next-order-forecasting |
| Orchestrate MLOps pipelines with Azure Databricks | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/idea/orchestrate-machine-learning-azure-databricks |
| Design a conversation analytics solution with Foundry tools | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/idea/unlock-insights-from-conversational-data |
| Design polyglot persistence with Cosmos DB and SQL | https://learn.microsoft.com/en-us/azure/architecture/databases/idea/combine-relational-nosql |
| Use Cosmos DB change feed for minimal storage replication | https://learn.microsoft.com/en-us/azure/architecture/databases/idea/minimal-storage-change-feed-replicate-data |
| Plan migration of IBM z/OS OLTP workloads to Azure | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/mainframe/ibm-zos-online-transaction-processing-azure |
| Integrate IBM message queues with Azure data platform | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/mainframe/integrate-ibm-message-queues-azure |
| Simulate IoT device behavior with Azure Load Testing and custom plugins | https://learn.microsoft.com/en-us/azure/architecture/guide/testing/load-testing/load-testing-with-custom-plugins |
| Build real-time analytics using Azure Service Bus and Microsoft Fabric | https://learn.microsoft.com/en-us/azure/architecture/solution-ideas/articles/analytics-service-bus |
| Design a modern analytics architecture with Azure Databricks | https://learn.microsoft.com/en-us/azure/architecture/solution-ideas/articles/azure-databricks-modern-analytics-architecture |
| Design first-layer defense with Azure security services | https://learn.microsoft.com/en-us/azure/architecture/solution-ideas/articles/azure-security-build-first-layer-defense |
| Design AKS-based real-time data streaming architecture | https://learn.microsoft.com/en-us/azure/architecture/solution-ideas/articles/data-streaming-scenario |
| Design a DevSecOps IaC pipeline with GitHub and Azure | https://learn.microsoft.com/en-us/azure/architecture/solution-ideas/articles/devsecops-infrastructure-as-code |
| Build batch and streaming ETL with Databricks and Delta Lake | https://learn.microsoft.com/en-us/azure/architecture/solution-ideas/articles/ingest-etl-stream-with-adb |
| Design IoT analytics with Azure Data Explorer and IoT Hub | https://learn.microsoft.com/en-us/azure/architecture/solution-ideas/articles/iot-azure-data-explorer |
| Design an Azure industrial IoT reference solution | https://learn.microsoft.com/en-us/azure/architecture/solution-ideas/articles/iot-industrial-solution-architecture |
| Replicate and sync mainframe files to Azure storage | https://learn.microsoft.com/en-us/azure/architecture/solution-ideas/articles/mainframe-azure-file-replication |
| Map organizational threats using Azure security tools | https://learn.microsoft.com/en-us/azure/architecture/solution-ideas/articles/map-threats-it-environment |
| Integrate Azure and Microsoft Defender XDR security services | https://learn.microsoft.com/en-us/azure/architecture/solution-ideas/articles/microsoft-365-defender-security-integrate-azure |
| Implement a second defense layer with Microsoft Defender XDR | https://learn.microsoft.com/en-us/azure/architecture/solution-ideas/articles/microsoft-defender-xdr-build-second-layer-defense |
| Automate incident response with Microsoft Sentinel playbooks | https://learn.microsoft.com/en-us/azure/architecture/solution-ideas/articles/microsoft-sentinel-automated-response |
| Plan cross-tenant workload migrations between Entra tenants | https://learn.microsoft.com/en-us/azure/architecture/solution-ideas/articles/migrate-cloud-workloads-across-security-tenants |
| Design multilayered security for Azure virtual machines | https://learn.microsoft.com/en-us/azure/architecture/solution-ideas/articles/multilayered-protection-azure-vm |
| Automate SAP infrastructure on Azure with SUSE | https://learn.microsoft.com/en-us/azure/architecture/solution-ideas/articles/sap-workload-automation-suse |
| Design cross-region TDE resiliency for SQL Managed Instance with Managed HSM | https://learn.microsoft.com/en-us/azure/architecture/solution-ideas/articles/secure-sql-managed-instance-managed-hardware-security-module |
| Design a modern SMB data platform with Fabric and Databricks | https://learn.microsoft.com/en-us/azure/architecture/solution-ideas/articles/small-medium-modern-data-platform |

### Design Patterns
| Topic | URL |
|-------|-----|
| Implement Transactional Outbox with Cosmos DB and Service Bus | https://learn.microsoft.com/en-us/azure/architecture/databases/guide/transactional-out-box-cosmos |
| Virtual hub extension pattern for shared services in Virtual WAN | https://learn.microsoft.com/en-us/azure/architecture/networking/guide/private-link-virtual-wan-dns-virtual-hub-extension-pattern |
| Implement the Ambassador pattern for helper services | https://learn.microsoft.com/en-us/azure/architecture/patterns/ambassador |
| Apply the Anti-Corruption Layer integration pattern | https://learn.microsoft.com/en-us/azure/architecture/patterns/anti-corruption-layer |
| Use the Asynchronous Request-Reply pattern for long tasks | https://learn.microsoft.com/en-us/azure/architecture/patterns/asynchronous-request-reply |
| Design Backends for Frontends for tailored clients | https://learn.microsoft.com/en-us/azure/architecture/patterns/backends-for-frontends |
| Apply the Bulkhead pattern to isolate failures | https://learn.microsoft.com/en-us/azure/architecture/patterns/bulkhead |
| Use the Cache-Aside pattern for on-demand caching | https://learn.microsoft.com/en-us/azure/architecture/patterns/cache-aside |
| Implement the Choreography pattern for workflows | https://learn.microsoft.com/en-us/azure/architecture/patterns/choreography |
| Use the Circuit Breaker pattern for resilient calls | https://learn.microsoft.com/en-us/azure/architecture/patterns/circuit-breaker |
| Apply the Claim-Check pattern for large messages | https://learn.microsoft.com/en-us/azure/architecture/patterns/claim-check |
| Apply the Compensating Transaction pattern in Azure | https://learn.microsoft.com/en-us/azure/architecture/patterns/compensating-transaction |
| Use the Competing Consumers pattern for scaling | https://learn.microsoft.com/en-us/azure/architecture/patterns/competing-consumers |
| Consolidate compute with the Resource Consolidation pattern | https://learn.microsoft.com/en-us/azure/architecture/patterns/compute-resource-consolidation |
| Apply the CQRS pattern to separate reads and writes | https://learn.microsoft.com/en-us/azure/architecture/patterns/cqrs |
| Implement the Deployment Stamps pattern for scale | https://learn.microsoft.com/en-us/azure/architecture/patterns/deployment-stamp |
| Implement Event Sourcing with an append-only store | https://learn.microsoft.com/en-us/azure/architecture/patterns/event-sourcing |
| Use the External Configuration Store pattern on Azure | https://learn.microsoft.com/en-us/azure/architecture/patterns/external-configuration-store |
| Implement federated identity authentication in Azure | https://learn.microsoft.com/en-us/azure/architecture/patterns/federated-identity |
| Implement the Gatekeeper security pattern on Azure | https://learn.microsoft.com/en-us/azure/architecture/patterns/gatekeeper |
| Apply the Gateway Aggregation pattern for backend calls | https://learn.microsoft.com/en-us/azure/architecture/patterns/gateway-aggregation |
| Apply the Gateway Offloading pattern for shared services | https://learn.microsoft.com/en-us/azure/architecture/patterns/gateway-offloading |
| Use the Gateway Routing pattern for single-endpoint APIs | https://learn.microsoft.com/en-us/azure/architecture/patterns/gateway-routing |
| Implement the Geode pattern for global active-active | https://learn.microsoft.com/en-us/azure/architecture/patterns/geodes |
| Apply the Health Endpoint Monitoring pattern | https://learn.microsoft.com/en-us/azure/architecture/patterns/health-endpoint-monitoring |
| Use the Index Table pattern to speed queries | https://learn.microsoft.com/en-us/azure/architecture/patterns/index-table |
| Implement the Leader Election pattern for coordination | https://learn.microsoft.com/en-us/azure/architecture/patterns/leader-election |
| Use the Materialized View pattern for fast queries | https://learn.microsoft.com/en-us/azure/architecture/patterns/materialized-view |
| Apply the Messaging Bridge pattern to integrate systems | https://learn.microsoft.com/en-us/azure/architecture/patterns/messaging-bridge |
| Implement the Pipes and Filters integration pattern | https://learn.microsoft.com/en-us/azure/architecture/patterns/pipes-and-filters |
| Use the Priority Queue pattern for workloads | https://learn.microsoft.com/en-us/azure/architecture/patterns/priority-queue |
| Apply the Publisher-Subscriber pattern on Azure | https://learn.microsoft.com/en-us/azure/architecture/patterns/publisher-subscriber |
| Implement the Quarantine pattern for software supply chain | https://learn.microsoft.com/en-us/azure/architecture/patterns/quarantine |
| Apply the Queue-Based Load Leveling pattern on Azure | https://learn.microsoft.com/en-us/azure/architecture/patterns/queue-based-load-leveling |
| Apply the Rate Limiting design pattern in Azure | https://learn.microsoft.com/en-us/azure/architecture/patterns/rate-limiting-pattern |
| Implement the Retry pattern for transient faults | https://learn.microsoft.com/en-us/azure/architecture/patterns/retry |
| Implement the Saga pattern for distributed transactions | https://learn.microsoft.com/en-us/azure/architecture/patterns/saga |
| Coordinate actions with Scheduler Agent Supervisor pattern | https://learn.microsoft.com/en-us/azure/architecture/patterns/scheduler-agent-supervisor |
| Apply the Sequential Convoy messaging pattern in Azure | https://learn.microsoft.com/en-us/azure/architecture/patterns/sequential-convoy |
| Implement the Sharding data partitioning pattern on Azure | https://learn.microsoft.com/en-us/azure/architecture/patterns/sharding |
| Use the Sidecar pattern for cross-cutting concerns | https://learn.microsoft.com/en-us/azure/architecture/patterns/sidecar |
| Host static content using the Static Content Hosting pattern | https://learn.microsoft.com/en-us/azure/architecture/patterns/static-content-hosting |
| Apply the Strangler Fig pattern for legacy migration | https://learn.microsoft.com/en-us/azure/architecture/patterns/strangler-fig |
| Implement the Throttling pattern for resilient Azure apps | https://learn.microsoft.com/en-us/azure/architecture/patterns/throttling |
| Secure direct access using the Valet Key pattern | https://learn.microsoft.com/en-us/azure/architecture/patterns/valet-key |

### Technology Choices
| Topic | URL |
|-------|-----|
| Compare Microsoft machine learning platforms and tools | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/guide/data-science-and-machine-learning |
| Choose Azure AI services for image and video processing | https://learn.microsoft.com/en-us/azure/architecture/data-guide/ai-services/image-video-processing |
| Select Azure speech recognition and generation services | https://learn.microsoft.com/en-us/azure/architecture/data-guide/ai-services/speech-recognition-generation |
| Choose Azure targeted language processing services | https://learn.microsoft.com/en-us/azure/architecture/data-guide/ai-services/targeted-language-processing |
| Select Azure data transfer tools and services | https://learn.microsoft.com/en-us/azure/architecture/data-guide/scenarios/data-transfer |
| Select appropriate Azure AI services for applications | https://learn.microsoft.com/en-us/azure/architecture/data-guide/technology-choices/ai-services |
| Choose Azure technologies for analytics and reporting | https://learn.microsoft.com/en-us/azure/architecture/data-guide/technology-choices/analysis-visualizations-reporting |
| Select the right analytical data store in Azure | https://learn.microsoft.com/en-us/azure/architecture/data-guide/technology-choices/analytical-data-stores |
| Select Azure batch processing technologies for big data | https://learn.microsoft.com/en-us/azure/architecture/data-guide/technology-choices/batch-processing |
| Select big data storage technologies in Azure | https://learn.microsoft.com/en-us/azure/architecture/data-guide/technology-choices/data-storage |
| Choose an analytical data store in Microsoft Fabric | https://learn.microsoft.com/en-us/azure/architecture/data-guide/technology-choices/fabric-analytical-data-stores |
| Select the right Microsoft Fabric deployment pattern | https://learn.microsoft.com/en-us/azure/architecture/data-guide/technology-choices/fabric-deployment-patterns |
| Select Azure services for NLP workloads | https://learn.microsoft.com/en-us/azure/architecture/data-guide/technology-choices/natural-language-processing |
| Choose Azure data pipeline orchestration services | https://learn.microsoft.com/en-us/azure/architecture/data-guide/technology-choices/pipeline-orchestration-data-movement |
| Choose an Azure search data store technology | https://learn.microsoft.com/en-us/azure/architecture/data-guide/technology-choices/search-options |
| Compare Azure real-time stream processing services | https://learn.microsoft.com/en-us/azure/architecture/data-guide/technology-choices/stream-processing |
| Compare Azure data store models for workloads | https://learn.microsoft.com/en-us/azure/architecture/data-guide/technology-choices/understand-data-store-models |
| Select the right Azure container hosting service | https://learn.microsoft.com/en-us/azure/architecture/guide/choose-azure-container-service |
| Choose the right Azure container service for workloads | https://learn.microsoft.com/en-us/azure/architecture/guide/container-service-general-considerations |
| Select the right Azure compute service | https://learn.microsoft.com/en-us/azure/architecture/guide/technology-choices/compute-decision-tree |
| Prepare to choose Azure data stores | https://learn.microsoft.com/en-us/azure/architecture/guide/technology-choices/data-stores-getting-started |
| Choose Azure hybrid hosting and connectivity options | https://learn.microsoft.com/en-us/azure/architecture/guide/technology-choices/hybrid-considerations |
| Select Azure load balancing services for applications | https://learn.microsoft.com/en-us/azure/architecture/guide/technology-choices/load-balancing-overview |
| Choose Azure asynchronous messaging services | https://learn.microsoft.com/en-us/azure/architecture/guide/technology-choices/messaging |
| Select the right Azure storage service | https://learn.microsoft.com/en-us/azure/architecture/guide/technology-choices/storage-options |
| Navigate Azure technology choice decision guides | https://learn.microsoft.com/en-us/azure/architecture/guide/technology-choices/technology-choices-overview |
| Select an Azure service for vector search | https://learn.microsoft.com/en-us/azure/architecture/guide/technology-choices/vector-search |
| Choose Azure compute platform for microservices workloads | https://learn.microsoft.com/en-us/azure/architecture/microservices/design/compute-options |
| Choose Azure compute platform for microservices workloads | https://learn.microsoft.com/en-us/azure/architecture/microservices/design/compute-options |
| Choose Kubernetes edge compute options in Azure | https://learn.microsoft.com/en-us/azure/architecture/operator-guides/aks/choose-kubernetes-edge-compute-option |
| Choose connectivity options for on-premises to Azure VNets | https://learn.microsoft.com/en-us/azure/architecture/reference-architectures/hybrid-networking/ |

### Architecture Styles
| Topic | URL |
|-------|-----|
| Understand and compare Azure architecture styles | https://learn.microsoft.com/en-us/azure/architecture/guide/architecture-styles/ |
| Apply Big Compute architecture style on Azure | https://learn.microsoft.com/en-us/azure/architecture/guide/architecture-styles/big-compute |
| Design Big Data architecture style on Azure | https://learn.microsoft.com/en-us/azure/architecture/guide/architecture-styles/big-data |
| Apply event-driven architecture style on Azure | https://learn.microsoft.com/en-us/azure/architecture/guide/architecture-styles/event-driven |
| Adopt microservices architecture style on Azure | https://learn.microsoft.com/en-us/azure/architecture/guide/architecture-styles/microservices |
| Implement N-tier architecture style on Azure | https://learn.microsoft.com/en-us/azure/architecture/guide/architecture-styles/n-tier |
| Use Web-Queue-Worker architecture style on Azure | https://learn.microsoft.com/en-us/azure/architecture/guide/architecture-styles/web-queue-worker |
| Design and implement microservices architecture on Azure | https://learn.microsoft.com/en-us/azure/architecture/microservices/design/ |

### Best Practices
| Topic | URL |
|-------|-----|
| Use a gateway to securely expose Foundry models | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/guide/azure-openai-gateway-guide |
| Extend existing MLOps to generative AI operations | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/guide/genaiops-for-mlops |
| Manage foundation model versions and life cycles | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/guide/manage-foundation-models-lifecycle |
| Implement agentic RAG architectures with Azure AI | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/guide/rag/rag-agentic |
| Configure and optimize RAG information retrieval on Azure | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/guide/rag/rag-information-retrieval |
| Engineer effective prompts for Azure RAG solutions | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/guide/rag/rag-prompt-engineering |
| Design and evaluate Azure RAG solutions rigorously | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/guide/rag/rag-solution-design-and-evaluation-guide |
| Securely design multitenant RAG inferencing solutions | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/guide/secure-multitenant-rag |
| Design RESTful web APIs using Azure best practices | https://learn.microsoft.com/en-us/azure/architecture/best-practices/api-design |
| Implement and publish RESTful web APIs effectively | https://learn.microsoft.com/en-us/azure/architecture/best-practices/api-implementation |
| Implement autoscaling best practices on Azure | https://learn.microsoft.com/en-us/azure/architecture/best-practices/auto-scaling |
| Implement reliable, scalable background jobs on Azure | https://learn.microsoft.com/en-us/azure/architecture/best-practices/background-jobs |
| Apply caching best practices for Azure architectures | https://learn.microsoft.com/en-us/azure/architecture/best-practices/caching |
| Implement CDN best practices for Azure workloads | https://learn.microsoft.com/en-us/azure/architecture/best-practices/cdn |
| Design data partitioning strategies for Azure solutions | https://learn.microsoft.com/en-us/azure/architecture/best-practices/data-partitioning |
| Apply Azure data partitioning strategies by service | https://learn.microsoft.com/en-us/azure/architecture/best-practices/data-partitioning-strategies |
| Preserve HTTP host headers behind Azure reverse proxies | https://learn.microsoft.com/en-us/azure/architecture/best-practices/host-name-preservation |
| Apply Azure cloud application best practices | https://learn.microsoft.com/en-us/azure/architecture/best-practices/index-best-practices |
| Choose message encoding formats for cloud messaging | https://learn.microsoft.com/en-us/azure/architecture/best-practices/message-encode |
| Implement monitoring and diagnostics best practices in Azure | https://learn.microsoft.com/en-us/azure/architecture/best-practices/monitoring |
| Handle transient faults in cloud-based applications | https://learn.microsoft.com/en-us/azure/architecture/best-practices/transient-faults |
| Design disaster recovery strategy for Azure data platforms | https://learn.microsoft.com/en-us/azure/architecture/data-guide/disaster-recovery/dr-for-azure-data-platform-overview |
| Apply DR recommendations and recovery objectives for Azure data | https://learn.microsoft.com/en-us/azure/architecture/data-guide/disaster-recovery/dr-for-azure-data-platform-recommendations |
| Plan DR activities for Azure data platform components | https://learn.microsoft.com/en-us/azure/architecture/data-guide/disaster-recovery/dr-for-azure-data-platform-scenario-details |
| Optimize Apache Cassandra performance on Azure VMs | https://learn.microsoft.com/en-us/azure/architecture/databases/guide/cassandra |
| Build AKS CI/CD pipelines using Azure Pipelines | https://learn.microsoft.com/en-us/azure/architecture/guide/aks/aks-cicd-azure-pipelines |
| Implement high availability for multitier AKS applications | https://learn.microsoft.com/en-us/azure/architecture/guide/aks/aks-high-availability |
| Implement blue-green deployment strategy for AKS clusters | https://learn.microsoft.com/en-us/azure/architecture/guide/aks/blue-green-deployment-for-aks |
| Apply coordination-minimizing practices for scalable services | https://learn.microsoft.com/en-us/azure/architecture/guide/design-principles/minimize-coordination |
| Scale Azure IoT Hub solutions to millions of devices | https://learn.microsoft.com/en-us/azure/architecture/guide/iot/scale-iot-solution-azure |
| Design multitenant architectures for Azure IoT Hub solutions | https://learn.microsoft.com/en-us/azure/architecture/guide/multitenant/approaches/iot |
| Secure inbound and outbound internet for SAP on Azure | https://learn.microsoft.com/en-us/azure/architecture/guide/sap/sap-internet-inbound-outbound |
| Apply Azure network best practices for SAP landscapes | https://learn.microsoft.com/en-us/azure/architecture/guide/sap/sap-whole-landscape |
| Apply best practices for workloads on Azure Spot VMs | https://learn.microsoft.com/en-us/azure/architecture/guide/spot/spot-eviction |
| Run continuous validation with Load Testing and Chaos Studio | https://learn.microsoft.com/en-us/azure/architecture/guide/testing/mission-critical-deployment-testing |
| Design hybrid DNS for Azure and on-premises | https://learn.microsoft.com/en-us/azure/architecture/hybrid/hybrid-dns-infra |
| Prevent IPv4 address exhaustion in large Azure networks | https://learn.microsoft.com/en-us/azure/architecture/networking/guide/internet-protocol-version-4-exhaustion |
| Use Azure Private Link in hub-spoke networks | https://learn.microsoft.com/en-us/azure/architecture/networking/guide/private-link-hub-spoke-network |
| Configure DNS for Private Link in Azure Virtual WAN | https://learn.microsoft.com/en-us/azure/architecture/networking/guide/private-link-virtual-wan-dns-guide |
| Check and troubleshoot AKS cluster health | https://learn.microsoft.com/en-us/azure/architecture/operator-guides/aks/aks-triage-cluster-health |
| Validate AKS admission controller health and impact | https://learn.microsoft.com/en-us/azure/architecture/operator-guides/aks/aks-triage-controllers |
| Monitor and triage AKS workload deployments | https://learn.microsoft.com/en-us/azure/architecture/operator-guides/aks/aks-triage-deployment |
| Diagnose AKS node and pod health issues | https://learn.microsoft.com/en-us/azure/architecture/operator-guides/aks/aks-triage-node-health |
| Use top-down triage practices for AKS operations | https://learn.microsoft.com/en-us/azure/architecture/operator-guides/aks/aks-triage-practices |
| Apply day-2 operations practices for AKS clusters | https://learn.microsoft.com/en-us/azure/architecture/operator-guides/aks/day-2-operations-guide |
| Troubleshoot networking issues in AKS clusters | https://learn.microsoft.com/en-us/azure/architecture/operator-guides/aks/troubleshoot-network-aks |
| Architect Event Hubs integrations with Azure Functions | https://learn.microsoft.com/en-us/azure/architecture/serverless/event-hubs-functions/event-hubs-functions |
| Monitor Event Hubs and Azure Functions with Application Insights | https://learn.microsoft.com/en-us/azure/architecture/serverless/event-hubs-functions/observability |
| Optimize Event Hubs-triggered Azure Functions performance | https://learn.microsoft.com/en-us/azure/architecture/serverless/event-hubs-functions/performance-scale |
| Design resilient Event Hubs-triggered Azure Functions | https://learn.microsoft.com/en-us/azure/architecture/serverless/event-hubs-functions/resilient-design |
| Secure Azure Functions integrated with Event Hubs | https://learn.microsoft.com/en-us/azure/architecture/serverless/event-hubs-functions/security |
| Protect APIs with Application Gateway and API Management | https://learn.microsoft.com/en-us/azure/architecture/web-apps/api-management/architectures/protect-apis |
| Securely access App Service apps from on-premises networks | https://learn.microsoft.com/en-us/azure/architecture/web-apps/guides/networking/access-multitenant-web-app-from-on-premises |
| Secure SPA authorization using Azure API Management | https://learn.microsoft.com/en-us/azure/architecture/web-apps/guides/security/secure-single-page-application-authorization |

### Anti-patterns
| Topic | URL |
|-------|-----|
| Identify and remediate common Azure performance antipatterns | https://learn.microsoft.com/en-us/azure/architecture/antipatterns/ |
| Identify and remediate the Busy Database antipattern | https://learn.microsoft.com/en-us/azure/architecture/antipatterns/busy-database/ |
| Detect and fix the Busy Front End antipattern | https://learn.microsoft.com/en-us/azure/architecture/antipatterns/busy-front-end/ |
| Detect and remediate Chatty I/O antipattern | https://learn.microsoft.com/en-us/azure/architecture/antipatterns/chatty-io/ |
| Mitigate the Extraneous Fetching antipattern in Azure | https://learn.microsoft.com/en-us/azure/architecture/antipatterns/extraneous-fetching/ |
| Avoid Improper Instantiation performance antipattern | https://learn.microsoft.com/en-us/azure/architecture/antipatterns/improper-instantiation/ |
| Address Monolithic Persistence data store antipattern | https://learn.microsoft.com/en-us/azure/architecture/antipatterns/monolithic-persistence/ |
| Identify and remediate the No-Caching antipattern | https://learn.microsoft.com/en-us/azure/architecture/antipatterns/no-caching/ |
| Mitigate Noisy Neighbor issues in multitenant systems | https://learn.microsoft.com/en-us/azure/architecture/antipatterns/noisy-neighbor/noisy-neighbor |
| Prevent Retry Storm antipattern in cloud services | https://learn.microsoft.com/en-us/azure/architecture/antipatterns/retry-storm/ |
| Avoid synchronous I/O to improve scalability in Azure apps | https://learn.microsoft.com/en-us/azure/architecture/antipatterns/synchronous-io/ |

### Example Workloads
| Topic | URL |
|-------|-----|
| Automate video analysis with Azure ML and Vision | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/architecture/analyze-video-computer-vision-machine-learning |
| Automate document classification with Azure Durable Functions | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/architecture/automate-document-classification-durable-functions |
| Implement automated PDF forms processing on Azure | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/architecture/automate-pdf-forms-processing |
| Build and deploy custom document models on Azure | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/architecture/build-deploy-custom-models |
| Index blob content and metadata with Azure AI Search | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/architecture/search-blob-metadata |
| Implement a secure Azure research environment for regulated data | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/architecture/secure-compute-for-research |
| Implement batch analytics for call center conversations with Azure OpenAI | https://learn.microsoft.com/en-us/azure/architecture/ai-ml/openai/architecture/call-center-openai-analytics |
| Design a medallion lakehouse with Azure Data Factory | https://learn.microsoft.com/en-us/azure/architecture/databases/architecture/azure-data-factory-on-azure-landing-zones-index |
| Implement DataOps for a modern Azure data warehouse | https://learn.microsoft.com/en-us/azure/architecture/databases/architecture/dataops-mdw |
| Implement write-through caching with Azure SQL and Redis | https://learn.microsoft.com/en-us/azure/architecture/databases/architecture/write-through-caching-azure-sql-managed-redis |
| Implement multitenant AKS ingress with Application Gateway for Containers | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/aks-agic/aks-agc |
| Secure AKS workloads with Azure Front Door and Private Link | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/aks-front-door/aks-front-door |
| Design an enterprise BI solution using Microsoft Fabric | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/analytics/enterprise-bi-microsoft-fabric |
| Sync MongoDB Atlas changes to Microsoft Fabric in real time | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/analytics/sync-mongodb-atlas-fabric-analytics |
| Implement real-time MongoDB Atlas to Fabric sync | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/analytics/sync-mongodb-atlas-fabric-analytics |
| Implement SCI-based sustainability scoring for Azure apps | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/apps/measure-azure-app-sustainability-sci-score |
| Implement high-availability SAP on Oracle in Azure | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/apps/sap-production |
| Apply SRE principles to scalable Azure API platforms | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/apps/scalable-apps-performance-modeling-site-reliability |
| Implement multiregion BCDR for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/azure-virtual-desktop/azure-virtual-desktop-multi-region-bcdr |
| Implement automated certificate lifecycle management on Azure | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/certificate-lifecycle/ |
| Implement a scalable Azure data warehouse and analytics pipeline | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/data/data-warehouse |
| Deploy Esri ArcGIS Pro on Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/data/esri-arcgis-azure-virtual-desktop |
| Implement a greenfield Microsoft Fabric lakehouse platform | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/data/greenfield-lakehouse-fabric |
| Implement near real-time lakehouse processing with Synapse | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/data/real-time-lakehouse-data-processing |
| Modernize SMB data warehouses with Fabric and Azure SQL | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/data/small-medium-data-warehouse |
| Build an end-to-end analytics platform with Fabric | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/dataplate2e/data-platform-end-to-end |
| Implement APIOps for automated Azure API deployments | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/devops/automated-api-deployments-apiops |
| Manage Microsoft 365 tenant configuration using Azure DevOps | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/devops/manage-microsoft-365-tenant-configuration-microsoft365dsc-devops |
| Implement resilient enterprise file shares with Azure NetApp Files | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/file-storage/enterprise-file-shares-disaster-recovery |
| Deploy scalable Moodle on Azure with NetApp Files | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/file-storage/moodle-azure-netapp-files |
| Run Oracle Database on Azure with NetApp Files | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/file-storage/oracle-azure-netapp-files |
| Run SQL Server on Azure VMs with Azure NetApp Files | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/file-storage/sql-server-azure-netapp-files |
| Implement computer forensics chain of custody on Azure | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/forensics/ |
| Implement Zero Trust network for web apps with Azure Firewall | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/gateway/application-gateway-before-azure-firewall |
| Secure virtual networks with Azure Firewall and Application Gateway | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/gateway/firewall-application-gateway |
| Operate AKS clusters using GitOps with Flux and Argo CD | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/gitops-aks/gitops-blueprint-aks |
| Implement a baseline AKS architecture on Azure Local | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/hybrid/aks-baseline |
| Build GitOps pipelines for AKS on Azure Local with Arc | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/hybrid/aks-hybrid-azure-local |
| Provide on-premises access to Azure Files securely | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/hybrid/azure-files-on-premises-authentication |
| Secure hybrid Outlook client access with MFA | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/hybrid/secure-hybrid-messaging-client |
| Secure hybrid Outlook mobile access with MFA | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/hybrid/secure-hybrid-messaging-mobile |
| Secure hybrid Outlook web access with MFA | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/hybrid/secure-hybrid-messaging-web |
| Extend on-premises Active Directory to Azure VNet | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/identity/adds-extend-domain |
| Implement HA and disaster recovery for multitier web apps | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/infrastructure/multi-tier-app-disaster-recovery |
| Implement secure API Management landing zone with App Gateway | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/integration/app-gateway-internal-api-management-function |
| Integrate enterprise systems using queues and events | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/integration/queues-events |
| Implement SMA OpCon on Azure Kubernetes for workload automation | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/integration/sma-opcon-azure |
| Move Azure IoT Hub solutions from test to production | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/iot/iot-move-to-production |
| Use IoT Hub for private file uploads to Storage | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/iot/iot-private-file-upload |
| Implement mainframe data replication to Azure with LIBER*IRIS | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/mainframe/mainframe-data-replication-azure-data-platform |
| Migrate mainframe data to Azure using Rocket RDRS | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/mainframe/mainframe-data-replication-azure-rdrs |
| Implement Qlik-based mainframe data replication to Azure | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/mainframe/mainframe-midrange-data-replication-azure-qlik |
| Replicate mainframe data to Azure using Precisely Connect | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/mainframe/mainframe-replication-precisely-connect |
| Modernize IBM mainframe and midrange data to Azure | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/mainframe/modernize-mainframe-data-to-azure |
| Process high-volume batch transactions with AKS and Service Bus | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/mainframe/process-batch-transactions |
| Reengineer mainframe batch applications on Azure | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/mainframe/reengineer-mainframe-batch-apps-azure |
| Rehost Software AG Adabas and Natural mainframe workloads on Azure | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/mainframe/rehost-adabas-software-ag |
| Rehost IMS databases and data communications on Azure | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/mainframe/rehost-ims-raincode-imsql |
| Implement Siemens Teamcenter PLM baseline on Azure | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/manufacturing/teamcenter-baseline |
| Build real-time monitoring and observability for media telemetry | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/monitoring/monitoring-observable-systems-media |
| Implement hybrid quantum-classical apps with Azure Quantum | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/quantum/quantum-computing-integration-with-classical-apps |
| Manage Azure VM compliance with image pipelines | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/security/virtual-machine-compliance |
| Replatform Kubernetes microservices to Azure Container Apps | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/serverless/microservices-with-container-apps |
| Build Dapr-based microservices on Azure Container Apps | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/serverless/microservices-with-container-apps-dapr |
| Plan WSUS deployment to update isolated Azure Windows VMs | https://learn.microsoft.com/en-us/azure/architecture/example-scenario/wsus/ |
| Enable ML inference on Azure IoT Edge devices | https://learn.microsoft.com/en-us/azure/architecture/guide/iot/machine-learning-inference-iot-edge |
| Architect and deploy SAS analytics workloads on Azure | https://learn.microsoft.com/en-us/azure/architecture/guide/sas/sas-overview |
| Manage hybrid Kubernetes clusters with Azure Arc | https://learn.microsoft.com/en-us/azure/architecture/hybrid/arc-hybrid-kubernetes |
| Deploy Azure Arc-enabled SQL Managed Instance for DR | https://learn.microsoft.com/en-us/azure/architecture/hybrid/arc-sql-managed-instance-disaster-recovery |
| Administer on-premises SQL Server using Azure Arc | https://learn.microsoft.com/en-us/azure/architecture/hybrid/azure-arc-sql-server |
| Integrate Azure file shares into hybrid AD DS environments | https://learn.microsoft.com/en-us/azure/architecture/hybrid/azure-file-share |
| Monitor hybrid VM performance with Azure Monitor | https://learn.microsoft.com/en-us/azure/architecture/hybrid/hybrid-perf-monitoring |
| Design massive-scale Azure Virtual WAN with multi-hub | https://learn.microsoft.com/en-us/azure/architecture/networking/architecture/massive-scale-azure-architecture |
| Virtual WAN design for mixed security and performance needs | https://learn.microsoft.com/en-us/azure/architecture/networking/architecture/performance-security-optimized-vwan |
| Single-region Private Link and DNS design in Virtual WAN | https://learn.microsoft.com/en-us/azure/architecture/networking/guide/private-link-virtual-wan-dns-single-region-workload |
| Implement ransomware-resilient backups with Azure Backup | https://learn.microsoft.com/en-us/azure/architecture/security/ransomware-resilient-backup-architecture/ |
| Design Windows 365 Azure network connections for Cloud PCs | https://learn.microsoft.com/en-us/azure/architecture/virtual-desktop/windows-365-azure-network-connection |

### Migration Guides
| Topic | URL |
|-------|-----|
| Map AWS services and concepts to Azure for migration | https://learn.microsoft.com/en-us/azure/architecture/aws-professional/ |
| Map AWS accounts and organizations to Azure structures | https://learn.microsoft.com/en-us/azure/architecture/aws-professional/accounts |
| Map and compare AWS compute services to Azure | https://learn.microsoft.com/en-us/azure/architecture/aws-professional/compute |
| Map AWS data and AI services to Azure equivalents | https://learn.microsoft.com/en-us/azure/architecture/aws-professional/data-ai |
| Map AWS database services to Azure offerings | https://learn.microsoft.com/en-us/azure/architecture/aws-professional/databases |
| Map Amazon EKS concepts and configs to Azure AKS | https://learn.microsoft.com/en-us/azure/architecture/aws-professional/eks-to-aks/ |
| Manage and optimize AKS costs versus Amazon EKS | https://learn.microsoft.com/en-us/azure/architecture/aws-professional/eks-to-aks/cost-management |
| Apply governance to AKS clusters versus EKS | https://learn.microsoft.com/en-us/azure/architecture/aws-professional/eks-to-aks/governance |
| Migrate Kubernetes workloads from EKS to AKS | https://learn.microsoft.com/en-us/azure/architecture/aws-professional/eks-to-aks/migrate |
| Compare and configure AKS vs EKS monitoring and logging | https://learn.microsoft.com/en-us/azure/architecture/aws-professional/eks-to-aks/monitoring |
| Manage AKS nodes and node pools versus EKS | https://learn.microsoft.com/en-us/azure/architecture/aws-professional/eks-to-aks/node-pools |
| Secure AKS API access compared to Amazon EKS | https://learn.microsoft.com/en-us/azure/architecture/aws-professional/eks-to-aks/private-clusters |
| Compare and select AKS storage when migrating from EKS | https://learn.microsoft.com/en-us/azure/architecture/aws-professional/eks-to-aks/storage |
| Compare Kubernetes workload identity on EKS and AKS | https://learn.microsoft.com/en-us/azure/architecture/aws-professional/eks-to-aks/workload-identity |
| Compare AWS and Azure messaging services | https://learn.microsoft.com/en-us/azure/architecture/aws-professional/messaging |
| Compare AWS and Azure networking capabilities | https://learn.microsoft.com/en-us/azure/architecture/aws-professional/networking |
| Understand AWS vs Azure regions and zones for resiliency | https://learn.microsoft.com/en-us/azure/architecture/aws-professional/regions-zones |
| Compare AWS and Azure resource management models | https://learn.microsoft.com/en-us/azure/architecture/aws-professional/resources |
| Map AWS identity services to Azure equivalents | https://learn.microsoft.com/en-us/azure/architecture/aws-professional/security-identity |
| Map AWS storage services to Azure storage options | https://learn.microsoft.com/en-us/azure/architecture/aws-professional/storage |
| Migrate on-premises Oracle Database to Azure VMs | https://learn.microsoft.com/en-us/azure/architecture/databases/idea/migrate-oracle-azure-iaas |
| Migrate Oracle Exadata workloads to Oracle Database@Azure | https://learn.microsoft.com/en-us/azure/architecture/databases/idea/migrate-oracle-odaa-exadata |
| Migrate on-premises Oracle databases to Azure | https://learn.microsoft.com/en-us/azure/architecture/databases/idea/topic-migrate-oracle-azure |
| Map Google Cloud services and concepts to Azure | https://learn.microsoft.com/en-us/azure/architecture/gcp-professional/ |
| Map Google Cloud services to Azure equivalents | https://learn.microsoft.com/en-us/azure/architecture/gcp-professional/services |
| Secure AWS environments with Microsoft security solutions | https://learn.microsoft.com/en-us/azure/architecture/guide/aws/aws-azure-security-solutions |
| Migrate Apache Kafka workloads to Azure services | https://learn.microsoft.com/en-us/azure/architecture/guide/hadoop/apache-kafka-migration |