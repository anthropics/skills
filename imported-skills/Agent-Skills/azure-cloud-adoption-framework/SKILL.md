---
name: azure-cloud-adoption-framework
description: Expert guidance for planning and executing cloud adoption using Azure Cloud Adoption Framework. Covers strategy, planning, readiness & landing zones, adoption patterns, governance, security, operations & management, organization & teams, and adoption scenarios. Use when adopting AKS/Arc, AVS/VMware, SAP/Oracle, AVD/Citrix, or AI agent workloads on Azure, and other Azure Cloud Adoption Framework related development tasks.
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Cloud Adoption Framework Skill

This skill provides expert guidance for planning and executing cloud adoption using Azure Cloud Adoption Framework. Covers strategy, planning, readiness & landing zones, adoption patterns, governance, security, operations & management, organization & teams, and adoption scenarios. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Strategy | L37-L55 | High-level cloud and AI strategy: defining business goals, executive alignment, unified data/ops, workload-specific plans (SAP, Oracle, AVD, VMware), and cost, resiliency, security, and sustainability objectives. |
| Planning | L56-L83 | Planning cloud adoption, migration waves, modernization roadmaps, cost/skills readiness, and detailed plans for workloads (AI, data, Oracle, SAP, AVS, AVD, analytics) on Azure. |
| Readiness & Landing Zones | L84-L201 | Designing and operating Azure landing zones: network topologies, identity, subscriptions, governance, automation/DevOps, multitenant setups, and workload-specific patterns (AVS, SAP, Oracle, AKS, Arc). |
| Adoption Patterns | L202-L226 | Patterns and step-by-step guidance for planning, migrating, modernizing, and operating Azure workloads (AI agents, cloud-native apps, AVD, VMware, Oracle, SAP) safely and efficiently |
| Governance | L227-L254 | Designing and enforcing Azure governance: policies, tagging, cost control, compliance, and security baselines across landing zones, AKS, AVD, AVS, Arc, SAP, and AI agents. |
| Security | L255-L281 | Security design and governance for Azure landing zones, including Zero Trust, IAM, encryption, DevOps, AKS, analytics, SAP/Oracle, Arc, and ongoing security operations. |
| Operations & Management | L282-L316 | Operating, monitoring, securing, and optimizing Azure environments and workloads (including AI, AKS, Arc, AVS, Oracle, SAP, analytics) plus BCDR, DevOps, and platform-level governance. |
| Organization & Teams | L317-L334 | Designing cloud org structures, roles, and RACI: governance, CCoE, DevOps, security, operations, data/analytics, cost management, and breaking silos for Azure adoption and operations |
| Adoption Scenarios | L335-L390 | End-to-end adoption patterns for AI agents, AKS, RHEL, ARO, AVD, Citrix, AVS, Oracle, SAP: landing zones, identity, networking, security, BCDR, automation, governance, and operations. |

### Strategy
| Topic | URL |
|-------|-----|
| Create a business plan for AI agent adoption | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ai-agents/business-strategy-plan |
| Define and align an enterprise AI strategy | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ai/strategy |
| Define executive strategy to unify data for AI | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/data/executive-strategy-unify-data-platform |
| Assess strategic benefits of Azure Virtual Desktop adoption | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/strategy |
| Incorporate Azure VMware Solution into cloud strategy | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/strategy |
| Define unified hybrid and multicloud operations strategy with Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/hybrid/strategy |
| Align Oracle on Azure migration with cloud strategy | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/oracle-landing-zone-strategy |
| Define cloud strategy for SAP workloads on Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/sap/strategy |
| Develop a measurable cloud adoption strategy | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/strategy/ |
| Establish and structure a cloud strategy team | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/strategy/define-your-team |
| Incorporate cost efficiency into cloud strategy | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/strategy/inform/cost-efficiency |
| Plan resiliency as part of cloud strategy | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/strategy/inform/resiliency |
| Integrate security considerations into cloud strategy | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/strategy/inform/security |
| Incorporate sustainability objectives into cloud strategy | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/strategy/inform/sustainability |
| Define cloud motivations, mission, and objectives | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/strategy/motivations |

### Planning
| Topic | URL |
|-------|-----|
| Plan enterprise data architecture to support AI agents | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ai-agents/data-architecture-plan |
| Define technology plan for AI agents on Microsoft | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ai-agents/technology-solutions-plan-strategy |
| Plan Azure migration waves for large estates | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/migrate/migration-wave-planning |
| Create detailed workload migration plans to Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/migrate/plan-migration |
| Prepare workloads for reliable migration to Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/migrate/prepare-workloads-cloud |
| Plan Azure cloud modernization strategies and roadmap | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/modernize/plan-cloud-modernization |
| Prepare organization for Azure cloud modernization | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/modernize/prepare-organization-cloud-modernization |
| Assess workloads for Azure cloud migration readiness | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/plan/assess-workloads-for-cloud-migration |
| Use a cloud-native startup adoption plan template | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/plan/cloud-native-adoption-plan |
| Discover and prioritize workload inventory for migration | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/plan/discover-existing-workload-inventory |
| Document a comprehensive Azure cloud adoption plan | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/plan/document-cloud-adoption-plan |
| Plan Azure architectures for accurate cost estimation | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/plan/estimate-total-cost-of-ownership |
| Use a migration-focused cloud adoption plan template | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/plan/migration-adoption-plan |
| Prepare your organization and plan for cloud adoption | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/plan/prepare-organization-for-cloud |
| Plan skills readiness and training for Azure adoption | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/plan/prepare-people-for-cloud |
| Select appropriate cloud migration strategies per workload | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/plan/select-cloud-migration-strategy |
| Plan Azure Virtual Desktop migration using CAF Migrate | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/plan |
| Plan cloud adoption with Azure VMware Solution workloads | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/plan |
| Plan capacity for Oracle workloads on Azure VMs | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/oracle-capacity-planning |
| Plan capacity for Oracle Autonomous Database@Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/oracle-capacity-planning-oracle-database-azure-autonomous-database |
| Plan capacity for Oracle Exadata Database@Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/oracle-capacity-planning-oracle-database-azure-exadata |
| Plan Oracle on Azure workload migration | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/oracle-landing-zone-plan |
| Plan migration of Oracle workloads to Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/oracle-migration-planning |
| Create a SAP on Azure cloud adoption plan | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/sap/plan |

### Readiness & Landing Zones
| Topic | URL |
|-------|-----|
| Prepare Azure landing zones for scalable workloads | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/ |
| Use Azure Virtual Network Manager in landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/azure-virtual-network-manager |
| Design on-premises connectivity topologies to Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/connectivity-to-azure |
| Design connectivity to Azure PaaS services securely | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/connectivity-to-azure-paas-services |
| Connect Azure landing zones to other cloud providers | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/connectivity-to-other-providers |
| Design Azure–Oracle Cloud Infrastructure connectivity | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/connectivity-to-other-providers-oci |
| Define Azure landing zone network topologies | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/define-an-azure-network-topology |
| Design DNS for hybrid on-premises and Azure environments | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/dns-for-on-premises-and-azure-resources |
| Plan secure, scalable Azure application delivery | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/plan-for-app-delivery |
| Plan inbound and outbound internet connectivity in Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/plan-for-inbound-and-outbound-internet-connectivity |
| Plan IP addressing for Azure and hybrid networks | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/plan-for-ip-addressing |
| Design Azure landing zones for traffic inspection | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/plan-for-traffic-inspection |
| Use Azure Bastion for secure VM remote access | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/plan-for-virtual-machine-remote-access |
| Integrate Private Link with Private DNS at scale | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/private-link-and-dns-integration-at-scale |
| Use standard abbreviations in Azure resource names | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/resource-abbreviations |
| Design and implement Azure resource naming conventions | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/resource-naming |
| Implement traditional hub-and-spoke Azure networking | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/traditional-azure-networking-topology |
| Design Virtual WAN network topology in landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/virtual-wan-network-topology |
| Set up Microsoft Entra ID for Azure identity | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-setup-guide/identity |
| Create and scale initial Azure subscriptions correctly | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-setup-guide/initial-subscriptions |
| Create and scale Azure subscriptions correctly from day one | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-setup-guide/initial-subscriptions |
| Design and manage Azure RBAC access control | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-setup-guide/manage-access |
| Configure Azure monitoring and reporting foundations | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-setup-guide/monitoring-reporting |
| Organize Azure resources for governance and cost | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-setup-guide/organize-resources |
| Select compliant, resilient Azure regions for workloads | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-setup-guide/regions |
| Refactor and expand Azure landing zones with IaC | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/considerations/ |
| Plan automation strategy for Azure landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/considerations/automation |
| Define development lifecycle strategy for landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/considerations/development-strategy-development-lifecycle |
| Apply test-driven development to Azure landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/considerations/development-strategy-test-driven-development |
| Apply DevOps principles to Azure landing zone deployment | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/considerations/devops-principles-and-practices |
| Select a DevOps toolchain for Azure landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/considerations/devops-toolchain |
| Design multistage environments for Azure delivery | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/considerations/environments |
| Use infrastructure as code to evolve landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/considerations/infrastructure-as-code-updates |
| Plan Azure regions for landing zone deployments | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/considerations/regions |
| Design and manage sandbox landing zone environments | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/considerations/sandbox-environments |
| Test Azure landing zone deployments and policies | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/enterprise-scale/testing-approach |
| Transition existing Azure environments to landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/enterprise-scale/transition |
| Understand Azure landing zones as environment foundation | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/ |
| Duplicate landing zone management group in audit-only mode | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/align-approach-duplicate-brownfield-audit-only |
| Transition existing management groups to landing zone hierarchy | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/align-scenario-multiple-management-groups |
| Align regional dev/test/prod structures to landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/align-scenario-regional-org |
| Transition a single-subscription Azure environment to CAF landing zone | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/align-scenario-single-subscription |
| Define and configure Microsoft Entra tenants for Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/azure-ad-define |
| Understand CSP service agreements in Azure landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/azure-billing-cloud-solution-provider |
| Design Enterprise Agreement enrollment for Azure landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/azure-billing-enterprise-agreement |
| Align Microsoft customer agreement with Entra tenants | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/azure-billing-microsoft-customer-agreement |
| Design Azure billing offers and Entra tenant alignment | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/azure-billing-microsoft-entra-tenant |
| Design identity and access management for Azure landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/identity-access |
| Implement hybrid identity with Entra ID in landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/identity-access-active-directory-hybrid-identity |
| Design application identity and access for cloud-native apps | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/identity-access-application-access |
| Design identity and access for Azure landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/identity-access-landing-zones |
| Keep Azure landing zone configurations current | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/keep-azure-landing-zone-up-to-date |
| Design management foundations for Azure environments | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/management |
| Manage app environments with landing zone subscriptions | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/management-application-environments |
| Implement inventory and visibility for Azure platforms | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/management-platform |
| Automate Azure landing zone deployments across tenants | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/multi-tenant/automation |
| Use canary environments for multitenant Azure landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/multi-tenant/canary |
| Apply multitenant considerations to Azure landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/multi-tenant/considerations-recommendations |
| Leverage Azure Lighthouse in multitenant landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/multi-tenant/lighthouse |
| Use multiple Entra tenants in Azure landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/multi-tenant/overview |
| Evaluate scenarios requiring multiple Entra tenants | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/multi-tenant/scenarios |
| Design Azure network topology and connectivity | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/network-topology-and-connectivity |
| Design platform automation and DevOps for landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/platform-automation-devops |
| Design Azure resource organization for landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/resource-org |
| Design Azure management group hierarchy for scale | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/resource-org-management-groups |
| Plan and design Azure subscription strategy | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/resource-org-subscriptions |
| Design and implement subscription vending in Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/subscription-vending |
| Define subscription vending product lines for workloads | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/subscription-vending-product-lines |
| Use Azure landing zone design areas for architecture | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-areas |
| Apply Azure landing zone core design principles | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-principles |
| Choose platform landing zone implementation options | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/implementation-options |
| Apply Azure landing zone patterns for ISVs | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/isv-landing-zone |
| Plan your journey to target Azure landing zone architecture | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/landing-zone-journey |
| Adapt Azure landing zones for multinational compliance | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/landing-zone-multinational |
| Prepare Azure landing zones specifically for migration | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/ready-azure-landing-zone |
| Tailor Azure landing zone reference implementations | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/tailoring-alz |
| Design and deploy Azure application landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/ |
| Deploy AKS clusters with landing zone accelerator | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/aks/landing-zone-accelerator |
| Use the RHEL landing zone accelerator for Azure workloads | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/azure-red-hat-enterprise-linux/landing-zone-accelerator |
| Prepare Azure landing zones for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/ready |
| Understand Azure VMware Solution networking fundamentals for design | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/azure-vmware-solution-network-basics |
| Establish cross-tenant network connectivity for Azure VMware SDDCs | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/cross-tenant-network-connectivity |
| Configure dual-region AVS connectivity with Virtual WAN and Global Reach | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/dual-region-virtual-wan-global-reach |
| Configure dual-region AVS connectivity with Virtual WAN without Global Reach | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/dual-region-virtual-wan-without-global-reach |
| Design dual-region network topology for Azure VMware Solution | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/eslz-dual-region-network-topology |
| Design identity and access for Azure VMware Solution landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/eslz-identity-and-access-management |
| Design enterprise-scale network topology for Azure VMware Solution | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/eslz-network-topology-connectivity |
| Automate Azure VMware Solution platform deployment and operations | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/eslz-platform-automation-and-devops |
| Choose enterprise-scale connectivity architectures for Azure VMware Solution | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/example-architectures |
| Use secure Virtual WAN topologies with Azure VMware Solution | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/introduction-virtual-wan-azure-vmware-solution |
| Design inbound internet connectivity for Azure VMware Solution workloads | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/network-design-guide-internet-inbound-connectivity |
| Design outbound internet connectivity for Azure VMware Solution | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/network-design-guide-internet-outbound-connectivity |
| Use the Azure VMware Solution network design guide for landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/network-design-guide-intro |
| Prepare network connectivity for Azure VMware Solution landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/network-get-started |
| Manage ingress and egress traffic from Azure VMware Solution natively | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/network-hub-spoke |
| Design on-premises connectivity for Azure VMware Solution | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/on-premises-connectivity |
| Review Azure landing zones for Azure VMware Solution | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/ready |
| Configure single-region AVS connectivity with Virtual WAN and Global Reach | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/single-region-virtual-wan-global-reach |
| Configure single-region AVS connectivity with Virtual WAN without Global Reach | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/single-region-virtual-wan-without-global-reach |
| Connect Azure VMware Solution private clouds to Azure virtual networks | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/virtual-network-connectivity |
| Design network connectivity for Arc-enabled Kubernetes clusters | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/hybrid/arc-enabled-kubernetes/eslz-arc-kubernetes-network-connectivity |
| Organize resources for Azure Arc-enabled Kubernetes | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/hybrid/arc-enabled-kubernetes/eslz-arc-kubernetes-resource-organization |
| Design network connectivity for Azure Arc-enabled servers | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/hybrid/arc-enabled-servers/eslz-arc-servers-connectivity |
| Organize Azure Arc-enabled server resources and tags | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/hybrid/arc-enabled-servers/eslz-resource-organization |
| Integrate Azure Arc resources into Azure landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/hybrid/enterprise-scale-landing-zone |
| Connect application tiers to Oracle Database@Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/application-connectivity-design |
| Configure Azure Arc connectivity for Oracle Database@Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/azure-arc-connectivity-design |
| Implement core networking for Oracle Database@Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/core-network-design |
| Design network topology for Oracle on Azure VMs | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/oracle-network-topology-iaas |
| Design Oracle Database@Azure landing zone networking | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/oracle-network-topology-odaa |
| Organize Oracle Database@Azure resources and subscriptions | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/oracle-resource-organization-oracle-database-azure |
| Design identity and access management for SAP on Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/sap/eslz-identity-and-access-management |
| Design SAP on Azure network topology and connectivity | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/sap/eslz-network-topology-and-connectivity |
| Prepare Azure landing zones for SAP migration | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/sap/ready |

### Adoption Patterns
| Topic | URL |
|-------|-----|
| Standardize process to build secure AI agents | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ai-agents/build-secure-process |
| Choose single-agent vs multi-agent AI architectures | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ai-agents/single-agent-multiple-agents |
| Build resilient cloud-native solutions on Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/cloud-native/build-cloud-native-solutions |
| Deploy cloud-native Azure solutions with safe rollout | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/cloud-native/deploy-cloud-native-solutions |
| Plan cloud-native Azure solutions aligned to CAF | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/cloud-native/plan-cloud-native-solutions |
| Decommission on-premises workloads after Azure migration | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/migrate/decommission-source-workload |
| Execute structured Azure workload migrations | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/migrate/execute-migration |
| Execute Azure cloud modernization projects safely | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/modernize/execute-cloud-modernization |
| Apply replatform, refactor, rearchitect patterns for Azure modernization | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/modernize/modernization-cloud-replatform-refactor-rearchitect |
| Assess environments for Azure Virtual Desktop migration | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/migrate-assess |
| Deploy and migrate Azure Virtual Desktop workloads | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/migrate-deploy |
| Execute post-deployment and release for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/migrate-release |
| Run an Azure Virtual Desktop proof of concept | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/proof-of-concept |
| Migrate on-premises VMware workloads to Azure VMware Solution | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/migrate |
| Design migration connectivity for Oracle Database@Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/migration-connectivity-design |
| Automate Oracle Exadata Database@Azure platform deployment | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/oracle-platform-automation-devops-oracle-database-azure |
| Automate SAP deployments on Azure with DevOps | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/sap/eslz-platform-automation-and-devops |
| Migrate SAP platforms to Azure using specialized tools | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/sap/migrate |
| Choose Azure connectors for SAP data integration | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/sap/sap-lza-choose-azure-connectors |
| Optimize SAP data extraction performance and troubleshooting | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/sap/sap-lza-data-extraction-performance-troubleshooting |
| Identify SAP data sources for Azure integration | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/sap/sap-lza-identify-sap-data-sources |

### Governance
| Topic | URL |
|-------|-----|
| Establish governance and security baseline for AI agents | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ai-agents/governance-security-across-organization |
| Assess and prioritize cloud governance risks | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/govern/assess-cloud-risks |
| Document effective Azure cloud governance policies | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/govern/document-cloud-governance-policies |
| Enforce Azure cloud governance policies at scale | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/govern/enforce-cloud-governance-policies |
| Monitor and remediate Azure cloud compliance | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/govern/monitor-cloud-governance |
| Design an Azure resource tagging strategy | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/resource-tagging |
| Implement cost tracking across Azure business units | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/track-costs |
| Configure Azure governance and compliance controls | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-setup-guide/governance-compliance |
| Set up Azure cost management and billing governance | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-setup-guide/manage-costs |
| Improve governance for Azure landing zones over time | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/considerations/landing-zone-governance |
| Map regulatory security controls to Azure landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/control-mapping/security-control-mapping |
| Implement policy-driven guardrails with DINE policies | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/enterprise-scale/dine-guidance |
| Design Azure governance tooling in landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/governance |
| Migrate custom Azure landing zone policies to built-ins | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/migrate-azure-landing-zone-policies |
| Adopt a service enablement framework for Azure services | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/service-enablement-framework |
| Update Azure landing zone custom policies safely | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/update-custom-policies |
| Apply cost governance to AKS using Kubecost | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/aks/cost-governance-with-kubecost |
| Extend cloud governance to Azure Virtual Desktop environments | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/govern |
| Apply security, governance, and compliance disciplines to Azure VMware Solution | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/eslz-security-governance-and-compliance |
| Extend cloud governance to Azure VMware Solution environments | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/govern |
| Set governance, security, and compliance baseline for Arc-enabled Kubernetes | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/hybrid/arc-enabled-kubernetes/eslz-arc-kubernetes-governance-disciplines |
| Implement cost governance for Azure Arc-enabled servers | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/hybrid/arc-enabled-servers/eslz-cost-governance |
| Establish governance, security, and compliance for Arc servers | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/hybrid/arc-enabled-servers/eslz-security-governance-and-compliance |
| Apply governance, security, and compliance for SAP on Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/sap/eslz-security-governance-and-compliance |

### Security
| Topic | URL |
|-------|-----|
| Define network encryption between on-premises and Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/define-network-encryption-requirements |
| Restrict cross-tenant Private Endpoint connections | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/limit-cross-tenant-private-endpoint-connections |
| Design Zero Trust-aligned landing zone segmentation | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/azure-best-practices/plan-for-landing-zone-network-segmentation |
| Enhance security posture of Azure landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/considerations/landing-zone-security |
| Secure Azure DevOps and GitHub for landing zone delivery | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/considerations/security-considerations-overview |
| Design RBAC and access control for DevOps tools | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/considerations/security-considerations-tools |
| Design encryption and key management in Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/encryption-and-keys |
| Establish a security foundation in Azure landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/security |
| Apply Zero Trust practices across landing zone design areas | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/security-zero-trust |
| Implement security governance and controls for AKS | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/aks/security |
| Design identity and access for Arc-enabled Kubernetes | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/hybrid/arc-enabled-kubernetes/eslz-arc-kubernetes-identity-access-management |
| Secure Azure Arc-enabled servers with identity and access controls | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/hybrid/arc-enabled-servers/eslz-identity-and-access-management |
| Design IAM for Oracle Database@Azure across Azure and OCI | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/oracle-iam-odaa |
| Implement defense-in-depth security for Oracle Database@Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/oracle-security-overview-odaa |
| Secure SAP data integration architectures on Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/sap/sap-lza-data-integration-security |
| Secure SQL Server databases for SAP on Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/sap/sap-lza-database-security |
| Implement security operations for SAP on Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/sap/sap-lza-security-operations |
| Apply security best practices during cloud adoption | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/secure/adopt |
| Govern Azure cloud estate with security focus | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/secure/govern |
| Manage Azure cloud estate with continuous security | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/secure/manage |
| Plan secure Azure cloud adoption activities | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/secure/plan |
| Prepare a secure Azure landing zone foundation | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/secure/ready |
| Integrate security into cloud adoption strategy | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/secure/strategy |

### Operations & Management
| Topic | URL |
|-------|-----|
| Integrate and operate AI agents across organization | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ai-agents/integrate-manage-operate |
| Optimize Azure cloud-native solutions post-deployment | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/cloud-native/optimize-cloud-native-solutions |
| Administer and control Azure cloud operations | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/manage/administer |
| Plan and configure monitoring for Azure estates | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/manage/monitor |
| Protect and ensure reliability of Azure estates | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/manage/protect |
| Prepare Azure cloud operations using RAMP model | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/manage/ready-cloud-operations |
| Optimize Azure workloads after migration | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/migrate/optimize-workloads-after-migration |
| Optimize and operate Azure workloads post-modernization | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/modernize/optimize-after-cloud-modernization |
| Implement shared management cloud operations model | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/plan/shared-management-operating-model |
| Design platform-level BCDR for Azure landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/management-business-continuity-disaster-recovery |
| Deploy baseline monitoring for Azure landing zone platform | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/management-monitor |
| Design operational compliance monitoring for Azure platforms | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/management-operational-compliance |
| Implement workload management and monitoring in landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/landing-zone/design-area/management-workloads |
| Operate and manage Azure Kubernetes Service environments | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/aks/management |
| Integrate Azure Virtual Desktop into operations management | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/manage |
| Implement enterprise-scale BCDR operations for Azure VMware Solution | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/eslz-business-continuity-and-disaster-recovery |
| Design management and monitoring for Azure VMware Solution | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/eslz-management-and-monitoring |
| Operate and manage Azure VMware Solution private clouds | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/manage |
| Automate onboarding and management of Arc-enabled Kubernetes | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/hybrid/arc-enabled-kubernetes/eslz-arc-kubernetes-automation-disciplines |
| Implement CI/CD and GitOps for Arc-enabled Kubernetes | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/hybrid/arc-enabled-kubernetes/eslz-arc-kubernetes-cicd-gitops-disciplines |
| Manage extensions for Azure Arc-enabled Kubernetes clusters | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/hybrid/arc-enabled-kubernetes/eslz-arc-kubernetes-extensions-management |
| Manage and monitor Azure Arc-enabled Kubernetes clusters | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/hybrid/arc-enabled-kubernetes/eslz-arc-kubernetes-management-disciplines |
| Automate onboarding and lifecycle of Arc-enabled servers | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/hybrid/arc-enabled-servers/eslz-automation-arc-server |
| Manage and monitor Azure Arc-enabled servers at scale | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/hybrid/arc-enabled-servers/eslz-management-and-monitoring-arc-server |
| Design BCDR connectivity for Oracle Database@Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/business-continuity-disaster-recovery-connectivity-design |
| Design BCDR for Oracle on Azure VM landing zone | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/oracle-disaster-recovery-iaas |
| Implement BCDR for Oracle Exadata Database@Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/oracle-disaster-recovery-oracle-database-azure |
| BCDR strategies for Oracle Autonomous Database@Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/oracle-disaster-recovery-oracle-database-azure-autonomous |
| Manage and monitor Oracle on Azure VM landing zone | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/oracle-manage-monitor-iaas |
| Manage and monitor Oracle Database@Azure deployments | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/oracle-manage-monitor-oracle-database-azure |
| Design BCDR for SAP migrations on Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/sap/eslz-business-continuity-and-disaster-recovery |

### Organization & Teams
| Topic | URL |
|-------|-----|
| Prepare organizational structures for AI agents | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ai-agents/organization-people-readiness-plan |
| Build and structure a cloud governance team | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/govern/build-cloud-governance-team |
| Establish cloud operating model organizational structures | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/organize/ |
| Define cloud automation functions and expertise | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/organize/cloud-automation |
| Implement a cloud center of excellence function | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/organize/cloud-center-of-excellence |
| Establish cloud data and analytics functions | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/organize/cloud-data |
| Define and staff cloud operations functions | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/organize/cloud-operations |
| Build a cost-conscious cloud organization | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/organize/cost-conscious-organization |
| Address silos and fiefdoms in cloud transformations | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/organize/fiefdoms-silos |
| Design mature cloud team structures by stage | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/organize/organization-structures |
| Create cross-team RACI for cloud responsibilities | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/organize/raci-alignment |
| Design DevOps team topologies for Azure platforms | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ready/considerations/devops-teams-topologies |
| Define security teams, roles, and functions for Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/secure/teams-roles |
| Prepare organizational alignment for cloud adoption | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/strategy/prepare-organizational-alignment |

### Adoption Scenarios
| Topic | URL |
|-------|-----|
| Adopt organization-wide AI agents with CAF | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/ai-agents/ |
| Design identity and access management for AKS | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/aks/identity-and-access-management |
| Design network topology and connectivity for AKS | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/aks/network-topology-and-connectivity |
| Implement platform automation and DevOps for AKS | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/aks/platform-automation-and-devops |
| Design AKS resource organization for app platforms | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/aks/resource-organization |
| Plan scalability for Azure Kubernetes Service environments | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/aks/scalability |
| Choose and configure storage options for AKS workloads | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/aks/storage |
| Plan BCDR for Red Hat Enterprise Linux on Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/azure-red-hat-enterprise-linux/business-continuity-disaster-recovery |
| Apply governance and compliance to RHEL on Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/azure-red-hat-enterprise-linux/governance-compliance |
| Design identity and access for RHEL on Azure landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/azure-red-hat-enterprise-linux/identity-access-management |
| Manage and monitor Red Hat Enterprise Linux on Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/azure-red-hat-enterprise-linux/management-monitoring |
| Design networking for Red Hat Enterprise Linux landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/azure-red-hat-enterprise-linux/network-topology-connectivity |
| Automate Red Hat Enterprise Linux lifecycle on Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/azure-red-hat-enterprise-linux/platform-automation-devops |
| Organize Azure resources for Red Hat Enterprise Linux deployments | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/azure-red-hat-enterprise-linux/resource-organization |
| Implement security for Red Hat Enterprise Linux on Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/azure-red-hat-enterprise-linux/security |
| Design identity and access for Azure Red Hat OpenShift landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/azure-red-hat-openshift/identity-access-management |
| Deploy Azure Red Hat OpenShift landing zone accelerator | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/azure-red-hat-openshift/landing-zone-accelerator |
| Design networking for Azure Red Hat OpenShift landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/azure-red-hat-openshift/network-topology-connectivity |
| Establish operations baseline for Azure Red Hat OpenShift | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/azure-red-hat-openshift/operations |
| Plan platform automation and DevOps for Azure Red Hat OpenShift | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/azure-red-hat-openshift/platform-automation-devops |
| Organize resources for Azure Red Hat OpenShift landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/azure-red-hat-openshift/resource-organization |
| Implement security for Azure Red Hat OpenShift deployments | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/app-platform/azure-red-hat-openshift/security |
| Migrate user desktops to Azure Virtual Desktop with CAF | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/ |
| Deploy Azure Virtual Desktop with enterprise-scale landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/enterprise-scale-landing-zone |
| Plan business continuity and disaster recovery for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/eslz-business-continuity-and-disaster-recovery |
| Apply enterprise enrollment design to Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/eslz-enterprise-enrollment |
| Configure identity and access management for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/eslz-identity-and-access-management |
| Establish a management baseline for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/eslz-management-and-monitoring |
| Design network topology and connectivity for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/eslz-network-topology-and-connectivity |
| Automate and apply DevOps practices for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/eslz-platform-automation-and-devops |
| Design resource organization for Azure Virtual Desktop landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/eslz-resource-organization |
| Design AVD landing zones for security and governance | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/eslz-security-governance-and-compliance |
| Design BCDR for Citrix on Azure virtual desktops | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/landing-zone-citrix/citrix-business-continuity-disaster-recovery |
| Implement enterprise-scale Citrix on Azure landing zone | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/landing-zone-citrix/citrix-enterprise-scale-landing-zone |
| Configure identity and access management for Citrix on Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/landing-zone-citrix/citrix-identity-access-management |
| Establish a management baseline for Citrix on Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/landing-zone-citrix/citrix-management-monitoring |
| Design hybrid networking for Citrix on Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/landing-zone-citrix/citrix-network-topology-connectivity |
| Design resource organization for Citrix on Azure landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/landing-zone-citrix/citrix-resource-organization |
| Apply security governance and compliance to Citrix on Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-virtual-desktop/landing-zone-citrix/citrix-security-governance-compliance |
| Adopt Azure VMware Solution using CAF guidance | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/ |
| Implement enterprise-scale landing zone for Azure VMware Solution | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/azure-vmware/enterprise-scale-landing-zone |
| Implement cost governance for Azure Arc-enabled Kubernetes | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/hybrid/arc-enabled-kubernetes/eslz-arc-kubernetes-cost-governance |
| Design services observability for Azure Arc-enabled Kubernetes | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/hybrid/arc-enabled-kubernetes/eslz-arc-kubernetes-services-observability |
| Unify hybrid and multicloud operations with Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/hybrid/strategy |
| Run Oracle workloads in Azure landing zones | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/ |
| Deploy Oracle on Azure IaaS landing zone accelerator | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/oracle-landing-zone-accelerator |
| Apply security guidelines for Oracle on Azure IaaS | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/oracle-on-azure/oracle-security-overview-iaas |
| Implement SAP on Azure landing zone accelerator | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/sap/enterprise-scale-landing-zone |
| Design SAP-to-Azure data integration reference architecture | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/sap/sap-lza-data-example-architecture |
| Implement SAP and Power Platform integration workflow | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/sap/sap-power-platform-architecture-workflow |
| Extend SAP landing zones to integrate with Power Platform | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/sap/sap-power-platform-extend-landing-zone |
| Apply SAP and Power Platform integration fundamentals | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/sap/sap-power-platform-fundamental |
| Define strategy for SAP adoption on Azure | https://learn.microsoft.com/en-us/azure/cloud-adoption-framework/scenarios/sap/strategy |