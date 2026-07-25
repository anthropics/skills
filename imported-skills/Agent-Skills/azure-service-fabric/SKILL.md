---
name: azure-service-fabric
description: Expert knowledge for Azure Service Fabric development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when designing Service Fabric clusters, Reliable Services/Actors, reverse proxy/API gateways, CI/CD upgrades, or sfctl/PowerShell ops, and other Azure Service Fabric related development tasks. Not for Azure Cloud Services (use azure-cloud-services), Azure Kubernetes Service (AKS) (use azure-kubernetes-service), Azure Container Apps (use azure-container-apps), Azure App Service (use azure-app-service).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-05"
  generator: "docs2skills/1.0.0"
---
# Azure Service Fabric Skill

This skill provides expert guidance for Azure Service Fabric. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L59 | Diagnosing and fixing Service Fabric issues: connectivity, upgrades, health, logging/monitoring, container and Java logs, reverse proxy, Reliable Services/Actors, and local cluster setup. |
| Best Practices | L60-L94 | Best-practice guidance for designing, scaling, upgrading, testing, monitoring, networking, backup/restore, and data/actor management in Azure Service Fabric clusters and apps. |
| Decision Making | L95-L106 | Guidance on planning and sizing Service Fabric clusters: OS/disk choices, stateless node types, capacity/durability/reliability planning, version selection, and migration targets for Cloud Services workloads. |
| Architecture & Design Patterns | L107-L120 | Designing Service Fabric cluster architecture: cross-AZ replica rings, CRP/CRM internals, service affinity, movement cost, defragmentation, metrics balancing, networking, and API gateway patterns. |
| Limits & Quotas | L121-L125 | Configuring Service Fabric app upgrade settings: health policies, rolling upgrade behavior, monitoring, and timeout parameters to control safe, reliable deployments. |
| Security | L126-L182 | Securing Service Fabric clusters/apps: cert and Entra auth, managed identities and secrets, disk encryption, network/DDoS/IP policies, remoting/endpoint security, and security best practices. |
| Configuration | L183-L302 | Configuring and operating Service Fabric clusters and apps: networking, scaling, backup/restore, manifests, actors, containers, monitoring/telemetry, resource governance, and test/fault tools. |
| Integrations & Coding Patterns | L303-L339 | Patterns and tools for integrating Service Fabric apps with Azure services, APIs, containers, remoting stacks, and managing clusters/apps via sfctl, PowerShell, and EventStore APIs |
| Deployment | L340-L401 | Deploying and upgrading Service Fabric clusters and apps (managed, classic, standalone), scaling and AZ/region migration, CI/CD pipelines, security, images, and maintenance/upgrade control. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Connect to Service Fabric managed clusters and handle SFX cert errors | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-connect |
| Troubleshoot SNAT port exhaustion in Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-troubleshoot-snat-port-exhaustion-issues |
| Troubleshoot Azure Service Fabric application upgrade issues | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-application-upgrade-troubleshooting |
| View and use Service Fabric container logs for diagnosis | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-containers-view-logs |
| Troubleshoot common Service Fabric code package errors | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-diagnostics-code-package-errors |
| Diagnose common monitoring and diagnostics scenarios in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-diagnostics-common-scenarios |
| Analyze Service Fabric events with Azure Monitor logs queries | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-diagnostics-event-analysis-oms |
| Monitor and diagnose Service Fabric apps locally on Windows | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-diagnostics-how-to-monitor-and-diagnose-services-locally |
| Monitor and diagnose Service Fabric apps locally on Linux | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-diagnostics-how-to-monitor-and-diagnose-services-locally-linux |
| Report and inspect Service Fabric health from code | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-diagnostics-how-to-report-and-check-service-health |
| Resolve common FabricClient exceptions in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-errors-and-exceptions |
| Monitor Service Fabric Reliable Actors runtime diagnostics | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-actors-diagnostics |
| Monitor Service Fabric ServiceRemoting with performance counters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-serviceremoting-diagnostics |
| Diagnose Stateful Reliable Services using Service Fabric diagnostics | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-services-diagnostics |
| Diagnose Service Fabric reverse proxy request failures | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reverse-proxy-diagnostics |
| Fix common local Service Fabric cluster setup issues | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-troubleshoot-local-cluster-setup |
| Debug and collect logs for Java apps on local Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-tutorial-debug-log-local-cluster |
| Use Service Fabric system health reports to troubleshoot | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-understand-and-troubleshoot-with-system-health-reports |
| Query and evaluate aggregated health in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-view-entities-aggregated-health |

### Best Practices
| Topic | URL |
|-------|-----|
| Best practices to migrate Cloud Services to Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/cloud-services-to-service-fabric-migration-guide |
| Patch Windows OS on Azure Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-patch-cluster-nodes-windows |
| Apply data serialization best practices for Service Fabric upgrades | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-application-upgrade-data-serialization |
| Avoid invalid Service Fabric ARM cluster configurations | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-azure-resource-manager-guardrails |
| Design Azure Service Fabric applications effectively | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-best-practices-applications |
| Plan and scale Azure Service Fabric cluster capacity | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-best-practices-capacity-scaling |
| Manage Service Fabric as code with ARM templates | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-best-practices-infrastructure-as-code |
| Apply monitoring best practices for Azure Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-best-practices-monitoring |
| Apply networking best practices for Azure Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-best-practices-networking |
| Configure stateful replica set size in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-best-practices-replica-set-size-configuration |
| Convert Cloud Services roles to Service Fabric stateless services | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cloud-services-migration-worker-role-stateless-service |
| Use automatic node repair in Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-node-auto-repair |
| Unit test stateful Service Fabric services effectively | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-concepts-unit-testing |
| Design disaster recovery strategies for Azure Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-disaster-recovery |
| Implement logging for .NET Service Fabric applications | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-how-to-diagnostics-log |
| Unit test Service Fabric stateful services effectively | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-how-to-unit-test-stateful-services |
| Use Service Fabric production readiness checklist | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-production-readiness-checklist |
| Design and manage Reliable Actor state in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-actors-access-save-remove-state |
| Implement backup and restore for Service Fabric actors | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-actors-backup-and-restore |
| Manually delete Reliable Actors and their state in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-actors-delete-actors |
| Define serializable types for Service Fabric actors | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-actors-notes-on-actor-type-serialization |
| Choose and use timers vs reminders in Reliable Actors | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-actors-timers-reminders |
| Plan and use Service Fabric Backup and Restore | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-services-backup-restore |
| Apply best practices for Service Fabric Reliable Collections | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-services-reliable-collections-guidelines |
| Handle throttling in Service Fabric Reliable Collections | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-services-reliable-collections-throttling-guidelines |
| Configure transactions and locks in Reliable Collections | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-services-reliable-collections-transactions-locks |
| Use ReliableConcurrentQueue for high-throughput messaging | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-services-reliable-concurrent-queue |
| Use replica soft delete for Service Fabric data protection | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-replica-soft-delete |
| Design and emit custom Service Fabric health reports | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-report-health |
| Design and test Service Fabric service-to-service communication | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-testability-scenarios-service-communication |
| Use Reliable Collections effectively in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-work-with-reliable-collections |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose Azure migration targets for Cloud Services workloads | https://learn.microsoft.com/en-us/azure/service-fabric/cloud-services-migration-decision-matrix |
| Use Ephemeral OS disks with Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-ephemeral-os-disks |
| Choose and configure managed disk types for Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-managed-disk |
| Deploy stateless node types in Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-stateless-node-type |
| Estimate resource capacity for Service Fabric applications | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-capacity-planning |
| Plan Service Fabric cluster capacity, durability, and reliability | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-capacity |
| Choose between Service Fabric on Linux or Windows | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-linux-windows-differences |
| Select supported Azure Service Fabric cluster versions | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-versions |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design Service Fabric cross-AZ auxiliary replica rings | https://learn.microsoft.com/en-us/azure/service-fabric/advanced-fault-tolerance-availability-zone-rings |
| Handle subclustered metrics balancing in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/cluster-resource-manager-subclustering |
| Use Azure API Management as gateway for Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-api-management-overview |
| Configure service affinity patterns in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-resource-manager-advanced-placement-rules-affinity |
| Service Fabric Cluster Resource Manager architecture details | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-resource-manager-architecture |
| Use defragmentation metrics strategy in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-resource-manager-defragmentation-metrics |
| Understand Service Fabric Cluster Resource Manager | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-resource-manager-introduction |
| Integrate Cluster Resource Manager with Service Fabric management | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-resource-manager-management-integration |
| Tune movement cost for Service Fabric services | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-resource-manager-movement-cost |
| Apply networking patterns for Azure Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-patterns-networking |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Configure Service Fabric application upgrade parameters and timeouts | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-application-upgrade-parameters |

### Security
| Topic | URL |
|-------|-----|
| Manage X.509 certificates for Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/cluster-security-certificate-management |
| Configure X.509 certificate authentication in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/cluster-security-certificates |
| Use managed identities with Azure Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/concepts-managed-identity |
| Enable managed identity token service on existing Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/configure-existing-cluster-enable-managed-identity-token-service |
| Configure managed identity support for new Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/configure-new-azure-service-fabric-enable-managed-identity |
| Deploy Service Fabric applications with system-assigned managed identity | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-deploy-service-fabric-application-system-assigned-managed-identity |
| Grant Service Fabric app managed identity access to Azure resources | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-grant-access-other-resources |
| Configure Service Fabric applications with managed identity on managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-application-managed-identity |
| Manage and deploy application secrets in Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-application-secrets |
| Configure Microsoft Entra client access for Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-azure-active-directory-client |
| Enable Azure DDoS Protection for Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-ddos-protection |
| Enable disk encryption for Service Fabric managed cluster nodes | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-enable-disk-encryption |
| Grant Azure resource access to Service Fabric managed identities | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-grant-access-other-resources |
| Configure IP tags for Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-ip-tags |
| Migrate Service Fabric clusters to TLS 1.3 | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-migrate-transport-layer-security |
| Apply deny assignment policies to Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/managed-cluster-deny-assignment |
| Understand blocking operations in Service Fabric Explorer | https://learn.microsoft.com/en-us/azure/service-fabric/managed-cluster-service-fabric-explorer-blocking-operation |
| Built-in Azure Policy definitions for Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/policy-reference |
| Apply Azure Policy compliance controls to Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/security-controls-policy |
| Secure Azure Service Fabric applications and services | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-application-and-service-security |
| Run Service Fabric applications under system and local accounts | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-application-runas-security |
| Manage and encrypt application secrets in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-application-secret-management |
| Configure encryption certificates for Linux Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-application-secret-management-linux |
| Configure encryption certificates for Windows Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-application-secret-management-windows |
| Use Service Fabric Central Secret Service for in-cluster secrets | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-application-secret-store |
| Assign security access policies to Service Fabric endpoints | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-assign-policy-to-endpoint |
| Apply Service Fabric cluster security best practices | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-best-practices-security |
| Migrate Service Fabric cluster certificates to common name | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-change-cert-thumbprint-to-cn |
| Set up Microsoft Entra ID client authentication for Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-creation-setup-aad |
| Configure Microsoft Entra ID authentication for Service Fabric in Azure portal | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-creation-setup-azure-ad-via-portal |
| Roll over Service Fabric cluster certificates using CN | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-rollover-cert-cn |
| Secure Azure Service Fabric clusters in production | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-security |
| Configure Service Fabric cluster client roles and permissions | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-security-roles |
| Manage X.509 certificates in Azure Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-security-update-certs-azure |
| Configure X.509 certificates for Service Fabric apps on Linux | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-configure-certificates-linux |
| Authenticate and securely connect clients to Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-connect-to-secure-cluster |
| Create Service Fabric clusters using certificate common names | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-create-cluster-using-cert-cn |
| Enable disk encryption for Linux Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-enable-azure-disk-encryption-linux |
| Enable disk encryption for Windows Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-enable-azure-disk-encryption-windows |
| Use Key Vault references for Service Fabric application secrets | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-keyvault-references |
| Enable secure data contract serialization for Service Fabric remoting exceptions | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-services-exception-serialization |
| Secure C# service remoting communication in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-services-secure-communication |
| Secure Java service remoting communication in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-services-secure-communication-java |
| Secure WCF-based Reliable Services communication in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-services-secure-communication-wcf |
| Secure Service Fabric reverse proxy end-to-end communication | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reverseproxy-configure-secure-communication |
| Run Service Fabric services as Active Directory users or groups | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-run-service-as-ad-user-or-group |
| Run Service Fabric services under gMSA accounts | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-run-service-as-gmsa |
| Import and manage certificates in Service Fabric container services | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-securing-containers |
| Set up gMSA for Service Fabric Windows container services | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-setup-gmsa-for-windows-containers |
| Configure HTTPS endpoints for ASP.NET Core services on Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-tutorial-dotnet-app-enable-https-endpoint |
| Configure secure Service Fabric cluster connections in Visual Studio | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-visualstudio-configure-secure-connections |
| Configure Windows security for standalone Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-windows-cluster-windows-security |
| Secure standalone Windows Service Fabric clusters with certificates | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-windows-cluster-x509-security |

### Configuration
| Topic | URL |
|-------|-----|
| Use Service Fabric Backup Explorer on local backups | https://learn.microsoft.com/en-us/azure/service-fabric/backup-explorer |
| Configure container registry credentials in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/configure-container-repository-credentials |
| Configure container image management in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/container-image-management |
| Configure Azure Load Balancer rules for Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/create-load-balancer-rule |
| Disable and enable Service Fabric services (scale to zero) | https://learn.microsoft.com/en-us/azure/service-fabric/disable-enable-service |
| Configure ARM-based app deployment to Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-app-deployment-template |
| Integrate Azure Application Gateway with Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-application-gateway |
| Configure autoscaling policies for Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-autoscale |
| Configure Azure Service Fabric managed cluster settings | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-configuration |
| Deploy Service Fabric managed clusters with a subnet per node type | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-deploy-with-subnet-per-nodetype |
| Configure large VM scale sets for Service Fabric secondary node types | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-large-virtual-machine-scale-sets |
| Modify node type configuration in Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-modify-node-type |
| Configure NAT gateway for Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-nat-gateway |
| Configure networking, NSGs, and load balancer for Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-networking |
| Use Public IP address prefixes with Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-public-ip-prefix |
| Configure scale-to-zero for Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-scale-to-zero |
| Configure multiple NICs and subnets for Service Fabric node types | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-use-multiple-network-interface-cards |
| Add VM scale set extensions to Service Fabric managed cluster node types | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-vmss-extension |
| Add managed identities to Service Fabric managed cluster node types | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-identity-managed-cluster-virtual-machine-scale-sets |
| Configure Initializer CodePackages in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/initializer-codepackages |
| Set up monitoring for Azure Service Fabric with Azure Monitor | https://learn.microsoft.com/en-us/azure/service-fabric/monitor-service-fabric |
| Monitoring data reference for Azure Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/monitor-service-fabric-reference |
| Configure liveness and readiness probes in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/probes-codepackage |
| Configure RunToCompletion services in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/run-to-completion |
| Define Service Fabric applications with manifests | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-application-and-service-manifests |
| Trigger on-demand backups for Service Fabric services | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-backup-restore-service-ondemand-backup |
| Restore Service Fabric state from periodic backups | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-backup-restore-service-trigger-restore |
| Configure periodic backup policies for Service Fabric services | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-backuprestoreservice-configure-periodic-backup |
| Configure periodic backup and restore for Service Fabric on Azure | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-backuprestoreservice-quickstart-azurecluster |
| Configure periodic backup and restore for standalone Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-backuprestoreservice-quickstart-standalonecluster |
| Use Service Fabric CLI to manage clusters and apps | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cli |
| Upgrade Azure Service Fabric cluster configuration via ARM | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-config-upgrade-azure |
| Upgrade configuration settings for standalone Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-config-upgrade-windows-server |
| Author ARM templates for secure Azure Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-creation-create-template |
| Customize Azure Service Fabric cluster fabric settings | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-fabric-settings |
| Configure standalone Service Fabric clusters via ClusterConfig.json | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-manifest |
| Configure node types and VM scale sets for Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-nodetypes |
| Remote connect to Azure Service Fabric cluster nodes | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-remote-connect-to-azure-cluster-node |
| Configure advanced placement policies in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-resource-manager-advanced-placement-rules-placement-policies |
| Configure throttling in Service Fabric Cluster Resource Manager | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-resource-manager-advanced-throttling |
| Configure Application Groups in Service Fabric Cluster Resource Manager | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-resource-manager-application-groups |
| Configure auto scaling policies for Service Fabric services | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-resource-manager-autoscaling |
| Configure cluster balancing with Service Fabric Cluster Resource Manager | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-resource-manager-balancing |
| Describe Service Fabric clusters for Cluster Resource Manager | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-resource-manager-cluster-description |
| Specify metrics and placement settings for Service Fabric services | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-resource-manager-configure-services |
| Configure ignore-metrics behavior in Service Fabric CRM | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-resource-manager-ignore-metrics |
| Configure InBuild throttling for Service Fabric replicas | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-resource-manager-inbuild-throttling |
| Configure and use Service Fabric load metrics | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-resource-manager-metrics |
| Use dynamic node tags to influence Service Fabric placement | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-resource-manager-node-tagging |
| Configure service sensitivity and maximum load in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-resource-manager-sensitivity |
| Understand contents of the Service Fabric standalone Windows package | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-standalone-package-contents |
| Modify node count in standalone Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-windows-server-add-remove-nodes |
| Configure Azure Files volume driver for Service Fabric containers | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-containers-volume-logging-drivers |
| Use Fault Injection and Cluster Analysis Service to induce chaos | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-controlled-chaos |
| Configure Java remote debugging for Service Fabric in Eclipse | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-debugging-your-application-java |
| Configure Service Fabric telemetry with Azure Monitor Agent and DCRs | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-diagnostics-azure-monitor-agent-data-collection-rules |
| Configure EventFlow for Service Fabric event aggregation | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-diagnostics-event-aggregation-eventflow |
| Aggregate Service Fabric Linux events with LAD | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-diagnostics-event-aggregation-lad |
| Aggregate Service Fabric events with Windows Azure Diagnostics | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-diagnostics-event-aggregation-wad |
| Configure platform-level monitoring for Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-diagnostics-event-generation-infra |
| Reference list of Azure Service Fabric operational events | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-diagnostics-event-generation-operational |
| Use built-in Azure Service Fabric events for monitoring | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-diagnostics-events |
| Use Azure Service Fabric Event Store for cluster state | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-diagnostics-eventstore |
| Configure Azure Monitor logs for Service Fabric containers | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-diagnostics-oms-containers |
| Configure Syslog for Service Fabric Linux cluster events | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-diagnostics-oms-syslog |
| Collect Service Fabric performance counters with Azure Diagnostics | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-diagnostics-perf-wad |
| Configure and use Azure Service Fabric DNS service | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-dnsservice |
| Deploy Docker Compose applications to Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-docker-compose |
| Environment variables reference for Azure Service Fabric services | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-environment-variables-reference |
| Set up Eclipse for Java development with Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-get-started-eclipse |
| Configure VS Code extension for Service Fabric development | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-get-started-vs-code |
| Parameterize Service Fabric configuration files for multiple environments | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-how-to-parameterize-configuration-files |
| Configure environment variables for Service Fabric services and containers | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-how-to-specify-environment-variables |
| Specify Service Fabric service ports using parameters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-how-to-specify-port-number-using-parameters |
| Configure the Service Fabric image store connection string | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-image-store-connection-string |
| Configure Service Fabric apps for multiple environments | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-manage-multiple-environment-app-configuration |
| Configure Service Fabric node types with managed disks | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-managed-disk |
| Configure manifests for multi-container Service Fabric apps | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-manifest-example-container-app |
| Configure manifests for Service Fabric reliable services apps | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-manifest-example-reliable-services-app |
| Service Fabric application and service manifest configuration examples | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-manifest-examples |
| Configure networking modes for Service Fabric container services | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-networking-modes |
| Start and stop Service Fabric cluster nodes for fault testing | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-node-transition-apis |
| Configure Patch Orchestration Application for Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-patch-orchestration-application |
| Configure FabricTransport communication settings for Service Fabric actors | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-actors-fabrictransportsettings |
| Configure KVSActorStateProvider settings in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-actors-kvsactorstateprovider-configuration |
| Configure and manage Service Fabric actor lifecycle | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-actors-lifecycle |
| Configure reentrancy behavior in Service Fabric actors | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-actors-reentrancy |
| Configure ReliableDictionaryActorStateProvider settings in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-actors-reliabledictionarystateprovider-configuration |
| Implement custom Service Fabric ActorService features | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-actors-using |
| Configure global and per-service settings for Reliable Services | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-services-configuration |
| Configure serialization for Service Fabric Reliable Collections | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-services-reliable-collections-serialization |
| Configure Service Fabric resource governance for services | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-resource-governance |
| Configure Service Fabric reverse proxy for microservices | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reverseproxy |
| Set up and configure Service Fabric reverse proxy | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reverseproxy-setup |
| Configure Service Fabric service startup scripts and RunAs policy | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-run-script-at-service-startup |
| Specify Service Fabric service endpoints and HTTPS settings | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-service-manifest-resources |
| Reference for Service Fabric service model XML schema | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-service-model-schema |
| Service Fabric service model XML schema attribute groups | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-service-model-schema-attribute-groups |
| Service Fabric service model XML schema complex types reference | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-service-model-schema-complex-types |
| Service Fabric service model XML schema element groups | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-service-model-schema-element-groups |
| Service Fabric service model XML schema elements reference | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-service-model-schema-elements |
| Service Fabric service model XML schema simple types reference | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-service-model-schema-simple-types |
| Run Service Fabric services inside Windows containers | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-services-inside-containers |
| Configure local Azure Service Fabric sfctl settings | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-sfctl-settings |
| Configure telemetry settings for Service Fabric sfctl | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-sfctl-settings-telemetry |
| Use StartupServices.xml to configure Service Fabric services | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-startupservices-model |
| Configure stateless-only node types in Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-stateless-node-types |
| Use Service Fabric testability actions to simulate failures | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-testability-actions |
| Use Fault Analysis Service to test Service Fabric apps | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-testability-overview |
| Create chaos and failover test scenarios for Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-testability-scenarios |
| Simulate faults with workload tests in Service Fabric apps | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-testability-workload-tests |
| Configure ELK stack monitoring for Service Fabric applications | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-tutorial-java-elk |
| Monitor Azure Service Fabric clusters with events and health reports | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-tutorial-monitor-cluster |
| Configure Azure Monitor logs for Windows containers on Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-tutorial-monitoring-wincontainers |
| Generate and package Service Fabric container applications with Yeoman | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-tutorial-package-containers |
| Use Service Fabric Explorer to inspect and manage clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-visualizing-your-cluster |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use managed identity in Service Fabric application code to access Azure services | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-managed-identity-service-fabric-app-code |
| Use managed identity in Service Fabric application code | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-identity-service-fabric-app-code |
| Manage Service Fabric with Azure CLI and sfctl | https://learn.microsoft.com/en-us/azure/service-fabric/samples-cli |
| Connect and communicate with Service Fabric services | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-connect-and-communicate-with-services |
| Query Service Fabric EventStore APIs for cluster events | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-diagnostics-eventstore-query |
| Containerize and deploy .NET apps to Service Fabric with Azure SQL | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-host-app-in-a-container |
| Generate and use Service Fabric Java client APIs from REST spec | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-java-rest-api-usage |
| Migrate Service Fabric Java apps from SDK to Maven dependencies | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-migrate-old-javaapp-to-use-maven |
| Use PowerShell to manage Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-powershell-samples |
| Enumerate Reliable Actors and metadata in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-actors-enumerate |
| Use events for communication in Service Fabric Reliable Actors | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-actors-events |
| Host ASP.NET Core services in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-services-communication-aspnetcore |
| Implement C# service remoting in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-services-communication-remoting |
| Implement Java service remoting in Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-services-communication-remoting-java |
| Use WCF communication stack with Service Fabric Reliable Services | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-reliable-services-communication-wcf |
| Reference for Azure Service Fabric sfctl CLI commands | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-sfctl |
| Manage Service Fabric applications with sfctl application commands | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-sfctl-application |
| Run Service Fabric chaos tests with sfctl chaos commands | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-sfctl-chaos |
| Configure Service Fabric chaos schedules with sfctl | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-sfctl-chaos-schedule |
| Manage Service Fabric clusters using sfctl cluster commands | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-sfctl-cluster |
| Manage Docker Compose apps on Service Fabric with sfctl | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-sfctl-compose |
| Run Service Fabric container operations with sfctl container | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-sfctl-container |
| Control Service Fabric infrastructure service with sfctl is commands | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-sfctl-is |
| Manage Service Fabric cluster nodes with sfctl node commands | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-sfctl-node |
| Query and manage Service Fabric partitions with sfctl | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-sfctl-partition |
| Store and query Service Fabric properties with sfctl property | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-sfctl-property |
| Manage Service Fabric replicas using sfctl replica commands | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-sfctl-replica |
| Use sfctl rpm to control Service Fabric repair manager | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-sfctl-rpm |
| Manage standalone Service Fabric clusters with sfctl sa-cluster | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-sfctl-sa-cluster |
| Create and manage Service Fabric services with sfctl service | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-sfctl-service |
| Perform image store file operations with sfctl store | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-sfctl-store |
| Create container images for multi-container Service Fabric apps | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-tutorial-create-container-images |
| Integrate Azure API Management with Service Fabric back-end services | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-tutorial-deploy-api-management |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy custom Windows images to Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-deploy-custom-image |
| Deploy Service Fabric apps with user-assigned managed identity | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-deploy-service-fabric-application-user-assigned-managed-identity |
| Deploy Service Fabric managed clusters across Availability Zones | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-availability-zones |
| Add Azure Dedicated Hosts to Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-dedicated-hosts |
| Enable coordinated Safe Deployment Process on Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-enable-safe-deployment-process |
| Configure maintenance control windows for Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-maintenance-control |
| Manage runtime upgrades for Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/how-to-managed-cluster-upgrades |
| Migrate Service Fabric clusters to availability zone support | https://learn.microsoft.com/en-us/azure/service-fabric/migrate-service-fabric-availability-zones |
| Deploy a classic Service Fabric cluster via portal | https://learn.microsoft.com/en-us/azure/service-fabric/quickstart-classic-cluster-portal |
| Create a Service Fabric cluster using Bicep | https://learn.microsoft.com/en-us/azure/service-fabric/quickstart-cluster-bicep |
| Deploy a Service Fabric cluster with ARM templates | https://learn.microsoft.com/en-us/azure/service-fabric/quickstart-cluster-template |
| Deploy a basic Service Fabric managed cluster via portal | https://learn.microsoft.com/en-us/azure/service-fabric/quickstart-managed-cluster-portal |
| Deploy a Service Fabric managed cluster with ARM templates | https://learn.microsoft.com/en-us/azure/service-fabric/quickstart-managed-cluster-template |
| Deploy and upgrade Service Fabric apps with ARM templates | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-application-arm-resource |
| Manage Service Fabric application lifecycle with sfctl CLI | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-application-lifecycle-sfctl |
| Plan and execute Service Fabric application upgrades | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-application-upgrade |
| Handle advanced Service Fabric application upgrade scenarios | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-application-upgrade-advanced |
| Perform zero-downtime Service Fabric app upgrades with Visual Studio | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-application-upgrade-tutorial |
| Perform monitored rolling upgrades of Service Fabric apps with PowerShell | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-application-upgrade-tutorial-powershell |
| Plan and prepare Azure Service Fabric cluster deployment | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-azure-deployment-preparation |
| Create a standalone Service Fabric cluster on Windows Server | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-creation-for-windows-server |
| Deploy secure Azure Service Fabric clusters using ARM templates | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-creation-via-arm |
| Create a secure Service Fabric cluster via Azure portal | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-creation-via-portal |
| Programmatically scale Azure Service Fabric clusters using Azure SDK | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-programmatic-scaling |
| Migrate Azure Service Fabric clusters between regions | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-region-move |
| Scale Azure Service Fabric clusters in and out with autoscale | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-scale-in-out |
| Scale Azure Service Fabric clusters in and out | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-scaling |
| Scale Azure Service Fabric standalone clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-scaling-standalone |
| Prepare environment for standalone Service Fabric cluster deployment | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-standalone-deployment-preparation |
| Upgrade Azure Service Fabric managed clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-upgrade |
| Migrate Service Fabric Linux clusters from Ubuntu 18.04 to 20.04 | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-upgrade-os |
| Upgrade Azure Service Fabric standalone clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-upgrade-standalone |
| Control Azure Service Fabric cluster runtime upgrades | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-upgrade-version-azure |
| Upgrade Service Fabric version on standalone clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cluster-upgrade-windows-server |
| Deploy Service Fabric clusters across Azure Availability Zones | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-cross-availability-zones |
| Deploy and remove Service Fabric applications using PowerShell | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-deploy-remove-applications |
| Deploy and remove Service Fabric applications using FabricClient APIs | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-deploy-remove-applications-fabricclient |
| Build, deploy, and debug .NET Core Service Fabric apps in VS Code | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-develop-csharp-applications-with-vs-code |
| Build, deploy, and debug Java Service Fabric apps in VS Code | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-develop-java-applications-with-vs-code |
| Package and deploy guest executables to Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-guest-executables-introduction |
| Publish .NET Core Service Fabric apps to remote Linux clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-how-to-publish-linux-app-vs |
| Deploy and manage Service Fabric apps in Visual Studio | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-manage-application-in-visual-studio |
| Package Service Fabric applications for deployment | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-package-apps |
| Scale up nonprimary node types in Azure Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-scale-up-non-primary-node-type |
| Scale up primary node types in Azure Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-scale-up-primary-node-type |
| Deploy a Linux Service Fabric cluster into an existing Azure VNet | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-tutorial-create-vnet-and-linux-cluster |
| Deploy a Windows Service Fabric cluster into an Azure virtual network | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-tutorial-create-vnet-and-windows-cluster |
| Deploy a Service Fabric app to Azure clusters with Visual Studio | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-tutorial-deploy-app |
| Set up CI/CD for Service Fabric apps with Azure Pipelines | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-tutorial-deploy-app-with-cicd-vsts |
| Set up CI/CD for Service Fabric container applications | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-tutorial-deploy-container-app-with-cicd-vsts |
| Deploy Java Service Fabric applications to Azure clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-tutorial-java-deploy-azure |
| Configure Jenkins CI for Java apps on Service Fabric | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-tutorial-java-jenkins |
| Scale Azure Service Fabric clusters and clean up resources | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-tutorial-scale-cluster |
| Create Azure VM infrastructure for standalone Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-tutorial-standalone-azure-create-infrastructure |
| Create AWS infrastructure for standalone Service Fabric clusters | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-tutorial-standalone-create-infrastructure |
| Install and configure Service Fabric standalone clusters and client | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-tutorial-standalone-create-service-fabric-cluster |
| Upgrade the Service Fabric runtime on Azure clusters with PowerShell | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-tutorial-upgrade-cluster |
| Configure Service Fabric application upgrades in Visual Studio | https://learn.microsoft.com/en-us/azure/service-fabric/service-fabric-visualstudio-configure-upgrade |
| Deploy a Service Fabric managed cluster for testing | https://learn.microsoft.com/en-us/azure/service-fabric/tutorial-managed-cluster-deploy |