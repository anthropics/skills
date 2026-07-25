---
name: azure-container-instances
description: Expert knowledge for Azure Container Instances development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, and deployment. Use when configuring ACI networking, standby pools, Spot containers, GitHub Actions deploys, or secure ACR access, and other Azure Container Instances related development tasks. Not for Azure Container Apps (use azure-container-apps), Azure Kubernetes Service (AKS) (use azure-kubernetes-service), Azure Virtual Machines (use azure-virtual-machines), Azure App Service (use azure-app-service).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-05"
  generator: "docs2skills/1.0.0"
---
# Azure Container Instances Skill

This skill provides expert guidance for Azure Container Instances. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L36-L42 | Diagnosing ACI issues by viewing logs/events, understanding provisioning/runtime states, and troubleshooting common deployment, startup, and container runtime failures. |
| Best Practices | L43-L47 | Guidance on designing and running ACI workloads reliably: resource sizing, networking, storage, security, scaling, image management, and operational best practices. |
| Decision Making | L48-L53 | Guidance on cost-optimizing ACI with Spot containers and using prediction-based sizing to configure and right-size Azure Container Instances standby pools. |
| Architecture & Design Patterns | L54-L60 | Design patterns for giving ACI containers static inbound/outbound IPs using Application Gateway, firewalls, and NAT Gateway for controlled, predictable network egress/ingress. |
| Limits & Quotas | L61-L69 | ACI limits, quotas, and behaviors: vCPU/memory caps, big containers, regional capacity checks, standby pool constraints, and VNet-related resource limitations. |
| Security | L70-L84 | Securing Azure Container Instances: TLS/HTTPS setup, image and secret protection, managed identities, RBAC, DNS safety, ACR auth, CMK encryption, and Azure Policy enforcement. |
| Configuration | L85-L117 | Configuring ACI container groups: YAML, env vars, DNS, volumes, probes, GPUs, restart/entrypoint, standby pools, networking, lifecycle, logging, and monitoring. |
| Deployment | L118-L121 | Using GitHub Actions to build, push, and automatically deploy container images to Azure Container Instances, including workflow YAML setup and authentication configuration. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Retrieve Azure Container Instances logs and events for troubleshooting | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-get-logs |
| Troubleshoot common deployment and runtime issues in Azure Container Instances | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-troubleshooting |
| Interpret Azure Container Instances provisioning and runtime states | https://learn.microsoft.com/en-us/azure/container-instances/container-state |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply Azure Container Instances workload best practices | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-best-practices-and-considerations |

### Decision Making
| Topic | URL |
|-------|-----|
| Decide when to use ACI Spot containers for cost savings | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-spot-containers-overview |
| Use prediction results to right-size Azure Container Instances standby pools | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-standby-pool-prediction-results |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Expose Azure Container Instances via Application Gateway static IP | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-application-gateway |
| Configure static outbound IP for Azure Container Instances with firewall | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-egress-ip-address |
| Configure Azure Container Instances egress via NAT Gateway | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-nat-gateway |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Use Big Containers with ACI vCPU and memory limits | https://learn.microsoft.com/en-us/azure/container-instances/big-containers |
| Azure Container Instances FAQs on limits and behavior | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-faq |
| Check ACI resource availability and quota limits by region | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-resource-and-quota-limits |
| FAQ and limits for Azure Container Instances standby pools | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-standby-pool-faq |
| Use Azure Container Instances with virtual networks | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-virtual-network-concepts |

### Security
| Topic | URL |
|-------|-----|
| Configure automatic HTTPS for Azure Container Instances using Caddy | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-container-group-automatic-ssl |
| Enable TLS for Azure Container Instances with Nginx sidecar | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-container-group-ssl |
| Encrypt Azure Container Instances deployment data with customer-managed keys | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-encrypt-data |
| Secure images and secrets for Azure Container Instances | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-image-security |
| Enable and use managed identities in Azure Container Instances | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-managed-identity |
| Configure RBAC permissions for Azure Container Instances standby pools | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-standby-pool-configure-permissions |
| Configure ACI to pull images from ACR using service principals | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-using-azure-container-registry |
| Mount secret volumes in Azure Container Instances | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-volume-secret |
| Set ACI DNS name reuse policy to prevent subdomain takeover | https://learn.microsoft.com/en-us/azure/container-instances/how-to-reuse-dns-names |
| Use built-in Azure Policy definitions for Container Instances | https://learn.microsoft.com/en-us/azure/container-instances/policy-reference |
| Use managed identities for ACI image pulls from private ACR | https://learn.microsoft.com/en-us/azure/container-instances/using-azure-container-registry-mi |

### Configuration
| Topic | URL |
|-------|-----|
| Use config maps to manage settings in Azure Container Instances | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-config-map |
| Configure custom DNS for Azure Container Instances container groups | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-custom-dns |
| Configure environment variables for Azure Container Instances | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-environment-variables |
| Execute commands in running Azure Container Instances containers | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-exec |
| Deploy GPU-enabled workloads on Azure Container Instances | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-gpu |
| Configure init containers in Azure Container Instances | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-init-container |
| Configure liveness probes for Azure Container Instances | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-liveness-probe |
| Send Azure Container Instances resource logs to Azure Monitor | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-log-analytics |
| Configure readiness probes for Azure Container Instances | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-readiness-probe |
| YAML configuration reference for Azure Container Instances container groups | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-reference-yaml |
| Configure ACI restart policies for run-once container tasks | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-restart-policy |
| Create standby pools for Azure Container Instances | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-standby-pool-create |
| Retrieve details of Azure Container Instances standby pools | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-standby-pool-get-details |
| Understand and query health state of Azure Container Instances standby pools | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-standby-pool-health-state |
| Use standby pools to reduce Azure Container Instances scale-out latency | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-standby-pool-overview |
| Request container groups from Azure Container Instances standby pools | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-standby-pool-request-container |
| Update or delete Azure Container Instances standby pools | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-standby-pool-update-delete |
| Monitor Azure Container Instances standby pool events with Log Analytics | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-standby-pools-monitor-pool-events |
| Override container entrypoint command in Azure Container Instances | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-start-command |
| Manually stop and start Azure Container Instances container groups | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-stop-start |
| Update running container groups in Azure Container Instances | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-update |
| Configure ACI container groups in Azure virtual networks via CLI | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-vnet |
| Mount Azure Files volumes in Azure Container Instances | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-volume-azure-files |
| Use emptyDir volumes to share data in Azure Container Instances | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-volume-emptydir |
| Mount gitRepo volumes in Azure Container Instances | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-volume-gitrepo |
| Configure monitoring and alerts for Azure Container Instances | https://learn.microsoft.com/en-us/azure/container-instances/monitor-azure-container-instances |
| Configure monitoring and alerts for Azure Container Instances | https://learn.microsoft.com/en-us/azure/container-instances/monitor-azure-container-instances |
| Monitoring data reference for Azure Container Instances | https://learn.microsoft.com/en-us/azure/container-instances/monitor-azure-container-instances-reference |
| View Azure Container Instances logs in Log Analytics via portal | https://learn.microsoft.com/en-us/azure/container-instances/viewing-logs-in-portal |

### Deployment
| Topic | URL |
|-------|-----|
| Automate ACI deployments with GitHub Actions workflow configuration | https://learn.microsoft.com/en-us/azure/container-instances/container-instances-github-action |