---
name: azure-cyclecloud
description: Expert knowledge for Azure CycleCloud development including troubleshooting, best practices, decision making, architecture & design patterns, security, configuration, integrations & coding patterns, and deployment. Use when automating CycleCloud via API/CLI, configuring Slurm/HTCondor clusters, tuning HB/HC VMs, or securing access, and other Azure CycleCloud related development tasks. Not for Azure Batch (use azure-batch), Azure HPC Cache (use azure-hpc-cache), Azure Virtual Machines (use azure-virtual-machines), Azure Kubernetes Service (AKS) (use azure-kubernetes-service).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure CycleCloud Skill

This skill provides expert guidance for Azure CycleCloud. Covers troubleshooting, best practices, decision making, architecture & design patterns, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L36-L43 | Diagnosing and fixing CycleCloud errors, unhealthy VMs, and cluster/node startup issues, plus finding and using diagnostic logs for deeper troubleshooting. |
| Best Practices | L44-L48 | Tuning CycleCloud clusters on HB/HC series: VM sizing, network and storage optimization, MPI/HPC performance tweaks, and cost/performance best practices. |
| Decision Making | L49-L58 | Guidance on planning/migrating CycleCloud clusters and workspaces, choosing Spot VMs, and understanding licensing, usage, and servicing policies for Azure CycleCloud. |
| Architecture & Design Patterns | L59-L64 | Designing resilient multi‑region CycleCloud HPC clusters and choosing VM placement strategies (single-zone, multi-zone, regional) for performance, availability, and cost optimization. |
| Security | L65-L79 | Securing CycleCloud: auth (Entra, service principals, managed identities), SSL, SSH/Bastion access, SELinux, telemetry/data usage, and portal/cluster user authentication setup. |
| Configuration | L80-L128 | Designing and configuring CycleCloud clusters: templates, nodes, networking, storage, autoscaling, images, events, monitoring, proxies, security, and deployment/CLI setup. |
| Integrations & Coding Patterns | L129-L148 | APIs, CLI, and Python SDK for automating CycleCloud, plus configuring and integrating schedulers (Slurm, Grid Engine, HTCondor, LSF, OpenPBS, HPC Pack), monitoring, and Event Grid. |
| Deployment | L149-L158 | Deploying and operating CycleCloud: installing via ARM/CLI/ACI, planning production setups, importing templates, moving cluster resources, and safely upgrading or migrating installations. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Resolve common Azure CycleCloud error messages | https://learn.microsoft.com/en-us/azure/cyclecloud/error-messages?view=cyclecloud-8 |
| Use CycleCloud HealthCheck services to manage unhealthy VMs | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/healthcheck?view=cyclecloud-8 |
| Diagnose and report Azure CycleCloud cluster and node startup issues | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/report-issues?view=cyclecloud-8 |
| Locate Azure CycleCloud diagnostic log files | https://learn.microsoft.com/en-us/azure/cyclecloud/log-locations?view=cyclecloud-8 |

### Best Practices
| Topic | URL |
|-------|-----|
| Optimize CycleCloud clusters on HB/HC series VMs | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/hb-hc-best-practices?view=cyclecloud-8 |

### Decision Making
| Topic | URL |
|-------|-----|
| Plan and size Azure CycleCloud HPC clusters | https://learn.microsoft.com/en-us/azure/cyclecloud/concepts/plan-and-size-hpc-clusters?view=cyclecloud-8 |
| Plan CycleCloud Workspace for Slurm deployment | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/ccws/plan-your-deployment?view=cyclecloud-8 |
| Plan migration for Azure CycleCloud 7 retirement | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/cyclecloud7-retirement-guide?view=cyclecloud-8 |
| Decide when and how to use Spot VMs in Azure CycleCloud | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/use-spot-instances?view=cyclecloud-8 |
| Apply Azure CycleCloud licensing and usage terms | https://learn.microsoft.com/en-us/azure/cyclecloud/licensing?view=cyclecloud-8 |
| Understand Azure CycleCloud servicing policy | https://learn.microsoft.com/en-us/azure/cyclecloud/service-policy?view=cyclecloud-8 |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design and operate multi‑region Azure CycleCloud HPC clusters | https://learn.microsoft.com/en-us/azure/cyclecloud/concepts/multi-region-cluster-deployment?view=cyclecloud-8 |
| Choose VM placement models for CycleCloud clusters | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/availability-sets?view=cyclecloud-8 |

### Security
| Topic | URL |
|-------|-----|
| Apply security best practices for Azure CycleCloud | https://learn.microsoft.com/en-us/azure/cyclecloud/concepts/security-best-practices?view=cyclecloud-8 |
| Review CycleCloud telemetry and data usage policy | https://learn.microsoft.com/en-us/azure/cyclecloud/data-policy?view=cyclecloud-8 |
| Securely SSH to CycleCloud login nodes via Bastion | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/ccws/connect-to-login-node-with-bastion?view=cyclecloud-8 |
| Secure CycleCloud portal access through Azure Bastion | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/ccws/connect-to-portal-with-bastion?view=cyclecloud-8 |
| Create Entra app registration for Azure CycleCloud | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/create-app-registration?view=cyclecloud-8 |
| Use managed identities to secure Azure CycleCloud clusters | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/managed-identities?view=cyclecloud-8 |
| Run Azure CycleCloud nodes with SELinux enforcing | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/selinux?view=cyclecloud-8 |
| Configure Azure CycleCloud with Microsoft Entra service principals | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/service-principals?view=cyclecloud-8 |
| Configure SSL certificates for secure Azure CycleCloud access | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/ssl-configuration?view=cyclecloud-8 |
| Configure user authentication for Azure CycleCloud clusters | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/user-access?view=cyclecloud-8 |
| Configure user authentication methods for Azure CycleCloud | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/user-authentication?view=cyclecloud-8 |

### Configuration
| Topic | URL |
|-------|-----|
| Configure cluster-init specs and project sources in Azure CycleCloud | https://learn.microsoft.com/en-us/azure/cyclecloud/cluster-references/cluster-init-reference?view=cyclecloud-8 |
| Configure the cluster section in Azure CycleCloud templates | https://learn.microsoft.com/en-us/azure/cyclecloud/cluster-references/cluster-reference?view=cyclecloud-8 |
| Understand Azure CycleCloud cluster template structure and hierarchy | https://learn.microsoft.com/en-us/azure/cyclecloud/cluster-references/cluster-template-reference?view=cyclecloud-8 |
| Configure Azure CycleCloud cluster configuration objects | https://learn.microsoft.com/en-us/azure/cyclecloud/cluster-references/configuration-reference?view=cyclecloud-8 |
| Define environment objects in CycleCloud cluster templates | https://learn.microsoft.com/en-us/azure/cyclecloud/cluster-references/environment-reference?view=cyclecloud-8 |
| Configure input endpoints and ports in Azure CycleCloud templates | https://learn.microsoft.com/en-us/azure/cyclecloud/cluster-references/input-endpoint-reference?view=cyclecloud-8 |
| Configure network-interface objects in Azure CycleCloud templates | https://learn.microsoft.com/en-us/azure/cyclecloud/cluster-references/network-interface-reference?view=cyclecloud-8 |
| Configure nodes and nodearrays in Azure CycleCloud templates | https://learn.microsoft.com/en-us/azure/cyclecloud/cluster-references/node-nodearray-reference?view=cyclecloud-8 |
| Use NodeRef objects in CycleCloud cluster templates | https://learn.microsoft.com/en-us/azure/cyclecloud/cluster-references/noderef-reference?view=cyclecloud-8 |
| Configure parameters in Azure CycleCloud cluster templates | https://learn.microsoft.com/en-us/azure/cyclecloud/cluster-references/parameter-reference?view=cyclecloud-8 |
| Apply special parameter parsing in Azure CycleCloud | https://learn.microsoft.com/en-us/azure/cyclecloud/cluster-references/special-parsing?view=cyclecloud-8 |
| Define and configure volume objects in Azure CycleCloud templates | https://learn.microsoft.com/en-us/azure/cyclecloud/cluster-references/volume-reference?view=cyclecloud-8 |
| Configure Azure CycleCloud service monitoring integrations | https://learn.microsoft.com/en-us/azure/cyclecloud/concepts/monitoring?view=cyclecloud-8 |
| Configure CycleServer via cycle_server.properties | https://learn.microsoft.com/en-us/azure/cyclecloud/cycleserver-configuration-reference?view=cyclecloud-8 |
| Configure CycleCloud node events and Event Grid | https://learn.microsoft.com/en-us/azure/cyclecloud/events?view=cyclecloud-8 |
| Configure Azure managed disks in CycleCloud nodes | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/add-disk?view=cyclecloud-8 |
| Configure node arrays for Azure CycleCloud clusters | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/add-node-array?view=cyclecloud-8 |
| Configure backup and restore for Azure CycleCloud | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/backup-and-restore?view=cyclecloud-8 |
| Configure Slurm cloud bursting with Azure CycleCloud | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/bursting/slurm-cloud-bursting-setup?view=cyclecloud-8 |
| Use cloud-init to customize CycleCloud VMs on boot | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/cloud-init?view=cyclecloud-8 |
| Define and customize Azure CycleCloud cluster templates | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/cluster-templates?view=cyclecloud-8 |
| Configure Azure networking for CycleCloud deployments | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/configuration?view=cyclecloud-8 |
| Configure autoscaling for Azure CycleCloud clusters | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/configure-autoscaling?view=cyclecloud-8 |
| Use custom and marketplace images in CycleCloud clusters | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/create-custom-image?view=cyclecloud-8 |
| Create and export NFS file shares in CycleCloud | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/create-fileserver?view=cyclecloud-8 |
| Configure Azure CycleCloud environment resources via ARM | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/environments?view=cyclecloud-8 |
| Configure Flex VM scale sets in Azure CycleCloud | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/flex-scalesets?view=cyclecloud-8 |
| Install and configure the Azure CycleCloud CLI | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/install-cyclecloud-cli?view=cyclecloud-8 |
| Manually install Jetpack on CycleCloud-managed VMs | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/install-jetpack?view=cyclecloud-8 |
| Manually install and configure Azure CycleCloud | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/install-manual?view=cyclecloud-8 |
| Configure keep-alive settings for Azure CycleCloud nodes | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/keep-alive?view=cyclecloud-8 |
| Configure alerts and logging for Azure CycleCloud clusters | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/monitor-clusters?view=cyclecloud-8 |
| Configure volume mountpoints in Azure CycleCloud templates | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/mount-disk?view=cyclecloud-8 |
| Configure NFS mounts and shares in Azure CycleCloud | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/mount-fileserver?view=cyclecloud-8 |
| Configure multiple Azure CycleCloud instances on one host | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/multiple-installs?view=cyclecloud-8 |
| Customize network security settings for Azure CycleCloud nodes | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/network-security?view=cyclecloud-8 |
| Define and use projects and specs in Azure CycleCloud | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/projects?view=cyclecloud-8 |
| Configure return proxy nodes for Azure CycleCloud clusters | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/return-proxy?view=cyclecloud-8 |
| Configure web proxy settings for Azure CycleCloud traffic | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/running-behind-proxy?view=cyclecloud-8 |
| Run Azure CycleCloud in locked-down network environments | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/running-in-locked-down-network?view=cyclecloud-8 |
| Configure Azure Scheduled Events handling in CycleCloud nodes | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/scheduled-events?view=cyclecloud-8 |
| Configure project and user blob storage in Azure CycleCloud | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/storage-blobs?view=cyclecloud-8 |
| Use and understand Azure CycleCloud node tagging | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/tag-nodes?view=cyclecloud-8 |
| Customize Azure CycleCloud UI theming with CSS | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/theming?view=cyclecloud-8 |
| Configure CycleCloud nodes with Jetpack | https://learn.microsoft.com/en-us/azure/cyclecloud/jetpack?view=cyclecloud-8 |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use Azure CycleCloud REST API endpoints | https://learn.microsoft.com/en-us/azure/cyclecloud/api?view=cyclecloud-8 |
| Manage Azure CycleCloud with CLI commands | https://learn.microsoft.com/en-us/azure/cyclecloud/cli?view=cyclecloud-8 |
| Author Chef cookbooks for CycleCloud clusters | https://learn.microsoft.com/en-us/azure/cyclecloud/cookbook-reference?view=cyclecloud-8 |
| Configure Grid Engine clusters in CycleCloud | https://learn.microsoft.com/en-us/azure/cyclecloud/gridengine?view=cyclecloud-8 |
| Configure Open OnDemand with CycleCloud Slurm clusters | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/ccws/configure-open-ondemand?view=cyclecloud-8 |
| Submit and manage Slurm jobs on Azure CycleCloud | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/ccws/submit-job-with-slurm?view=cyclecloud-8 |
| Integrate Azure CycleCloud events with Event Grid | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/event-grid?view=cyclecloud-8 |
| Integrate Prometheus and Azure Managed Grafana with CycleCloud clusters | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/monitor-cyclecloud-cluster-using-prometheus-grafana?view=cyclecloud-8 |
| Use the Azure CycleCloud REST API for automated cluster management | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/use-rest-api?view=cyclecloud-8 |
| Configure Microsoft HPC Pack with CycleCloud | https://learn.microsoft.com/en-us/azure/cyclecloud/hpcpack?view=cyclecloud-8 |
| Integrate HTCondor scheduler with CycleCloud | https://learn.microsoft.com/en-us/azure/cyclecloud/htcondor?view=cyclecloud-8 |
| Connect IBM Spectrum LSF to CycleCloud | https://learn.microsoft.com/en-us/azure/cyclecloud/lsf?view=cyclecloud-8 |
| Integrate OpenPBS scheduler with CycleCloud | https://learn.microsoft.com/en-us/azure/cyclecloud/openpbs?view=cyclecloud-8 |
| Install and use CycleCloud Python API | https://learn.microsoft.com/en-us/azure/cyclecloud/python-api?view=cyclecloud-8 |
| Configure CycleCloud Slurm integration v3.0+ | https://learn.microsoft.com/en-us/azure/cyclecloud/slurm-3?view=cyclecloud-8 |
| Enable Slurm scheduler on CycleCloud clusters | https://learn.microsoft.com/en-us/azure/cyclecloud/slurm?view=cyclecloud-8 |

### Deployment
| Topic | URL |
|-------|-----|
| Download and import CycleCloud cluster templates | https://learn.microsoft.com/en-us/azure/cyclecloud/download-cluster-templates?view=cyclecloud-8 |
| Deploy CycleCloud Workspace for Slurm using CLI | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/ccws/deploy-with-cli?view=cyclecloud-8 |
| Deploy Azure CycleCloud using ARM templates | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/install-arm?view=cyclecloud-8 |
| Move Azure CycleCloud cluster resources between resource groups | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/move-resource-group?view=cyclecloud-8 |
| Plan a production-grade Azure CycleCloud deployment | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/plan-prod-deployment?view=cyclecloud-8 |
| Run Azure CycleCloud in Azure Container Instances | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/run-in-container?view=cyclecloud-8 |
| Upgrade or migrate Azure CycleCloud installations safely | https://learn.microsoft.com/en-us/azure/cyclecloud/how-to/upgrade-and-migrate?view=cyclecloud-8 |