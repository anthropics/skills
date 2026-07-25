---
name: azure-nat-gateway
description: Expert knowledge for Azure NAT Gateway development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, and deployment. Use when sizing SNAT ports, configuring NAT Gateway V2, reading flow logs, scaling outbound IPs, or securing egress traffic, and other Azure NAT Gateway related development tasks. Not for Azure Load Balancer (use azure-load-balancer), Azure Virtual Network (use azure-virtual-network), Azure Virtual Network Manager (use azure-virtual-network-manager), Azure Virtual WAN (use azure-virtual-wan).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure NAT Gateway Skill

This skill provides expert guidance for Azure NAT Gateway. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L36-L40 | Diagnosing and fixing NAT Gateway issues: reading flow logs, resolving misconfigurations, connectivity failures with Azure services, and outbound internet connection problems. |
| Best Practices | L41-L45 | Guidance on reducing SNAT port exhaustion and optimizing outbound connectivity patterns when using Azure NAT Gateway. |
| Decision Making | L46-L52 | Guidance on when to use NAT Gateway Standard vs StandardV2, how to migrate between SKUs, and how to move existing outbound access patterns to NAT Gateway. |
| Architecture & Design Patterns | L53-L58 | Designing VNETs with NAT Gateway, choosing patterns for outbound connectivity, and scaling/combining NAT Gateway with Azure Firewall for secure, high-throughput egress traffic. |
| Limits & Quotas | L59-L63 | NAT Gateway limits, quotas, and behaviors: SNAT port allocation, connection scaling, IP/VM limits, per-subscription caps, and FAQs on throughput and high-connection scenarios. |
| Security | L64-L68 | Security best practices for NAT Gateway: hardening design, minimizing exposure, managing outbound IPs, monitoring traffic, and integrating with NSGs, firewalls, and other Azure security controls. |
| Configuration | L69-L77 | Configuring NAT Gateway V2 (IPs, deployment via ARM/Bicep/Terraform), plus monitoring setup: metrics, alerts, and flow logs for traffic and diagnostics |
| Deployment | L78-L82 | Guides for redeploying NAT Gateway after cross-region moves and migrating VM outbound traffic from public IPs to use NAT Gateway |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Monitor and troubleshoot with NAT Gateway flow logs | https://learn.microsoft.com/en-us/azure/nat-gateway/monitor-nat-gateway-flow-logs |

### Best Practices
| Topic | URL |
|-------|-----|
| Optimize SNAT usage with Azure NAT Gateway | https://learn.microsoft.com/en-us/azure/nat-gateway/nat-gateway-snat |

### Decision Making
| Topic | URL |
|-------|-----|
| Migrate Azure NAT Gateway from Standard to StandardV2 | https://learn.microsoft.com/en-us/azure/nat-gateway/nat-gateway-v2-migrate |
| Choose between Azure NAT Gateway Standard and StandardV2 SKUs | https://learn.microsoft.com/en-us/azure/nat-gateway/nat-sku |
| Migrate Azure outbound access to NAT Gateway | https://learn.microsoft.com/en-us/azure/nat-gateway/tutorial-migrate-outbound-nat |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design Azure virtual networks with NAT Gateway | https://learn.microsoft.com/en-us/azure/nat-gateway/nat-gateway-design |
| Scale outbound traffic with NAT Gateway and Azure Firewall | https://learn.microsoft.com/en-us/azure/nat-gateway/tutorial-hub-spoke-nat-firewall |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Azure NAT Gateway FAQ with limits and behaviors | https://learn.microsoft.com/en-us/azure/nat-gateway/faq |

### Security
| Topic | URL |
|-------|-----|
| Apply security best practices to Azure NAT Gateway | https://learn.microsoft.com/en-us/azure/nat-gateway/secure-nat-gateway |

### Configuration
| Topic | URL |
|-------|-----|
| Manage Azure NAT Gateway configuration and IPs | https://learn.microsoft.com/en-us/azure/nat-gateway/manage-nat-gateway |
| Reference for Azure NAT Gateway monitoring data | https://learn.microsoft.com/en-us/azure/nat-gateway/monitor-nat-gateway-reference |
| Enable and use StandardV2 NAT Gateway flow logs | https://learn.microsoft.com/en-us/azure/nat-gateway/nat-gateway-flow-logs |
| Configure metrics and alerts for Azure NAT Gateway | https://learn.microsoft.com/en-us/azure/nat-gateway/nat-metrics |
| Deploy NAT Gateway V2 using ARM, Bicep, or Terraform | https://learn.microsoft.com/en-us/azure/nat-gateway/quickstart-create-nat-gateway-v2-templates |

### Deployment
| Topic | URL |
|-------|-----|
| Redeploy NAT gateway after cross-region resource moves | https://learn.microsoft.com/en-us/azure/nat-gateway/region-move-nat-gateway |
| Move VM public IP outbound traffic to NAT Gateway | https://learn.microsoft.com/en-us/azure/nat-gateway/tutorial-migrate-ilip-nat |