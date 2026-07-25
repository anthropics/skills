---
name: azure-container-registry
description: Expert knowledge for Azure Container Registry development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when using ACR Tasks, geo-replication, connected registries, Defender scanning, or Kubernetes image pulls, and other Azure Container Registry related development tasks. Not for Azure Container Apps (use azure-container-apps), Azure Container Instances (use azure-container-instances), Azure Kubernetes Service (AKS) (use azure-kubernetes-service), Azure Red Hat OpenShift (use azure-redhat-openshift).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Container Registry Skill

This skill provides expert guidance for Azure Container Registry. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L52 | Diagnosing and fixing ACR issues: health checks, error codes, login/auth, network, performance, transfer, logs, artifact cache/streaming, Arc extension, and customer-managed keys. |
| Best Practices | L53-L60 | Best practices for ACR operations: managing public image dependencies, safe image deletion and storage cleanup, and robust image tagging/versioning strategies. |
| Decision Making | L61-L67 | Guidance on choosing ACR auth for Kubernetes, migrating image signing from Docker Content Trust to Notary, and planning/configuring geo-replication for multi-region registries. |
| Architecture & Design Patterns | L68-L73 | Patterns for ACR performance and governance: caching image pulls, geo-replication strategies, connected registries for edge/offline, and gated import workflows for public images. |
| Limits & Quotas | L74-L79 | Details on ACR SKUs (Basic/Standard/Premium) feature differences, performance and throughput limits, and how image storage capacity and quotas are calculated and enforced. |
| Security | L80-L118 | Securing ACR access: auth methods (Entra, managed identity, tokens), RBAC/ABAC, network/firewall/VNet rules, policy/compliance, encryption keys, image signing/verification, and Defender scanning. |
| Configuration | L119-L138 | Configuring ACR behavior: cache and wildcard rules, purge/locks/soft delete, retention and IPv6, tasks (YAML, timers, agent pools, patching), webhooks, and monitoring metrics/logs. |
| Integrations & Coding Patterns | L139-L155 | Integrating ACR with Kubernetes, ACI, GitHub Actions, Helm, ORAS, and ACR Transfer; configuring auth, caching, webhooks, and image signing/verification workflows. |
| Deployment | L156-L160 | Using ARM templates to automate ACR quick tasks and data transfer, and deploying/managing ACR connected registries via Azure Arc extension |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Run az acr check-health for quick ACR diagnostics | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-check-health |
| Troubleshoot common Azure Container Registry issues | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-faq |
| Interpret az acr check-health error codes and fixes | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-health-error-reference |
| View and manage Azure Container Registry task run logs | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-tasks-logs |
| Troubleshoot Azure Container Registry Transfer issues | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-transfer-troubleshooting |
| Troubleshoot Azure Container Registry network connectivity | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-troubleshoot-access |
| Troubleshoot ACR login, authentication, and authorization issues | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-troubleshoot-login-authn-authz |
| Troubleshoot Azure Container Registry performance problems | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-troubleshoot-performance |
| Troubleshoot Azure Container Registry artifact cache issues | https://learn.microsoft.com/en-us/azure/container-registry/troubleshoot-artifact-cache |
| Diagnose and fix Azure Container Registry artifact streaming issues | https://learn.microsoft.com/en-us/azure/container-registry/troubleshoot-artifact-streaming |
| Troubleshoot connected registry Arc extension issues | https://learn.microsoft.com/en-us/azure/container-registry/troubleshoot-connected-registry-arc |
| Troubleshoot customer-managed keys in Azure Container Registry | https://learn.microsoft.com/en-us/azure/container-registry/tutorial-troubleshoot-customer-managed-keys |

### Best Practices
| Topic | URL |
|-------|-----|
| Manage public image dependencies using ACR | https://learn.microsoft.com/en-us/azure/container-registry/buffer-gate-public-content |
| Follow operational best practices for Azure Container Registry | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-best-practices |
| Delete ACR images safely to manage registry storage | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-delete |
| Apply image tagging and versioning best practices in ACR | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-image-tag-version |

### Decision Making
| Topic | URL |
|-------|-----|
| Select Kubernetes authentication options for Azure Container Registry | https://learn.microsoft.com/en-us/azure/container-registry/authenticate-kubernetes-options |
| Migrate ACR signing from DCT to Notary Project | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-content-trust-deprecation |
| Plan and configure geo-replication for Azure Container Registry | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-geo-replication |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design and use connected registries with ACR | https://learn.microsoft.com/en-us/azure/container-registry/intro-connected-registry |
| Implement gated import workflow for public images in ACR | https://learn.microsoft.com/en-us/azure/container-registry/tasks-consume-public-content |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Compare Azure Container Registry SKU features and limits | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-skus |
| Review Azure Container Registry image storage limits | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-storage |

### Security
| Topic | URL |
|-------|-----|
| Allow trusted Azure services to access network-restricted ACR | https://learn.microsoft.com/en-us/azure/container-registry/allow-access-trusted-services |
| Enable anonymous pull access for Azure Container Registry | https://learn.microsoft.com/en-us/azure/container-registry/anonymous-pull-access |
| Configure cross-tenant AKS authentication to Azure Container Registry | https://learn.microsoft.com/en-us/azure/container-registry/authenticate-aks-cross-tenant |
| Restrict Azure Container Registry public access by IP rules | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-access-selected-networks |
| Use Microsoft Entra service principals to access ACR | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-auth-service-principal |
| Choose and configure authentication methods for Azure Container Registry | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-authentication |
| Configure managed identity authentication to Azure Container Registry | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-authentication-managed-identity |
| Use Azure Policy to audit ACR compliance | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-azure-policy |
| Configure Microsoft Entra Conditional Access policies for ACR | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-configure-conditional-access |
| Enable Docker Content Trust for Azure Container Registry | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-content-trust |
| Use dedicated data endpoints to secure ACR traffic | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-dedicated-data-endpoints |
| Control accepted Microsoft Entra auth scopes for ACR | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-disable-authentication-as-arm |
| Configure firewall rules for Azure Container Registry access | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-firewall-rules |
| Configure Azure ABAC repository permissions in Container Registry | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-rbac-abac-repository-permissions |
| Reference for Azure Container Registry built-in RBAC roles | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-rbac-built-in-roles-directory-reference |
| Assign and manage ACR RBAC built-in roles | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-rbac-built-in-roles-overview |
| Create and assign custom RBAC roles for Azure Container Registry | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-rbac-custom-roles |
| Use Azure Container Registry service tags for network rules | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-service-tag |
| Access Key Vault secrets from ACR Tasks via managed identity | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-tasks-authentication-key-vault |
| Configure managed identity for ACR Tasks | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-tasks-authentication-managed-identity |
| Use managed identity for cross-registry auth in ACR Tasks | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-tasks-cross-registry-authentication |
| Configure token-based repository permissions in Azure Container Registry | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-token-based-repository-permissions |
| Sign ACR images with CA certs via Key Vault | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-tutorial-sign-trusted-ca |
| Enforce AKS image signature verification with Ratify | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-tutorial-verify-with-ratify-aks |
| Restrict ACR access with virtual network service endpoints | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-vnet |
| Disable artifact export to prevent ACR data exfiltration | https://learn.microsoft.com/en-us/azure/container-registry/data-loss-prevention |
| Manage ACR Tasks network bypass policy with trusted services | https://learn.microsoft.com/en-us/azure/container-registry/manage-network-bypass-policy-for-tasks |
| Reference of built-in Azure Policy definitions for ACR | https://learn.microsoft.com/en-us/azure/container-registry/policy-reference |
| Configure client tokens to pull from connected registries | https://learn.microsoft.com/en-us/azure/container-registry/pull-images-from-connected-registry |
| Scan ACR images with Microsoft Defender for Cloud | https://learn.microsoft.com/en-us/azure/container-registry/scan-images-defender |
| Apply Azure Policy compliance controls to ACR | https://learn.microsoft.com/en-us/azure/container-registry/security-controls-policy |
| Secure connected registry Arc extension deployments | https://learn.microsoft.com/en-us/azure/container-registry/tutorial-connected-registry-arc |
| Configure customer-managed encryption keys for ACR | https://learn.microsoft.com/en-us/azure/container-registry/tutorial-customer-managed-keys |
| Enable customer-managed keys on Azure Container Registry | https://learn.microsoft.com/en-us/azure/container-registry/tutorial-enable-customer-managed-keys |
| Rotate and revoke customer-managed keys for ACR | https://learn.microsoft.com/en-us/azure/container-registry/tutorial-rotate-revoke-customer-managed-keys |

### Configuration
| Topic | URL |
|-------|-----|
| Configure artifact cache in ACR using Azure CLI | https://learn.microsoft.com/en-us/azure/container-registry/artifact-cache-cli |
| Configure and run acr purge for Azure Container Registry | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-auto-purge |
| Reference Azure Container Registry endpoint types and flags | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-endpoint-reference |
| Configure delete locks on ACR images and repositories | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-image-lock |
| Enable IPv6 dual-stack endpoints for Azure Container Registry | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-ipv6-dual-stack |
| Configure retention policy for Azure Container Registry | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-retention-policy |
| Configure and use ACR soft delete retention policy | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-soft-delete-policy |
| Use multi-step ACR Tasks to build, test, and patch images | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-tasks-multi-step |
| YAML schema reference for Azure Container Registry Tasks | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-tasks-reference-yaml |
| Schedule Azure Container Registry Tasks with timers | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-tasks-scheduled |
| Configure multi-step ACR Tasks for build workflows | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-tutorial-multistep-task |
| Webhook payload schema for Azure Container Registry events | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-webhook-reference |
| Configure continuous patching for Azure Container Registry | https://learn.microsoft.com/en-us/azure/container-registry/how-to-continuous-patching |
| Monitoring metrics and logs reference for Azure Container Registry | https://learn.microsoft.com/en-us/azure/container-registry/monitor-container-registry-reference |
| Configure dedicated agent pools for ACR Tasks | https://learn.microsoft.com/en-us/azure/container-registry/tasks-agent-pools |
| Configure wildcard rules for ACR artifact cache | https://learn.microsoft.com/en-us/azure/container-registry/wildcards-artifact-cache |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Configure ACR-to-ACR artifact caching with managed identity | https://learn.microsoft.com/en-us/azure/container-registry/artifact-cache-acr-to-acr-cli |
| Grant Azure Container Instances access to ACR with service principals | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-auth-aci |
| Create Kubernetes pull secrets for Azure Container Registry access | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-auth-kubernetes |
| Host and manage Helm chart repositories in ACR | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-helm-repos |
| Manage OCI and supply chain artifacts in ACR with ORAS | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-manage-artifact |
| Build images with Buildpacks using az acr pack build | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-tasks-pack-build |
| Automate ACR Transfer using ARM templates | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-transfer-arm-template |
| Use ACR Transfer with Azure CLI extension | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-transfer-cli |
| Build, push, and sign ACR images in GitHub Actions with Notation | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-tutorial-github-sign-notation-artifact-signing |
| Verify signed ACR images in GitHub Actions workflows | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-tutorial-github-verify-notation-artifact-signing |
| Sign ACR images with Notation using Azure Key Vault certificates | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-tutorial-sign-build-push |
| Sign and verify ACR images using Notation and Artifact Signing | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-tutorial-sign-verify-notation-artifact-signing |
| Configure ACR webhooks for registry event notifications | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-webhook |

### Deployment
| Topic | URL |
|-------|-----|
| Queue ACR quick task runs with ARM templates | https://learn.microsoft.com/en-us/azure/container-registry/container-registry-task-run-template |
| Deploy the ACR connected registry Arc extension | https://learn.microsoft.com/en-us/azure/container-registry/quickstart-connected-registry-arc-cli |