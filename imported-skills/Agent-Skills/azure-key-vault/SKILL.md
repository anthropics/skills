---
name: azure-key-vault
description: Expert knowledge for Azure Key Vault development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when managing vault/HSM keys & secrets, RBAC vs policies, Private Link, BYOK/HSM transfer, or key rotation, and other Azure Key Vault related development tasks. Not for Azure Dedicated HSM (use azure-dedicated-hsm), Azure Cloud Hsm (use azure-cloud-hsm), Azure Payment Hsm (use azure-payment-hsm), Azure Attestation (use azure-attestation).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Key Vault Skill

This skill provides expert guidance for Azure Key Vault. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L46 | Diagnosing and fixing Key Vault errors: REST/API error codes, Private Link and access policy issues, Azure Policy enforcement, and Managed HSM external key management problems. |
| Best Practices | L47-L53 | Best practices for securing Key Vault keys, handling Managed HSM disaster recovery, and generating/importing BYOK HSM keys for compliant, resilient key management. |
| Decision Making | L54-L64 | Guidance on planning and migrating key workloads, choosing RBAC vs access policies, using and retiring Managed HSM external keys, SLA/responsibility tradeoffs, and capacity/scaling decisions. |
| Architecture & Design Patterns | L65-L70 | Architecture and workflows for using external key stores with Managed HSM, including key lifecycle management, integration patterns, and operational considerations. |
| Limits & Quotas | L71-L82 | Key Vault and Managed HSM limits, quotas, throttling, logging latency, certificate/secret size behaviors, soft-delete/recovery, and network/IP firewall configuration. |
| Security | L83-L110 | Securing Azure Key Vault and Managed HSM: auth/RBAC vs access policies, firewall/VNet/private endpoints, mTLS, soft delete, BYOK/HSM key transfer, backups, and security best practices. |
| Configuration | L111-L135 | Configuring Key Vault and Managed HSM: auth requests, policies, logging/monitoring, alerts, key/secret types, key import/rotation, release policies, replication, and soft-delete/purge protection. |
| Integrations & Coding Patterns | L136-L166 | Patterns for integrating Key Vault with apps and services (Event Grid, Logic Apps, Private Link, Databricks, DigiCert) and using keys/secrets from .NET, Node.js, Python, JavaScript, and Managed HSM. |
| Deployment | L167-L170 | How to deploy and provision Azure Key Vault and Managed HSM (vaults, keys, secrets) using ARM templates, Bicep, Terraform, Azure CLI, and PowerShell |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Resolve common Azure Key Vault error codes | https://learn.microsoft.com/en-us/azure/key-vault/general/common-error-codes |
| Diagnose and fix Azure Key Vault Private Link configuration issues | https://learn.microsoft.com/en-us/azure/key-vault/general/private-link-diagnostics |
| Interpret Azure Key Vault REST API error codes | https://learn.microsoft.com/en-us/azure/key-vault/general/rest-error-codes |
| Troubleshoot Azure Policy enforcement on Key Vault | https://learn.microsoft.com/en-us/azure/key-vault/general/troubleshoot-azure-policy-for-key-vault |
| Troubleshoot Azure Key Vault access policy failures | https://learn.microsoft.com/en-us/azure/key-vault/general/troubleshooting-access-issues |
| Troubleshoot Managed HSM external key management issues | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/external-key-management-troubleshooting |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply security best practices for Azure Key Vault keys | https://learn.microsoft.com/en-us/azure/key-vault/keys/secure-keys |
| Execute disaster recovery for Azure Managed HSM disruptions | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/disaster-recovery-guide |
| Generate and import BYOK HSM keys into Azure Managed HSM | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/hsm-protected-keys-byok |

### Decision Making
| Topic | URL |
|-------|-----|
| Plan and execute migration of cryptographic key workloads | https://learn.microsoft.com/en-us/azure/key-vault/general/migrate-key-workloads |
| Migrate Azure Key Vault from access policies to RBAC | https://learn.microsoft.com/en-us/azure/key-vault/general/rbac-migration |
| Answer common questions on Managed HSM external keys | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/external-key-management-faq |
| Migrate workloads off Managed HSM external keys | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/external-key-management-migration |
| Decide when to use Managed HSM external key management | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/external-key-management-overview |
| Evaluate SLA and responsibilities for Managed HSM external keys | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/external-key-management-shared-responsibility |
| Plan capacity and scaling for Azure Managed HSM | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/scaling-guidance |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Understand Managed HSM external key management architecture | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/external-key-management-architecture |
| Manage external key lifecycle in Managed HSM | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/external-key-management-key-lifecycle |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Understand Azure Key Vault certificate limits and behaviors | https://learn.microsoft.com/en-us/azure/key-vault/certificates/faq |
| Configure and interpret Azure Key Vault logging latency | https://learn.microsoft.com/en-us/azure/key-vault/general/logging |
| Understand and handle Azure Key Vault throttling limits | https://learn.microsoft.com/en-us/azure/key-vault/general/overview-throttling |
| Review Azure Key Vault and Managed HSM service limits | https://learn.microsoft.com/en-us/azure/key-vault/general/service-limits |
| Configure Managed HSM IP firewall and network security | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/configure-network-security |
| Review Azure Managed HSM service limits and quotas | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/service-limits |
| Use soft-delete and recovery for Managed HSM resources | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/soft-delete-overview |
| Understand Azure Key Vault secret size limits | https://learn.microsoft.com/en-us/azure/key-vault/secrets/about-secrets |

### Security
| Topic | URL |
|-------|-----|
| Apply security best practices to Key Vault certificates | https://learn.microsoft.com/en-us/azure/key-vault/certificates/secure-certificates |
| Allow Azure Key Vault access from clients behind firewalls | https://learn.microsoft.com/en-us/azure/key-vault/general/access-behind-firewall |
| Prepare for Azure Key Vault RBAC default and API retirement | https://learn.microsoft.com/en-us/azure/key-vault/general/access-control-default |
| Configure Azure Key Vault access policies with CLI | https://learn.microsoft.com/en-us/azure/key-vault/general/assign-access-policy |
| Configure authentication to Azure Key Vault with Entra ID | https://learn.microsoft.com/en-us/azure/key-vault/general/authentication |
| Configure network security options for Azure Key Vault | https://learn.microsoft.com/en-us/azure/key-vault/general/network-security |
| Restrict Azure Key Vault access with VNet service endpoints | https://learn.microsoft.com/en-us/azure/key-vault/general/overview-vnet-service-endpoints |
| Choose Azure RBAC vs access policies for Key Vault | https://learn.microsoft.com/en-us/azure/key-vault/general/rbac-access-policy |
| Configure Azure RBAC permissions for Azure Key Vault | https://learn.microsoft.com/en-us/azure/key-vault/general/rbac-guide |
| Apply Zero Trust security practices to Azure Key Vault | https://learn.microsoft.com/en-us/azure/key-vault/general/secure-key-vault |
| Configure and use Azure Key Vault soft-delete safely | https://learn.microsoft.com/en-us/azure/key-vault/general/soft-delete-overview |
| Generate and transfer HSM-protected keys to Key Vault | https://learn.microsoft.com/en-us/azure/key-vault/keys/hsm-protected-keys |
| Implement BYOK HSM key transfer for Azure Key Vault | https://learn.microsoft.com/en-us/azure/key-vault/keys/hsm-protected-keys-byok |
| Configure access control for Azure Key Vault Managed HSM | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/access-control |
| Configure ARM access for Managed HSM key management | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/authorize-azure-resource-manager |
| Perform full and selective backup/restore for Azure Managed HSM | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/backup-restore |
| Use Managed HSM built-in local RBAC roles | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/built-in-roles |
| Configure networking and mTLS for Managed HSM external keys | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/external-key-management-networking |
| Implement secure access control for Azure Managed HSM | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/how-to-secure-access |
| Configure network security and firewall for Managed HSM | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/network-security |
| Configure Managed HSM private endpoints with Private Link | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/private-link |
| Manage data plane RBAC roles for Azure Managed HSM | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/role-management |
| Apply security best practices to Managed HSM deployments | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/secure-managed-hsm |
| Apply security best practices for Key Vault secrets | https://learn.microsoft.com/en-us/azure/key-vault/secrets/secure-secrets |

### Configuration
| Topic | URL |
|-------|-----|
| Configure health and throttling alerts for Azure Key Vault | https://learn.microsoft.com/en-us/azure/key-vault/general/alert |
| Formulate authenticated JSON requests to Azure Key Vault | https://learn.microsoft.com/en-us/azure/key-vault/general/authentication-requests-and-responses |
| Apply Azure Policy to govern Azure Key Vault | https://learn.microsoft.com/en-us/azure/key-vault/general/azure-policy |
| Enable and configure Azure Key Vault diagnostic logging | https://learn.microsoft.com/en-us/azure/key-vault/general/howto-logging |
| Configure monitoring for Azure Key Vault with Azure Monitor | https://learn.microsoft.com/en-us/azure/key-vault/general/monitor-key-vault |
| Reference for Azure Key Vault monitoring metrics and logs | https://learn.microsoft.com/en-us/azure/key-vault/general/monitor-key-vault-reference |
| Configure Azure Key Vault key types and algorithms | https://learn.microsoft.com/en-us/azure/key-vault/keys/about-keys-details |
| Follow BYOK specification for importing HSM keys to Key Vault | https://learn.microsoft.com/en-us/azure/key-vault/keys/byok-specification |
| Configure automatic cryptographic key rotation in Azure Key Vault | https://learn.microsoft.com/en-us/azure/key-vault/keys/how-to-configure-key-rotation |
| Author secure key release policies in Key Vault | https://learn.microsoft.com/en-us/azure/key-vault/keys/policy-grammar |
| Configure key types and algorithms in Managed HSM | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/about-keys-details |
| Configure health and performance alerts for Managed HSM | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/configure-alerts |
| Configure logging and monitoring for Managed HSM external keys | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/external-key-management-logging-monitoring |
| Configure automated key rotation in Azure Managed HSM | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/key-rotation |
| Configure logging and audit events for Azure Managed HSM | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/logging |
| Configure multi-region replication for Azure Managed HSM | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/multi-region-replication |
| Author secure key release policies for Managed HSM | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/policy-grammar |
| Configure soft-delete and purge protection for Managed HSM | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/recovery |
| Configure Azure Key Vault to store multiline secrets | https://learn.microsoft.com/en-us/azure/key-vault/secrets/multiline-secrets |
| Automate single-credential secret rotation in Key Vault | https://learn.microsoft.com/en-us/azure/key-vault/secrets/tutorial-rotation |
| Configure dual-credential secret rotation in Key Vault | https://learn.microsoft.com/en-us/azure/key-vault/secrets/tutorial-rotation-dual |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate Azure Key Vault with DigiCert CA | https://learn.microsoft.com/en-us/azure/key-vault/certificates/how-to-integrate-certificate-authority |
| Trigger Logic Apps from Key Vault events via Event Grid | https://learn.microsoft.com/en-us/azure/key-vault/general/event-grid-logicapps |
| Integrate Azure Key Vault events with Azure Event Grid | https://learn.microsoft.com/en-us/azure/key-vault/general/event-grid-overview |
| Handle Azure Key Vault notifications with Event Grid and Automation | https://learn.microsoft.com/en-us/azure/key-vault/general/event-grid-tutorial |
| Access Blob Storage via Databricks using Key Vault secrets | https://learn.microsoft.com/en-us/azure/key-vault/general/integrate-databricks-blob-storage |
| Integrate Azure Key Vault with Azure Private Link | https://learn.microsoft.com/en-us/azure/key-vault/general/private-link-service |
| Use Node.js on VMs to read secrets from Key Vault | https://learn.microsoft.com/en-us/azure/key-vault/general/tutorial-javascript-virtual-machine |
| Connect ASP.NET Core web apps to Azure Key Vault | https://learn.microsoft.com/en-us/azure/key-vault/general/tutorial-net-create-vault-azure-web-app |
| Integrate .NET VM apps with Azure Key Vault secrets | https://learn.microsoft.com/en-us/azure/key-vault/general/tutorial-net-virtual-machine |
| Access Azure Key Vault from Python on virtual machines | https://learn.microsoft.com/en-us/azure/key-vault/general/tutorial-python-virtual-machine |
| Back up, delete, and restore keys in JavaScript | https://learn.microsoft.com/en-us/azure/key-vault/keys/javascript-developer-guide-backup-delete-restore-key |
| Create and rotate Key Vault keys in JavaScript | https://learn.microsoft.com/en-us/azure/key-vault/keys/javascript-developer-guide-create-update-rotate-key |
| Enable or disable Key Vault keys in JavaScript | https://learn.microsoft.com/en-us/azure/key-vault/keys/javascript-developer-guide-enable-disable-key |
| Encrypt and decrypt with Key Vault keys in JavaScript | https://learn.microsoft.com/en-us/azure/key-vault/keys/javascript-developer-guide-encrypt-decrypt-key |
| Retrieve Azure Key Vault keys in JavaScript | https://learn.microsoft.com/en-us/azure/key-vault/keys/javascript-developer-guide-get-key |
| Import keys into Azure Key Vault with JavaScript | https://learn.microsoft.com/en-us/azure/key-vault/keys/javascript-developer-guide-import-key |
| List Azure Key Vault keys using JavaScript | https://learn.microsoft.com/en-us/azure/key-vault/keys/javascript-developer-guide-list-key-version |
| Sign and verify with Key Vault keys in JavaScript | https://learn.microsoft.com/en-us/azure/key-vault/keys/javascript-developer-guide-sign-verify-key |
| Implement EKM Proxy API for Managed HSM external keys | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/external-key-management-proxy-api-reference |
| Create external keys with Managed HSM using Azure CLI | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/external-key-management-quickstart-cli |
| Create external keys with Managed HSM in Azure portal | https://learn.microsoft.com/en-us/azure/key-vault/managed-hsm/external-key-management-quickstart-portal |
| Back up and restore Key Vault secrets in JavaScript | https://learn.microsoft.com/en-us/azure/key-vault/secrets/javascript-developer-guide-backup-secrets |
| Delete and purge Key Vault secrets with JavaScript | https://learn.microsoft.com/en-us/azure/key-vault/secrets/javascript-developer-guide-delete-secret |
| Enable or disable Key Vault secrets using JavaScript | https://learn.microsoft.com/en-us/azure/key-vault/secrets/javascript-developer-guide-enable-disable-secret |
| Retrieve Azure Key Vault secrets with JavaScript | https://learn.microsoft.com/en-us/azure/key-vault/secrets/javascript-developer-guide-get-secret |
| Use Azure Key Vault secrets from JavaScript applications | https://learn.microsoft.com/en-us/azure/key-vault/secrets/javascript-developer-guide-get-started |
| Create, update, and rotate Key Vault secrets with JavaScript | https://learn.microsoft.com/en-us/azure/key-vault/secrets/javascript-developer-guide-set-update-rotate-secret |

### Deployment
| Topic | URL |
|-------|-----|
| Provision Key Vault and key using Terraform | https://learn.microsoft.com/en-us/azure/key-vault/keys/quick-create-terraform |