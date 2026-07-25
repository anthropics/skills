---
name: azure-cloud-hsm
description: Expert knowledge for Azure Cloud Hsm development including troubleshooting, best practices, limits & quotas, security, and integrations & coding patterns. Use when configuring Cloud HSM auth/network, PKCS#11 cert storage, key lifecycle, quotas, or cluster sync issues, and other Azure Cloud Hsm related development tasks. Not for Azure Dedicated HSM (use azure-dedicated-hsm), Azure Payment Hsm (use azure-payment-hsm), Azure Key Vault (use azure-key-vault), Azure Attestation (use azure-attestation).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Cloud Hsm Skill

This skill provides expert guidance for Azure Cloud Hsm. Covers troubleshooting, best practices, limits & quotas, security, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L33-L38 | Diagnosing and fixing Azure Cloud HSM cluster issues, including user/key synchronization problems, common error codes, connectivity failures, and operational faults. |
| Best Practices | L39-L43 | Guidance on secure key lifecycle management, HSM partition/role design, access control, network and operational hardening, and compliance-oriented security practices for Azure Cloud HSM deployments. |
| Limits & Quotas | L44-L49 | Service capacity limits (objects, transactions), quotas, and which cryptographic algorithms and key sizes are supported by Azure Cloud HSM |
| Security | L50-L60 | Security setup for Cloud HSM: auth methods, compliance, network hardening, user management, and configuring/streaming operation logs to Event Hubs. |
| Integrations & Coding Patterns | L61-L65 | Using PKCS#11 with Azure Cloud HSM to store, access, and manage X.509 certificates, including configuring certificate storage and integration patterns for apps and services. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Fix user and key sync issues in Azure Cloud HSM clusters | https://learn.microsoft.com/en-us/azure/cloud-hsm/synchronize-users-keys |
| Troubleshoot common Azure Cloud HSM errors and issues | https://learn.microsoft.com/en-us/azure/cloud-hsm/troubleshoot |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply key management best practices in Cloud HSM | https://learn.microsoft.com/en-us/azure/cloud-hsm/key-management |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Review Azure Cloud HSM service object and transaction limits | https://learn.microsoft.com/en-us/azure/cloud-hsm/service-limits |
| Review supported algorithms and key sizes in Azure Cloud HSM | https://learn.microsoft.com/en-us/azure/cloud-hsm/supported-algorithms |

### Security
| Topic | URL |
|-------|-----|
| Configure authentication methods for Azure Cloud HSM | https://learn.microsoft.com/en-us/azure/cloud-hsm/authentication |
| Understand security, compliance, and usage for Azure Cloud HSM | https://learn.microsoft.com/en-us/azure/cloud-hsm/faq |
| Secure Azure Cloud HSM network with endpoints, DNS, and NSGs | https://learn.microsoft.com/en-us/azure/cloud-hsm/network-security |
| Apply security best practices to Azure Cloud HSM deployments | https://learn.microsoft.com/en-us/azure/cloud-hsm/secure-cloud-hsm |
| Route Azure Cloud HSM logs to Event Hubs | https://learn.microsoft.com/en-us/azure/cloud-hsm/tutorial-configure-event-hub |
| Configure and query Azure Cloud HSM operation logs | https://learn.microsoft.com/en-us/azure/cloud-hsm/tutorial-operation-event-logging |
| Implement secure user management in Azure Cloud HSM | https://learn.microsoft.com/en-us/azure/cloud-hsm/user-management |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use PKCS#11 API to manage certificates in Azure Cloud HSM | https://learn.microsoft.com/en-us/azure/cloud-hsm/pkcs-api-certificate-storage |
| Configure PKCS#11 certificate storage with Azure Cloud HSM | https://learn.microsoft.com/en-us/azure/cloud-hsm/tutorial-certificate-storage |