---
name: azure-confidential-ledger
description: Expert knowledge for Azure Confidential Ledger development including troubleshooting, decision making, security, integrations & coding patterns, and deployment. Use when configuring ACL auth/attestation, integrating with Blob/Cosmos, using MST payloads, or deploying via ARM/Terraform, and other Azure Confidential Ledger related development tasks. Not for Azure Confidential Computing (use azure-confidential-computing), Azure Key Vault (use azure-key-vault), Azure Dedicated HSM (use azure-dedicated-hsm), Azure Payment Hsm (use azure-payment-hsm).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Confidential Ledger Skill

This skill provides expert guidance for Azure Confidential Ledger. Covers troubleshooting, decision making, security, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L33-L38 | Diagnosing and resolving Microsoft Signing Transparency (MST) ledger verification issues, plus steps to verify ledger integrity and inspect individual ledger entries. |
| Decision Making | L39-L44 | Choosing between ACL Explorer tools for viewing/querying ledgers, and guidance on migrating applications and data from Managed CCF to Azure Confidential Ledger |
| Security | L45-L57 | Auth, attestation, identity, and access control for Confidential Ledger: Entra ID setup, app registration, RBAC, cert-based users, client certs, node quote verification, and deployment security. |
| Integrations & Coding Patterns | L58-L67 | Patterns and examples for integrating ACL with Blob Storage, Power Automate, Cosmos DB, organizing ledger data, designing MST payloads/claims, and writing JavaScript user-defined functions. |
| Deployment | L68-L72 | How to deploy and provision Azure Confidential Ledger instances using ARM templates or Terraform, including required parameters and configuration steps. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Microsoft’s Signing Transparency Ledger verification issues | https://learn.microsoft.com/en-us/azure/confidential-ledger/microsoft-signing-transparency-troubleshoot |
| Verify MST ledger integrity and inspect entries | https://learn.microsoft.com/en-us/azure/confidential-ledger/microsoft-signing-transparency-verify-signatures |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose between Azure Confidential Ledger Explorer tools | https://learn.microsoft.com/en-us/azure/confidential-ledger/ledger-explorer-concepts |
| Migrate from Managed CCF to Azure Confidential Ledger | https://learn.microsoft.com/en-us/azure/confidential-ledger/managed-confidential-consortium-framework-migration |

### Security
| Topic | URL |
|-------|-----|
| Authenticate and attest Azure Confidential Ledger nodes securely | https://learn.microsoft.com/en-us/azure/confidential-ledger/authenticate-ledger-nodes |
| Configure Microsoft Entra authentication for Azure confidential ledger | https://learn.microsoft.com/en-us/azure/confidential-ledger/authentication-azure-ad |
| Create and configure client certificates for Confidential Ledger | https://learn.microsoft.com/en-us/azure/confidential-ledger/create-client-certificate |
| Manage Entra token-based users and roles in Confidential Ledger | https://learn.microsoft.com/en-us/azure/confidential-ledger/manage-azure-ad-token-based-users |
| Manage certificate-based users and roles in Confidential Ledger | https://learn.microsoft.com/en-us/azure/confidential-ledger/manage-certificate-based-users |
| Register Confidential Ledger applications in Microsoft Entra ID | https://learn.microsoft.com/en-us/azure/confidential-ledger/register-application |
| Secure Azure Confidential Ledger deployments and access | https://learn.microsoft.com/en-us/azure/confidential-ledger/secure-confidential-ledger |
| Implement advanced UDFs with RBAC in Confidential Ledger | https://learn.microsoft.com/en-us/azure/confidential-ledger/user-defined-endpoints |
| Verify node quotes and establish trust in Confidential Ledger | https://learn.microsoft.com/en-us/azure/confidential-ledger/verify-node-quotes |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate Blob Storage digests with Azure Confidential Ledger | https://learn.microsoft.com/en-us/azure/confidential-ledger/create-blob-managed-app |
| Integrate Azure confidential ledger with Power Automate and Cosmos DB | https://learn.microsoft.com/en-us/azure/confidential-ledger/create-power-automate-workflow |
| Organize and access data in Azure confidential ledger | https://learn.microsoft.com/en-us/azure/confidential-ledger/data-organization |
| Design MST payloads, claims, and auditing workflows | https://learn.microsoft.com/en-us/azure/confidential-ledger/microsoft-signing-transparency-usage |
| Run user-defined functions in Azure Confidential Ledger | https://learn.microsoft.com/en-us/azure/confidential-ledger/server-side-programming |
| Create simple JavaScript UDFs in Confidential Ledger | https://learn.microsoft.com/en-us/azure/confidential-ledger/user-defined-functions |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy Azure Confidential Ledger via ARM template | https://learn.microsoft.com/en-us/azure/confidential-ledger/quickstart-template |
| Provision Azure Confidential Ledger using Terraform | https://learn.microsoft.com/en-us/azure/confidential-ledger/quickstart-terraform |