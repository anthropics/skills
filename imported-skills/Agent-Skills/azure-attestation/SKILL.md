---
name: azure-attestation
description: Expert knowledge for Azure Attestation development including troubleshooting, best practices, security, configuration, and deployment. Use when validating attestation tokens, authoring policies, enforcing SGX/TPM baselines, or configuring private endpoints, and other Azure Attestation related development tasks. Not for Azure Confidential Computing (use azure-confidential-computing), Azure Virtual Enclaves (use azure-virtual-enclaves), Azure Dedicated HSM (use azure-dedicated-hsm), Azure Key Vault (use azure-key-vault).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Attestation Skill

This skill provides expert guidance for Azure Attestation. Covers troubleshooting, best practices, security, configuration, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L33-L37 | Diagnosing and fixing common Azure Attestation failures, error codes, policy/quote validation issues, configuration mistakes, and connectivity or runtime problems. |
| Best Practices | L38-L46 | Guidance on validating attestation tokens, writing secure attestation policies, and configuring/enforcing SGX and TPM attestation baselines using sample policies. |
| Security | L47-L52 | Using Azure Policy with Attestation, enforcing compliance, and best practices to harden, secure, and protect Azure Attestation deployments and configurations. |
| Configuration | L53-L69 | Configuring Azure Attestation policies (grammar, versions, claim rules), policy signer certs, and monitoring/logging via Azure Monitor, CLI, PowerShell, and log schema. |
| Deployment | L70-L73 | How to create and configure a private endpoint for Azure Attestation using PowerShell, including network setup and secure access to attestation resources. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot common Azure Attestation errors and issues | https://learn.microsoft.com/en-us/azure/attestation/troubleshoot-guide |

### Best Practices
| Topic | URL |
|-------|-----|
| Interpret and validate Azure Attestation tokens with examples | https://learn.microsoft.com/en-us/azure/attestation/attestation-token-examples |
| Author secure and correct Azure Attestation policies | https://learn.microsoft.com/en-us/azure/attestation/author-sign-policy |
| Configure custom TCB baseline enforcement for SGX attestation | https://learn.microsoft.com/en-us/azure/attestation/custom-tcb-baseline-enforcement |
| Use sample SGX attestation policies in Azure | https://learn.microsoft.com/en-us/azure/attestation/policy-examples |
| Use sample TPM attestation policies in Azure | https://learn.microsoft.com/en-us/azure/attestation/tpm-attestation-sample-policies |

### Security
| Topic | URL |
|-------|-----|
| Apply built-in Azure Policy definitions for Attestation | https://learn.microsoft.com/en-us/azure/attestation/policy-reference |
| Harden and secure Azure Attestation deployments | https://learn.microsoft.com/en-us/azure/attestation/secure-attestation |

### Configuration
| Topic | URL |
|-------|-----|
| Use Azure Attestation claim rule functions and operators | https://learn.microsoft.com/en-us/azure/attestation/claim-rule-functions |
| Use Azure Attestation claim rule grammar in policies | https://learn.microsoft.com/en-us/azure/attestation/claim-rule-grammar |
| Understand Azure Attestation claim sets and categories | https://learn.microsoft.com/en-us/azure/attestation/claim-sets |
| Enable diagnostic logging for Azure Attestation | https://learn.microsoft.com/en-us/azure/attestation/enable-logging |
| Reference for Azure Attestation monitoring and log schema | https://learn.microsoft.com/en-us/azure/attestation/logs-data-reference |
| Monitor Azure Attestation with Azure Monitor | https://learn.microsoft.com/en-us/azure/attestation/monitor-logs |
| Configure Azure Attestation policy signer certificates | https://learn.microsoft.com/en-us/azure/attestation/policy-signer-examples |
| Configure Azure Attestation policy language version 1.0 | https://learn.microsoft.com/en-us/azure/attestation/policy-version-1-0 |
| Configure Azure Attestation policy language version 1.1 | https://learn.microsoft.com/en-us/azure/attestation/policy-version-1-1 |
| Configure Azure Attestation policy language version 1.2 | https://learn.microsoft.com/en-us/azure/attestation/policy-version-1-2 |
| Set up Azure Attestation using Azure CLI | https://learn.microsoft.com/en-us/azure/attestation/quickstart-azure-cli |
| Configure Azure Attestation provider with PowerShell | https://learn.microsoft.com/en-us/azure/attestation/quickstart-powershell |
| Understand and use Azure Attestation log data | https://learn.microsoft.com/en-us/azure/attestation/view-logs |

### Deployment
| Topic | URL |
|-------|-----|
| Create Azure Attestation private endpoint with PowerShell | https://learn.microsoft.com/en-us/azure/attestation/private-endpoint-powershell |