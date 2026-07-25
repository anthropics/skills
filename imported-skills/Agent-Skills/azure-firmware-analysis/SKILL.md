---
name: azure-firmware-analysis
description: Expert knowledge for Azure Firmware Analysis development including best practices, security, integrations & coding patterns, and deployment. Use when configuring RBAC access, deploying workspaces via ARM/Bicep/Terraform, or automating firmware uploads via CLI/PowerShell/Python, and other Azure Firmware Analysis related development tasks. Not for Azure Defender For Iot (use azure-defender-for-iot), Azure IoT Edge (use azure-iot-edge), Azure IoT Hub (use azure-iot-hub), Azure Confidential Computing (use azure-confidential-computing).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Firmware Analysis Skill

This skill provides expert guidance for Azure Firmware Analysis. Covers best practices, security, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Best Practices | L32-L38 | Guidance on running Azure firmware analysis, reading SBOM extractor paths, and interpreting/prioritizing detected firmware vulnerabilities and weaknesses. |
| Security | L39-L44 | Managing secure access to Azure Firmware Analysis using service principals and configuring role-based access control (RBAC) permissions for users and apps |
| Integrations & Coding Patterns | L45-L51 | How to programmatically upload firmware for analysis in Azure using CLI, PowerShell, or Python, including auth, commands/scripts, and basic automation patterns. |
| Deployment | L52-L57 | How to provision and deploy an Azure Firmware Analysis workspace using infrastructure-as-code tools: ARM templates, Bicep, and Terraform configuration and setup. |

### Best Practices
| Topic | URL |
|-------|-----|
| Interpret SBOM extractor paths in firmware analysis | https://learn.microsoft.com/en-us/azure/firmware-analysis/interpreting-extractor-paths |
| Analyze firmware images with Azure firmware analysis | https://learn.microsoft.com/en-us/azure/firmware-analysis/tutorial-analyze-firmware |
| Interpret and prioritize firmware weaknesses data | https://learn.microsoft.com/en-us/azure/firmware-analysis/understand-weaknesses-data |

### Security
| Topic | URL |
|-------|-----|
| Automate firmware analysis with service principals | https://learn.microsoft.com/en-us/azure/firmware-analysis/automate-firmware-analysis-service-principals |
| Configure RBAC access for Azure firmware analysis | https://learn.microsoft.com/en-us/azure/firmware-analysis/firmware-analysis-rbac |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Upload firmware to Azure analysis using CLI | https://learn.microsoft.com/en-us/azure/firmware-analysis/quickstart-upload-firmware-using-azure-command-line-interface |
| Upload firmware to Azure analysis with PowerShell | https://learn.microsoft.com/en-us/azure/firmware-analysis/quickstart-upload-firmware-using-powershell |
| Upload firmware to Azure analysis using Python | https://learn.microsoft.com/en-us/azure/firmware-analysis/quickstart-upload-firmware-using-python |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy firmware analysis workspace via ARM template | https://learn.microsoft.com/en-us/azure/firmware-analysis/quickstart-firmware-analysis-arm |
| Deploy firmware analysis workspace with Bicep | https://learn.microsoft.com/en-us/azure/firmware-analysis/quickstart-firmware-analysis-bicep |
| Provision firmware analysis workspace using Terraform | https://learn.microsoft.com/en-us/azure/firmware-analysis/quickstart-firmware-analysis-terraform |