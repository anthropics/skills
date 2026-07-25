---
name: azure-data-science-vm
description: Expert knowledge for Azure Data Science Virtual Machines development including troubleshooting, decision making, architecture & design patterns, security, configuration, integrations & coding patterns, and deployment. Use when managing DSVM images/tools, IaC deployment (Bicep/ARM), Key Vault secrets, MLflow, or GPU/Jupyter issues, and other Azure Data Science Virtual Machines related development tasks. Not for Azure Virtual Machines (use azure-virtual-machines), Azure Machine Learning (use azure-machine-learning), Azure Databricks (use azure-databricks), Azure HDInsight (use azure-hdinsight).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-04-12"
  generator: "docs2skills/1.0.0"
---
# Azure Data Science Virtual Machines Skill

This skill provides expert guidance for Azure Data Science Virtual Machines. Covers troubleshooting, decision making, architecture & design patterns, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L35-L39 | Diagnosing and resolving common Azure Data Science VM issues, including VM creation, package/environment errors, Jupyter access, GPU/driver problems, and performance or connectivity failures. |
| Decision Making | L40-L44 | Guidance for upgrading Azure Data Science VMs from Ubuntu 18.04 to 20.04, including migration steps, compatibility considerations, and preserving tools/configurations. |
| Architecture & Design Patterns | L45-L50 | Designing scalable DSVM-based analytics environments, including architecture patterns, shared VM pools, team workflows, and resource management for data science teams. |
| Security | L51-L56 | Managing identities and credentials for Azure DSVMs, including shared identity setup, managed identities, and securing secrets with Azure Key Vault. |
| Configuration | L57-L69 | Details of all preinstalled tools, frameworks, languages, and images on Azure DSVMs, including ML/deep learning, data ingestion, dev/productivity tools, and release/version info. |
| Integrations & Coding Patterns | L70-L74 | Using MLflow on Azure DSVMs to track experiments, log metrics/artifacts, and integrate runs with Azure Machine Learning for centralized experiment management |
| Deployment | L75-L79 | How to deploy Azure Data Science VMs using infrastructure-as-code, including Bicep and ARM templates, parameters, and configuration best practices. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot known issues on Azure DSVM | https://learn.microsoft.com/en-us/azure/machine-learning/data-science-virtual-machine/reference-known-issues?view=azureml-api-2 |

### Decision Making
| Topic | URL |
|-------|-----|
| Migrate DSVM from Ubuntu 18.04 to 20.04 | https://learn.microsoft.com/en-us/azure/machine-learning/data-science-virtual-machine/ubuntu-upgrade?view=azureml-api-2 |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design team analytics environments with DSVM | https://learn.microsoft.com/en-us/azure/machine-learning/data-science-virtual-machine/dsvm-enterprise-overview?view=azureml-api-2 |
| Architect shared DSVM pools for analytics teams | https://learn.microsoft.com/en-us/azure/machine-learning/data-science-virtual-machine/dsvm-pools?view=azureml-api-2 |

### Security
| Topic | URL |
|-------|-----|
| Configure common identity for multiple DSVMs | https://learn.microsoft.com/en-us/azure/machine-learning/data-science-virtual-machine/dsvm-common-identity?view=azureml-api-2 |
| Secure DSVM credentials with managed identities and Key Vault | https://learn.microsoft.com/en-us/azure/machine-learning/data-science-virtual-machine/dsvm-secure-access-keys?view=azureml-api-2 |

### Configuration
| Topic | URL |
|-------|-----|
| Use preinstalled ML tools on Azure DSVM | https://learn.microsoft.com/en-us/azure/machine-learning/data-science-virtual-machine/dsvm-tools-data-science?view=azureml-api-2 |
| Check deep learning frameworks on Azure DSVM | https://learn.microsoft.com/en-us/azure/machine-learning/data-science-virtual-machine/dsvm-tools-deep-learning-frameworks?view=azureml-api-2 |
| Identify development tools available on DSVM | https://learn.microsoft.com/en-us/azure/machine-learning/data-science-virtual-machine/dsvm-tools-development?view=azureml-api-2 |
| Use data ingestion tools on Azure DSVM | https://learn.microsoft.com/en-us/azure/machine-learning/data-science-virtual-machine/dsvm-tools-ingestion?view=azureml-api-2 |
| Review programming languages preinstalled on DSVM | https://learn.microsoft.com/en-us/azure/machine-learning/data-science-virtual-machine/dsvm-tools-languages?view=azureml-api-2 |
| Leverage productivity tools on Azure DSVM | https://learn.microsoft.com/en-us/azure/machine-learning/data-science-virtual-machine/dsvm-tools-productivity?view=azureml-api-2 |
| Reference tools installed on Ubuntu DSVM | https://learn.microsoft.com/en-us/azure/machine-learning/data-science-virtual-machine/reference-ubuntu-vm?view=azureml-api-2 |
| Review Azure DSVM release changes and versions | https://learn.microsoft.com/en-us/azure/machine-learning/data-science-virtual-machine/release-notes?view=azureml-api-2 |
| Review preinstalled tools on Azure DSVM images | https://learn.microsoft.com/en-us/azure/machine-learning/data-science-virtual-machine/tools-included?view=azureml-api-2 |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Track DSVM experiments with MLflow and Azure ML | https://learn.microsoft.com/en-us/azure/machine-learning/data-science-virtual-machine/how-to-track-experiments?view=azureml-api-2 |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy Azure DSVM using Bicep templates | https://learn.microsoft.com/en-us/azure/machine-learning/data-science-virtual-machine/dsvm-tutorial-bicep?view=azureml-api-2 |
| Deploy Azure DSVM with ARM templates | https://learn.microsoft.com/en-us/azure/machine-learning/data-science-virtual-machine/dsvm-tutorial-resource-manager?view=azureml-api-2 |