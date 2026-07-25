---
name: azure-quantum
description: Expert knowledge for Azure Quantum development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when running Q# jobs on IonQ/Quantinuum/Rigetti, managing quotas, RBAC access, hybrid jobs, or resource estimation, and other Azure Quantum related development tasks. Not for Azure HDInsight (use azure-hdinsight), Azure Databricks (use azure-databricks), Azure Machine Learning (use azure-machine-learning), Azure Virtual Machines (use azure-virtual-machines).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Quantum Skill

This skill provides expert guidance for Azure Quantum. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L44 | Troubleshooting Azure Quantum provider issues: diagnosing job failures and support/escalation policies and limits for IonQ, Quantinuum, and Rigetti hardware on Azure Quantum. |
| Best Practices | L45-L49 | Tools and techniques for testing, debugging, and validating quantum programs with the Azure Quantum Development Kit (QDK), including simulators, logging, and troubleshooting. |
| Decision Making | L50-L56 | Guidance on Azure Quantum costs, provider pricing and regions, workspace migration, choosing Q# dev tools, and planning quantum-safe cryptography with the resource estimator. |
| Architecture & Design Patterns | L57-L61 | Guidance on designing hybrid quantum-classical workflows in Azure Quantum, including architecture options, orchestration patterns, and when to offload tasks to quantum hardware. |
| Limits & Quotas | L62-L68 | Managing Azure Quantum quotas, job/session limits, timeouts, and Rigetti-specific hardware constraints and target capabilities. |
| Security | L69-L79 | Managing secure access to Azure Quantum workspaces: RBAC and access control, bulk user assignment, ARM locks, managed identities, service principals, and secure handling of access keys. |
| Configuration | L80-L92 | Configuring Azure Quantum workspaces, QDK tools, simulators, and hardware targets, plus setting up and customizing Quantum Resource Estimator models and outputs. |
| Integrations & Coding Patterns | L93-L106 | Integrating quantum frameworks (Q#, OpenQASM, QIR, Qiskit, Cirq, Pulser) with Azure Quantum, configuring simulators/noise models, visualization, hybrid jobs, and resource estimation. |
| Deployment | L107-L111 | Deploying Azure Quantum workspaces with Bicep and running/submitting Q# quantum programs from VS Code to Azure Quantum backends |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Diagnose and resolve common Azure Quantum issues | https://learn.microsoft.com/en-us/azure/quantum/azure-quantum-common-issues |
| Support and escalation policy for IonQ on Azure Quantum | https://learn.microsoft.com/en-us/azure/quantum/provider-support-ionq |
| Support policy for Quantinuum on Azure Quantum | https://learn.microsoft.com/en-us/azure/quantum/provider-support-quantinuum |
| Support policy for Rigetti on Azure Quantum | https://learn.microsoft.com/en-us/azure/quantum/provider-support-rigetti |

### Best Practices
| Topic | URL |
|-------|-----|
| Test and debug quantum programs with QDK tools | https://learn.microsoft.com/en-us/azure/quantum/testing-debugging |

### Decision Making
| Topic | URL |
|-------|-----|
| Migrate Azure Quantum workspace data between regions | https://learn.microsoft.com/en-us/azure/quantum/migration-guide |
| Compare Azure Quantum provider pricing plans | https://learn.microsoft.com/en-us/azure/quantum/pricing |
| Check regional availability of Azure Quantum providers | https://learn.microsoft.com/en-us/azure/quantum/provider-global-availability |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Choose hybrid quantum computing architectures in Azure Quantum | https://learn.microsoft.com/en-us/azure/quantum/hybrid-computing-overview |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Review and manage Azure Quantum usage quotas | https://learn.microsoft.com/en-us/azure/quantum/azure-quantum-quotas |
| Manage Azure Quantum sessions and avoid timeouts | https://learn.microsoft.com/en-us/azure/quantum/how-to-work-with-sessions |
| Rigetti provider targets and hardware limits in Azure Quantum | https://learn.microsoft.com/en-us/azure/quantum/provider-rigetti |

### Security
| Topic | URL |
|-------|-----|
| Bulk assign Azure Quantum workspace access via CSV | https://learn.microsoft.com/en-us/azure/quantum/bulk-add-users-to-a-workspace |
| Protect Azure Quantum resources with ARM locks | https://learn.microsoft.com/en-us/azure/quantum/how-to-set-resource-locks |
| Share Azure Quantum workspace using RBAC roles | https://learn.microsoft.com/en-us/azure/quantum/how-to-share-access-quantum-workspace |
| Configure Azure Quantum workspace access control | https://learn.microsoft.com/en-us/azure/quantum/manage-workspace-access |
| Authenticate to Azure Quantum using managed identity | https://learn.microsoft.com/en-us/azure/quantum/optimization-authenticate-managed-identity |
| Authenticate to Azure Quantum using service principals | https://learn.microsoft.com/en-us/azure/quantum/optimization-authenticate-service-principal |
| Manage Azure Quantum workspace access keys securely | https://learn.microsoft.com/en-us/azure/quantum/security-manage-access-keys |

### Configuration
| Topic | URL |
|-------|-----|
| Configure Azure Quantum workspaces with Azure CLI | https://learn.microsoft.com/en-us/azure/quantum/how-to-manage-quantum-workspaces-with-the-azure-cli |
| Use the QDK neutral atom device visualizer | https://learn.microsoft.com/en-us/azure/quantum/how-to-use-neutral-atom-visualizer |
| Set up QDK VS Code extension and environment | https://learn.microsoft.com/en-us/azure/quantum/install-overview-qdk |
| Install and configure QDK quantum simulators | https://learn.microsoft.com/en-us/azure/quantum/install-qdk-quantum-simulators |
| Configure and use IonQ targets in Azure Quantum | https://learn.microsoft.com/en-us/azure/quantum/provider-ionq |
| Configure hardware architecture models for the Quantum resource estimator | https://learn.microsoft.com/en-us/azure/quantum/qre-build-architecture-models |
| Define error correction and magic state models for resource estimation | https://learn.microsoft.com/en-us/azure/quantum/qre-build-error-correction-models |
| Build custom application models for the Quantum resource estimator | https://learn.microsoft.com/en-us/azure/quantum/qre-custom-applications |
| Access and customize Quantum resource estimator output | https://learn.microsoft.com/en-us/azure/quantum/qre-estimation-results |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Connect to Azure Quantum workspace via qdk.azure | https://learn.microsoft.com/en-us/azure/quantum/how-to-connect-workspace |
| Visualize Q# and OpenQASM circuits with QDK | https://learn.microsoft.com/en-us/azure/quantum/how-to-visualize-circuits |
| Run integrated hybrid quantum jobs with Adaptive RI in Azure Quantum | https://learn.microsoft.com/en-us/azure/quantum/hybrid-computing-integrated |
| Configure neutral atom noise models with QDK Python APIs | https://learn.microsoft.com/en-us/azure/quantum/neutral-atom-noise-models |
| Run OpenQASM programs with Azure Quantum QDK | https://learn.microsoft.com/en-us/azure/quantum/qdk-openqasm-integration |
| Build and configure QDK simulator noise models in Python | https://learn.microsoft.com/en-us/azure/quantum/qdk-simulator-noise-models |
| Create application models from quantum frameworks for resource estimation | https://learn.microsoft.com/en-us/azure/quantum/qre-supported-applications |
| Submit Cirq circuits to Azure Quantum with QDK | https://learn.microsoft.com/en-us/azure/quantum/quickstart-microsoft-cirq |
| Submit QIR, OpenQASM, and Pulser circuits to Azure Quantum | https://learn.microsoft.com/en-us/azure/quantum/quickstart-microsoft-provider-format |
| Submit Qiskit circuits to Azure Quantum with QDK | https://learn.microsoft.com/en-us/azure/quantum/quickstart-microsoft-qiskit |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy Azure Quantum workspaces using Bicep templates | https://learn.microsoft.com/en-us/azure/quantum/how-to-manage-quantum-workspaces-using-bicep |
| Submit and run Q# programs on Azure Quantum from VS Code | https://learn.microsoft.com/en-us/azure/quantum/how-to-submit-jobs |