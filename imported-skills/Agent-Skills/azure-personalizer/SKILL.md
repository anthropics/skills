---
name: azure-personalizer
description: Expert knowledge for Azure AI Personalizer development including troubleshooting, decision making, security, configuration, and integrations & coding patterns. Use when choosing single vs multi-slot, tuning exploration policies, configuring CMK encryption, debugging low rewards, or using local inference SDK, and other Azure AI Personalizer related development tasks. Not for Azure AI Metrics Advisor (use azure-metrics-advisor), Azure AI Anomaly Detector (use azure-anomaly-detector), Azure Machine Learning (use azure-machine-learning).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-07"
  generator: "docs2skills/1.0.0"
---
# Azure AI Personalizer Skill

This skill provides expert guidance for Azure AI Personalizer. Covers troubleshooting, decision making, security, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L33-L37 | Diagnosing and fixing common Azure Personalizer problems: configuration and training issues, API/latency errors, low reward performance, and steps to debug and resolve service failures. |
| Decision Making | L38-L42 | Guidance on when to use single-slot vs multi-slot Personalizer, comparing scenarios, behavior, and design tradeoffs for different personalization needs. |
| Security | L43-L48 | Configuring encryption at rest (including customer-managed keys) and controlling data collection, storage, and privacy settings for Azure Personalizer. |
| Configuration | L49-L56 | Configuring Personalizer’s learning behavior: policies, hyperparameters, exploration, apprentice mode, explainability, model export, and learning loop settings. |
| Integrations & Coding Patterns | L57-L60 | Using the Personalizer local inference SDK for low-latency, offline/edge scenarios, including setup, integration patterns, and best practices for calling the model locally. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Diagnose and resolve common Azure Personalizer issues | https://learn.microsoft.com/en-us/azure/ai-services/personalizer/frequently-asked-questions |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose between single-slot and multi-slot Personalizer | https://learn.microsoft.com/en-us/azure/ai-services/personalizer/concept-multi-slot-personalization |

### Security
| Topic | URL |
|-------|-----|
| Configure data-at-rest encryption and CMK for Personalizer | https://learn.microsoft.com/en-us/azure/ai-services/personalizer/encrypt-data-at-rest |
| Manage data usage and privacy in Personalizer | https://learn.microsoft.com/en-us/azure/ai-services/personalizer/responsible-data-and-privacy |

### Configuration
| Topic | URL |
|-------|-----|
| Enable and use inference explainability in Personalizer | https://learn.microsoft.com/en-us/azure/ai-services/personalizer/how-to-inference-explainability |
| Configure apprentice mode learning behavior in Personalizer | https://learn.microsoft.com/en-us/azure/ai-services/personalizer/how-to-learning-behavior |
| Export and manage Personalizer model and learning settings | https://learn.microsoft.com/en-us/azure/ai-services/personalizer/how-to-manage-model |
| Configure Azure Personalizer learning loop settings | https://learn.microsoft.com/en-us/azure/ai-services/personalizer/how-to-settings |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use Personalizer local inference SDK for low latency | https://learn.microsoft.com/en-us/azure/ai-services/personalizer/how-to-thick-client |