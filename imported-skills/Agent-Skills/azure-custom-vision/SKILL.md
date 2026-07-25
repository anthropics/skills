---
name: azure-custom-vision
description: Expert knowledge for Azure AI Custom Vision development including best practices, decision making, limits & quotas, security, integrations & coding patterns, and deployment. Use when exporting Custom Vision models, calling prediction APIs, using ONNX/TensorFlow, managing CMK/RBAC, or Smart Labeler, and other Azure AI Custom Vision related development tasks. Not for Azure AI Vision (use azure-ai-vision), Azure AI services (use microsoft-foundry-tools), Azure Machine Learning (use azure-machine-learning), Azure AI Foundry Local (use microsoft-foundry-local).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-21"
  generator: "docs2skills/1.0.0"
---
# Azure AI Custom Vision Skill

This skill provides expert guidance for Azure AI Custom Vision. Covers best practices, decision making, limits & quotas, security, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Best Practices | L34-L39 | Improving Custom Vision model quality with better data collection/labeling strategies and using Smart Labeler to speed and automate image annotation |
| Decision Making | L40-L45 | Guidance on selecting the best Custom Vision domain for your scenario and planning migrations from Custom Vision to other Azure or third‑party vision services. |
| Limits & Quotas | L46-L50 | Details on Custom Vision usage limits per pricing tier, including training/prediction quotas, project and image caps, and how limits affect model training and deployment. |
| Security | L51-L57 | Managing Custom Vision security: encryption with customer-managed keys, secure data handling/export/deletion, and configuring Azure RBAC roles and permissions. |
| Integrations & Coding Patterns | L58-L68 | Using Custom Vision models and APIs in apps: exporting via SDK, running ONNX/TensorFlow in Windows ML/Python, calling classification/detection APIs, and integrating with Azure Storage. |
| Deployment | L69-L73 | Deploying Custom Vision models: copying/backing up projects across regions and exporting models for offline, edge, and mobile (TensorFlow, ONNX, iOS/Android) use. |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply Custom Vision data strategies to improve models | https://learn.microsoft.com/en-us/azure/ai-services/custom-vision-service/getting-started-improving-your-classifier |
| Speed up Custom Vision labeling with Smart Labeler | https://learn.microsoft.com/en-us/azure/ai-services/custom-vision-service/suggested-tags |

### Decision Making
| Topic | URL |
|-------|-----|
| Plan migration from Custom Vision to alternative services | https://learn.microsoft.com/en-us/azure/ai-services/custom-vision-service/migration-options |
| Choose the right Custom Vision domain for your project | https://learn.microsoft.com/en-us/azure/ai-services/custom-vision-service/select-domain |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Review Custom Vision limits and quotas by tier | https://learn.microsoft.com/en-us/azure/ai-services/custom-vision-service/limits-and-quotas |

### Security
| Topic | URL |
|-------|-----|
| Configure customer-managed keys for Custom Vision encryption | https://learn.microsoft.com/en-us/azure/ai-services/custom-vision-service/encrypt-data-at-rest |
| View, export, and delete Custom Vision data securely | https://learn.microsoft.com/en-us/azure/ai-services/custom-vision-service/export-delete-data |
| Configure Azure RBAC roles for Custom Vision projects | https://learn.microsoft.com/en-us/azure/ai-services/custom-vision-service/role-based-access-control |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate Custom Vision ONNX models with Windows ML apps | https://learn.microsoft.com/en-us/azure/ai-services/custom-vision-service/custom-vision-onnx-windows-ml |
| Run exported Custom Vision TensorFlow models in Python | https://learn.microsoft.com/en-us/azure/ai-services/custom-vision-service/export-model-python |
| Export Custom Vision models programmatically with SDK | https://learn.microsoft.com/en-us/azure/ai-services/custom-vision-service/export-programmatically |
| Use Custom Vision SDK for image classification | https://learn.microsoft.com/en-us/azure/ai-services/custom-vision-service/quickstarts/image-classification |
| Call Custom Vision object detection APIs with SDK | https://learn.microsoft.com/en-us/azure/ai-services/custom-vision-service/quickstarts/object-detection |
| Integrate Custom Vision with Azure Storage queues and blobs | https://learn.microsoft.com/en-us/azure/ai-services/custom-vision-service/storage-integration |
| Use Custom Vision prediction API to test images | https://learn.microsoft.com/en-us/azure/ai-services/custom-vision-service/use-prediction-api |

### Deployment
| Topic | URL |
|-------|-----|
| Copy and back up Custom Vision projects across regions | https://learn.microsoft.com/en-us/azure/ai-services/custom-vision-service/copy-move-projects |
| Export Custom Vision models for offline and mobile use | https://learn.microsoft.com/en-us/azure/ai-services/custom-vision-service/export-your-model |