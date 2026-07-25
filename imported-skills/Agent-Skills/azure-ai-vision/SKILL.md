---
name: azure-ai-vision
description: Expert knowledge for Azure AI Vision development including decision making, limits & quotas, configuration, integrations & coding patterns, and deployment. Use when using Image Analysis, Read OCR containers, smart-crop thumbnails, background removal, or video frame analysis, and other Azure AI Vision related development tasks. Not for Azure AI Custom Vision (use azure-custom-vision), Azure AI Video Indexer (use azure-video-indexer), Azure AI Document Intelligence (use azure-document-intelligence), Azure AI Immersive Reader (use azure-immersive-reader).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-21"
  generator: "docs2skills/1.0.0"
---
# Azure AI Vision Skill

This skill provides expert guidance for Azure AI Vision. Covers decision making, limits & quotas, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Decision Making | L33-L39 | Guidance on migrating and upgrading Azure Vision Image Analysis and Read OCR apps/containers, including choosing migration paths and moving from v2.x to v3.x APIs. |
| Limits & Quotas | L40-L50 | Limits, thresholds, and taxonomies for Image Analysis: category lists, adult content scores, object/people detection constraints, smart-crop behavior, and OCR language support. |
| Configuration | L51-L56 | Configuring Vision Read OCR containers and setting up Azure Blob Storage access for image input, including environment settings, storage permissions, and connection details. |
| Integrations & Coding Patterns | L57-L67 | How to call and configure Azure Vision/Read APIs and SDKs for OCR, embeddings, thumbnails, background removal, domain models, and live video frame analysis. |
| Deployment | L68-L71 | Installing, configuring, and running the Azure AI Vision Read OCR container locally or on-premises, including prerequisites, deployment steps, and runtime settings. |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose migration path from Azure Vision Image Analysis | https://learn.microsoft.com/en-us/azure/ai-services/computer-vision/migration-options |
| Migrate to Azure Vision Read OCR container v3.x | https://learn.microsoft.com/en-us/azure/ai-services/computer-vision/read-container-migration-guide |
| Upgrade applications from Read v2.x to v3.0 | https://learn.microsoft.com/en-us/azure/ai-services/computer-vision/upgrade-api-versions |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Reference taxonomy categories for Azure Vision | https://learn.microsoft.com/en-us/azure/ai-services/computer-vision/category-taxonomy |
| Understand Image Analysis 3.2 categorization taxonomy limits | https://learn.microsoft.com/en-us/azure/ai-services/computer-vision/concept-categorizing-images |
| Interpret adult content detection scores and thresholds | https://learn.microsoft.com/en-us/azure/ai-services/computer-vision/concept-detecting-adult-content |
| Use object detection and understand feature limits | https://learn.microsoft.com/en-us/azure/ai-services/computer-vision/concept-object-detection |
| Understand Image Analysis 4.0 object detection limits | https://learn.microsoft.com/en-us/azure/ai-services/computer-vision/concept-object-detection-40 |
| Use people detection and understand its limits | https://learn.microsoft.com/en-us/azure/ai-services/computer-vision/concept-people-detection |
| Check supported languages for Azure Vision OCR | https://learn.microsoft.com/en-us/azure/ai-services/computer-vision/language-support |

### Configuration
| Topic | URL |
|-------|-----|
| Configure Azure Vision Read OCR containers | https://learn.microsoft.com/en-us/azure/ai-services/computer-vision/computer-vision-resource-container-config |
| Configure Azure Blob Storage for Vision image retrieval | https://learn.microsoft.com/en-us/azure/ai-services/computer-vision/how-to/blob-storage-search |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Call domain-specific models with Azure Vision | https://learn.microsoft.com/en-us/azure/ai-services/computer-vision/concept-detecting-domain-content |
| Analyze live video frames with Azure Vision API | https://learn.microsoft.com/en-us/azure/ai-services/computer-vision/how-to/analyze-video |
| Call and configure Image Analysis 3.2 API | https://learn.microsoft.com/en-us/azure/ai-services/computer-vision/how-to/call-analyze-image |
| Call and configure Image Analysis 4.0 API | https://learn.microsoft.com/en-us/azure/ai-services/computer-vision/how-to/call-analyze-image-40 |
| Call and configure Azure Vision Read v3.2 API | https://learn.microsoft.com/en-us/azure/ai-services/computer-vision/how-to/call-read-api |
| Use multimodal embeddings for image retrieval | https://learn.microsoft.com/en-us/azure/ai-services/computer-vision/how-to/image-retrieval |
| Use OCR client libraries for text extraction | https://learn.microsoft.com/en-us/azure/ai-services/computer-vision/quickstarts-sdk/client-library |

### Deployment
| Topic | URL |
|-------|-----|
| Install and run Azure Vision Read OCR container | https://learn.microsoft.com/en-us/azure/ai-services/computer-vision/computer-vision-how-to-install-containers |