---
name: azure-document-intelligence
description: Expert knowledge for Azure AI Document Intelligence development including troubleshooting, best practices, decision making, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when training custom models, composing templates, using REST/SDK APIs, deploying containers, or planning v4.0 upgrades, and other Azure AI Document Intelligence related development tasks. Not for Azure AI Search (use azure-cognitive-search), Azure AI Custom Vision (use azure-custom-vision), Azure AI Language (use azure-language-service), Azure AI Video Indexer (use azure-video-indexer).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure AI Document Intelligence Skill

This skill provides expert guidance for Azure AI Document Intelligence. Covers troubleshooting, best practices, decision making, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L36-L42 | Diagnosing latency, understanding and fixing Document Intelligence API error codes, and handling known service issues and limitations. |
| Best Practices | L43-L54 | Guidance on training, labeling, composing, and managing custom/classification/template models to maximize Document Intelligence accuracy, confidence, and lifecycle quality. |
| Decision Making | L55-L61 | Guidance on choosing the right Document Intelligence model, estimating usage/costs, and planning migration and version upgrades (including to v4.0). |
| Limits & Quotas | L62-L72 | Capacity add-ons, container image tags, OCR and model language/locale support, batch processing at scale, and service quotas/limits for Azure Document Intelligence. |
| Security | L73-L80 | Securing Document Intelligence resources: creating SAS tokens, configuring data-at-rest encryption with customer-managed keys, and using managed identities and VNETs for secure access. |
| Configuration | L81-L86 | Configuring and deploying Document Intelligence containers, and managing/sharing custom model projects in Document Intelligence Studio for collaborative use. |
| Integrations & Coding Patterns | L87-L97 | How to call Document Intelligence via REST/SDKs, use the sample tool, and integrate outputs (JSON/Markdown) into workflows with Azure Functions and Logic Apps. |
| Deployment | L98-L105 | Guides for deploying Document Intelligence: Docker/container setup (including offline), SDK/REST API usage, disaster recovery, and deploying the sample labeling tool. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Azure Document Intelligence latency issues | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/concept/troubleshoot-latency?view=doc-intel-4.0.0 |
| Reference and resolve Document Intelligence API errors | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/how-to-guides/resolve-errors?view=doc-intel-4.0.0 |
| Handle known issues in Azure Document Intelligence | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/reference/known-issues?view=doc-intel-4.0.0 |

### Best Practices
| Topic | URL |
|-------|-----|
| Improve Document Intelligence accuracy and confidence | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/concept/accuracy-confidence?view=doc-intel-4.0.0 |
| Train custom document classification models | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/how-to-guides/build-a-custom-classifier?view=doc-intel-4.0.0 |
| Build and train custom Document Intelligence models | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/how-to-guides/build-a-custom-model?view=doc-intel-4.0.0 |
| Create and compose custom Document Intelligence models | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/how-to-guides/compose-custom-models?view=doc-intel-4.0.0 |
| Use efficient labeling tips in Document Intelligence Studio | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/train/custom-label-tips?view=doc-intel-4.0.0 |
| Apply labeling best practices for high-accuracy custom models | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/train/custom-labels?view=doc-intel-4.0.0 |
| Manage Azure Document Intelligence custom model lifecycle | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/train/custom-lifecycle?view=doc-intel-4.0.0 |
| Train template models using supervised table tags | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/v21/supervised-table-tags?view=doc-intel-2.1.0 |

### Decision Making
| Topic | URL |
|-------|-----|
| Select the right Azure Document Intelligence model | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/concept/choose-model-feature?view=doc-intel-4.0.0 |
| Estimate Document Intelligence usage and cost | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/how-to-guides/estimate-cost?view=doc-intel-4.0.0 |
| Decide and migrate to Document Intelligence v4.0 | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/versioning/migration-guide-overview?view=doc-intel-4.0.0 |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Increase Document Intelligence capacity with add-ons | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/concept/add-on-capabilities?view=doc-intel-4.0.0 |
| Reference Document Intelligence container image tags | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/containers/image-tags?view=doc-intel-4.0.0 |
| Understand language support for custom Document Intelligence models | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/language-support/custom?view=doc-intel-4.0.0 |
| Check OCR language and locale support for Read/Layout | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/language-support/ocr?view=doc-intel-4.0.0 |
| Review language support for Document Intelligence prebuilt models | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/language-support/prebuilt?view=doc-intel-4.0.0 |
| Use Document Intelligence batch analysis at scale | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/prebuilt/batch-analysis?view=doc-intel-4.0.0 |
| Service quotas and limits for Azure Document Intelligence | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/service-limits?view=doc-intel-4.0.0 |

### Security
| Topic | URL |
|-------|-----|
| Create SAS tokens for Document Intelligence storage | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/authentication/create-sas-tokens?view=doc-intel-4.0.0 |
| Manage data-at-rest encryption and CMK for Document Intelligence | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/authentication/encrypt-data-at-rest?view=doc-intel-4.0.0 |
| Secure Document Intelligence with managed identities and VNETs | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/authentication/managed-identities-secured-access?view=doc-intel-4.0.0 |
| Configure managed identities for Document Intelligence | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/authentication/managed-identities?view=doc-intel-4.0.0 |

### Configuration
| Topic | URL |
|-------|-----|
| Configure Azure Document Intelligence containers | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/containers/configuration?view=doc-intel-4.0.0 |
| Share custom model projects in Document Intelligence Studio | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/how-to-guides/project-share-custom-models?view=doc-intel-4.0.0 |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use AnalyzeDocument API response objects effectively | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/concept/analyze-document-response?view=doc-intel-4.0.0 |
| Consume Document Intelligence Markdown output | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/concept/markdown-elements?view=doc-intel-4.0.0 |
| Integrate Document Intelligence via SDKs and REST | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/how-to-guides/use-sdk-rest-api?view=doc-intel-4.0.0 |
| Process documents with Azure Functions and Document Intelligence | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/tutorial/azure-function?view=doc-intel-4.0.0 |
| Integrate Document Intelligence with Azure Logic Apps | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/tutorial/logic-apps?view=doc-intel-4.0.0 |
| Use sample tool with REST API to train models | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/v21/label-tool?view=doc-intel-2.1.0 |
| Label, train, and analyze forms with sample tool | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/v21/try-sample-label-tool?view=doc-intel-2.1.0 |

### Deployment
| Topic | URL |
|-------|-----|
| Run Document Intelligence containers in disconnected environments | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/containers/disconnected?view=doc-intel-4.0.0 |
| Install and run Document Intelligence Docker containers | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/containers/install-run?view=doc-intel-4.0.0 |
| Implement disaster recovery for Document Intelligence models | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/how-to-guides/disaster-recovery?view=doc-intel-4.0.0 |
| Start using Document Intelligence SDKs and REST API | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/quickstarts/get-started-sdks-rest-api?view=doc-intel-4.0.0 |
| Deploy the Document Intelligence Sample Labeling tool | https://learn.microsoft.com/en-us/azure/ai-services/document-intelligence/v21/deploy-label-tool?view=doc-intel-2.1.0 |