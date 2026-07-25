---
name: microsoft-foundry-tools
description: Expert knowledge for Microsoft Foundry Tools (aka Azure AI services, Azure Cognitive Services) development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, and integrations & coding patterns. Use when using Content Moderator, Content Safety, Content Understanding analyzers, REST/.NET APIs, or document extraction workloads, and other Microsoft Foundry Tools related development tasks. Not for Microsoft Foundry (use microsoft-foundry), Microsoft Foundry Classic (use microsoft-foundry-classic), Microsoft Foundry Local (use microsoft-foundry-local).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-28"
  generator: "docs2skills/1.0.0"
---
# Microsoft Foundry Tools Skill

This skill provides expert guidance for Microsoft Foundry Tools. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L36-L40 | Troubleshooting steps and FAQs for Content Understanding features, including diagnosing model issues, configuration problems, and resolving common errors in content analysis workflows. |
| Best Practices | L41-L46 | Guidance on improving Content Understanding accuracy, grounding and confidence in document extraction, and migrating from preview to GA Content Understanding APIs. |
| Decision Making | L47-L55 | Guidance for choosing and migrating between Azure AI/Foundry content tools (Content Moderator, Content Safety, Content Understanding), including feature comparisons and pricing/usage planning. |
| Architecture & Design Patterns | L56-L60 | Guidance on choosing and configuring deployment options (serverless, managed, custom) for Content Understanding models, including trade-offs, scalability, and integration patterns. |
| Limits & Quotas | L61-L68 | Quotas, limits, and supported languages for Content Moderator image/list APIs and Content Understanding, plus .NET samples showing how to stay within list and usage limits. |
| Security | L69-L73 | Securing Azure Content Understanding analyzers and data: auth options, network isolation, encryption, access control, and best practices for protecting analyzer inputs/outputs. |
| Configuration | L74-L83 | Configuring and customizing Content Understanding analyzers (prebuilt and custom), document layout, face detection, and cross-resource capacity settings. |
| Integrations & Coding Patterns | L84-L98 | Using Content Moderator and Content Understanding via REST/.NET: text/image/video moderation, term lists, multimodal analysis, and consuming Markdown/structured outputs |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot and answer FAQs for Content Understanding | https://learn.microsoft.com/en-us/azure/ai-services/content-understanding/faq |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply best practices for Content Understanding accuracy | https://learn.microsoft.com/en-us/azure/ai-services/content-understanding/concepts/best-practices |
| Improve document extraction with confidence and grounding | https://learn.microsoft.com/en-us/azure/ai-services/content-understanding/document/analyzer-improvement |

### Decision Making
| Topic | URL |
|-------|-----|
| Migrate Azure Content Moderator workloads to Content Safety | https://learn.microsoft.com/en-us/azure/ai-services/content-moderator/content-moderator |
| Choose Azure AI tools for document processing | https://learn.microsoft.com/en-us/azure/ai-services/content-understanding/choosing-right-ai-tool |
| Choose between Foundry and Content Understanding Studio features | https://learn.microsoft.com/en-us/azure/ai-services/content-understanding/foundry-vs-content-understanding-studio |
| Migrate Content Understanding from preview to GA APIs | https://learn.microsoft.com/en-us/azure/ai-services/content-understanding/how-to/migration-preview-to-ga |
| Estimate and plan Content Understanding pricing | https://learn.microsoft.com/en-us/azure/ai-services/content-understanding/pricing-explainer |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Select model deployment options for Content Understanding | https://learn.microsoft.com/en-us/azure/ai-services/content-understanding/concepts/models-deployments |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Use Content Moderator image lists within quota limits | https://learn.microsoft.com/en-us/azure/ai-services/content-moderator/image-lists-quickstart-dotnet |
| Use supported languages in Content Moderator API | https://learn.microsoft.com/en-us/azure/ai-services/content-moderator/language-support |
| Apply Content Moderator .NET samples with list limits | https://learn.microsoft.com/en-us/azure/ai-services/content-moderator/samples-dotnet |
| Content Understanding service quotas and limits reference | https://learn.microsoft.com/en-us/azure/ai-services/content-understanding/service-limits |

### Security
| Topic | URL |
|-------|-----|
| Secure Azure Content Understanding analyzers and data | https://learn.microsoft.com/en-us/azure/ai-services/content-understanding/concepts/secure-communications |

### Configuration
| Topic | URL |
|-------|-----|
| Configure and reference analyzers in Azure Content Understanding | https://learn.microsoft.com/en-us/azure/ai-services/content-understanding/concepts/analyzer-reference |
| Use and customize Content Understanding prebuilt analyzers | https://learn.microsoft.com/en-us/azure/ai-services/content-understanding/concepts/prebuilt-analyzers |
| Configure document layout analysis with Content Understanding | https://learn.microsoft.com/en-us/azure/ai-services/content-understanding/document/elements |
| Configure face detection and recognition in Content Understanding | https://learn.microsoft.com/en-us/azure/ai-services/content-understanding/face/overview |
| Configure cross-resource capacity for Content Understanding | https://learn.microsoft.com/en-us/azure/ai-services/content-understanding/how-to/bring-your-own-cross-resource-capacity |
| Build and refine custom analyzers in Content Understanding Studio | https://learn.microsoft.com/en-us/azure/ai-services/content-understanding/how-to/customize-analyzer-content-understanding-studio |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Content Moderator REST API operations reference | https://learn.microsoft.com/en-us/azure/ai-services/content-moderator/api-reference |
| Integrate Content Moderator via .NET client library | https://learn.microsoft.com/en-us/azure/ai-services/content-moderator/client-libraries |
| Call Content Moderator image moderation APIs | https://learn.microsoft.com/en-us/azure/ai-services/content-moderator/image-moderation-api |
| Call Content Moderator REST APIs from C# samples | https://learn.microsoft.com/en-us/azure/ai-services/content-moderator/samples-rest |
| Use .NET SDK term lists with Content Moderator | https://learn.microsoft.com/en-us/azure/ai-services/content-moderator/term-lists-quickstart-dotnet |
| Use Content Moderator text moderation APIs | https://learn.microsoft.com/en-us/azure/ai-services/content-moderator/text-moderation-api |
| Moderate video content using Content Moderator .NET SDK | https://learn.microsoft.com/en-us/azure/ai-services/content-moderator/video-moderation-api |
| Consume Content Understanding document Markdown output | https://learn.microsoft.com/en-us/azure/ai-services/content-understanding/document/markdown |
| Call Content Understanding REST API for multimodal data | https://learn.microsoft.com/en-us/azure/ai-services/content-understanding/quickstart/use-rest-api |
| Create custom Content Understanding analyzers via REST API | https://learn.microsoft.com/en-us/azure/ai-services/content-understanding/tutorial/create-custom-analyzer |
| Extract structured audiovisual content with Content Understanding | https://learn.microsoft.com/en-us/azure/ai-services/content-understanding/video/elements |
| Use audiovisual Markdown output from Content Understanding | https://learn.microsoft.com/en-us/azure/ai-services/content-understanding/video/markdown |