---
name: azure-translator
description: Expert knowledge for Azure Translator development including troubleshooting, best practices, decision making, limits & quotas, security, configuration, and integrations & coding patterns. Use when using text/doc translation APIs, Custom Translator, glossaries/dictionaries, containers, or neural dictionary features, and other Azure Translator related development tasks. Not for Azure AI Language (use azure-language-service), Azure AI Speech (use azure-speech), Azure AI Immersive Reader (use azure-immersive-reader), Azure AI Search (use azure-cognitive-search).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Translator Skill

This skill provides expert guidance for Azure Translator. Covers troubleshooting, best practices, decision making, limits & quotas, security, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L35-L41 | Troubleshooting Azure Translator errors: common usage problems, known service issues, HTTP status/error codes, and how to diagnose, interpret, and fix them. |
| Best Practices | L42-L51 | Best practices for preparing training data, managing glossaries, and building reliable end-to-end workflows for Custom Translator and batch/document translation in Azure Translator. |
| Decision Making | L52-L60 | Guidance on choosing custom vs baseline models, planning upgrades, selecting Document Translation infrastructure, and migrating apps between Translator API versions. |
| Limits & Quotas | L61-L67 | Language/feature and locale support matrices, plus usage limits and quotas for Azure Translator text, document translation, and Translator Pro. |
| Security | L68-L79 | Securing Azure Translator: encryption, keys, auth (Entra ID, SAS, managed identities), firewalls/VNet endpoints, and protecting data and deployments. |
| Configuration | L80-L105 | Configuring Azure Translator and Custom Translator: containers, resources, APIs, parameters, filters, tagging, dictionaries, alignment, monitoring, and sovereign cloud setup. |
| Integrations & Coding Patterns | L106-L143 | Patterns and code for calling Translator REST/SDK: text, transliteration, neural dictionary, custom/adaptive models, containers, document batch/sync APIs, jobs, status, and supported formats. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Resolve common Azure Translator usage issues (FAQ) | https://learn.microsoft.com/en-us/azure/ai-services/translator/faq |
| Diagnose and mitigate known issues in Azure Translator | https://learn.microsoft.com/en-us/azure/ai-services/translator/reference/known-issues |
| Interpret Azure Translator HTTP status and error codes | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/reference/status-response-codes |

### Best Practices
| Topic | URL |
|-------|-----|
| Prepare and filter training data for Custom Translator | https://learn.microsoft.com/en-us/azure/ai-services/translator/custom-translator/concepts/data-filtering |
| Prepare and upload Custom Translator training documents | https://learn.microsoft.com/en-us/azure/ai-services/translator/custom-translator/how-to/create-manage-training-documents |
| Train Custom Translator models with proper datasets | https://learn.microsoft.com/en-us/azure/ai-services/translator/custom-translator/how-to/train-custom-model |
| Apply FAQ-based usage tips for Document translation | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/faq |
| Create and apply glossaries in Document translation | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/how-to-guides/create-use-glossaries |
| Implement reliable end-to-end batch document translation workflow | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/latest/end-to-end-batch-workflow |

### Decision Making
| Topic | URL |
|-------|-----|
| Evaluate and compare Custom vs baseline Translator models | https://learn.microsoft.com/en-us/azure/ai-services/translator/custom-translator/how-to/test-your-model |
| Plan and execute Custom Translator platform upgrade | https://learn.microsoft.com/en-us/azure/ai-services/translator/custom-translator/platform-upgrade |
| Choose and set up infrastructure for Document Translation API | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/latest/prerequisites |
| Decide and migrate from Translator v3.0 to 2026-06-06 | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/how-to/migrate-to-2026-06-06 |
| Migrate applications from Translator V2 to V3 | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/how-to/migrate-to-v3 |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Check language and feature support in Azure Translator | https://learn.microsoft.com/en-us/azure/ai-services/translator/language-support |
| Service limits for Azure Translator text and documents | https://learn.microsoft.com/en-us/azure/ai-services/translator/service-limits |
| Check language and locale support in Translator Pro | https://learn.microsoft.com/en-us/azure/ai-services/translator/solutions/translator-pro/language-support |

### Security
| Topic | URL |
|-------|-----|
| Configure customer-managed keys for Azure Translator data at rest | https://learn.microsoft.com/en-us/azure/ai-services/translator/custom-translator/concepts/encrypt-data-at-rest |
| Configure VNet service endpoints for Custom Translator | https://learn.microsoft.com/en-us/azure/ai-services/translator/custom-translator/how-to/enable-vnet-service-endpoint |
| Create SAS tokens for Document translation storage access | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/how-to-guides/create-sas-tokens |
| Configure managed identities for Document translation storage access | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/how-to-guides/create-use-managed-identities |
| Configure Microsoft Entra ID auth for Azure Translator | https://learn.microsoft.com/en-us/azure/ai-services/translator/how-to/microsoft-entra-id-auth |
| Enable Azure Translator access behind firewalls | https://learn.microsoft.com/en-us/azure/ai-services/translator/how-to/use-firewalls |
| Secure Azure Translator data and deployments | https://learn.microsoft.com/en-us/azure/ai-services/translator/secure-deployment |
| Authenticate and authorize requests to Azure Translator | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/reference/authentication |

### Configuration
| Topic | URL |
|-------|-----|
| Configure Azure Translator container runtime settings | https://learn.microsoft.com/en-us/azure/ai-services/translator/containers/configuration |
| Install and run Azure Translator Docker container | https://learn.microsoft.com/en-us/azure/ai-services/translator/containers/install-run |
| Apply document formats and naming rules in Custom Translator | https://learn.microsoft.com/en-us/azure/ai-services/translator/custom-translator/concepts/document-formats-naming-convention |
| Configure and manage Custom Translator projects | https://learn.microsoft.com/en-us/azure/ai-services/translator/custom-translator/how-to/create-manage-project |
| Configure and manage Custom Translator workspaces | https://learn.microsoft.com/en-us/azure/ai-services/translator/custom-translator/how-to/create-manage-workspace |
| Publish Custom Translator models to regions | https://learn.microsoft.com/en-us/azure/ai-services/translator/custom-translator/how-to/publish-model |
| Configure Document Translation REST API 2026-03-01 operations | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/latest/rest-api/guide-overview |
| Create and configure Azure Translator resources | https://learn.microsoft.com/en-us/azure/ai-services/translator/how-to/create-translator-resource |
| Use Azure Translator in sovereign cloud environments | https://learn.microsoft.com/en-us/azure/ai-services/translator/reference/sovereign-clouds |
| Use Translator 2026-06-06 translate API parameters | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/2026-06-06/translate-api |
| Tag content to prevent translation in Azure Translator | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/how-to/prevent-translation |
| Use dynamic dictionary markup in Azure Translator | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/how-to/use-dynamic-dictionary |
| Configure profanity filtering in Azure Translator | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/how-to/use-profanity-filtering |
| Enable word alignment in Azure Translator responses | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/how-to/word-alignment |
| Monitor Azure Translator usage with Azure Monitor metrics | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/reference/metrics |
| Use Translator V3 BreakSentence method for sentence boundaries | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/reference/v3/break-sentence |
| Call Translator V3 detect method to identify language | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/reference/v3/detect |
| Use Translator V3 dictionary examples for contextual usage | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/reference/v3/dictionary-examples |
| Use Translator V3 dictionary lookup for alternative translations | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/reference/v3/dictionary-lookup |
| Configure and call Translator V3.0 JSON Web API | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/reference/v3/reference |
| Use Translator V3 translate method parameters | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/reference/v3/translate |
| Configure script transliteration with Translator V3 | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/reference/v3/transliterate |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Deploy user-managed glossary in Translator containers | https://learn.microsoft.com/en-us/azure/ai-services/translator/containers/deploy-user-managed-glossary |
| Call Translator container document translation API | https://learn.microsoft.com/en-us/azure/ai-services/translator/containers/translate-document-parameters |
| Use Translator container text translation parameters | https://learn.microsoft.com/en-us/azure/ai-services/translator/containers/translate-text-parameters |
| Use Translator container transliteration API parameters | https://learn.microsoft.com/en-us/azure/ai-services/translator/containers/transliterate-text-parameters |
| Call Translator API using a Custom Translator model | https://learn.microsoft.com/en-us/azure/ai-services/translator/custom-translator/how-to/translate-with-custom-model |
| Integrate asynchronous batch document translation with Blob Storage | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/latest/quickstarts/asynchronous |
| Integrate synchronous single-file document translation API | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/latest/quickstarts/synchronous |
| Cancel an asynchronous document translation job | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/latest/rest-api/cancel-translation |
| Retrieve status for all documents in a job | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/latest/rest-api/get-status-all-documents |
| List all document translation jobs via REST | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/latest/rest-api/get-status-all-translations |
| Get status for a single translated document | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/latest/rest-api/get-status-specific-document |
| Get status of a specific translation job | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/latest/rest-api/get-status-specific-translation |
| Query supported document formats for translation | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/latest/rest-api/get-supported-document-formats |
| Query supported glossary formats for translation | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/latest/rest-api/get-supported-glossary-formats |
| Start asynchronous batch document translation jobs | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/latest/rest-api/translate-asynchronous |
| Call synchronous document translation REST endpoint | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/latest/rest-api/translate-synchronous |
| Cancel a batch document translation job | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/reference/cancel-translation |
| Get status for a specific document in a job | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/reference/get-document-status |
| Get status for all documents in a translation job | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/reference/get-documents-status |
| Retrieve supported document formats via REST | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/reference/get-supported-document-formats |
| Retrieve supported glossary formats via REST | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/reference/get-supported-glossary-formats |
| Get status of a document translation request | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/reference/get-translation-status |
| List translation jobs and statuses via REST | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/reference/get-translations-status |
| Navigate Document translation REST API operations | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/reference/rest-api-guide |
| Start batch document translation via REST | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/reference/start-batch-translation |
| Use synchronous text translation REST API for documents | https://learn.microsoft.com/en-us/azure/ai-services/translator/document-translation/reference/translate-document |
| Integrate with adaptive custom translation (AdaptCT) API | https://learn.microsoft.com/en-us/azure/ai-services/translator/foundry/adaptive-custom-translation |
| Build document translation flows with Translator connector | https://learn.microsoft.com/en-us/azure/ai-services/translator/solutions/connector/document-translation-flow |
| Configure text translation flows using Translator connector | https://learn.microsoft.com/en-us/azure/ai-services/translator/solutions/connector/text-translator-flow |
| Use Azure Translator text translation REST APIs | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/2026-06-06/rest-api-guide |
| Call Azure Translator transliterate REST method | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/2026-06-06/transliterate-api |
| Use Azure Translator neural dictionary in apps | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/how-to/use-neural-dictionary |
| Use Azure Translator REST APIs with code examples | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/how-to/use-rest-api |
| Integrate Azure Translator via SDK client libraries | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/quickstart/client-library-sdk |
| Call Azure Translator REST API programmatically | https://learn.microsoft.com/en-us/azure/ai-services/translator/text-translation/quickstart/rest-api |