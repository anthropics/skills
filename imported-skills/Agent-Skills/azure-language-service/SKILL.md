---
name: azure-language-service
description: Expert knowledge for Azure AI Language development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when building CLU apps, custom NER, sentiment/key phrase analysis, CQA bots, or health/FHIR text pipelines, and other Azure AI Language related development tasks. Not for Azure AI Search (use azure-cognitive-search), Azure AI Document Intelligence (use azure-document-intelligence), Azure AI Speech (use azure-speech), Azure Translator (use azure-translator).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure AI Language Skill

This skill provides expert guidance for Azure AI Language. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L42 | Diagnosing and fixing common issues in Azure Language custom NER and conversational question answering (CQA), including model errors, configuration problems, and troubleshooting workflows. |
| Best Practices | L43-L54 | Best practices for designing and authoring CLU, custom NER, PII, and CQA projects, including data prep, schemas, lifecycles, chitchat personas, and document formatting. |
| Decision Making | L55-L64 | Guides for choosing regions and app types, planning CQA solutions, and deciding or executing migrations from LUIS, QnA Maker, Text Analytics, and Language Studio to Azure Language/Fountry. |
| Architecture & Design Patterns | L65-L72 | Designing and implementing regional failover and high-availability patterns for CLU, custom NER, custom text classification, and orchestration workflow models in Azure AI Language. |
| Limits & Quotas | L73-L96 | Limits, quotas, languages, and supported entities for Azure Language features (CLU, NER, classification, CQA, health), including data size, rate/throughput, training and model lifecycles. |
| Security | L97-L107 | Securing Language/CQA data and access: encryption at rest (incl. CMK), RBAC, managed identities, SAS tokens, and network isolation/Private Link for storage and fine-tuning. |
| Configuration | L108-L128 | Configuring Azure AI Language projects and containers: resources, versioning, NER entities/skills, orchestration intents, CQA behavior/telemetry, health analytics, and storage/security settings. |
| Integrations & Coding Patterns | L129-L151 | How to call Azure AI Language REST/SDK APIs for NER, sentiment, key phrases, entity linking, health/FHIR, CQA/CLU, PII redaction, async workflows, and integration with .NET and Power Automate. |
| Deployment | L152-L164 | Guides for deploying Azure Language services and custom projects (NER, key phrases, sentiment, health, CQA) across regions, Docker/on-prem, and AKS, plus moving CQA between environments. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Resolve common issues with custom NER in Azure Language | https://learn.microsoft.com/en-us/azure/ai-services/language-service/custom-named-entity-recognition/faq |
| Troubleshoot common CQA issues and errors | https://learn.microsoft.com/en-us/azure/ai-services/language-service/question-answering/how-to/troubleshooting |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply CLU project authoring best practices | https://learn.microsoft.com/en-us/azure/ai-services/language-service/conversational-language-understanding/concepts/best-practices |
| Prepare data and design schema for custom NER models | https://learn.microsoft.com/en-us/azure/ai-services/language-service/custom-named-entity-recognition/how-to/design-schema |
| Adapt PII detection to custom domain terminology | https://learn.microsoft.com/en-us/azure/ai-services/language-service/personally-identifiable-information/how-to/adapt-to-domain-pii |
| Implement CQA project best practices | https://learn.microsoft.com/en-us/azure/ai-services/language-service/question-answering/concepts/best-practices |
| Follow CQA project development lifecycle | https://learn.microsoft.com/en-us/azure/ai-services/language-service/question-answering/concepts/project-development-lifecycle |
| Apply authoring best practices to CQA projects | https://learn.microsoft.com/en-us/azure/ai-services/language-service/question-answering/how-to/best-practices |
| Add chitchat personas to CQA projects | https://learn.microsoft.com/en-us/azure/ai-services/language-service/question-answering/how-to/chit-chat |
| Apply document formatting best practices for custom Q&A | https://learn.microsoft.com/en-us/azure/ai-services/language-service/question-answering/reference/document-format-guidelines |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose Azure regions for Language service features | https://learn.microsoft.com/en-us/azure/ai-services/language-service/concepts/regional-support |
| Choose CLU app vs orchestration workflow | https://learn.microsoft.com/en-us/azure/ai-services/language-service/conversational-language-understanding/concepts/app-architecture |
| Migrate Azure Language Studio projects to Microsoft Foundry | https://learn.microsoft.com/en-us/azure/ai-services/language-service/migration-studio-to-foundry |
| Plan a CQA app and select Azure resources | https://learn.microsoft.com/en-us/azure/ai-services/language-service/question-answering/concepts/plan |
| Decide migration from LUIS and QnA Maker to Azure Language | https://learn.microsoft.com/en-us/azure/ai-services/language-service/reference/migrate |
| Migrate Text Analytics apps to Azure Language API | https://learn.microsoft.com/en-us/azure/ai-services/language-service/reference/migrate-language-service-latest |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design regional failover for CLU models | https://learn.microsoft.com/en-us/azure/ai-services/language-service/conversational-language-understanding/how-to/fail-over |
| Design regional failover for custom NER models | https://learn.microsoft.com/en-us/azure/ai-services/language-service/custom-named-entity-recognition/fail-over |
| Design regional failover for custom text classification | https://learn.microsoft.com/en-us/azure/ai-services/language-service/custom-text-classification/fail-over |
| Implement regional failover for orchestration workflow models | https://learn.microsoft.com/en-us/azure/ai-services/language-service/orchestration-workflow/concepts/fail-over |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Data size and rate limits for Azure Language features | https://learn.microsoft.com/en-us/azure/ai-services/language-service/concepts/data-limits |
| Understand lifecycle timelines for Azure Language models | https://learn.microsoft.com/en-us/azure/ai-services/language-service/concepts/model-lifecycle |
| Use CLU containers with on-premises limits | https://learn.microsoft.com/en-us/azure/ai-services/language-service/conversational-language-understanding/how-to/use-containers |
| Check CLU supported languages and locales | https://learn.microsoft.com/en-us/azure/ai-services/language-service/conversational-language-understanding/language-support |
| Reference CLU prebuilt entity components | https://learn.microsoft.com/en-us/azure/ai-services/language-service/conversational-language-understanding/prebuilt-component-reference |
| Review CLU data and throughput limits | https://learn.microsoft.com/en-us/azure/ai-services/language-service/conversational-language-understanding/service-limits |
| Understand training job expiration for custom NER | https://learn.microsoft.com/en-us/azure/ai-services/language-service/custom-named-entity-recognition/how-to/train-model |
| Check language support matrix for custom text classification | https://learn.microsoft.com/en-us/azure/ai-services/language-service/custom-text-classification/language-support |
| Review data and rate limits for custom text classification | https://learn.microsoft.com/en-us/azure/ai-services/language-service/custom-text-classification/service-limits |
| Check language support for entity linking | https://learn.microsoft.com/en-us/azure/ai-services/language-service/entity-linking/language-support |
| Review language support for Key Phrase Extraction | https://learn.microsoft.com/en-us/azure/ai-services/language-service/key-phrase-extraction/language-support |
| Understand NER entity categories and types | https://learn.microsoft.com/en-us/azure/ai-services/language-service/named-entity-recognition/concepts/named-entity-categories |
| Check language support for the NER feature | https://learn.microsoft.com/en-us/azure/ai-services/language-service/named-entity-recognition/language-support |
| Check language support for orchestration workflow projects | https://learn.microsoft.com/en-us/azure/ai-services/language-service/orchestration-workflow/language-support |
| Review data and throughput limits for orchestration workflow | https://learn.microsoft.com/en-us/azure/ai-services/language-service/orchestration-workflow/service-limits |
| Use PII detection containers with call size limits | https://learn.microsoft.com/en-us/azure/ai-services/language-service/personally-identifiable-information/how-to/use-containers |
| Understand CQA project and service limits | https://learn.microsoft.com/en-us/azure/ai-services/language-service/question-answering/concepts/limits |
| Review language support for CQA projects | https://learn.microsoft.com/en-us/azure/ai-services/language-service/question-answering/language-support |
| Use health entity categories in Text Analytics | https://learn.microsoft.com/en-us/azure/ai-services/language-service/text-analytics-for-health/concepts/health-entity-categories |
| Review language support for Text Analytics for health | https://learn.microsoft.com/en-us/azure/ai-services/language-service/text-analytics-for-health/language-support |

### Security
| Topic | URL |
|-------|-----|
| Understand data-at-rest encryption in Language service | https://learn.microsoft.com/en-us/azure/ai-services/language-service/concepts/encryption-data-at-rest |
| Configure RBAC for Azure Language resources | https://learn.microsoft.com/en-us/azure/ai-services/language-service/concepts/role-based-access-control |
| Configure managed identities for Azure storage access | https://learn.microsoft.com/en-us/azure/ai-services/language-service/native-document-support/managed-identities |
| Create SAS tokens for Azure storage blobs securely | https://learn.microsoft.com/en-us/azure/ai-services/language-service/native-document-support/shared-access-signatures |
| Configure Azure resources for CQA fine-tuning | https://learn.microsoft.com/en-us/azure/ai-services/language-service/question-answering/how-to/configure-azure-resources |
| Configure CMK encryption for CQA data at rest | https://learn.microsoft.com/en-us/azure/ai-services/language-service/question-answering/how-to/encrypt-data-at-rest |
| Enable network isolation and Private Link for CQA | https://learn.microsoft.com/en-us/azure/ai-services/language-service/question-answering/how-to/network-isolation |

### Configuration
| Topic | URL |
|-------|-----|
| Configure Azure resources for CLU fine-tune models | https://learn.microsoft.com/en-us/azure/ai-services/language-service/concepts/configure-azure-resources |
| Configure Azure Language service containers settings | https://learn.microsoft.com/en-us/azure/ai-services/language-service/concepts/configure-containers |
| Manage project versioning in conversational language | https://learn.microsoft.com/en-us/azure/ai-services/language-service/concepts/custom-features/project-versioning |
| Use supported data formats for custom NER | https://learn.microsoft.com/en-us/azure/ai-services/language-service/custom-named-entity-recognition/concepts/data-formats |
| Create and manage Azure custom NER projects and resources | https://learn.microsoft.com/en-us/azure/ai-services/language-service/custom-named-entity-recognition/how-to/create-project |
| Use NER entity metadata and resolutions | https://learn.microsoft.com/en-us/azure/ai-services/language-service/named-entity-recognition/concepts/entity-metadata |
| Map NER entity types and tags across API versions | https://learn.microsoft.com/en-us/azure/ai-services/language-service/named-entity-recognition/concepts/ga-preview-mapping |
| Configure NER skill parameters and options | https://learn.microsoft.com/en-us/azure/ai-services/language-service/named-entity-recognition/how-to/skill-parameters |
| Configure the None intent behavior in orchestration workflow | https://learn.microsoft.com/en-us/azure/ai-services/language-service/orchestration-workflow/concepts/none-intent |
| Reference list of PII entity categories | https://learn.microsoft.com/en-us/azure/ai-services/language-service/personally-identifiable-information/concepts/entity-categories-list |
| Interpret and configure CQA confidence scores | https://learn.microsoft.com/en-us/azure/ai-services/language-service/question-answering/concepts/confidence-score |
| Enable and query CQA analytics telemetry | https://learn.microsoft.com/en-us/azure/ai-services/language-service/question-answering/how-to/analytics |
| Configure default answer behavior in CQA | https://learn.microsoft.com/en-us/azure/ai-services/language-service/question-answering/how-to/change-default-answer |
| Manage CQA project settings and sources | https://learn.microsoft.com/en-us/azure/ai-services/language-service/question-answering/how-to/manage-knowledge-base |
| Use assertion detection in Text Analytics for health | https://learn.microsoft.com/en-us/azure/ai-services/language-service/text-analytics-for-health/concepts/assertion-detection |
| Interpret relation extraction output in health analytics | https://learn.microsoft.com/en-us/azure/ai-services/language-service/text-analytics-for-health/concepts/relation-extraction |
| Configure storage, logging, and security for health containers | https://learn.microsoft.com/en-us/azure/ai-services/language-service/text-analytics-for-health/how-to/configure-containers |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate Azure Language via SDK and REST APIs | https://learn.microsoft.com/en-us/azure/ai-services/language-service/concepts/developer-guide |
| Use Azure Language features asynchronously via API | https://learn.microsoft.com/en-us/azure/ai-services/language-service/concepts/use-asynchronously |
| Call the custom NER prediction API | https://learn.microsoft.com/en-us/azure/ai-services/language-service/custom-named-entity-recognition/how-to/call-api |
| Start building custom NER models via Foundry or REST | https://learn.microsoft.com/en-us/azure/ai-services/language-service/custom-named-entity-recognition/quickstart |
| Call the entity linking API with correct parameters | https://learn.microsoft.com/en-us/azure/ai-services/language-service/entity-linking/how-to/call-api |
| Invoke the Key Phrase Extraction API correctly | https://learn.microsoft.com/en-us/azure/ai-services/language-service/key-phrase-extraction/how-to/call-api |
| Call Azure Language Detection API and interpret scores | https://learn.microsoft.com/en-us/azure/ai-services/language-service/language-detection/how-to/call-api |
| Implement language detection using SDKs and REST | https://learn.microsoft.com/en-us/azure/ai-services/language-service/language-detection/quickstart |
| Perform NER using Azure Language APIs | https://learn.microsoft.com/en-us/azure/ai-services/language-service/named-entity-recognition/how-to-call |
| Create a .NET app using the NER client library | https://learn.microsoft.com/en-us/azure/ai-services/language-service/named-entity-recognition/quickstart |
| Integrate CLU and custom Q&A via orchestration workflow | https://learn.microsoft.com/en-us/azure/ai-services/language-service/orchestration-workflow/tutorials/connect-services |
| Redact PII from native documents via Azure Language | https://learn.microsoft.com/en-us/azure/ai-services/language-service/personally-identifiable-information/how-to/redact-document-pii |
| Automate CQA authoring with REST API | https://learn.microsoft.com/en-us/azure/ai-services/language-service/question-answering/how-to/authoring |
| Use the CQA prebuilt answering API | https://learn.microsoft.com/en-us/azure/ai-services/language-service/question-answering/how-to/prebuilt |
| Call sentiment analysis and opinion mining APIs correctly | https://learn.microsoft.com/en-us/azure/ai-services/language-service/sentiment-opinion-mining/how-to/call-api |
| Request FHIR-structured output from health analytics | https://learn.microsoft.com/en-us/azure/ai-services/language-service/text-analytics-for-health/concepts/fhir |
| Extract medical information using Text Analytics for health | https://learn.microsoft.com/en-us/azure/ai-services/language-service/text-analytics-for-health/how-to/call-api |
| Call Text Analytics for health via REST and SDKs | https://learn.microsoft.com/en-us/azure/ai-services/language-service/text-analytics-for-health/quickstart |
| Integrate Azure Language with Power Automate flows | https://learn.microsoft.com/en-us/azure/ai-services/language-service/tutorials/power-automate |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy custom language projects to multiple regions | https://learn.microsoft.com/en-us/azure/ai-services/language-service/concepts/custom-features/multi-region-deployment |
| Deploy custom NER with Docker containers | https://learn.microsoft.com/en-us/azure/ai-services/language-service/custom-named-entity-recognition/how-to/use-containers |
| Deploy Key Phrase Extraction containers on-premises | https://learn.microsoft.com/en-us/azure/ai-services/language-service/key-phrase-extraction/how-to/use-containers |
| Deploy Azure Language Detection via Docker containers | https://learn.microsoft.com/en-us/azure/ai-services/language-service/language-detection/how-to/use-containers |
| Run NER Docker containers on-premises | https://learn.microsoft.com/en-us/azure/ai-services/language-service/named-entity-recognition/how-to/use-containers |
| Create and deploy a CQA agent in Foundry | https://learn.microsoft.com/en-us/azure/ai-services/language-service/question-answering/how-to/deploy-agent |
| Move CQA projects between environments | https://learn.microsoft.com/en-us/azure/ai-services/language-service/question-answering/how-to/migrate-knowledge-base |
| Deploy Sentiment Analysis containers on-premises | https://learn.microsoft.com/en-us/azure/ai-services/language-service/sentiment-opinion-mining/how-to/use-containers |
| Run Text Analytics for health in Docker containers | https://learn.microsoft.com/en-us/azure/ai-services/language-service/text-analytics-for-health/how-to/use-containers |
| Deploy Language key phrase container to AKS | https://learn.microsoft.com/en-us/azure/ai-services/language-service/tutorials/use-kubernetes-service |