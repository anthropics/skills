---
name: azure-cognitive-search
description: Expert knowledge for Azure AI Search development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when building indexes/indexers, AI enrichment skillsets, semantic/vector search, or secure multi-region deployments, and other Azure AI Search related development tasks. Not for Azure Cosmos DB (use azure-cosmos-db), Azure Data Explorer (use azure-data-explorer), Azure SQL Database (use azure-sql-database), Azure Synapse Analytics (use azure-synapse-analytics).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure AI Search Skill

This skill provides expert guidance for Azure AI Search. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L48 | Diagnosing and fixing Azure AI Search indexer and skillset errors, debug sessions, OData filter issues, private link problems, and storage/metrics-related failures. |
| Best Practices | L49-L67 | Design, performance, cost, and reliability best practices for Azure AI Search: AI enrichment, custom skills, indexing/updates, vectors/chunking, concurrency, blob changes, and query/index tuning. |
| Decision Making | L68-L82 | Guidance on planning and upgrading Azure AI Search: migrations (skills, APIs, SDKs), capacity and region choices, pricing tiers, cost management, and connector selection. |
| Architecture & Design Patterns | L83-L88 | Designing Azure AI Search architectures for multitenancy vs isolated indexes, and planning resilient multi-region deployments, failover, and data locality. |
| Limits & Quotas | L89-L99 | Limits, quotas, and scheduling for indexers and services, including billing/free enrichment, tier caps, vector index size, and how to manage and run indexers with .NET. |
| Security | L100-L136 | Securing Azure AI Search: RBAC/keys, Entra auth, policies, encryption/CMK, network isolation (firewalls, private endpoints), and securing indexer connections and document-level/query-time access. |
| Configuration | L137-L219 | Configuring Azure AI Search behavior: indexes, indexers, analyzers, vectorization, skillsets/enrichment, semantic ranking, retrieval/answer synthesis, logging, and query/OData options. |
| Integrations & Coding Patterns | L220-L305 | Integrating Azure AI Search with data sources, indexers, skills, vectorization, query syntax, semantic ranking, and knowledge bases for agentic and organizational retrieval. |
| Deployment | L306-L314 | Deploying and moving Azure AI Search services: ARM/Bicep/Terraform provisioning, region moves and feature availability, and deploying search apps to Static Web Apps. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Azure AI Search indexer errors and warnings | https://learn.microsoft.com/en-us/azure/search/cognitive-search-common-errors-warnings |
| Understand Debug Sessions for skillset troubleshooting | https://learn.microsoft.com/en-us/azure/search/cognitive-search-debug-session |
| Debug and troubleshoot Azure AI Search skillsets | https://learn.microsoft.com/en-us/azure/search/cognitive-search-how-to-debug-skillset |
| Debug Azure AI Search skillsets using portal sessions | https://learn.microsoft.com/en-us/azure/search/cognitive-search-tutorial-debug-sessions |
| Diagnose and fix Azure AI Search indexer issues | https://learn.microsoft.com/en-us/azure/search/search-indexer-troubleshooting |
| Troubleshoot OData collection filter errors in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-query-troubleshoot-collection-filters |
| Troubleshoot shared private link resource issues in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/troubleshoot-shared-private-link-resources |
| Troubleshoot Azure AI Search storage metric issues | https://learn.microsoft.com/en-us/azure/search/troubleshoot-storage-metrics |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply AI enrichment design tips in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-concept-troubleshooting |
| Scale and manage custom skills in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-custom-skill-scale |
| Apply responsible AI best practices for GenAI Prompt skill | https://learn.microsoft.com/en-us/azure/search/responsible-ai-best-practices-genai-prompt-skill |
| Handle changed and deleted blobs in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-how-to-index-azure-blob-changed-deleted |
| Optimize large-scale indexing in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-how-to-large-index |
| Apply optimistic concurrency for Azure AI Search resources | https://learn.microsoft.com/en-us/azure/search/search-howto-concurrency |
| Update or rebuild Azure AI Search indexes safely | https://learn.microsoft.com/en-us/azure/search/search-howto-reindex |
| Analyze Azure AI Search query and indexing performance | https://learn.microsoft.com/en-us/azure/search/search-performance-analysis |
| Optimize Azure AI Search query and indexing performance | https://learn.microsoft.com/en-us/azure/search/search-performance-tips |
| Optimize Azure AI Search Serverless costs and usage | https://learn.microsoft.com/en-us/azure/search/serverless-cost-optimization |
| Efficient C# indexing with Azure AI Search Push API | https://learn.microsoft.com/en-us/azure/search/tutorial-optimize-indexing-push-api |
| Use narrow vector data types to reduce Azure AI Search storage | https://learn.microsoft.com/en-us/azure/search/vector-search-how-to-assign-narrow-data-types |
| Chunk large documents for Azure AI Search vector retrieval | https://learn.microsoft.com/en-us/azure/search/vector-search-how-to-chunk-documents |
| Choose vector optimization and compression in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/vector-search-how-to-configure-compression-storage |
| Truncate text-embedding-3 dimensions using MRL in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/vector-search-how-to-truncate-dimensions |

### Decision Making
| Topic | URL |
|-------|-----|
| Migrate from deprecated Azure AI Search skills | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-deprecated |
| Migrate Azure AI Search REST API versions safely | https://learn.microsoft.com/en-us/azure/search/search-api-migration |
| Estimate Azure AI Search capacity needs | https://learn.microsoft.com/en-us/azure/search/search-capacity-planning |
| Choose appropriate data source connectors for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-data-sources-gallery |
| Upgrade Azure AI Search .NET management SDKs | https://learn.microsoft.com/en-us/azure/search/search-dotnet-mgmt-sdk-migration |
| Upgrade Azure AI Search .NET apps to SDK v11 | https://learn.microsoft.com/en-us/azure/search/search-dotnet-sdk-migration-version-11 |
| Compare Azure AI Search features by tier and region | https://learn.microsoft.com/en-us/azure/search/search-features-list |
| Upgrade Azure AI Search to higher capacity | https://learn.microsoft.com/en-us/azure/search/search-how-to-upgrade |
| Choose alternative regions for Azure AI Search capacity | https://learn.microsoft.com/en-us/azure/search/search-region-capacity |
| Plan and manage Azure AI Search costs | https://learn.microsoft.com/en-us/azure/search/search-sku-manage-costs |
| Choose Azure AI Search pricing model and tier | https://learn.microsoft.com/en-us/azure/search/search-sku-tier |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design multitenant and isolated content in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-modeling-multitenant-saas-applications |
| Design multi-region architectures for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-multi-region |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Billing limits and free quotas for Azure AI Search enrichment | https://learn.microsoft.com/en-us/azure/search/cognitive-search-attach-cognitive-services |
| Manage Azure AI Search indexer runs and resets | https://learn.microsoft.com/en-us/azure/search/search-howto-run-reset-indexers |
| Configure Azure AI Search indexer schedules and limits | https://learn.microsoft.com/en-us/azure/search/search-howto-schedule-indexers |
| Understand indexer execution quotas on Serverless and S3 HD | https://learn.microsoft.com/en-us/azure/search/search-indexer-high-density-serverless-overview |
| Azure AI Search service limits by tier | https://learn.microsoft.com/en-us/azure/search/search-limits-quotas-capacity |
| Create and load Azure AI Search index with .NET | https://learn.microsoft.com/en-us/azure/search/tutorial-csharp-create-load-index |
| Understand Azure AI Search vector index size limits | https://learn.microsoft.com/en-us/azure/search/vector-search-index-size |

### Security
| Topic | URL |
|-------|-----|
| Use built-in Azure Policy definitions for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/policy-reference |
| Implement document-level access control in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-document-level-access-overview |
| Configure keyless RBAC access to Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-get-started-rbac |
| Configure managed identity access to SQL Managed Instance | https://learn.microsoft.com/en-us/azure/search/search-how-to-index-sql-managed-instance-with-managed-identity |
| Secure AI Search indexer connections to SQL Server VMs | https://learn.microsoft.com/en-us/azure/search/search-how-to-index-sql-server |
| Configure managed identities and RBAC for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-how-to-managed-identities |
| Secure Azure Functions indexer connections with Easy Auth | https://learn.microsoft.com/en-us/azure/search/search-howto-managed-identities-azure-functions |
| Secure Cosmos DB indexer connections with managed identity | https://learn.microsoft.com/en-us/azure/search/search-howto-managed-identities-cosmos-db |
| Configure managed identity access from Azure AI Search to Azure SQL | https://learn.microsoft.com/en-us/azure/search/search-howto-managed-identities-sql |
| Configure managed identity access from Azure AI Search to Storage | https://learn.microsoft.com/en-us/azure/search/search-howto-managed-identities-storage |
| Index ACL and RBAC metadata via Azure AI Search REST API | https://learn.microsoft.com/en-us/azure/search/search-index-access-control-lists-and-rbac-push-api |
| Connect Azure AI Search indexers to SQL Managed Instance privately | https://learn.microsoft.com/en-us/azure/search/search-indexer-how-to-access-private-sql |
| Configure Azure AI Search indexer access through IP firewalls | https://learn.microsoft.com/en-us/azure/search/search-indexer-howto-access-ip-restricted |
| Configure shared private link access for Azure AI Search indexers | https://learn.microsoft.com/en-us/azure/search/search-indexer-howto-access-private |
| Use trusted service exception for Azure AI Search indexers | https://learn.microsoft.com/en-us/azure/search/search-indexer-howto-access-trusted-service-exception |
| Secure indexer access to network-protected resources in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-indexer-securing-resources |
| Configure indexers to ingest Purview sensitivity labels | https://learn.microsoft.com/en-us/azure/search/search-indexer-sensitivity-labels |
| Configure security and access for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-manage |
| Enforce ACL and RBAC at query time in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-query-access-control-rbac-enforcement |
| Enforce Purview sensitivity labels at query time in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-query-sensitivity-labels |
| Manage Azure AI Search admin and query API keys | https://learn.microsoft.com/en-us/azure/search/search-security-api-keys |
| Apply security best practices to Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-security-best-practices |
| Enable RBAC and Entra ID auth for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-security-enable-roles |
| Retrieve encryption key details for Azure AI Search resources | https://learn.microsoft.com/en-us/azure/search/search-security-get-encryption-keys |
| Configure customer-managed encryption keys for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-security-manage-encryption-keys |
| Set up cross-tenant CMK encryption for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-security-managed-encryption-cross-tenant |
| Join Azure AI Search to a network security perimeter | https://learn.microsoft.com/en-us/azure/search/search-security-network-security-perimeter |
| Assign Azure RBAC roles for Azure AI Search access | https://learn.microsoft.com/en-us/azure/search/search-security-rbac |
| Configure client applications for keyless RBAC access to Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-security-rbac-client-code |
| Implement document-level security filters in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-security-trimming-for-azure-search |
| Use Azure Policy compliance controls for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/security-controls-policy |
| Configure IP firewall and trusted service access for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/service-configure-firewall |
| Configure Azure AI Search private endpoints | https://learn.microsoft.com/en-us/azure/search/service-create-private-endpoint |

### Configuration
| Topic | URL |
|-------|-----|
| Enable or disable Web Knowledge Source access in Azure | https://learn.microsoft.com/en-us/azure/search/agentic-knowledge-source-how-to-web-manage |
| Configure answer synthesis for Azure AI Search knowledge bases | https://learn.microsoft.com/en-us/azure/search/agentic-retrieval-how-to-answer-synthesis |
| Configure freshness-aware retrieval for agentic knowledge sources | https://learn.microsoft.com/en-us/azure/search/agentic-retrieval-how-to-configure-freshness |
| Define Azure AI Search index for agentic retrieval | https://learn.microsoft.com/en-us/azure/search/agentic-retrieval-how-to-create-index |
| Configure agentic retrieval billing consent in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/agentic-retrieval-how-to-enable-disable |
| Configure image serving for agentic retrieval answer synthesis | https://learn.microsoft.com/en-us/azure/search/agentic-retrieval-how-to-image-serving |
| Set retrieval reasoning effort for agentic Azure AI Search | https://learn.microsoft.com/en-us/azure/search/agentic-retrieval-how-to-set-retrieval-reasoning-effort |
| Use annotation syntax to reference enriched nodes in skillsets | https://learn.microsoft.com/en-us/azure/search/cognitive-search-concept-annotations-syntax |
| Define and configure skillsets in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-defining-skillset |
| Configure output field mappings for Azure AI Search skillsets | https://learn.microsoft.com/en-us/azure/search/cognitive-search-output-field-mapping |
| Configure and use predefined skills in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-predefined-skills |
| Use skill context and annotation language in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-annotation-language |
| Configure Azure Content Understanding skill in AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-content-understanding |
| Configure Custom Entity Lookup skill parameters | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-custom-entity-lookup |
| Configure Document Layout skill in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-document-intelligence-layout |
| Configure Entity Recognition skill v2 in skillsets | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-entity-recognition |
| Set up GenAI Prompt skill in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-genai-prompt |
| Configure Image Analysis skill in Azure AI Search enrichment | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-image-analysis |
| Configure PII Detection skill in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-pii-detection |
| Use Shaper skill to restructure enrichment output | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-shaper |
| Configure Text Split skill for chunking content | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-textsplit |
| Design and configure skillsets for AI enrichment | https://learn.microsoft.com/en-us/azure/search/cognitive-search-working-with-skillsets |
| Configure enrichment caching in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/enrichment-cache-how-to-configure |
| Manage enrichment cache storage for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/enrichment-cache-how-to-manage |
| Define custom analyzers for Azure AI Search indexes | https://learn.microsoft.com/en-us/azure/search/index-add-custom-analyzers |
| Add language analyzers to Azure AI Search fields | https://learn.microsoft.com/en-us/azure/search/index-add-language-analyzers |
| Define and apply scoring profiles in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/index-add-scoring-profiles |
| Configure BM25 relevance scoring in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/index-ranking-similarity |
| Define and configure knowledge store projection shapes | https://learn.microsoft.com/en-us/azure/search/knowledge-store-projection-shape |
| Reference for Azure AI Search monitoring metrics and logs | https://learn.microsoft.com/en-us/azure/search/monitor-azure-cognitive-search-data-reference |
| Reference stopword lists for Azure AI Search analyzers | https://learn.microsoft.com/en-us/azure/search/reference-stopwords |
| Configure analyzers for text processing in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-analyzers |
| Use Azure AI Search preview APIs and features | https://learn.microsoft.com/en-us/azure/search/search-api-preview |
| Use content metadata properties in Azure AI Search indexers | https://learn.microsoft.com/en-us/azure/search/search-blob-metadata-properties |
| Configure API Management gateway for Azure OpenAI skills in Search | https://learn.microsoft.com/en-us/azure/search/search-how-to-configure-azure-openai-api-management |
| Configure Azure AI Search indexers for data ingestion | https://learn.microsoft.com/en-us/azure/search/search-how-to-create-indexers |
| Define and create search index schemas in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-how-to-create-search-index |
| Configure index projections for vectorized AI Search data | https://learn.microsoft.com/en-us/azure/search/search-how-to-define-index-projections |
| Delete documents from Azure AI Search indexes via APIs | https://learn.microsoft.com/en-us/azure/search/search-how-to-delete-documents |
| Configure delimitedText parsing for CSV blobs in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-how-to-index-azure-blob-csv |
| Configure JSON blob parsing for Azure AI Search indexers | https://learn.microsoft.com/en-us/azure/search/search-how-to-index-azure-blob-json |
| Index Markdown blobs with Azure AI Search blob indexer | https://learn.microsoft.com/en-us/azure/search/search-how-to-index-azure-blob-markdown |
| Configure one-to-many blob parsing for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-how-to-index-azure-blob-one-to-many |
| Set parsing modes for plain text blob indexing in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-how-to-index-azure-blob-plaintext |
| Configure Azure Cosmos DB NoSQL indexer for AI Search | https://learn.microsoft.com/en-us/azure/search/search-how-to-index-cosmosdb-sql |
| Configure Azure AI Search indexer for OneLake files | https://learn.microsoft.com/en-us/azure/search/search-how-to-index-onelake-files |
| Configure SharePoint Online indexer for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-how-to-index-sharepoint-online |
| Enable SQL Managed Instance connections for Azure AI Search indexers | https://learn.microsoft.com/en-us/azure/search/search-how-to-index-sql-managed-instance |
| Load and refresh data into Azure AI Search indexes | https://learn.microsoft.com/en-us/azure/search/search-how-to-load-search-index |
| Configure complex data types in Azure AI Search indexes | https://learn.microsoft.com/en-us/azure/search/search-howto-complex-data-types |
| Configure field mappings for Azure AI Search indexers | https://learn.microsoft.com/en-us/azure/search/search-indexer-field-mappings |
| Manage Azure AI Search services with Azure CLI | https://learn.microsoft.com/en-us/azure/search/search-manage-azure-cli |
| Manage Azure AI Search with PowerShell scripts | https://learn.microsoft.com/en-us/azure/search/search-manage-powershell |
| Manage Azure AI Search via Management REST API | https://learn.microsoft.com/en-us/azure/search/search-manage-rest |
| Configure Azure AI Search diagnostic logging | https://learn.microsoft.com/en-us/azure/search/search-monitor-enable-logging |
| Configure and monitor Azure AI Search queries | https://learn.microsoft.com/en-us/azure/search/search-monitor-queries |
| Use moreLikeThis query parameter in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-more-like-this |
| Configure text normalizers for filters, facets, and sort | https://learn.microsoft.com/en-us/azure/search/search-normalizers |
| Use OData collection operators in Azure AI Search filters | https://learn.microsoft.com/en-us/azure/search/search-query-odata-collection-operators |
| Use OData comparison operators in Azure AI Search filters | https://learn.microsoft.com/en-us/azure/search/search-query-odata-comparison-operators |
| Use OData geo-spatial functions in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-query-odata-geo-spatial-functions |
| Use OData logical operators in Azure AI Search filters | https://learn.microsoft.com/en-us/azure/search/search-query-odata-logical-operators |
| Configure OData $orderby in Azure AI Search queries | https://learn.microsoft.com/en-us/azure/search/search-query-odata-orderby |
| Use OData search.in function in Azure AI Search filters | https://learn.microsoft.com/en-us/azure/search/search-query-odata-search-in-function |
| Use OData search.score function in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-query-odata-search-score-function |
| Configure OData $select fields in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-query-odata-select |
| OData expression syntax for Azure AI Search queries | https://learn.microsoft.com/en-us/azure/search/search-query-odata-syntax-reference |
| Configure Azure AI Search indexer for JSON blob data | https://learn.microsoft.com/en-us/azure/search/search-semi-structured-data |
| Migrate Azure AI Search semantic ranking code | https://learn.microsoft.com/en-us/azure/search/semantic-code-migration |
| Configure semantic ranker settings for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/semantic-how-to-configure |
| Configure semantic ranker billing plans in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/semantic-how-to-enable-disable |
| Configure spell check in Azure AI Search queries | https://learn.microsoft.com/en-us/azure/search/speller-how-to-add |
| Create and configure custom analyzers in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/tutorial-create-custom-analyzer |
| Configure vectorizers and vector profiles in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/vector-search-how-to-configure-vectorizer |
| Configure vector indexes and fields in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/vector-search-how-to-create-index |
| Configure binary vector fields for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/vector-search-how-to-index-binary-data |
| Configure vector quantization in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/vector-search-how-to-quantization |
| Configure vector storage options in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/vector-search-how-to-storage-options |
| Configure integrated vectorization in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/vector-search-integrated-vectorization |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Create Azure SQL knowledge sources for agentic retrieval | https://learn.microsoft.com/en-us/azure/search/agentic-knowledge-source-how-to-azure-sql |
| Create blob knowledge sources for agentic retrieval | https://learn.microsoft.com/en-us/azure/search/agentic-knowledge-source-how-to-blob |
| Create Fabric Data Agent knowledge sources for live grounding | https://learn.microsoft.com/en-us/azure/search/agentic-knowledge-source-how-to-fabric-data-agent |
| Create Fabric Ontology knowledge sources for agentic retrieval | https://learn.microsoft.com/en-us/azure/search/agentic-knowledge-source-how-to-fabric-ontology |
| Create file-based knowledge sources for agentic retrieval | https://learn.microsoft.com/en-us/azure/search/agentic-knowledge-source-how-to-file |
| Create MCP server knowledge sources for agentic retrieval | https://learn.microsoft.com/en-us/azure/search/agentic-knowledge-source-how-to-mcp-server |
| Create OneLake knowledge sources for agentic retrieval | https://learn.microsoft.com/en-us/azure/search/agentic-knowledge-source-how-to-onelake |
| Create indexed SharePoint knowledge sources in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/agentic-knowledge-source-how-to-sharepoint-indexed |
| Create remote SharePoint knowledge sources for agentic retrieval | https://learn.microsoft.com/en-us/azure/search/agentic-knowledge-source-how-to-sharepoint-remote |
| Create web knowledge sources for agentic retrieval | https://learn.microsoft.com/en-us/azure/search/agentic-knowledge-source-how-to-web |
| Create Work IQ knowledge sources for organizational grounding | https://learn.microsoft.com/en-us/azure/search/agentic-knowledge-source-how-to-work-iq |
| Create knowledge bases for agentic retrieval in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/agentic-retrieval-how-to-create-knowledge-base |
| Migrate Azure AI Search agentic retrieval code | https://learn.microsoft.com/en-us/azure/search/agentic-retrieval-how-to-migrate |
| Integrate custom AML models as AI Search skills | https://learn.microsoft.com/en-us/azure/search/cognitive-search-aml-skill |
| Create Bing Entity Search custom skill in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-create-custom-skill-example |
| Define custom skill web interface for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-custom-skill-interface |
| Implement Custom Web API skill for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-custom-skill-web-api |
| Configure Azure OpenAI Embedding skill in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-azure-openai-embedding |
| Configure Conditional skill in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-conditional |
| Configure Document Extraction skill in AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-document-extraction |
| Configure Entity Linking skill in AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-entity-linking-v3 |
| Configure Entity Recognition v3 skill in AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-entity-recognition-v3 |
| Configure Key Phrase Extraction skill in AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-keyphrases |
| Configure Language Detection skill in AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-language-detection |
| Configure Named Entity Recognition v2 skill | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-named-entity-recognition |
| Configure OCR skill for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-ocr |
| Configure Sentiment v2 skill in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-sentiment |
| Configure Sentiment v3 skill in AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-sentiment-v3 |
| Configure Text Translation skill in AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-text-translation |
| Configure Text Merge skill in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-textmerger |
| Configure Azure Vision multimodal embeddings skill | https://learn.microsoft.com/en-us/azure/search/cognitive-search-skill-vision-vectorize |
| Connect Azure AI Search knowledge store to Power BI | https://learn.microsoft.com/en-us/azure/search/knowledge-store-connect-power-bi |
| Create Azure AI Search knowledge stores via REST APIs | https://learn.microsoft.com/en-us/azure/search/knowledge-store-create-rest |
| Implement complex projection shapes for knowledge stores | https://learn.microsoft.com/en-us/azure/search/knowledge-store-projection-example-long |
| Define knowledge store projections in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/knowledge-store-projections-examples |
| Use Lucene query syntax with Azure AI Search | https://learn.microsoft.com/en-us/azure/search/query-lucene-syntax |
| Construct OData expressions for Azure AI Search queries | https://learn.microsoft.com/en-us/azure/search/query-odata-filter-orderby-syntax |
| Use simple query syntax in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/query-simple-syntax |
| Implement autocomplete and suggestions in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-add-autocomplete-suggestions |
| Ingest Azure Blob RBAC scopes with search indexers | https://learn.microsoft.com/en-us/azure/search/search-blob-indexer-role-based-access |
| Index Azure Blob Storage content with Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-blob-storage-integration |
| Index Azure Files shares with Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-file-storage-integration |
| Author filter expressions for Azure AI Search queries | https://learn.microsoft.com/en-us/azure/search/search-filters |
| Create and configure Azure AI Search skillsets | https://learn.microsoft.com/en-us/azure/search/search-get-started-skillset |
| Use Python SDK and REST APIs for vector search | https://learn.microsoft.com/en-us/azure/search/search-get-started-vector |
| Use Azure.Search.Documents .NET client for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-how-to-dotnet-sdk |
| Index client-side encrypted blobs with Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-how-to-index-azure-blob-encrypted |
| Configure Azure Blob indexer for automated search indexing | https://learn.microsoft.com/en-us/azure/search/search-how-to-index-azure-blob-storage |
| Configure ADLS Gen2 indexer for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-how-to-index-azure-data-lake-storage |
| Configure Azure Table indexers for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-how-to-index-azure-tables |
| Index Azure Cosmos DB Gremlin data with AI Search | https://learn.microsoft.com/en-us/azure/search/search-how-to-index-cosmosdb-gremlin |
| Index Azure Cosmos DB for MongoDB with AI Search | https://learn.microsoft.com/en-us/azure/search/search-how-to-index-cosmosdb-mongodb |
| Configure Logic Apps workflows for Azure AI Search indexing | https://learn.microsoft.com/en-us/azure/search/search-how-to-index-logic-apps |
| Index Azure Database for MySQL with AI Search | https://learn.microsoft.com/en-us/azure/search/search-how-to-index-mysql |
| Configure Azure SQL indexer for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-how-to-index-sql-database |
| Configure REST-based integrated vectorization in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-how-to-integrated-vectorization |
| Page Azure AI Search list API results | https://learn.microsoft.com/en-us/azure/search/search-how-to-page-list-results |
| Use Document Layout skill for semantic chunking and vectorization | https://learn.microsoft.com/en-us/azure/search/search-how-to-semantic-chunking |
| Use Content Understanding skill for semantic chunking | https://learn.microsoft.com/en-us/azure/search/search-how-to-semantic-chunking-content-understanding |
| Ingest ADLS Gen2 ACL and RBAC metadata with indexers | https://learn.microsoft.com/en-us/azure/search/search-indexer-access-control-lists-and-role-based-access |
| Ingest SharePoint ACL metadata using Azure AI Search indexers | https://learn.microsoft.com/en-us/azure/search/search-indexer-sharepoint-access-control-lists |
| Implement C# indexer integration with Azure SQL and Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-indexer-tutorial |
| Visualize Azure AI Search logs and metrics in Power BI | https://learn.microsoft.com/en-us/azure/search/search-monitor-logs-powerbi |
| Implement fuzzy search and typo tolerance in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-query-fuzzy |
| Use Lucene query syntax in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-query-lucene-examples |
| Use OData $filter in Azure AI Search queries | https://learn.microsoft.com/en-us/azure/search/search-query-odata-filter |
| Use OData full-text search functions in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-query-odata-full-text-search-functions |
| Query partial terms and patterns in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-query-partial-matching |
| Use simple query syntax in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/search-query-simple-examples |
| Combine scoring profiles with semantic ranking in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/semantic-how-to-enable-scoring-profiles |
| Invoke semantic ranking in Azure AI Search queries | https://learn.microsoft.com/en-us/azure/search/semantic-how-to-query-request |
| Implement semantic query rewriting with Azure AI Search | https://learn.microsoft.com/en-us/azure/search/semantic-how-to-query-rewrite |
| Integrate Azure AI Search queries in .NET apps | https://learn.microsoft.com/en-us/azure/search/tutorial-csharp-search-query-integration |
| Index multiple Azure data sources into one search index | https://learn.microsoft.com/en-us/azure/search/tutorial-multiple-data-sources |
| Apply filters and modes to Azure AI vector queries | https://learn.microsoft.com/en-us/azure/search/vector-search-filters |
| Generate and integrate embeddings for Azure AI Search indexes | https://learn.microsoft.com/en-us/azure/search/vector-search-how-to-generate-embeddings |
| Create and send vector queries in Azure AI Search | https://learn.microsoft.com/en-us/azure/search/vector-search-how-to-query |
| Integrate Microsoft Foundry embedding models with Azure AI Search | https://learn.microsoft.com/en-us/azure/search/vector-search-integrated-vectorization-ai-studio |
| Configure Azure Vision vectorizer for AI Search | https://learn.microsoft.com/en-us/azure/search/vector-search-vectorizer-ai-services-vision |
| Configure Foundry model catalog vectorizer | https://learn.microsoft.com/en-us/azure/search/vector-search-vectorizer-azure-machine-learning-ai-studio-catalog |
| Configure Azure OpenAI vectorizer for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/vector-search-vectorizer-azure-open-ai |
| Build Custom Web API vectorizer for Azure AI Search | https://learn.microsoft.com/en-us/azure/search/vector-search-vectorizer-custom-web-api |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy Azure AI Search with ARM templates | https://learn.microsoft.com/en-us/azure/search/search-get-started-arm |
| Deploy Azure AI Search using Bicep | https://learn.microsoft.com/en-us/azure/search/search-get-started-bicep |
| Provision Azure AI Search with Terraform | https://learn.microsoft.com/en-us/azure/search/search-get-started-terraform |
| Move Azure AI Search services across regions | https://learn.microsoft.com/en-us/azure/search/search-howto-move-across-regions |
| Check Azure AI Search regional feature availability | https://learn.microsoft.com/en-us/azure/search/search-region-support |
| Deploy Azure AI Search app to Static Web Apps | https://learn.microsoft.com/en-us/azure/search/tutorial-csharp-deploy-static-web-app |