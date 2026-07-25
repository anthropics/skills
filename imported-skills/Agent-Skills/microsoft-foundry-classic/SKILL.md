---
name: microsoft-foundry-classic
description: Expert knowledge for Microsoft Foundry Classic (aka Azure AI Foundry classic) development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when configuring Foundry agents/models, Azure OpenAI/RAG, multi-agent routing, secure endpoints, or CI/CD deployments, and other Microsoft Foundry Classic related development tasks. Not for Microsoft Foundry (use microsoft-foundry), Microsoft Foundry Local (use microsoft-foundry-local), Microsoft Foundry Tools (use microsoft-foundry-tools).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Microsoft Foundry Classic Skill

This skill provides expert guidance for Microsoft Foundry Classic. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L46 | Diagnosing and fixing Foundry classic issues: prompt flow compute, deployments/monitoring, private endpoints, Azure OpenAI (incl. fine-tuning), risks & safety alerts, and known portal bugs. |
| Best Practices | L47-L61 | Best practices for designing system/safety prompts, fine-tuning and using GPT/DeepSeek models, optimizing latency/throughput, and evaluating/operating Foundry chat apps in production |
| Decision Making | L62-L90 | Guides for choosing and comparing Foundry/Azure OpenAI models, regions, deployments, billing and PTU sizing, and planning migrations, lifecycle, versioning, and model retirement. |
| Architecture & Design Patterns | L91-L98 | Designing multi-agent architectures, configuring Foundry Agent Service for resilience, and understanding model router behavior, failover, and disaster recovery strategies. |
| Limits & Quotas | L99-L114 | Quotas, rate limits, and regional availability for Foundry agents and models (incl. Azure OpenAI/Claude), plus how to manage, request, and increase deployment and throughput limits. |
| Security | L115-L161 | Security, privacy, and compliance for Foundry: auth/RBAC, encryption keys, networks/Private Link, Azure Policy guardrails, content filters, PII, copyright, and data handling for models and tools. |
| Configuration | L162-L215 | Configuring and monitoring Foundry classic: agents, evaluators, models, compute, networking, storage, tracing, Azure OpenAI, RAG indexes, and continuous quality/safety evaluation. |
| Integrations & Coding Patterns | L216-L327 | Patterns and code for integrating Foundry/ Azure OpenAI agents and models with tools, data sources, SDKs, search/grounding, function calling, realtime audio, fine-tuning, and external services. |
| Deployment | L328-L348 | Deploying and managing Foundry models, hubs, and workflows across Azure (CLI, Bicep, Terraform, portal), including serverless/managed endpoints, CI/CD evaluations, regions, and feature availability. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Prompt Flow compute session issues in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/prompt-flow-troubleshoot |
| Troubleshoot Foundry deployments and monitoring issues | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/troubleshoot-deploy-and-monitor |
| Troubleshoot Foundry private endpoint connection errors | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/troubleshoot-secure-connection-project |
| Troubleshoot Azure OpenAI fine-tuning in Foundry classic | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/fine-tuning-troubleshoot |
| Monitor and troubleshoot Risks & Safety in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/risks-safety-monitor |
| Resolve known issues in Microsoft Foundry classic portal | https://learn.microsoft.com/en-us/azure/foundry-classic/reference/foundry-known-issues |

### Best Practices
| Topic | URL |
|-------|-----|
| Deploy and use DeepSeek-R1 reasoning model in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/tutorials/get-started-deepseek-r1 |
| Design effective system messages for Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/concepts/advanced-prompt-engineering |
| Apply safety system message templates in Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/concepts/safety-system-message-templates |
| Author safety system messages for Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/concepts/system-message |
| Apply safety evaluation when fine-tuning Foundry models | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/fine-tuning-safety-evaluation |
| Fine-tune GPT-4 vision models with image data | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/fine-tuning-vision |
| Optimize Azure OpenAI latency and throughput in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/latency |
| Apply best practices for Azure OpenAI On Your Data | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/on-your-data-best-practices |
| Optimize Azure OpenAI predicted outputs for latency | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/predicted-outputs |
| Operate Foundry provisioned throughput in production | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/provisioned-get-started |
| Evaluate and improve Foundry-based chat apps with SDK | https://learn.microsoft.com/en-us/azure/foundry-classic/tutorials/copilot-sdk-evaluate |

### Decision Making
| Topic | URL |
|-------|-----|
| Select Azure OpenAI models and regions for Foundry Agents | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/concepts/model-region-support |
| Decide when and how to fine-tune models in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/fine-tuning-overview |
| Compare Foundry models using benchmarks and leaderboards | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/model-benchmarks |
| Manage lifecycle of managed compute Foundry models | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/model-retirement-managed-compute |
| Choose the right Azure resource type for Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/resource-types |
| Choose Microsoft Foundry deployment types | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/concepts/deployment-types |
| Plan and manage model versioning in Foundry Models | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/concepts/model-versions |
| Plan and manage model versioning in Foundry Models | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/concepts/model-versions |
| Select Azure-sold Foundry models by capability | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/concepts/models-sold-directly-by-azure |
| Choose Foundry models by Azure region availability | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/concepts/models-sold-directly-by-azure-region-availability |
| Choose between GPT-5 and GPT-4.1 in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/how-to/model-choice-guide |
| Compare models with Foundry leaderboards | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/benchmark-model-in-catalog |
| Plan and manage costs for Microsoft Foundry hubs | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/costs-plan-manage |
| Migrate from hub-based to new Foundry projects | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/migrate-project |
| Decide and plan migration from Prompt Flow to Agent Framework | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/prompt-flow-migration-overview |
| Choose content streaming and filtering modes in Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/concepts/content-streaming |
| Plan migrations using Foundry model retirement schedule | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/concepts/model-retirement-schedule |
| Plan around Foundry model lifecycle and support | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/concepts/model-retirements |
| Evaluate 2024 Azure OpenAI provisioned throughput updates | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/concepts/provisioned-migration |
| Choose billing options for Foundry PTU deployments | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/concepts/provisioned-throughput-billing |
| Handle retired Foundry models and alternatives | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/concepts/retired-models |
| Plan using your data with Azure OpenAI deployments | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/concepts/use-your-data |
| Size provisioned throughput units for Foundry workloads | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/provisioned-throughput-sizing |
| Migrate from preview to GA Realtime API protocol | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/realtime-audio-preview-api-migration-guide |
| Decide migration path from stored completions to Responses API | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/stored-completions-retirement |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design multi-agent systems with Foundry connected agents | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/connected-agents |
| Plan disaster recovery for Foundry Agent Service | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/agent-service-disaster-recovery |
| Recover Foundry Agent Service from resource and data loss | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/agent-service-operator-disaster-recovery |
| Recover Foundry Agent Service from platform outages | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/agent-service-platform-disaster-recovery |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Review quotas and limits for Foundry Agent Service | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/quotas-limits |
| Evaluate Foundry classic with regional limits and quotas | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/evaluation-regions-limits-virtual-network |
| Compare Claude model capabilities, quotas, and regions in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/concepts/claude-models |
| Reference quotas and limits for Foundry Models | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/quotas-limits |
| Manage and request quotas for Microsoft Foundry hub resources | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/hub-quota |
| Manage and increase model deployment quotas in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/quota |
| Understand Foundry provisioned throughput limits and quotas | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/concepts/provisioned-throughput |
| Use Azure OpenAI global batch processing quotas | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/batch |
| Use dynamic quota for Azure OpenAI deployments | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/dynamic-quota |
| Manage Azure OpenAI quota and rate limits in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/quota |
| Use reinforcement fine-tuning with Azure OpenAI reasoning models | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/reinforcement-fine-tuning |
| Reference Azure OpenAI quotas and limits in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/quotas-limits |

### Security
| Topic | URL |
|-------|-----|
| Configure Browser Automation tool securely for Foundry agents | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/browser-automation |
| Securely use Foundry Computer Use tool with agents | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/computer-use |
| Configure authentication and authorization for Microsoft Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/authentication-authorization-foundry |
| Configure customer-managed keys for Foundry encryption | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/encryption-keys-portal |
| Configure customer-managed keys for Foundry hub projects | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/hub-encryption-keys-portal |
| Configure RBAC for Microsoft Foundry hubs and projects | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/hub-rbac-foundry |
| Configure guardrails for Azure-sold Foundry models | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/model-catalog-content-safety |
| Configure RBAC roles for Microsoft Foundry projects | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/rbac-foundry |
| Understand vulnerability management for Microsoft Foundry images | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/vulnerability-management |
| Use default safety policies for Foundry Models | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/concepts/default-safety-policies |
| Create custom Azure Policies to restrict Foundry model deployments | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/how-to/configure-deployment-policies |
| Configure keyless Entra ID authentication for Foundry models | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/how-to/configure-entra-id |
| Allow Foundry managed networks to access on-premises resources | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/access-on-premises-resources |
| Associate Foundry resources with a network security perimeter | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/add-foundry-to-network-security-perimeter |
| Apply Azure Policy to govern Foundry hubs and projects | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/azure-policy |
| Control Foundry model deployments with Azure Policy | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/built-in-policy-model-deployment |
| Understand data handling and privacy in Foundry models | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/concept-data-privacy |
| Configure managed network isolation for Foundry hubs | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/configure-managed-network |
| Configure private link for secure Foundry projects | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/configure-private-link |
| Create and manage a Microsoft Foundry hub securely | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/create-azure-ai-resource |
| Create a secure Microsoft Foundry hub with managed VNet | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/create-secure-ai-hub |
| Create custom Azure Policy definitions for Foundry resources | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/custom-policy-definition |
| Disable shared key access to Foundry hub storage | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/disable-local-auth |
| Configure storage accounts and access for Foundry evaluations | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/evaluations-storage-account |
| Configure Private Link for Microsoft Foundry hubs | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/hub-configure-private-link |
| Set up managed virtual networks for Foundry projects | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/managed-virtual-network |
| Use Azure Policy to govern Foundry model deployments | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/model-deployment-policy |
| Secure configuration for Foundry playground chat on your data | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/secure-data-playground |
| Set up Azure Key Vault connection for Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/set-up-key-vault-connection |
| Use Content Credentials for Azure OpenAI images | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/concepts/content-credentials |
| Configure and use PII filtering in Foundry OpenAI | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/concepts/content-filter-personal-information |
| Understand default Guardrail safety policies in Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/concepts/default-safety-policies |
| Understand Azure OpenAI prompt transformation for image safety | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/concepts/prompt-transformation |
| Configure Azure OpenAI content filters and gating | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/content-filters |
| Configure Microsoft Entra ID auth for Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/managed-identity |
| Secure Azure OpenAI with virtual networks and private endpoints | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/network |
| Add Azure OpenAI to a network security perimeter | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/network-security-perimeter |
| Apply Azure RBAC roles to Azure OpenAI resources | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/role-based-access-control |
| Configure custom block lists for Azure OpenAI content filtering | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/use-blocklists |
| Configure data privacy and security for Claude in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/responsible-ai/claude-models/data-privacy |
| Apply copyright commitment mitigations for Azure OpenAI in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/responsible-ai/openai/customer-copyright-commitment |
| Understand data privacy and security for Foundry Models | https://learn.microsoft.com/en-us/azure/foundry-classic/responsible-ai/openai/data-privacy |
| Apply limited access policy for Azure OpenAI in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/responsible-ai/openai/limited-access |

### Configuration
| Topic | URL |
|-------|-----|
| Configure and manage Foundry classic capability hosts | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/concepts/capability-hosts |
| Configure standard agent resources for Foundry Agent Service | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/concepts/standard-agent-setup |
| Monitor Foundry Agent Service with Azure Monitor and KQL | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/metrics |
| Connect and configure your own Azure resources for Foundry agents | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/use-your-own-resources |
| Configure private networking for Foundry Agent Service | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/virtual-networks |
| Use Azure Monitor metrics and logs for Foundry Agent Service | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/reference/monitor-service |
| Configure and use built-in Foundry evaluators | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/built-in-evaluators |
| Configure agent evaluators for Azure AI agents | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/evaluation-evaluators/agent-evaluators |
| Use Azure OpenAI graders for model evaluation | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/evaluation-evaluators/azure-openai-graders |
| Create and configure custom evaluators in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/evaluation-evaluators/custom-evaluators |
| Configure general-purpose evaluators for generative AI | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/evaluation-evaluators/general-purpose-evaluators |
| Configure RAG evaluators for relevance and groundedness | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/evaluation-evaluators/rag-evaluators |
| Configure risk and safety evaluators in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/evaluation-evaluators/risk-safety-evaluators |
| Use textual similarity evaluators in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/evaluation-evaluators/textual-similarity-evaluators |
| Configure and use endpoints for Foundry Models | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/concepts/endpoints |
| Configure Foundry model content filters and gated changes | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/how-to/configure-content-filters |
| Configure Foundry Models project connection settings | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/how-to/configure-project-connection |
| Configure Azure Monitor for Foundry model deployments | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/how-to/monitor-models |
| Upgrade AI project to use Foundry model deployments | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/how-to/quickstart-ai-project |
| Configure and use MAI image models in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/how-to/use-foundry-models-mai |
| Select SDKs and languages for Foundry Models | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/supported-languages |
| Configure bring-your-own Azure Storage for Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/bring-your-own-azure-storage-foundry |
| Configure BYOS for Speech and Language in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/bring-your-own-azure-storage-speech-language-services |
| Set up continuous evaluation for AI agents in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/continuous-evaluation-agents |
| Configure and manage Foundry compute instances | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/create-manage-compute |
| Configure and manage Foundry prompt flow compute sessions | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/create-manage-compute-session |
| Add and manage data in Foundry hub-based projects | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/data-add |
| Configure cross-project access to serverless model APIs | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/deploy-models-serverless-connect |
| Create a Foundry hub via Azure ML SDK and CLI | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/develop/create-hub-project-sdk |
| Configure tools and SDKs for Foundry classic development | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/develop/install-cli-sdk |
| Generate synthetic and simulated data for Foundry evaluation | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/develop/simulator-interaction-data |
| Trace and observe Foundry agents with OpenTelemetry | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/develop/trace-agents-sdk |
| Enable tracing and feedback for prompt flow deployments | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/develop/trace-production-sdk |
| Hide Foundry preview features using Azure tags | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/disable-preview-features |
| Create and use vector indexes for RAG in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/index-add |
| Configure continuous monitoring for Foundry AI applications | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/monitor-applications |
| Monitor quality and token usage for prompt flow apps | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/monitor-quality-safety |
| Configure and use Azure OpenAI v1 API in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/api-version-lifecycle |
| Enable and interpret Prompt Shields in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/concepts/content-filter-prompt-shields |
| Automate Azure OpenAI deployments and TPM quota | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/automate-quota-deployments |
| Configure Azure Blob Storage for OpenAI Batch I/O | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/batch-blob-storage |
| Configure and run Azure OpenAI model evaluations | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/evaluations |
| Apply direct preference optimization to Azure OpenAI models | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/fine-tuning-direct-preference-optimization |
| Configure monitoring and logging for Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/monitor-openai |
| Configure network and access for On Your Data | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/on-your-data-configuration |
| Configure prompt caching for Azure OpenAI requests | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/prompt-caching |
| Configure reproducible output for Azure OpenAI chats | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/reproducible-output |
| Configure spillover traffic for Foundry provisioned deployments | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/spillover-traffic-management |
| Configure stored completions and distillation in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/stored-completions |
| Reference Azure OpenAI monitoring metrics and logs | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/monitor-openai-reference |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Connect Foundry agents to existing Azure AI Search indexes | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/azure-ai-search |
| Ground Foundry agents with Azure AI Search content | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/azure-ai-search-samples |
| Integrate Azure Functions as tools with Foundry Agent Service | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/azure-functions |
| Use Azure Functions and Storage Queues with Foundry agents | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/azure-functions-samples |
| Use Bing Search grounding tool with code samples | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/bing-code-samples |
| Configure Custom Bing Search grounding for agents | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/bing-custom-search |
| Call Custom Bing Search grounding tool from code | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/bing-custom-search-samples |
| Ground Foundry agents with Bing Search results | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/bing-grounding |
| Automate website tasks with Foundry Browser Automation tool | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/browser-automation-samples |
| Run Python code with Foundry Code Interpreter tool | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/code-interpreter |
| Use Computer Use tool with Azure AI Projects SDK | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/computer-use-samples |
| Configure deprecated Deep Research tool for agents | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/deep-research |
| Integrate Deep Research tool with Azure AI Projects SDK | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/deep-research-samples |
| Integrate Foundry classic agents with Microsoft Fabric data | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/fabric |
| Configure and use Foundry file search tool | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/file-search |
| Upload files to Foundry file search from code | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/file-search-upload-files |
| Implement function calling with Foundry Agent Service | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/function-calling |
| Connect Foundry agents to external MCP servers | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/model-context-protocol |
| MCP server integration code samples for Foundry agents | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/model-context-protocol-samples |
| Configure OpenAPI tools and auth for Foundry agents | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/openapi-spec |
| Use OpenAPI-based tools with Foundry agents in code | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/openapi-spec-samples |
| Use SharePoint content as a tool in Foundry classic agents | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/sharepoint |
| Use SharePoint grounding tool with Foundry agents | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/tools-classic/sharepoint-samples |
| Trigger Foundry classic agents from Azure Logic Apps events | https://learn.microsoft.com/en-us/azure/foundry-classic/agents/how-to/triggers |
| Serverless API inference examples for Foundry Models | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/models-inference-examples |
| Call Foundry Responses API for text generation | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/how-to/generate-responses |
| Use reasoning models with Foundry Models service | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/how-to/use-chat-reasoning |
| Generate text embeddings with Foundry Models | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/how-to/use-embeddings |
| Deploy and integrate Anthropic Claude in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/how-to/use-foundry-models-claude |
| Deploy and use FLUX image models in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/how-to/use-foundry-models-flux |
| Generate image embeddings with Foundry Models | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/how-to/use-image-embeddings |
| Use structured outputs with Foundry chat models | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/how-to/use-structured-outputs |
| Configure project connections in Foundry classic | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/connections-add |
| Run local evaluations with Azure AI Evaluation SDK | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/develop/evaluate-sdk |
| Integrate LangChain with Microsoft Foundry models | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/develop/langchain |
| Connect LangGraph and LangChain apps to Foundry agents | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/develop/langchain-agents |
| Use LlamaIndex with Microsoft Foundry deployments | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/develop/llama-index |
| Run AI Red Teaming Agent in the cloud with Foundry SDK | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/develop/run-ai-red-teaming-cloud |
| Run AI Red Teaming Agent locally with Azure AI SDK | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/develop/run-scans-ai-red-teaming-agent |
| Choose and use Microsoft Foundry SDKs and endpoints | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/develop/sdk-overview |
| Use Semantic Kernel with Foundry model catalog | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/develop/semantic-kernel |
| View OpenAI SDK traces with OpenTelemetry in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/develop/trace-application |
| Configure MCP server tools for Foundry agents in VS Code | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/develop/vs-code-agents-mcp |
| Deploy and use CXRReportGen healthcare AI model | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/healthcare-ai/deploy-cxrreportgen |
| Deploy and invoke MedImageInsight embeddings model | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/healthcare-ai/deploy-medimageinsight |
| Use MedImageParse medical image segmentation models | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/healthcare-ai/deploy-medimageparse |
| Rebuild Prompt Flow workflows using Agent Framework | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/how-to-migrate-prompt-flow-to-agent-framework |
| Create and manage hub-scoped connections in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/hub-connections-add |
| Migrate Azure AI Inference SDK apps to OpenAI SDK | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/model-inference-to-openai-migration |
| Use image-to-text models from Foundry catalog | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/use-image-models |
| Get started with Azure OpenAI audio generation | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/audio-completions-quickstart |
| Interpret Guardrail annotations for Azure OpenAI in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/concepts/content-filter-annotations |
| Format prompts with document embeddings for Guardrails in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/concepts/content-filter-document-embedding |
| Use groundedness detection for RAG in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/concepts/content-filter-groundedness |
| Apply protected material detection to LLM outputs in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/concepts/content-filter-protected-material |
| Create Azure OpenAI Assistants with tools in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/assistant |
| Implement Assistants function calling in Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/assistant-functions |
| Trigger Azure Logic Apps from Foundry Assistants | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/assistants-logic-apps |
| Work with Azure OpenAI chat completion models | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/chatgpt |
| Run code with Azure OpenAI Assistants Code Interpreter | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/code-interpreter |
| Use Codex CLI and VS Code with Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/codex |
| Implement Computer Use agents in Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/computer-use |
| Use Azure OpenAI image generation and editing APIs | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/dall-e |
| Run deep research using Azure OpenAI Responses API | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/deep-research |
| Migrate from Azure.AI.OpenAI .NET 1.x beta to 2.x | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/dotnet-migration |
| Generate and use embeddings with Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/embeddings |
| Test fine-tuned models using Chat Completions and Evaluations | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/fine-tune-test |
| Fine-tune Foundry models via Python, REST, or portal | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/fine-tuning |
| Fine-tune Azure OpenAI function calling in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/fine-tuning-functions |
| Implement function calling with Azure OpenAI in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/function-calling |
| Use Azure OpenAI vision-enabled chat models via API | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/gpt-with-vision |
| Configure Azure OpenAI JSON mode responses | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/json-mode |
| Migrate Azure OpenAI apps to OpenAI Python v1.x | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/migration |
| Migrate Azure OpenAI apps to OpenAI JavaScript v4 | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/migration-javascript |
| Integrate GPT Realtime audio via SIP in Azure | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/realtime-audio-sip |
| Use Azure OpenAI GPT Realtime via WebRTC | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/realtime-audio-webrtc |
| Connect to GPT Realtime audio using WebSockets | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/realtime-audio-websockets |
| Use Azure OpenAI Responses API in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/responses |
| Use structured outputs and JSON Schema with Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/structured-outputs |
| Switch Python code between OpenAI and Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/switching-endpoints |
| Configure web_search tool with Azure Responses API | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/web-search |
| Configure Azure OpenAI webhooks for API events | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/webhooks |
| Integrate Azure OpenAI fine-tuning with Weights & Biases | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/weights-and-biases-integration |
| Use Azure OpenAI v1 REST API in Foundry Models | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/latest |
| Use Azure OpenAI v1 REST API in Foundry Models | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/latest |
| Use Azure OpenAI v1 REST API in Foundry Models | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/latest |
| Use Azure OpenAI v1 REST API in Foundry Models | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/latest |
| Use Azure OpenAI v1 REST API in Foundry Models | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/latest |
| Use Azure OpenAI v1 REST API in Foundry Models | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/latest |
| Use Azure OpenAI v1 REST API in Foundry Models | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/latest |
| Use Azure OpenAI v1 REST API in Foundry Models | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/latest |
| Use Azure OpenAI v1 REST API in Foundry Models | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/latest |
| Use realtime audio events with Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/realtime-audio-reference |
| Implement GA realtime audio events in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/realtime-audio-reference-ga |
| Call Azure OpenAI image and audio REST APIs | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/reference |
| Integrate with Azure OpenAI preview REST APIs | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/reference-preview |
| Use Azure OpenAI v1 preview REST APIs | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/reference-preview-latest |
| Call Azure OpenAI on Azure Search data via API | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/references/azure-search |
| Use Azure OpenAI with Azure Cosmos DB data APIs | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/references/cosmos-db |
| Integrate Azure OpenAI with Elasticsearch data via API | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/references/elasticsearch |
| Use Azure OpenAI with MongoDB Atlas via API | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/references/mongo-db |
| Call Azure OpenAI On Your Data via Python and REST | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/references/on-your-data |
| Integrate Azure OpenAI with Pinecone vector data | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/references/pinecone |
| Convert text to speech with Azure OpenAI voices | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/text-to-speech-quickstart |
| Fine-tune gpt-4o-mini on Azure OpenAI in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/tutorials/fine-tune |
| Transcribe speech with Azure OpenAI Whisper | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/whisper-quickstart |
| Use Foundry SDK to deploy a model and chat app | https://learn.microsoft.com/en-us/azure/foundry-classic/quickstarts/hub-get-started-code |
| Build a RAG chat app with Microsoft Foundry SDK | https://learn.microsoft.com/en-us/azure/foundry-classic/tutorials/copilot-sdk-build-rag |

### Deployment
| Topic | URL |
|-------|-----|
| Evaluate deployment options for Foundry Models | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/deployments-overview |
| Plan organization-wide deployment of Microsoft Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/concepts/planning |
| Deploy Foundry Models using Azure CLI and Bicep | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/how-to/create-model-deployments |
| Deploy Foundry Models via Microsoft Foundry portal | https://learn.microsoft.com/en-us/azure/foundry-classic/foundry-models/how-to/deploy-foundry-models |
| Deploy a Microsoft Foundry hub using Bicep | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/create-azure-ai-hub-template |
| Provision a Foundry hub and project with Terraform | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/create-hub-terraform |
| Provision Microsoft Foundry classic resources with Terraform | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/create-resource-terraform |
| Deploy models with managed compute in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/deploy-models-managed |
| Deploy Hugging Face Hub models to Foundry managed endpoints | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/deploy-models-managed-hugging-face |
| Deploy models as serverless APIs in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/deploy-models-serverless |
| Run Foundry evaluations in Azure DevOps pipelines | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/evaluation-azure-devops |
| Run Foundry evaluations in GitHub Actions pipelines | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/evaluation-github-action |
| Deploy fine-tuned models via serverless API in Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/fine-tune-serverless |
| Deploy Foundry prompt flows as managed online endpoints | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/flow-deploy |
| Deploy and operate Agent Framework workflows on Azure | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/how-to-deploy-migrated-agent-framework-workflow |
| Upgrade Azure OpenAI resources to Foundry | https://learn.microsoft.com/en-us/azure/foundry-classic/how-to/upgrade-azure-openai |
| Deploy fine-tuned Azure OpenAI models in Foundry classic | https://learn.microsoft.com/en-us/azure/foundry-classic/openai/how-to/fine-tuning-deploy |
| Check Microsoft Foundry feature availability by region | https://learn.microsoft.com/en-us/azure/foundry-classic/reference/region-support |