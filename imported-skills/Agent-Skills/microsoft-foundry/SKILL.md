---
name: microsoft-foundry
description: Expert knowledge for Microsoft Foundry (aka Azure AI Foundry) development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when building Foundry agents with IQ retrieval, azure.yaml configs, M365/Teams apps, Azure OpenAI, or realtime APIs, and other Microsoft Foundry related development tasks. Not for Microsoft Foundry Classic (use microsoft-foundry-classic), Microsoft Foundry Local (use microsoft-foundry-local), Microsoft Foundry Tools (use microsoft-foundry-tools).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Microsoft Foundry Skill

This skill provides expert guidance for Microsoft Foundry. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L47 | Diagnosing and fixing hosted agent and partner model issues, log-based troubleshooting, recovery from data/resource loss, webhook problems, and known Foundry service errors/workarounds. |
| Best Practices | L48-L66 | Best practices for designing, optimizing, testing, evaluating, and safely operating Foundry agents, including prompts, tools, routing, retrieval, human evals, and performance. |
| Decision Making | L67-L110 | Guides for choosing Foundry models, deployments, networking, costs, lifecycle, and migration/upgrade paths (agents, portals, APIs, PTU) across Azure and Azure Government. |
| Architecture & Design Patterns | L111-L118 | Patterns for network/subnet design, private retrieval with Foundry IQ, shared session pooling, and high-availability architectures for Foundry agents. |
| Limits & Quotas | L119-L137 | Quotas, rate limits, regions, and lifecycle for Foundry and Azure OpenAI models/agents, including sessions, vector stores, evaluations, caching, costs, and government/enterprise options. |
| Security | L138-L183 | Security, identity, RBAC, networking, guardrails, data privacy, compliance, and policy controls for securing Foundry agents, models, tools, and infrastructure. |
| Configuration | L184-L255 | Configuring and operating Foundry agents and models: schemas, azure.yaml, tools/skills, networking, security/guardrails, monitoring, tracing, evaluations, and Azure OpenAI integration. |
| Integrations & Coding Patterns | L256-L337 | Patterns and code to integrate Foundry agents and models into apps: SDK usage, tools/MCP, knowledge bases, external services (Azure/OpenAI/Fabric/M365), routing, tracing, fine-tuning, and realtime APIs. |
| Deployment | L338-L363 | Deploying and publishing Foundry agents and models: azd setup, containers, registries, CI/CD, workflows, evaluations, red teaming, M365/Teams integration, and healthcare/premium models. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Check hosted agent project health with agent doctor | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/agent-doctor |
| Diagnose and fix common hosted agent issues | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/debug-hosted-agent |
| Monitor and troubleshoot Foundry hosted agent logs | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/monitor-hosted-agent-logs |
| Recover Foundry Agent Service from resource and data loss | https://learn.microsoft.com/en-us/azure/foundry/how-to/agent-service-operator-disaster-recovery |
| Troubleshoot Foundry evaluation and observability issues | https://learn.microsoft.com/en-us/azure/foundry/observability/how-to/troubleshooting |
| Set up and troubleshoot Azure OpenAI webhooks | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/webhooks |
| Known issues and workarounds for Microsoft Foundry services | https://learn.microsoft.com/en-us/azure/foundry/reference/foundry-known-issues |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply tool usage best practices in Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/agents/concepts/tool-best-practice |
| Validate private agentic retrieval and grounded responses | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/foundry-iq-tutorial-private-retrieval |
| Test hosted agents with unit and integration suites | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/test-hosted-agent |
| Optimize hosted agent instructions with Agent Optimizer | https://learn.microsoft.com/en-us/azure/foundry/agents/quickstarts/quickstart-optimize-hosted-agent |
| Use Task Adherence signals for Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/guardrails/task-adherence |
| Evaluate Microsoft Foundry agents with built-in metrics | https://learn.microsoft.com/en-us/azure/foundry/observability/how-to/evaluate-agent |
| Configure human evaluation workflows for Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/observability/how-to/human-evaluation |
| Improve Foundry agent prompts with Prompt Optimizer | https://learn.microsoft.com/en-us/azure/foundry/observability/how-to/prompt-optimizer |
| Design effective system messages for Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry/openai/concepts/advanced-prompt-engineering |
| Apply prompt engineering techniques for vision-enabled GPT models | https://learn.microsoft.com/en-us/azure/foundry/openai/concepts/gpt-4-v-prompt-engineering |
| Apply routing modes and best practices for model router | https://learn.microsoft.com/en-us/azure/foundry/openai/concepts/model-router-how-it-works |
| Apply safety system message templates in Foundry | https://learn.microsoft.com/en-us/azure/foundry/openai/concepts/safety-system-message-templates |
| Fine-tune GPT-4 vision models with images | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/fine-tuning-vision |
| Optimize Azure OpenAI latency and throughput in Foundry | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/latency |
| Operate provisioned throughput deployments in production | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/provisioned-get-started |

### Decision Making
| Topic | URL |
|-------|-----|
| Check Foundry Agent Service feature availability in Azure Government | https://learn.microsoft.com/en-us/azure/foundry/agents/concepts/azure-government |
| Choose networking options for Foundry Agent Service | https://learn.microsoft.com/en-us/azure/foundry/agents/concepts/networking-options |
| Decide how to migrate to the new Foundry Agent Service | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/migrate |
| Migrate legacy Agent Applications to new model | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/migrate-agent-applications |
| Migrate Foundry hosted agents from preview to latest backend | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/migrate-hosted-agent-preview |
| Choose the right web grounding tool for Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/web-overview |
| Choose the right Microsoft Foundry build approach | https://learn.microsoft.com/en-us/azure/foundry/concepts/choose-build-approach |
| Plan migration to the GA Microsoft Foundry portal | https://learn.microsoft.com/en-us/azure/foundry/concepts/general-availability |
| Plan and manage Microsoft Foundry cost usage | https://learn.microsoft.com/en-us/azure/foundry/concepts/manage-costs |
| Optimize Foundry model cost and performance | https://learn.microsoft.com/en-us/azure/foundry/control-plane/how-to-optimize-cost-performance |
| Understand Claude CCU billing and migration in Foundry | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/concepts/claude-models-billing |
| Compare Azure vs Anthropic hosting for Claude models | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/concepts/claude-models-hosting-comparison |
| Choose Microsoft Foundry model deployment types | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/concepts/deployment-types |
| Choose Foundry deployment types in Azure Government | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/concepts/deployment-types-gov |
| Manage model versioning and upgrade policies in Foundry | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/concepts/model-versions |
| Choose and manage model version policies in Foundry Gov | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/concepts/model-versions-gov |
| Choose partner and community Foundry models | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/concepts/models-from-partners |
| Select Azure-sold Foundry models by capabilities | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/concepts/models-sold-directly-by-azure |
| Select Azure-sold Foundry models by region and deployment type | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/concepts/models-sold-directly-by-azure-region-availability |
| Upgrade GitHub Models workloads to Foundry Models | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/how-to/quickstart-github-models |
| Plan disaster recovery for Foundry Agent Service | https://learn.microsoft.com/en-us/azure/foundry/how-to/agent-service-disaster-recovery |
| Use Foundry model leaderboard for selection | https://learn.microsoft.com/en-us/azure/foundry/how-to/benchmark-model-in-catalog |
| Select and deploy Microsoft Foundry AI templates | https://learn.microsoft.com/en-us/azure/foundry/how-to/develop/ai-template-get-started |
| Interpret and compare Foundry evaluation results | https://learn.microsoft.com/en-us/azure/foundry/how-to/evaluate-results |
| Select and use healthcare AI models in Foundry | https://learn.microsoft.com/en-us/azure/foundry/how-to/healthcare-ai/healthcare-ai-models |
| Choose integration patterns for Microsoft Foundry APIs | https://learn.microsoft.com/en-us/azure/foundry/how-to/integrate-with-other-apps |
| Plan migration from Foundry classic to current portal | https://learn.microsoft.com/en-us/azure/foundry/how-to/navigate-from-classic |
| Decide when to upgrade Azure OpenAI to Foundry | https://learn.microsoft.com/en-us/azure/foundry/how-to/upgrade-azure-openai |
| Use Ask AI to upgrade or switch Foundry models | https://learn.microsoft.com/en-us/azure/foundry/observability/how-to/optimization-model-upgrade |
| Choose content streaming and filtering modes in Foundry | https://learn.microsoft.com/en-us/azure/foundry/openai/concepts/content-streaming |
| Use Foundry model retirement schedule in Azure Government | https://learn.microsoft.com/en-us/azure/foundry/openai/concepts/model-retirement-schedule-gov |
| Plan around Foundry Models lifecycle and support policy | https://learn.microsoft.com/en-us/azure/foundry/openai/concepts/model-retirements |
| Plan Foundry Models lifecycle in Azure Government | https://learn.microsoft.com/en-us/azure/foundry/openai/concepts/model-retirements-gov |
| Plan and size provisioned throughput deployments in Foundry | https://learn.microsoft.com/en-us/azure/foundry/openai/concepts/provisioned-throughput |
| Choose PTU billing mode and manage costs | https://learn.microsoft.com/en-us/azure/foundry/openai/concepts/provisioned-throughput-billing |
| Identify retired Foundry Models and choose alternatives | https://learn.microsoft.com/en-us/azure/foundry/openai/concepts/retired-models |
| Estimate and manage fine-tuning costs in Foundry | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/fine-tuning-cost-management |
| Use Foundry model router with agents for optimal model selection | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/model-router-agents |
| Determine PTU capacity for Foundry workloads | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/provisioned-throughput-sizing |
| Migrate from preview to GA Realtime API | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/realtime-audio-preview-api-migration-guide |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design networking and subnet sizing for Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/agents/concepts/agents-networking-deep-dive |
| Design private agentic retrieval architecture with Foundry IQ | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/foundry-iq-tutorial-private-overview |
| Pool multiple users into shared Foundry agent sessions | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/multiplex-session-users |
| Design high availability for Microsoft Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/how-to/high-availability-resiliency |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Quotas, limits, regions, and models for Foundry Agent Service | https://learn.microsoft.com/en-us/azure/foundry/agents/concepts/limits-quotas-regions |
| Manage vector store limits and file search behavior | https://learn.microsoft.com/en-us/azure/foundry/agents/concepts/vector-stores |
| Manage Foundry hosted agent sessions and timeouts | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/manage-hosted-sessions |
| Evaluation rate limits, regions, and enterprise options in Foundry | https://learn.microsoft.com/en-us/azure/foundry/concepts/evaluation-regions-limits-virtual-network |
| Configure token rate limits and quotas for Foundry models | https://learn.microsoft.com/en-us/azure/foundry/control-plane/how-to-enforce-limits-models |
| Understand Claude model capabilities and quotas in Foundry | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/concepts/claude-models |
| Reference quotas and limits for Foundry Models | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/quotas-limits |
| Manage Microsoft Foundry model deployment quotas | https://learn.microsoft.com/en-us/azure/foundry/how-to/quota |
| Plan around Foundry model retirement schedule | https://learn.microsoft.com/en-us/azure/foundry/openai/concepts/model-retirement-schedule |
| Use Azure OpenAI global batch processing and quotas | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/batch |
| Use prompt caching to reduce Azure OpenAI costs | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/prompt-caching |
| Manage Azure OpenAI quota and rate limits in Foundry | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/quota |
| Use reinforcement fine-tuning with cost safeguards | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/reinforcement-fine-tuning |
| Azure OpenAI quotas and limits in Foundry | https://learn.microsoft.com/en-us/azure/foundry/openai/quotas-limits |
| Reference quotas and limits for Azure OpenAI in Azure Government | https://learn.microsoft.com/en-us/azure/foundry/openai/quotas-limits-gov |

### Security
| Topic | URL |
|-------|-----|
| Configure Agent 365 identity and governance for Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/agents/concepts/agent-365-integration |
| Configure and govern agent identities in Microsoft Foundry | https://learn.microsoft.com/en-us/azure/foundry/agents/concepts/agent-identity |
| Configure authentication for Agent2Agent tools | https://learn.microsoft.com/en-us/azure/foundry/agents/concepts/agent-to-agent-authentication |
| Reference permissions for Foundry hosted agents | https://learn.microsoft.com/en-us/azure/foundry/agents/concepts/hosted-agent-permissions |
| Configure RBAC roles and environment for Foundry Agent Service | https://learn.microsoft.com/en-us/azure/foundry/agents/environment-setup |
| Understand Foundry Agent Service data and access | https://learn.microsoft.com/en-us/azure/foundry/agents/faq |
| Attach Responsible AI guardrails to Foundry hosted agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/add-hosted-agent-guardrails |
| Publish Foundry agent applications with auth and permissions | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/agent-applications |
| Configure Agent 365 data collection for Foundry | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/configure-agent-365-data-collection |
| Assign Agent 365 observability app role in Entra | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/grant-agent-365-permissions |
| Isolate Microsoft Foundry hosted agent sessions per user | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/isolate-sessions-per-user |
| Control and disable Grounding with Bing access | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/manage-grounding-with-bing |
| Configure authentication for MCP servers in Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/mcp-authentication |
| Use isolation keys with Foundry hosted agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/pass-isolation-keys |
| Govern MCP tools via AI gateway and API Management | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/governance |
| Configure private networking for Foundry Agent Service | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/virtual-networks |
| Map elevated roles to admin tasks in Foundry | https://learn.microsoft.com/en-us/azure/foundry/concepts/administrator-guide |
| Configure authentication and authorization in Microsoft Foundry | https://learn.microsoft.com/en-us/azure/foundry/concepts/authentication-authorization-foundry |
| Configure customer-managed keys for Microsoft Foundry | https://learn.microsoft.com/en-us/azure/foundry/concepts/encryption-keys-portal |
| Use Microsoft Foundry in Azure Government | https://learn.microsoft.com/en-us/azure/foundry/concepts/foundry-azure-government |
| Apply role-based access control in Microsoft Foundry | https://learn.microsoft.com/en-us/azure/foundry/concepts/rbac-foundry |
| Govern Foundry agent infrastructure as Entra admin | https://learn.microsoft.com/en-us/azure/foundry/control-plane/govern-agent-infrastructure-entra-admin |
| Manage compliance and security for Microsoft Foundry assets | https://learn.microsoft.com/en-us/azure/foundry/control-plane/how-to-manage-compliance-security |
| Create and apply Foundry guardrail policies | https://learn.microsoft.com/en-us/azure/foundry/control-plane/quickstart-create-guardrail-policy |
| Configure Claude Code with secure Microsoft Foundry access | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/how-to/configure-claude-code |
| Set up Claude Desktop with Microsoft Foundry as provider | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/how-to/configure-claude-desktop |
| Configure keyless Entra ID authentication for Foundry Models | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/how-to/configure-entra-id |
| Configure guided safety and security guardrails for agents | https://learn.microsoft.com/en-us/azure/foundry/guardrails/guided-set-up |
| Create custom Azure Policy rules for Foundry resources | https://learn.microsoft.com/en-us/azure/foundry/how-to/custom-policy-definition |
| Restrict Microsoft Foundry preview features with RBAC and tags | https://learn.microsoft.com/en-us/azure/foundry/how-to/disable-preview-features |
| Enable and govern Fireworks models in Foundry | https://learn.microsoft.com/en-us/azure/foundry/how-to/fireworks/enable-fireworks-models |
| Secure Foundry with managed virtual network isolation | https://learn.microsoft.com/en-us/azure/foundry/how-to/managed-virtual-network |
| Use Azure Policy to govern Foundry model deployment | https://learn.microsoft.com/en-us/azure/foundry/how-to/model-deployment-policy |
| Enforce Foundry model router choices with Azure Policy | https://learn.microsoft.com/en-us/azure/foundry/how-to/model-router-policy |
| Secure Foundry MCP Server with RBAC and policies | https://learn.microsoft.com/en-us/azure/foundry/mcp/security-best-practices |
| Control and govern trace data collection in Foundry | https://learn.microsoft.com/en-us/azure/foundry/observability/concepts/trace-data |
| Understand default Guardrail safety policies in Foundry | https://learn.microsoft.com/en-us/azure/foundry/openai/concepts/default-safety-policies |
| Design safety system messages for Azure OpenAI in Foundry | https://learn.microsoft.com/en-us/azure/foundry/openai/concepts/system-message |
| Apply safety evaluation to fine-tuned models | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/fine-tuning-safety-evaluation |
| Understand data privacy and security in Foundry Agent Service | https://learn.microsoft.com/en-us/azure/foundry/responsible-ai/agents/data-privacy-security |
| Understand data privacy for Claude models in Foundry | https://learn.microsoft.com/en-us/azure/foundry/responsible-ai/claude-models/data-privacy |
| Understand data privacy and security for Foundry Models | https://learn.microsoft.com/en-us/azure/foundry/responsible-ai/openai/data-privacy |

### Configuration
| Topic | URL |
|-------|-----|
| Define Foundry hosted agents with agent.yaml schema | https://learn.microsoft.com/en-us/azure/foundry/agents/concepts/agent-yaml-reference |
| Configure Foundry hosted agents with azure.yaml reference | https://learn.microsoft.com/en-us/azure/foundry/agents/concepts/azure-yaml-reference |
| Configure and troubleshoot Foundry capability hosts for data routing | https://learn.microsoft.com/en-us/azure/foundry/agents/concepts/capability-hosts |
| Implement the runtime contract for Foundry hosted agents | https://learn.microsoft.com/en-us/azure/foundry/agents/concepts/hosted-agent-contract |
| Inspect local hosted agents with Agent Inspector | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/agent-inspector |
| Author azure.yaml configuration for Foundry hosted agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/author-azure-yaml |
| Configure Foundry project context for azd AI commands | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/cli-project-context |
| Configure and publish Microsoft Foundry agent endpoints | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/configure-agent |
| Configure environment variables for Foundry hosted agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/configure-hosted-agent-env-variables |
| Configure Connected Foundry Models in Agent Service | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/connected-models |
| Disable classic agents and assistants in Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/disable-classic-agents |
| Configure private inbound connectivity for Foundry IQ | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/foundry-iq-tutorial-private-inbound |
| Configure private outbound dependencies for Foundry IQ | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/foundry-iq-tutorial-private-outbound |
| Install and verify azd Foundry AI extensions | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/install-cli-foundry-extensions |
| Configure and manage Foundry hosted agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/manage-hosted-agent |
| Configure and use memory in Foundry Agent Service | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/memory-usage |
| Configure a private tool catalog for Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/private-tool-catalog |
| Register external agents for Foundry observability and evaluation | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/register-external-agent |
| Configure structured inputs for Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/structured-inputs |
| Configure custom MCP-based code interpreter for Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/custom-code-interpreter |
| Configure MCP tool connections for Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/model-context-protocol |
| Manage and configure versioned skills for Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/skills |
| Configure tool search for large Foundry toolboxes | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/tool-search |
| Configure and manage toolboxes for Foundry hosted agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/toolbox |
| Update model deployments for Foundry hosted agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/update-hosted-agent-model |
| Automate azd AI usage with coding agents and scripts | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/use-cli-with-coding-agents |
| Configure Foundry Agent Service to use existing Azure resources | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/use-your-own-resources |
| Reference built-in evaluators and parameters in Foundry | https://learn.microsoft.com/en-us/azure/foundry/concepts/built-in-evaluators |
| Configure rubric evaluators for Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/concepts/evaluation-evaluators/rubric-evaluators |
| Configure AI Gateway token limits in Foundry | https://learn.microsoft.com/en-us/azure/foundry/configuration/enable-ai-api-management-gateway-portal |
| Register and configure custom agents in Foundry | https://learn.microsoft.com/en-us/azure/foundry/control-plane/register-custom-agent |
| Use Microsoft Foundry model endpoints and authentication | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/concepts/endpoints |
| Configure Foundry model deployments with CLI and Bicep | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/how-to/create-model-deployments |
| Configure Azure Monitor for Foundry model deployments | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/how-to/monitor-models |
| Configure guardrails and controls in Microsoft Foundry | https://learn.microsoft.com/en-us/azure/foundry/guardrails/how-to-create-guardrails |
| Configure Foundry managed network access to on-premises | https://learn.microsoft.com/en-us/azure/foundry/how-to/access-on-premises-resources |
| Configure bring-your-own storage for Microsoft Foundry | https://learn.microsoft.com/en-us/azure/foundry/how-to/bring-your-own-azure-storage-foundry |
| Set up BYOS for Speech and Language in Foundry | https://learn.microsoft.com/en-us/azure/foundry/how-to/bring-your-own-azure-storage-speech-language-services |
| Configure private endpoints for Microsoft Foundry | https://learn.microsoft.com/en-us/azure/foundry/how-to/configure-private-link |
| Use the Microsoft Foundry Skill with coding agents | https://learn.microsoft.com/en-us/azure/foundry/how-to/develop/use-microsoft-foundry-skill |
| Configure diagnostic logging for Microsoft Foundry | https://learn.microsoft.com/en-us/azure/foundry/how-to/diagnostic-logging |
| Run model and agent evaluations in Foundry portal | https://learn.microsoft.com/en-us/azure/foundry/how-to/evaluate-generative-ai-app |
| Import and deploy custom Fireworks models in Foundry | https://learn.microsoft.com/en-us/azure/foundry/how-to/fireworks/import-custom-models |
| Configure health and performance alerts for Foundry | https://learn.microsoft.com/en-us/azure/foundry/how-to/stay-informed-service-health |
| Understand agent tracing behavior and data in Foundry | https://learn.microsoft.com/en-us/azure/foundry/observability/concepts/trace-agent-concept |
| Run Foundry agent evaluations with azd CLI | https://learn.microsoft.com/en-us/azure/foundry/observability/how-to/azure-developer-cli-evaluation |
| Generate synthetic evaluation datasets in Foundry | https://learn.microsoft.com/en-us/azure/foundry/observability/how-to/evaluation-dataset-synthetic |
| Configure Agent Monitoring Dashboard for Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/observability/how-to/how-to-monitor-agents-dashboard |
| Log end user feedback with OpenTelemetry in Foundry | https://learn.microsoft.com/en-us/azure/foundry/observability/how-to/log-end-user-feedback |
| Use Ask AI to interpret Foundry monitoring dashboards | https://learn.microsoft.com/en-us/azure/foundry/observability/how-to/optimization-dashboard |
| Analyze agent traces with Trace Replay in Foundry | https://learn.microsoft.com/en-us/azure/foundry/observability/how-to/trace-agent-replay |
| Set up tracing to Application Insights for Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/observability/how-to/trace-agent-setup |
| Annotate Foundry traces with human feedback signals | https://learn.microsoft.com/en-us/azure/foundry/observability/how-to/trace-annotations |
| Convert Foundry agent traces into evaluation datasets | https://learn.microsoft.com/en-us/azure/foundry/observability/how-to/traces-to-dataset |
| Configure evaluation test suites for hosted agents | https://learn.microsoft.com/en-us/azure/foundry/observability/quickstarts/quickstart-evaluate-hosted-agent |
| Enable and review tracing for hosted agents | https://learn.microsoft.com/en-us/azure/foundry/observability/quickstarts/quickstart-tracing-hosted-agent |
| Configure and use Azure OpenAI v1 API in Foundry | https://learn.microsoft.com/en-us/azure/foundry/openai/api-version-lifecycle |
| Configure Prompt Shields for Foundry model security | https://learn.microsoft.com/en-us/azure/foundry/openai/concepts/content-filter-prompt-shields |
| Automate Azure OpenAI deployments and TPM quota settings | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/automate-quota-deployments |
| Call chat completion models with Azure OpenAI in Foundry | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/chatgpt |
| Configure Azure OpenAI image generation models | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/dall-e |
| Configure DPO fine-tuning for Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/fine-tuning-direct-preference-optimization |
| Create and manage reusable skills for Responses API shell | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/skills |
| Configure spillover traffic management for provisioned Azure OpenAI deployments | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/spillover-traffic-management |
| Monitor Azure OpenAI Foundry with Azure Monitor | https://learn.microsoft.com/en-us/azure/foundry/openai/monitor-openai-reference |
| Configure Azure OpenAI Realtime API events in Foundry | https://learn.microsoft.com/en-us/azure/foundry/openai/realtime-audio-reference |
| Check Azure OpenAI language support in Foundry Models | https://learn.microsoft.com/en-us/azure/foundry/openai/supported-languages |
| Set up core Microsoft Foundry resources and access | https://learn.microsoft.com/en-us/azure/foundry/tutorials/quickstart-create-foundry-resources |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use agents, conversations, and responses via SDKs | https://learn.microsoft.com/en-us/azure/foundry/agents/concepts/runtime-components |
| Add Responses or Invocations protocol adapters to hosted agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/add-protocol-adapter |
| Integrate BYOM via AI gateways with Foundry Agent Service | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/ai-gateway |
| Enable Agent2Agent endpoints for Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/enable-agent-to-agent-endpoint |
| Connect Foundry agents to Foundry IQ knowledge bases | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/foundry-iq-connect |
| Invoke hosted agents with azd commands | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/invoke-hosted-agent |
| Enable optimizer integration for Foundry hosted agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/make-agent-optimizer-ready |
| Connect Foundry agents to remote A2A endpoints | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/agent-to-agent |
| Integrate Azure AI Search with Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/ai-search |
| Integrate Azure Speech MCP tool with Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/azure-ai-speech |
| Integrate Azure Functions as tools for agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/azure-functions |
| Use Bing grounding tools with Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/bing-tools |
| Configure Browser Automation tool for Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/browser-automation |
| Use Code Interpreter tool in Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/code-interpreter |
| Integrate Foundry agents with computer use tool | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/computer-use |
| Add managed MCP connector servers to Foundry | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/connectors |
| Connect Foundry agents to Microsoft Fabric data | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/fabric |
| Integrate Foundry agents with Fabric IQ workload | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/fabric-iq |
| Configure file search tool for Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/file-search |
| Implement function calling with Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/function-calling |
| Use image generation tool in Foundry Agent Service | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/image-generation |
| Connect OpenAPI tools to Microsoft Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/openapi |
| Ground Foundry agents with SharePoint content | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/sharepoint |
| Enable web search tool in Foundry Agent Service | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/web-search |
| Connect Foundry agents to Microsoft 365 via Work IQ | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/tools/work-iq |
| Add declarative agent workflows using Foundry VS Code toolkit | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/vs-code-agents-workflow-low-code |
| Ground hosted agents in Foundry IQ knowledge bases | https://learn.microsoft.com/en-us/azure/foundry/agents/quickstarts/quickstart-foundry-iq-hosted-agent |
| Add persistent memory to Foundry hosted agents | https://learn.microsoft.com/en-us/azure/foundry/agents/quickstarts/quickstart-memory-hosted-agent |
| Build and consume Foundry toolboxes with hosted agents | https://learn.microsoft.com/en-us/azure/foundry/agents/quickstarts/quickstart-toolbox-agent |
| Call Foundry Responses API from application code | https://learn.microsoft.com/en-us/azure/foundry/agents/quickstarts/responses-api |
| Run fine-tuning jobs with azd extension | https://learn.microsoft.com/en-us/azure/foundry/fine-tuning/fine-tune-cli |
| Generate text with Foundry Models via Responses API | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/how-to/generate-responses |
| Deploy and call Hugging Face models in Microsoft Foundry | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/how-to/hugging-face-models |
| Deploy and call DeepSeek-R1 in Foundry Models | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/tutorials/get-started-deepseek-r1 |
| Integrate third-party safety guardrails with Foundry | https://learn.microsoft.com/en-us/azure/foundry/guardrails/third-party-integrations |
| Configure and manage Microsoft Foundry connections | https://learn.microsoft.com/en-us/azure/foundry/how-to/connections-add |
| Host Microsoft Agent Framework agents on Foundry | https://learn.microsoft.com/en-us/azure/foundry/how-to/develop/framework-hosted-agents |
| Build LangGraph agents with Foundry Agent Service | https://learn.microsoft.com/en-us/azure/foundry/how-to/develop/langchain-agents |
| Host LangGraph agents on Foundry hosted agents | https://learn.microsoft.com/en-us/azure/foundry/how-to/develop/langchain-hosted-agents |
| Add Foundry long-term memory to LangChain apps | https://learn.microsoft.com/en-us/azure/foundry/how-to/develop/langchain-memory |
| Integrate Foundry Content Safety middleware in LangChain | https://learn.microsoft.com/en-us/azure/foundry/how-to/develop/langchain-middleware |
| Use Foundry Toolbox tools and skills in LangChain | https://learn.microsoft.com/en-us/azure/foundry/how-to/develop/langchain-toolbox |
| Trace LangChain apps with Foundry and Azure Monitor | https://learn.microsoft.com/en-us/azure/foundry/how-to/develop/langchain-traces |
| Run AI Red Teaming Agent scans locally | https://learn.microsoft.com/en-us/azure/foundry/how-to/develop/run-scans-ai-red-teaming-agent |
| Select and use Microsoft Foundry SDKs and endpoints | https://learn.microsoft.com/en-us/azure/foundry/how-to/develop/sdk-overview |
| Migrate Azure AI Inference SDK calls to OpenAI SDK | https://learn.microsoft.com/en-us/azure/foundry/how-to/model-inference-to-openai-migration |
| Integrate Azure Key Vault with Microsoft Foundry | https://learn.microsoft.com/en-us/azure/foundry/how-to/set-up-key-vault-connection |
| Use Foundry MCP Server tools and prompts | https://learn.microsoft.com/en-us/azure/foundry/mcp/available-tools |
| Build and register custom MCP servers for Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/mcp/build-your-own-mcp-server |
| Connect VS Code to Foundry MCP Server securely | https://learn.microsoft.com/en-us/azure/foundry/mcp/get-started |
| Add OpenTelemetry client-side tracing to Foundry agents | https://learn.microsoft.com/en-us/azure/foundry/observability/how-to/trace-agent-client-side |
| Configure OpenTelemetry tracing for AI agent frameworks | https://learn.microsoft.com/en-us/azure/foundry/observability/how-to/trace-agent-framework |
| Use Azure OpenAI audio completions API | https://learn.microsoft.com/en-us/azure/foundry/openai/audio-completions-quickstart |
| Use groundedness detection with Foundry OpenAI | https://learn.microsoft.com/en-us/azure/foundry/openai/concepts/content-filter-groundedness |
| Configure and use Codex CLI with Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/codex |
| Call o3-deep-research via Azure OpenAI Responses API | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/deep-research |
| Fine-tune Foundry models via SDK and REST | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/fine-tuning |
| Fine-tune tool calling behavior in Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/fine-tuning-functions |
| Implement function calling with Azure OpenAI in Foundry | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/function-calling |
| Call Azure OpenAI vision-enabled chat models | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/gpt-with-vision |
| Configure JSON mode responses for Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/json-mode |
| Use Foundry model router to route prompts | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/model-router |
| Optimize latency with predicted outputs in Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/predicted-outputs |
| Implement GPT Realtime audio with Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/realtime-audio |
| Use GPT Realtime API over SIP | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/realtime-audio-sip |
| Use GPT Realtime audio via WebRTC in Azure | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/realtime-audio-webrtc |
| Use GPT Realtime audio via WebSockets in Azure | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/realtime-audio-websockets |
| Use Azure OpenAI Responses API with Python and REST | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/responses |
| Call Foundry models via Responses API with routing | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/responses-model-routing |
| Run shell commands with Azure OpenAI Responses API | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/shells |
| Use structured outputs and JSON schema with Azure OpenAI | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/structured-outputs |
| Enable and configure web search tool in Responses API | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/web-search |
| Use WebSocket mode with Azure OpenAI Responses API | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/websockets |
| Use Azure OpenAI image and audio REST APIs (GA) | https://learn.microsoft.com/en-us/azure/foundry/openai/reference |
| Use Azure OpenAI image and audio REST APIs (preview) | https://learn.microsoft.com/en-us/azure/foundry/openai/reference-preview |
| Use Azure OpenAI image, audio, and video REST APIs (preview) | https://learn.microsoft.com/en-us/azure/foundry/openai/reference-preview-latest |
| Use Azure OpenAI Whisper for speech to text | https://learn.microsoft.com/en-us/azure/foundry/openai/whisper-quickstart |
| Get started coding with the Microsoft Foundry SDK | https://learn.microsoft.com/en-us/azure/foundry/quickstarts/get-started-code |

### Deployment
| Topic | URL |
|-------|-----|
| Scaffold and customize hosted agent infrastructure with azd Bicep | https://learn.microsoft.com/en-us/azure/foundry/agents/concepts/cli-infrastructure |
| Deploy containerized Foundry hosted agents via SDK and REST | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/deploy-hosted-agent |
| Deploy hosted Foundry agents directly from source | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/deploy-hosted-agent-code |
| Deploy Foundry hosted agents using private Azure Container Registry | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/deploy-hosted-agent-private-azure-container-registry |
| Initialize Foundry hosted agent projects with azd | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/init-agent-project |
| Publish Foundry agents to Microsoft 365 Copilot and Teams | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/publish-copilot |
| Publish private-network Foundry agents to Microsoft 365 and Teams via REST | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/publish-copilot-virtual-network |
| Run and test Foundry hosted agents locally with azd | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/run-hosted-agent-locally |
| Configure CI/CD pipelines for Foundry hosted agents | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/set-up-ci-cd-cli |
| Update Foundry hosted agent endpoints and cards with azd | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/update-agent-endpoint-cli |
| Create and deploy hosted agent workflows from VS Code | https://learn.microsoft.com/en-us/azure/foundry/agents/how-to/vs-code-agents-workflow-pro-code |
| Deploy containerized hosted agents to Foundry | https://learn.microsoft.com/en-us/azure/foundry/agents/quickstarts/quickstart-hosted-agent |
| Set up GitHub Actions CI/CD for hosted agents | https://learn.microsoft.com/en-us/azure/foundry/agents/quickstarts/set-up-cicd-hosted-agent |
| Deploy Microsoft Foundry Models via Foundry portal | https://learn.microsoft.com/en-us/azure/foundry/foundry-models/how-to/deploy-foundry-models |
| Recover Foundry Agent Service from regional platform outages | https://learn.microsoft.com/en-us/azure/foundry/how-to/agent-service-platform-disaster-recovery |
| Deploy open-source models on Foundry managed compute | https://learn.microsoft.com/en-us/azure/foundry/how-to/deploy-models-managed |
| Run cloud-scale evaluations with Foundry SDK | https://learn.microsoft.com/en-us/azure/foundry/how-to/develop/cloud-evaluation |
| Run AI Red Teaming Agent scans in the cloud | https://learn.microsoft.com/en-us/azure/foundry/how-to/develop/run-ai-red-teaming-cloud |
| Run Foundry agent evaluations in Azure DevOps | https://learn.microsoft.com/en-us/azure/foundry/how-to/evaluation-azure-devops |
| Run Foundry agent evaluations in GitHub Actions | https://learn.microsoft.com/en-us/azure/foundry/how-to/evaluation-github-action |
| Deploy CxrReportGen Premium healthcare model in Foundry | https://learn.microsoft.com/en-us/azure/foundry/how-to/healthcare-ai/deploy-cxrreportgen-premium |
| Deploy MedImageInsight Premium healthcare model in Foundry | https://learn.microsoft.com/en-us/azure/foundry/how-to/healthcare-ai/deploy-medimageinsight-premium |
| Deploy fine-tuned Azure OpenAI models in Foundry | https://learn.microsoft.com/en-us/azure/foundry/openai/how-to/fine-tuning-deploy |