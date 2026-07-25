---
name: microsoft-foundry-local
description: Expert knowledge for Microsoft Foundry Local (aka Azure AI Foundry Local) development including best practices, decision making, configuration, and integrations & coding patterns. Use when compiling HF models with Olive, using Foundry Local CLI, chat/embeddings APIs, tool calling, or SDK migration, and other Microsoft Foundry Local related development tasks. Not for Microsoft Foundry (use microsoft-foundry), Microsoft Foundry Classic (use microsoft-foundry-classic), Microsoft Foundry Tools (use microsoft-foundry-tools), Azure Local (use azure-local).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-21"
  generator: "docs2skills/1.0.0"
---
# Microsoft Foundry Local Skill

This skill provides expert guidance for Microsoft Foundry Local. Covers best practices, decision making, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Best Practices | L32-L36 | CLI usage tips, common error diagnostics, troubleshooting install/auth/deploy issues, and recommended workflows for using the Foundry Local CLI effectively. |
| Decision Making | L37-L41 | Guidance for upgrading apps from the legacy Foundry Local SDK to the current one, including API changes, migration steps, and compatibility considerations. |
| Configuration | L42-L48 | Compiling Hugging Face models with Olive for Foundry Local and using the Foundry Local CLI to install, manage, and configure local models and their command options. |
| Integrations & Coding Patterns | L49-L61 | Using Foundry Local APIs/SDKs for chat, embeddings, transcription, OpenAI-compatible clients, LangChain apps, tool calling, and REST/SDK reference (C#, JS, Python, Rust, legacy). |

### Best Practices
| Topic | URL |
|-------|-----|
| Best practices and troubleshooting for Foundry Local CLI | https://learn.microsoft.com/en-us/azure/foundry-local/reference/reference-best-practice |

### Decision Making
| Topic | URL |
|-------|-----|
| Migrate from legacy to current Foundry Local SDK | https://learn.microsoft.com/en-us/azure/foundry-local/reference/reference-sdk-migration |

### Configuration
| Topic | URL |
|-------|-----|
| Compile Hugging Face models for Foundry Local with Olive | https://learn.microsoft.com/en-us/azure/foundry-local/how-to/how-to-compile-hugging-face-models |
| Use Foundry Local CLI to manage local models | https://learn.microsoft.com/en-us/azure/foundry-local/how-to/how-to-use-foundry-local-cli |
| Foundry Local CLI command and options reference | https://learn.microsoft.com/en-us/azure/foundry-local/reference/reference-cli |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Generate text embeddings with Foundry Local SDK | https://learn.microsoft.com/en-us/azure/foundry-local/how-to/how-to-generate-embeddings |
| Integrate Foundry Local with OpenAI-style inference SDKs | https://learn.microsoft.com/en-us/azure/foundry-local/how-to/how-to-integrate-with-inference-sdks |
| Live microphone transcription with Foundry Local | https://learn.microsoft.com/en-us/azure/foundry-local/how-to/how-to-live-transcribe-audio |
| Transcribe audio using Foundry Local transcription API | https://learn.microsoft.com/en-us/azure/foundry-local/how-to/how-to-transcribe-audio |
| Build a LangChain translation app with Foundry Local | https://learn.microsoft.com/en-us/azure/foundry-local/how-to/how-to-use-langchain-with-foundry-local |
| Use Foundry Local native chat completions API | https://learn.microsoft.com/en-us/azure/foundry-local/how-to/how-to-use-native-chat-completions |
| Implement tool calling with Foundry Local models | https://learn.microsoft.com/en-us/azure/foundry-local/how-to/how-to-use-tool-calling-with-foundry-local |
| Foundry Local REST API reference for local inference | https://learn.microsoft.com/en-us/azure/foundry-local/reference/reference-rest |
| Reference for Foundry Local SDKs in C#, JS, Python, Rust | https://learn.microsoft.com/en-us/azure/foundry-local/reference/reference-sdk-current |
| Legacy Foundry Local SDK reference and CLI-dependent APIs | https://learn.microsoft.com/en-us/azure/foundry-local/reference/reference-sdk-legacy |