# Live Documentation Sources

This file contains WebFetch URLs for fetching current information from platform.claude.com and Agent SDK repositories. Use these when users need the latest data that may have changed since the cached content was last updated.

## When to Use WebFetch

- User explicitly asks for "latest" or "current" information
- Cached data seems incorrect
- User asks about features not covered in cached content
- User needs specific API details or examples

## Claude API Documentation URLs

### Models & Pricing

| Topic           | URL                                                                   | Extraction Prompt                                                               |
| --------------- | --------------------------------------------------------------------- | ------------------------------------------------------------------------------- |
| Models Overview | `https://platform.claude.com/docs/en/about-claude/models/overview.md` | "Extract current model IDs, context windows, and pricing for all Claude models" |
| Pricing         | `https://platform.claude.com/docs/en/pricing.md`                      | "Extract current pricing per million tokens for input and output"               |

### Core Features

| Topic             | URL                                                                          | Extraction Prompt                                                                      |
| ----------------- | ---------------------------------------------------------------------------- | -------------------------------------------------------------------------------------- |
| Extended Thinking | `https://platform.claude.com/docs/en/build-with-claude/extended-thinking.md` | "Extract extended thinking parameters, budget_tokens requirements, and usage examples" |
| Adaptive Thinking | `https://platform.claude.com/docs/en/build-with-claude/adaptive-thinking.md` | "Extract adaptive thinking setup, effort levels, and Claude Opus 4.6 usage examples"         |
| Effort Parameter  | `https://platform.claude.com/docs/en/build-with-claude/effort.md`            | "Extract effort levels, cost-quality tradeoffs, and interaction with thinking"        |
| Tool Use          | `https://platform.claude.com/docs/en/agents-and-tools/tool-use/overview.md`  | "Extract tool definition schema, tool_choice options, and handling tool results"       |
| Streaming         | `https://platform.claude.com/docs/en/build-with-claude/streaming.md`         | "Extract streaming event types, SDK examples, and best practices"                      |
| Prompt Caching    | `https://platform.claude.com/docs/en/build-with-claude/prompt-caching.md`    | "Extract cache_control usage, pricing benefits, and implementation examples"           |

### Media & Files

| Topic       | URL                                                                    | Extraction Prompt                                                 |
| ----------- | ---------------------------------------------------------------------- | ----------------------------------------------------------------- |
| Vision      | `https://platform.claude.com/docs/en/build-with-claude/vision.md`      | "Extract supported image formats, size limits, and code examples" |
| PDF Support | `https://platform.claude.com/docs/en/build-with-claude/pdf-support.md` | "Extract PDF handling capabilities, limits, and examples"         |

### API Operations

| Topic            | URL                                                                         | Extraction Prompt                                                                                       |
| ---------------- | --------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------- |
| Batch Processing | `https://platform.claude.com/docs/en/build-with-claude/batch-processing.md` | "Extract batch API endpoints, request format, and polling for results"                                  |
| Files API        | `https://platform.claude.com/docs/en/build-with-claude/files.md`            | "Extract file upload, download, and referencing in messages, including supported types and beta header" |
| Token Counting   | `https://platform.claude.com/docs/en/build-with-claude/token-counting.md`   | "Extract token counting API usage and examples"                                                         |
| Rate Limits      | `https://platform.claude.com/docs/en/api/rate-limits.md`                    | "Extract current rate limits by tier and model"                                                         |
| Errors           | `https://platform.claude.com/docs/en/api/errors.md`                         | "Extract HTTP error codes, meanings, and retry guidance"                                                |

### Tools

| Topic          | URL                                                                                    | Extraction Prompt                                                                        |
| -------------- | -------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------- |
| Code Execution | `https://platform.claude.com/docs/en/agents-and-tools/tool-use/code-execution-tool.md` | "Extract code execution tool setup, file upload, container reuse, and response handling" |
| Computer Use   | `https://platform.claude.com/docs/en/agents-and-tools/tool-use/computer-use.md`        | "Extract computer use tool setup, capabilities, and implementation examples"             |

### Advanced Features

| Topic              | URL                                                                           | Extraction Prompt                                   |
| ------------------ | ----------------------------------------------------------------------------- | --------------------------------------------------- |
| Structured Outputs | `https://platform.claude.com/docs/en/build-with-claude/structured-outputs.md` | "Extract output_config.format usage and schema enforcement"                           |
| Compaction         | `https://platform.claude.com/docs/en/build-with-claude/compaction.md`         | "Extract compaction setup, trigger config, and streaming with compaction"             |
| Citations          | `https://platform.claude.com/docs/en/build-with-claude/citations.md`          | "Extract citation format and implementation"        |
| Context Windows    | `https://platform.claude.com/docs/en/build-with-claude/context-windows.md`    | "Extract context window sizes and token management" |

---

## Claude API SDK Repositories

| SDK        | URL                                                       | Description                    |
| ---------- | --------------------------------------------------------- | ------------------------------ |
| Python     | `https://github.com/anthropics/anthropic-sdk-python`     | `anthropic` pip package source |
| TypeScript | `https://github.com/anthropics/anthropic-sdk-typescript` | `@anthropic-ai/sdk` npm source |
| Java       | `https://github.com/anthropics/anthropic-sdk-java`       | `anthropic-java` Maven source  |
| Go         | `https://github.com/anthropics/anthropic-sdk-go`         | Go module source               |
| Ruby       | `https://github.com/anthropics/anthropic-sdk-ruby`       | `anthropic` gem source         |
| C#         | `https://github.com/anthropics/anthropic-sdk-csharp`     | NuGet package source           |
| PHP        | `https://github.com/anthropics/anthropic-sdk-php`        | Composer package source        |

---

## Agent SDK Documentation URLs

### Core Documentation

| Topic                | URL                                                         | Extraction Prompt                                               |
| -------------------- | ----------------------------------------------------------- | --------------------------------------------------------------- |
| Agent SDK Overview   | `https://platform.claude.com/docs/en/agent-sdk.md`          | "Extract the Agent SDK overview, key features, and use cases"   |
| Agent SDK Python     | `https://github.com/anthropics/claude-agent-sdk-python`     | "Extract Python SDK installation, imports, and basic usage"     |
| Agent SDK TypeScript | `https://github.com/anthropics/claude-agent-sdk-typescript` | "Extract TypeScript SDK installation, imports, and basic usage" |

### SDK Reference (GitHub READMEs)

| Topic          | URL                                                                                       | Extraction Prompt                                            |
| -------------- | ----------------------------------------------------------------------------------------- | ------------------------------------------------------------ |
| Python SDK     | `https://raw.githubusercontent.com/anthropics/claude-agent-sdk-python/main/README.md`     | "Extract Python SDK API reference, classes, and methods"     |
| TypeScript SDK | `https://raw.githubusercontent.com/anthropics/claude-agent-sdk-typescript/main/README.md` | "Extract TypeScript SDK API reference, types, and functions" |

### npm/PyPI Packages

| Package                             | URL                                                            | Description               |
| ----------------------------------- | -------------------------------------------------------------- | ------------------------- |
| claude-agent-sdk (Python)           | `https://pypi.org/project/claude-agent-sdk/`                   | Python package on PyPI    |
| @anthropic-ai/claude-agent-sdk (TS) | `https://www.npmjs.com/package/@anthropic-ai/claude-agent-sdk` | TypeScript package on npm |

### GitHub Repositories

| Resource       | URL                                                         | Description                         |
| -------------- | ----------------------------------------------------------- | ----------------------------------- |
| Python SDK     | `https://github.com/anthropics/claude-agent-sdk-python`     | Python package source               |
| TypeScript SDK | `https://github.com/anthropics/claude-agent-sdk-typescript` | TypeScript/Node.js package source   |
| MCP Servers    | `https://github.com/modelcontextprotocol`                   | Official MCP server implementations |

---

## Fallback Strategy

If WebFetch fails (network issues, URL changed):

1. Use cached content from the language-specific files (note the cache date)
2. Inform user the data may be outdated
3. Suggest they check platform.claude.com or the GitHub repos directly
