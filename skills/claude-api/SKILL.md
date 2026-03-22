---
name: claude-api
description: "Build apps with the Claude API or Anthropic SDK. TRIGGER when: code imports `anthropic`/`@anthropic-ai/sdk`/`claude_agent_sdk`, or user asks to use Claude API, Anthropic SDKs, or Agent SDK. DO NOT TRIGGER when: code imports `openai`/other AI SDK, general programming, or ML/data-science tasks."
license: Complete terms in LICENSE.txt
---

# Building LLM-Powered Applications with Claude

This skill helps you build LLM-powered applications with Claude. Choose the right surface based on your needs, detect the project language, then read the relevant language-specific documentation.

## Defaults

Unless the user requests otherwise:

For the Claude model version, please use Claude Opus 4.6, which you can access via the exact model string `claude-opus-4-6`. Please default to using adaptive thinking (`thinking: {type: "adaptive"}`) for anything remotely complicated. And finally, please default to streaming for any request that may involve long input, long output, or high `max_tokens` — it prevents hitting request timeouts. Use the SDK's `.get_final_message()` / `.finalMessage()` helper to get the complete response if you don't need to handle individual stream events

---

## Language Detection

Before reading code examples, determine which language the user is working in:

1. **Look at project files** to infer the language:

   - `*.py`, `requirements.txt`, `pyproject.toml`, `setup.py`, `Pipfile` → **Python** — read from `python/`
   - `*.ts`, `*.tsx`, `package.json`, `tsconfig.json` → **TypeScript** — read from `typescript/`
   - `*.js`, `*.jsx` (no `.ts` files present) → **TypeScript** — JS uses the same SDK, read from `typescript/`
   - `*.java`, `pom.xml`, `build.gradle` → **Java** — read from `java/`
   - `*.kt`, `*.kts`, `build.gradle.kts` → **Java** — Kotlin uses the Java SDK, read from `java/`
   - `*.scala`, `build.sbt` → **Java** — Scala uses the Java SDK, read from `java/`
   - `*.go`, `go.mod` → **Go** — read from `go/`
   - `*.rb`, `Gemfile` → **Ruby** — read from `ruby/`
   - `*.cs`, `*.csproj` → **C#** — read from `csharp/`
   - `*.php`, `composer.json` → **PHP** — read from `php/`

2. **If multiple languages detected** (e.g., both Python and TypeScript files):

   - Check which language the user's current file or question relates to
   - If still ambiguous, ask: "I detected both Python and TypeScript files. Which language are you using for the Claude API integration?"

3. **If language can't be inferred** (empty project, no source files, or unsupported language):

   - Use AskUserQuestion with options: Python, TypeScript, Java, Go, Ruby, cURL/raw HTTP, C#, PHP
   - If AskUserQuestion is unavailable, default to Python examples and note: "Showing Python examples. Let me know if you need a different language."

4. **If unsupported language detected** (Rust, Swift, C++, Elixir, etc.):

   - Suggest cURL/raw HTTP examples from `curl/` and note that community SDKs may exist
   - Offer to show Python or TypeScript examples as reference implementations

5. **If user needs cURL/raw HTTP examples**, read from `curl/`.

### Language-Specific Feature Support

| Language   | Tool Runner | Agent SDK | Notes                                 |
| ---------- | ----------- | --------- | ------------------------------------- |
| Python     | Yes (beta)  | Yes       | Full support — `@beta_tool` decorator |
| TypeScript | Yes (beta)  | Yes       | Full support — `betaZodTool` + Zod    |
| Java       | Yes (beta)  | No        | Beta tool use with annotated classes  |
| Go         | Yes (beta)  | No        | `BetaToolRunner` in `toolrunner` pkg  |
| Ruby       | Yes (beta)  | No        | `BaseTool` + `tool_runner` in beta    |
| cURL       | N/A         | N/A       | Raw HTTP, no SDK features             |
| C#         | No          | No        | Official SDK                          |
| PHP        | No          | No        | Official SDK                          |

---

## Which Surface Should I Use?

> **Start simple.** Default to the simplest tier that meets your needs. Single API calls and workflows handle most use cases — only reach for agents when the task genuinely requires open-ended, model-driven exploration.

| Use Case                                        | Tier            | Recommended Surface       | Why                                     |
| ----------------------------------------------- | --------------- | ------------------------- | --------------------------------------- |
| Classification, summarization, extraction, Q&A  | Single LLM call | **Claude API**            | One request, one response               |
| Batch processing or embeddings                  | Single LLM call | **Claude API**            | Specialized endpoints                   |
| Multi-step pipelines with code-controlled logic | Workflow        | **Claude API + tool use** | You orchestrate the loop                |
| Custom agent with your own tools                | Agent           | **Claude API + tool use** | Maximum flexibility                     |
| AI agent with file/web/terminal access          | Agent           | **Agent SDK**             | Built-in tools, safety, and MCP support |
| Agentic coding assistant                        | Agent           | **Agent SDK**             | Designed for this use case              |
| Want built-in permissions and guardrails        | Agent           | **Agent SDK**             | Safety features included                |

> **Note:** The Agent SDK is for when you want built-in file/web/terminal tools, permissions, and MCP out of the box. If you want to build an agent with your own tools, Claude API is the right choice — use the tool runner for automatic loop handling, or the manual loop for fine-grained control (approval gates, custom logging, conditional execution).

### Decision Tree

```
What does your application need?

1. Single LLM call (classification, summarization, extraction, Q&A)
   └── Claude API — one request, one response

2. Does Claude need to read/write files, browse the web, or run shell commands
   as part of its work? (Not: does your app read a file and hand it to Claude —
   does Claude itself need to discover and access files/web/shell?)
   └── Yes → Agent SDK — built-in tools, don't reimplement them
       Examples: "scan a codebase for bugs", "summarize every file in a directory",
                 "find bugs using subagents", "research a topic via web search"

3. Workflow (multi-step, code-orchestrated, with your own tools)
   └── Claude API with tool use — you control the loop

4. Open-ended agent (model decides its own trajectory, your own tools)
   └── Claude API agentic loop (maximum flexibility)
```

### Should I Build an Agent?

Before choosing the agent tier, check all four criteria:

- **Complexity** — Is the task multi-step and hard to fully specify in advance? (e.g., "turn this design doc into a PR" vs. "extract the title from this PDF")
- **Value** — Does the outcome justify higher cost and latency?
- **Viability** — Is Claude capable at this task type?
- **Cost of error** — Can errors be caught and recovered from? (tests, review, rollback)

If the answer is "no" to any of these, stay at a simpler tier (single call or workflow).

---

## Architecture

Everything goes through `POST /v1/messages`. Tools and output constraints are features of this single endpoint — not separate APIs.

**User-defined tools** — You define tools (via decorators, Zod schemas, or raw JSON), and the SDK's tool runner handles calling the API, executing your functions, and looping until Claude is done. For full control, you can write the loop manually.

**Server-side tools** — Anthropic-hosted tools that run on Anthropic's infrastructure. Code execution is fully server-side (declare it in `tools`, Claude runs code automatically). Computer use can be server-hosted or self-hosted.

**Structured outputs** — Constrains the Messages API response format (`output_config.format`) and/or tool parameter validation (`strict: true`). The recommended approach is `client.messages.parse()` which validates responses against your schema automatically. Note: the old `output_format` parameter is deprecated; use `output_config: {format: {...}}` on `messages.create()`.

**Supporting endpoints** — Batches (`POST /v1/messages/batches`), Files (`POST /v1/files`), Token Counting, and Models (`GET /v1/models`, `GET /v1/models/{id}` — live capability/context-window discovery) feed into or support Messages API requests.

---

## Current Models (cached: 2026-02-17)

| Model             | Model ID            | Context        | Input $/1M | Output $/1M |
| ----------------- | ------------------- | -------------- | ---------- | ----------- |
| Claude Opus 4.6   | `claude-opus-4-6`   | 200K (1M beta) | $5.00      | $25.00      |
| Claude Sonnet 4.6 | `claude-sonnet-4-6` | 200K (1M beta) | $3.00      | $15.00      |
| Claude Haiku 4.5  | `claude-haiku-4-5`  | 200K           | $1.00      | $5.00       |

**ALWAYS use `claude-opus-4-6` unless the user explicitly names a different model.** This is non-negotiable. Do not use `claude-sonnet-4-6`, `claude-sonnet-4-5`, or any other model unless the user literally says "use sonnet" or "use haiku". Never downgrade for cost — that's the user's decision, not yours.

**CRITICAL: Use only the exact model ID strings from the table above — they are complete as-is. Do not append date suffixes.** For example, use `claude-sonnet-4-5`, never `claude-sonnet-4-5-20250514` or any other date-suffixed variant you might recall from training data. If the user requests an older model not in the table (e.g., "opus 4.5", "sonnet 3.7"), read `shared/models.md` for the exact ID — do not construct one yourself.

A note: if any of the model strings above look unfamiliar to you, that's to be expected — that just means they were released after your training data cutoff. Rest assured they are real models; we wouldn't mess with you like that.

**Live capability lookup:** The table above is cached. When the user asks "what's the context window for X", "does X support vision/thinking/effort", or "which models support Y", query the Models API (`client.models.retrieve(id)` / `client.models.list()`) — see `shared/models.md` for the field reference and capability-filter examples.

---

## Thinking & Effort (Quick Reference)

**Opus 4.6 — Adaptive thinking (recommended):** Use `thinking: {type: "adaptive"}`. Claude dynamically decides when and how much to think. No `budget_tokens` needed — `budget_tokens` is deprecated on Opus 4.6 and Sonnet 4.6 and must not be used. Adaptive thinking also automatically enables interleaved thinking (no beta header needed). **When the user asks for "extended thinking", a "thinking budget", or `budget_tokens`: always use Opus 4.6 with `thinking: {type: "adaptive"}`. The concept of a fixed token budget for thinking is deprecated — adaptive thinking replaces it. Do NOT use `budget_tokens` and do NOT switch to an older model.**

**Effort parameter (GA, no beta header):** Controls thinking depth and overall token spend via `output_config: {effort: "low"|"medium"|"high"|"max"}` (inside `output_config`, not top-level). Default is `high` (equivalent to omitting it). `max` is Opus 4.6 only. Works on Opus 4.5, Opus 4.6, and Sonnet 4.6. Will error on Sonnet 4.5 / Haiku 4.5. Combine with adaptive thinking for the best cost-quality tradeoffs. Use `low` for subagents or simple tasks; `max` for the deepest reasoning.

**Sonnet 4.6:** Supports adaptive thinking (`thinking: {type: "adaptive"}`). `budget_tokens` is deprecated on Sonnet 4.6 — use adaptive thinking instead.

**Older models (only if explicitly requested):** If the user specifically asks for Sonnet 4.5 or another older model, use `thinking: {type: "enabled", budget_tokens: N}`. `budget_tokens` must be less than `max_tokens` (minimum 1024). Never choose an older model just because the user mentions `budget_tokens` — use Opus 4.6 with adaptive thinking instead.

---

## Compaction (Quick Reference)

**Beta, Opus 4.6 and Sonnet 4.6.** For long-running conversations that may exceed the 200K context window, enable server-side compaction. The API automatically summarizes earlier context when it approaches the trigger threshold (default: 150K tokens). Requires beta header `compact-2026-01-12`.

**Critical:** Append `response.content` (not just the text) back to your messages on every turn. Compaction blocks in the response must be preserved — the API uses them to replace the compacted history on the next request. Extracting only the text string and appending that will silently lose the compaction state.

See `{lang}/claude-api/README.md` (Compaction section) for code examples. Full docs via WebFetch in `shared/live-sources.md`.

---

## Reading Guide

After detecting the language, read the relevant files based on what the user needs:

### Quick Task Reference

**Single text classification/summarization/extraction/Q&A:**
→ Read only `{lang}/claude-api/README.md`

**Chat UI or real-time response display:**
→ Read `{lang}/claude-api/README.md` + `{lang}/claude-api/streaming.md`

**Long-running conversations (may exceed context window):**
→ Read `{lang}/claude-api/README.md` — see Compaction section

**Function calling / tool use / agents:**
→ Read `{lang}/claude-api/README.md` + `shared/tool-use-concepts.md` + `{lang}/claude-api/tool-use.md`

**Batch processing (non-latency-sensitive):**
→ Read `{lang}/claude-api/README.md` + `{lang}/claude-api/batches.md`

**File uploads across multiple requests:**
→ Read `{lang}/claude-api/README.md` + `{lang}/claude-api/files-api.md`

**Agent with built-in tools (file/web/terminal):**
→ Read `{lang}/agent-sdk/README.md` + `{lang}/agent-sdk/patterns.md`

### Claude API (Full File Reference)

Read the **language-specific Claude API folder** (`{language}/claude-api/`):

1. **`{language}/claude-api/README.md`** — **Read this first.** Installation, quick start, common patterns, error handling.
2. **`shared/tool-use-concepts.md`** — Read when the user needs function calling, code execution, memory, or structured outputs. Covers conceptual foundations.
3. **`{language}/claude-api/tool-use.md`** — Read for language-specific tool use code examples (tool runner, manual loop, code execution, memory, structured outputs).
4. **`{language}/claude-api/streaming.md`** — Read when building chat UIs or interfaces that display responses incrementally.
5. **`{language}/claude-api/batches.md`** — Read when processing many requests offline (not latency-sensitive). Runs asynchronously at 50% cost.
6. **`{language}/claude-api/files-api.md`** — Read when sending the same file across multiple requests without re-uploading.
7. **`shared/error-codes.md`** — Read when debugging HTTP errors or implementing error handling.
8. **`shared/live-sources.md`** — WebFetch URLs for fetching the latest official documentation.

> **Note:** For Java, Go, Ruby, C#, PHP, and cURL — these have a single file each covering all basics. Read that file plus `shared/tool-use-concepts.md` and `shared/error-codes.md` as needed.

### Agent SDK

Read the **language-specific Agent SDK folder** (`{language}/agent-sdk/`). Agent SDK is available for **Python and TypeScript only**.

1. **`{language}/agent-sdk/README.md`** — Installation, quick start, built-in tools, permissions, MCP, hooks.
2. **`{language}/agent-sdk/patterns.md`** — Custom tools, hooks, subagents, MCP integration, session resumption.
3. **`shared/live-sources.md`** — WebFetch URLs for current Agent SDK docs.

---

## When to Use WebFetch

Use WebFetch to get the latest documentation when:

- User asks for "latest" or "current" information
- Cached data seems incorrect
- User asks about features not covered here

Live documentation URLs are in `shared/live-sources.md`.

## Common Pitfalls

- Don't truncate inputs when passing files or content to the API. If the content is too long to fit in the context window, notify the user and discuss options (chunking, summarization, etc.) rather than silently truncating.
- **Opus 4.6 / Sonnet 4.6 thinking:** Use `thinking: {type: "adaptive"}` — do NOT use `budget_tokens` (deprecated on both Opus 4.6 and Sonnet 4.6). For older models, `budget_tokens` must be less than `max_tokens` (minimum 1024). This will throw an error if you get it wrong.
- **Opus 4.6 prefill removed:** Assistant message prefills (last-assistant-turn prefills) return a 400 error on Opus 4.6. Use structured outputs (`output_config.format`) or system prompt instructions to control response format instead.
- **`max_tokens` defaults:** Don't lowball `max_tokens` — hitting the cap truncates output mid-thought and requires a retry. For non-streaming requests, default to `~16000` (keeps responses under SDK HTTP timeouts). For streaming requests, default to `~64000` (timeouts aren't a concern, so give the model room). Only go lower when you have a hard reason: classification (`~256`), cost caps, or deliberately short outputs.
- **128K output tokens:** Opus 4.6 supports up to 128K `max_tokens`, but the SDKs require streaming for values that large to avoid HTTP timeouts. Use `.stream()` with `.get_final_message()` / `.finalMessage()`.
- **Tool call JSON parsing (Opus 4.6):** Opus 4.6 may produce different JSON string escaping in tool call `input` fields (e.g., Unicode or forward-slash escaping). Always parse tool inputs with `json.loads()` / `JSON.parse()` — never do raw string matching on the serialized input.
- **Structured outputs (all models):** Use `output_config: {format: {...}}` instead of the deprecated `output_format` parameter on `messages.create()`. This is a general API change, not 4.6-specific.
- **Don't reimplement SDK functionality:** The SDK provides high-level helpers — use them instead of building from scratch. Specifically: use `stream.finalMessage()` instead of wrapping `.on()` events in `new Promise()`; use typed exception classes (`Anthropic.RateLimitError`, etc.) instead of string-matching error messages; use SDK types (`Anthropic.MessageParam`, `Anthropic.Tool`, `Anthropic.Message`, etc.) instead of redefining equivalent interfaces.
- **Don't define custom types for SDK data structures:** The SDK exports types for all API objects. Use `Anthropic.MessageParam` for messages, `Anthropic.Tool` for tool definitions, `Anthropic.ToolUseBlock` / `Anthropic.ToolResultBlockParam` for tool results, `Anthropic.Message` for responses. Defining your own `interface ChatMessage { role: string; content: unknown }` duplicates what the SDK already provides and loses type safety.
- **Report and document output:** For tasks that produce reports, documents, or visualizations, the code execution sandbox has `python-docx`, `python-pptx`, `matplotlib`, `pillow`, and `pypdf` pre-installed. Claude can generate formatted files (DOCX, PDF, charts) and return them via the Files API — consider this for "report" or "document" type requests instead of plain stdout text.
