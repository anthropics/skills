---
name: claude-api
description: |-
  Reference for the Claude API and Anthropic SDKs: model IDs and pricing, request parameters, streaming, tool use, prompt caching, token counting, model migration, agents, MCP, and error codes. Use when writing or editing Claude API/SDK code (anthropic imports, client calls, tool definitions, agent loops), when a task is LLM-shaped with provider unstated (agent, MCP, tool-definition, RAG, or structured-output work; debugging refusals, cutoffs, streaming, tool calls, or tokens), or when answering specific Claude API questions (model choice, pricing, limits, caching, migration). Do NOT trigger on prose-only mentions of model names (editing a file named CLAUDE.md, discussing models in docs), on other providers (OpenAI, Gemini, Llama, Mistral, Cohere, Ollama), or on tasks with no API surface. Read SKILL.md fully, then read only the reference and language files your task needs.
license: Complete terms in LICENSE.txt
---

# Building LLM-Powered Applications with Claude

This skill is a reference for building with the Claude API and the official Anthropic SDKs. It follows **progressive disclosure**: this SKILL.md is the index and routing guide; detailed material lives in separate files that you read on demand. Do not read every file — read only the ones your task needs, per the Reference Index and Reading Guide below.

## When to Use This Skill

Use this skill when the task has a real Claude API / SDK surface:

- Writing or editing code that calls Claude — `anthropic` imports, SDK client construction, `messages.create` / streaming calls, tool definitions, agent loops, MCP connectors, structured outputs.
- Tasks that are LLM-shaped with the provider unstated — agent / MCP / tool-definition / RAG / LLM-judge / computer-use work; generate / summarize / extract / classify / rewrite / converse over natural language; debugging refusals, cutoffs, streaming, tool calls, or token counts.
- Specific Claude API questions — model choice, pricing, limits, caching, migration between models.

**Skip this skill** when:

- Another provider is being worked on: OpenAI / GPT / Gemini / Llama / Mistral / Cohere / Ollama named in the query, or `grep -rE 'openai|langchain_openai|google.generativeai|genai|mistralai|cohere|ollama'` over the project hits (run this grep first if no provider is named).
- The prompt mentions a model name only in prose — e.g. editing a file named `CLAUDE.md`, updating docs, or casual discussion of models. A model name alone is not a trigger; the task must actually need API/SDK reference material.

Use your judgement: a one-line config edit does not need this skill.

**Non-Anthropic target files:** if the target file (or project) carries non-Anthropic provider markers — `import openai`, `from openai`, `langchain_openai`, `OpenAI(`, `gpt-4`, `gpt-5`, file names like `agent-openai.py` or `*-generic.py`, or an explicit instruction to keep code provider-neutral — tell the user this skill produces Claude/Anthropic SDK code and ask whether they want the file switched to Claude or a non-Claude implementation. Do not edit a non-Anthropic file with Anthropic SDK calls.

## Output Requirement

When the user asks you to add, modify, or implement a Claude feature, your code must call Claude through one of:

1. **The official Anthropic SDK** for the project's language (`anthropic`, `@anthropic-ai/sdk`, `com.anthropic.*`, etc.). This is the default whenever a supported SDK exists for the project.
2. **Raw HTTP** (`curl`, `requests`, `fetch`, `httpx`, etc.) — only when the user explicitly asks for cURL/REST/raw HTTP, the project is a shell/cURL project, or the language has no official SDK.

Never mix the two — don't reach for `requests`/`fetch` in a Python or TypeScript project just because it feels lighter. Never fall back to OpenAI-compatible shims.

**Never guess SDK usage.** Function names, class names, namespaces, method signatures, and import paths must come from explicit documentation — either the `{lang}/` files in this skill or the official SDK repositories or documentation links listed in `shared/live-sources.md`. If the binding you need is not explicitly documented in the skill files, WebFetch the relevant SDK repo from `shared/live-sources.md` before writing code. Do not infer Ruby/Java/Go/PHP/C# APIs from cURL shapes or from another language's SDK.

**If WebFetch or repository access fails** (network restricted, timeouts, clone blocked): do not keep retrying — write code from the patterns and namespace/package tables in the `{lang}/` file, run the compiler or interpreter on it, and iterate on the error output. For statically-typed SDKs (C#, Java, Go) a compile-fix loop against local errors reaches working code faster than blocked network research.

## Defaults

Unless the user requests otherwise:

For the Claude model version, please use Claude Opus 5, which you can access via the exact model string `claude-opus-5`. Please default to using adaptive thinking (`thinking: {type: "adaptive"}`) for anything remotely complicated. And finally, please default to streaming for any request that may involve long input, long output, or high `max_tokens` — it prevents hitting request timeouts. Use the SDK's `.get_final_message()` / `.finalMessage()` helper to get the complete response if you don't need to handle individual stream events.

## ⚠️ API Drift — Your Training Prior May Be Stale

Several common Claude API shapes changed in 2025–2026. If you recall a pattern from training, verify it against the `{lang}/` files in this skill before writing — the most frequent drift points (extended thinking → `adaptive`, web search tool types, PHP camelCase params, Managed Agents vault credentials) are in **`references/api-drift.md`**. The `{lang}/` files in this skill are authoritative over recalled patterns.

## Subcommands

If the User Request at the bottom of this prompt is a bare subcommand string (no prose), search every **Subcommands** table in this document — including any in sections appended below — and follow the matching Action column directly. This lets users invoke specific flows via `/claude-api <subcommand>`. If no table matches, treat the request as normal prose.

| Subcommand | Action |
|---|---|
| `migrate` | Migrate existing Claude API code to a newer model. **Read `shared/model-migration.md` immediately** and follow it in order: Step 0 (confirm scope — ask which files/directories before any edit), Step 1 (classify each file), then the per-target breaking-changes section. Do not summarize the guide — execute it. If the user did not name a target model, ask which model to migrate to in the same turn as the scope question. After the per-target changes are applied, audit the in-scope prompt text, tool descriptions, and request code against `shared/prompt-audit.md` — prompting written for the source model is part of every migration, and it does not announce itself. |
| `prompt-audit` | Audit existing prompts, skills, and tool descriptions for dated patterns ("cruft") written for older models. **Read `shared/prompt-audit.md` immediately** and follow it in order: Step 0 (establish scope and target model from the request and the repository — state the assumptions in the report, do not stop to ask), inventory, provenance, then the pattern scan. Produce both deliverables in full — the audit report (findings with `file:line`, pattern, why it's obsolete for the target model, confidence) and a proposed diff — without pausing for confirmation; apply edits only if the request explicitly asked for them. Do not summarize the guide — execute it. |

---

## Language Detection

First decide whether the request involves a specific SDK language at all. Some tasks don't: auditing prompt text (`prompt-audit`), choosing a model, pricing and limits questions, and conceptual API questions are language-agnostic. For those, skip this section and don't ask the user for a language.

When the task does involve reading or writing SDK code, determine which language the user is working in before reading code examples:

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

Every SDK language above supports both the beta Tool Runner and Managed Agents (beta) — Python (`@beta_tool` decorator), TypeScript (`betaZodTool` + Zod), Java (annotated classes), Go (`BetaToolRunner` in the `toolrunner` pkg), Ruby (`BaseTool` + `tool_runner`), C# (`BetaToolRunner` + raw JSON schema), PHP (`BetaRunnableTool` + `toolRunner()`); code entry points are in `references/tool-use-patterns.md`. cURL is raw HTTP (no SDK features) and supports Managed Agents.

> **Managed Agents code examples**: see the reading guide in the `## Managed Agents (Beta)` section below.

---

## Which Surface Should I Use?

> **Start simple.** Default to the simplest tier that meets your needs; only reach for agents when the task genuinely requires open-ended, model-driven exploration.

| Use case | Recommended surface |
|---|---|
| Classification, summarization, extraction, Q&A, batch, embeddings | **Claude API** (single call / batches) |
| Multi-step pipeline or custom agent with your own tools | **Claude API + tool use** |
| Stateful agent with hosted workspace, schedules, or persisted configs | **Managed Agents** |
| Batteries-included coding/filesystem agent on your own infra | **Claude Agent SDK** (separate product) |

Full decision detail — the surface table with rationale, the four approaches, the Tool Runner ≠ Claude Agent SDK disambiguation, and the build-vs-buy criteria — is in **`references/agent-design.md`**; read it when choosing a surface or building an agent. Cloud-provider access: Claude Platform on AWS (`shared/claude-platform-on-aws.md`) and per-feature availability on Bedrock / Vertex / Foundry (`shared/platform-availability.md`).

---

## Reference Index

Read only the file(s) your task needs. Do not read the whole index up front.

| Topic | Read |
|---|---|
| Model IDs, pricing, model-selection rules, live capability lookup | `references/models.md` |
| Adaptive thinking, effort levels, `budget_tokens` rules per model | `references/thinking-effort.md` |
| Prompt caching breakpoints, cache invalidation, pre-warming | `references/prompt-caching.md` |
| Server-side compaction for long conversations | `references/compaction.md` |
| Fast mode (Opus 5 / 4.8 only) | `references/fast-mode.md` |
| Task budgets for agentic loops | `references/task-budgets.md` |
| Bedrock (Mantle), Vertex, Foundry clients | `references/provider-clients.md` |
| Context editing (clear tool results / thinking) | `references/context-editing.md` |
| Mid-conversation system messages | `references/mid-conversation-system-messages.md` |
| Server tools: web search, web fetch, code execution | `references/server-tools.md` |
| PDF / Files API / citations / document input | `references/document-file-input.md` |
| Strict tool use, parallel calls, Tool Runner, programmatic tool calling | `references/tool-use-patterns.md` |
| Batches, Models API, stop details, client config | `references/other-api-surfaces.md` |
| Workload Identity Federation | `references/workload-identity-federation.md` |
| Auth: `ant` CLI, OAuth, API keys, profiles | `references/auth.md` |
| Stale-prior API shapes (drift) | `references/api-drift.md` |
| Common pitfalls and gotchas | `references/common-pitfalls.md` |
| Architecture: endpoints, structured outputs, supporting APIs | `references/architecture.md` |

---

## Managed Agents (Beta)

**Managed Agents** is a third surface: server-managed stateful agents with Anthropic-hosted tool execution. You create a persisted, versioned Agent config (`POST /v1/agents`), then start Sessions that reference it. Each session provisions a container as the agent's workspace — bash, file ops, and code execution run there; the agent loop itself runs on Anthropic's orchestration layer and acts on the container via tools. The session streams events; you send messages and tool results back.

Availability: `shared/platform-availability.md`. For agents on Bedrock / Vertex / Foundry (where Managed Agents is unsupported), use Claude API + tool use.

**Mandatory flow:** Agent (once) → Session (every run). `model`/`system`/`tools` live on the agent, never the session. See `shared/managed-agents-overview.md` for the full reading guide, beta headers, and pitfalls.

**Beta headers:** `managed-agents-2026-04-01` — the SDK sets this automatically for all `client.beta.{agents,environments,sessions,vaults,memory_stores,deployments,deployment_runs}.*` calls. Skills API uses `skills-2025-10-02` and Files API uses `files-api-2025-04-14`, but you don't need to explicitly pass those in for endpoints other than `/v1/skills` and `/v1/files`.

**Subcommands** — invoke directly with `/claude-api <subcommand>`:

| Subcommand | Action |
|---|---|
| `managed-agents-onboard` | Walk the user through setting up a Managed Agent from scratch. **Read `shared/managed-agents-onboarding.md` immediately** and follow its interview script: **describe → configure the agent (propose, don't interrogate) → environment → session** (same arc as the Console quickstart, auth deferred to the session step) — defaults and inline suggestions do the work, with a silent viability gate (job vs tools/credentials/data) before any code is emitted. Do not summarize — run the interview. |

**Reading guide, routing, and pitfalls:** the full guide — persistent-agent rule, `ant` CLI flow, per-language READMEs, and route-by-intent pointers for onboarding, client-code patterns, vault credentials, scheduled deployments, and multiagent — is in **`references/managed-agents.md`**; read it when the task touches Managed Agents. Start with `shared/managed-agents-overview.md`, then the topical `shared/managed-agents-*.md` files.

---

## Reading Guide

After detecting the language, read the relevant files based on what the user needs.

**All SDK languages use the same multi-file layout** — directory `{lang}/claude-api/` containing `README.md` (install, client init, basic request, thinking, caching, stop details), `tool-use.md`, `streaming.md`, `batches.md`, `files-api.md`. Not every language has every file (e.g., Ruby has no `batches.md`); if a file is absent, fall back to the cURL shape or WebFetch the SDK repo from `shared/live-sources.md`. **cURL** → `curl/examples.md`.

The Quick Task Reference below uses the `{lang}/claude-api/` directory notation for all languages.

### Quick Task Reference

**Single text classification/summarization/extraction/Q&A:**
→ Read only `{lang}/claude-api/README.md` — **always read the README first** for any task

**Chat UI or real-time response display:**
→ Read `{lang}/claude-api/README.md` + `{lang}/claude-api/streaming.md`

**Long-running conversations (may exceed context window):**
→ Read `{lang}/claude-api/README.md` — see Compaction section
**Migrating to a newer model (Fable 5 / Opus 5 / Opus 4.8 / Opus 4.7 / Opus 4.6 / Sonnet 5 / Sonnet 4.6), replacing a retired model, or translating `budget_tokens` / prefill patterns to the current API:**
→ Read `shared/model-migration.md`
**Prompting or tuning Fable 5 (long turns, effort, verbosity, autonomous runs, sub-agents):**
→ Read `shared/model-migration.md` → Migrating to Fable 5 → Behavioral shifts (prompt-tunable) + Long-running agent recommendations
**Prompt caching / optimize caching / "why is my cache hit rate low":**
→ Read `shared/prompt-caching.md` + `{lang}/claude-api/README.md` (Prompt Caching section)
**Auditing or cleaning up prompts, skills, or tool descriptions ("is this prompt outdated", "remove the cruft"):**
→ Read `shared/prompt-audit.md` — dated-pattern tables, the keep list, and the report + diff output contract
**Count tokens in a file / prompt / diff ("how many tokens is X"):**
→ Read `shared/token-counting.md` — use `messages.count_tokens`, never `tiktoken`

**Function calling / tool use / agents:**
→ Read `{lang}/claude-api/README.md` + `shared/tool-use-concepts.md` + `{lang}/claude-api/tool-use.md`

**Agent design (tool surface, context management, caching strategy):**
→ Read `shared/agent-design.md`

**Batch processing (non-latency-sensitive; runs asynchronously at 50% cost):**
→ Read `{lang}/claude-api/README.md` + `{lang}/claude-api/batches.md`

**File uploads across multiple requests (same file without re-uploading):**
→ Read `{lang}/claude-api/README.md` + `{lang}/claude-api/files-api.md`

**Debugging HTTP errors or implementing error handling:**
→ Read `shared/error-codes.md` — per-SDK typed exception class table and the Go `errors.As` pattern

**Latest official documentation:**
→ WebFetch the URLs in `shared/live-sources.md`

**Managed Agents (server-managed stateful agents with workspace):**
→ See the reading guide in the `## Managed Agents (Beta)` section above — it lists every `shared/managed-agents-*.md` file and the language-specific READMEs (`{lang}/managed-agents/README.md`, `curl/managed-agents.md`).

---

## When to Use WebFetch

Use WebFetch to get the latest documentation when:

- User asks for "latest" or "current" information
- Cached data seems incorrect
- User asks about features not covered here

Live documentation URLs are in `shared/live-sources.md`.

## Common Pitfalls

The full pitfall list is in **`references/common-pitfalls.md`** — read it when debugging. The highest-value ones, inline:

- Don't truncate inputs when passing files or content to the API. If the content is too long to fit in the context window, notify the user and discuss options rather than silently truncating.
- **Prefill removed (Fable 5, Opus 5, Sonnet 5, and the 4.6/4.7/4.8 family):** Assistant message prefills return a 400. Use structured outputs (`output_config.format`) or system prompt instructions instead.
- **Confirm migration scope before editing:** unless the prompt names an exact file, directory, or file list, **ask which scope to apply first** — "migrate my codebase" is ambiguous. See `shared/model-migration.md` Step 0.
- **`max_tokens` defaults:** don't lowball — default `~16000` non-streaming, `~64000` streaming; `max_tokens: 0` for cache pre-warming.
- **Server-tool errors don't raise.** Web search/fetch errors return HTTP 200 with an error object in `content`, not a raised exception — branch on list vs. object before indexing.
