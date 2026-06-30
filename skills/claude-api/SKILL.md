---
name: claude-api
description: |-
  Reference for the Claude API / Anthropic SDK — model ids, pricing, params, streaming, tool use, MCP, agents, caching, token counting, model migration.
  TRIGGER — read BEFORE opening the target file; don't skip because it "looks like a one-liner" — whenever: the prompt names Claude/Anthropic in any form (Claude, Anthropic, Fable, Opus, Sonnet, Haiku, `anthropic`, `@anthropic-ai`, `claude-*`, `us.anthropic.*`, `[1m]`); the user asks about an LLM (pricing/model choice/limits/caching) — never answer from memory; OR the task is LLM-shaped with provider unstated (agent/MCP/tool-definition/multi-agent/RAG/LLM-judge/computer-use; generate/summarize/extract/classify/rewrite/converse over NL; debugging refusals/cutoffs/streaming/tool-calls/tokens).
  SKIP only when another provider is being worked on (overrides all triggers): OpenAI/GPT/Gemini/Llama/Mistral/Cohere/Ollama named in the query; OR `grep -rE 'openai|langchain_openai|google.generativeai|genai|mistralai|cohere|ollama'` over the project hits (run this grep FIRST if no provider named — don't Read the file).
license: Complete terms in LICENSE.txt
---

# Building LLM-Powered Applications with Claude

This skill helps you build LLM-powered applications with Claude. Choose the right surface based on your needs, detect the project language, then read the relevant language-specific documentation.

## Before You Start

Scan the target file (or, if no target file, the prompt and project) for non-Anthropic provider markers — `import openai`, `from openai`, `langchain_openai`, `OpenAI(`, `gpt-4`, `gpt-5`, file names like `agent-openai.py` or `*-generic.py`, or any explicit instruction to keep the code provider-neutral. If you find any, stop and tell the user that this skill produces Claude/Anthropic SDK code; ask whether they want to switch the file to Claude or want a non-Claude implementation. Do not edit a non-Anthropic file with Anthropic SDK calls.

## Output Requirement

When the user asks you to add, modify, or implement a Claude feature, your code must call Claude through one of:

1. **The official Anthropic SDK** for the project's language (`anthropic`, `@anthropic-ai/sdk`, `com.anthropic.*`, etc.). This is the default whenever a supported SDK exists for the project.
2. **Raw HTTP** (`curl`, `requests`, `fetch`, `httpx`, etc.) — only when the user explicitly asks for cURL/REST/raw HTTP, the project is a shell/cURL project, or the language has no official SDK.

Never mix the two — don't reach for `requests`/`fetch` in a Python or TypeScript project just because it feels lighter. Never fall back to OpenAI-compatible shims.

**Never guess SDK usage.** Function names, class names, namespaces, method signatures, and import paths must come from explicit documentation — either the `{lang}/` files in this skill or the official SDK repositories or documentation links listed in `shared/live-sources.md`. If the binding you need is not explicitly documented in the skill files, WebFetch the relevant SDK repo from `shared/live-sources.md` before writing code. Do not infer Ruby/Java/Go/PHP/C# APIs from cURL shapes or from another language's SDK.

**If WebFetch or repository access fails** (network restricted, timeouts, clone blocked): do not keep retrying — write code from the patterns and namespace/package tables in the `{lang}/` file, run the compiler or interpreter on it, and iterate on the error output. For statically-typed SDKs (C#, Java, Go) a compile-fix loop against local errors reaches working code faster than blocked network research.

## Defaults

Unless the user requests otherwise:

For the Claude model version, please use Claude Opus 4.8, which you can access via the exact model string `claude-opus-4-8`. Please default to using adaptive thinking (`thinking: {type: "adaptive"}`) for anything remotely complicated. And finally, please default to streaming for any request that may involve long input, long output, or high `max_tokens` — it prevents hitting request timeouts. Use the SDK's `.get_final_message()` / `.finalMessage()` helper to get the complete response if you don't need to handle individual stream events

## ⚠️ API Drift — Your Training Prior May Be Stale

Several common Claude API shapes changed in 2025–2026. If you recall a pattern from training, verify it against the `{lang}/` files in this skill before writing — the rows below are the most frequent drift points:

| Area | Stale prior | Current API |
|---|---|---|
| Extended thinking | `thinking: {type: "enabled", budget_tokens: N}` | On Claude 4.6+ models: `thinking: {type: "adaptive"}`. `budget_tokens` is deprecated on Opus 4.6 / Sonnet 4.6 and **rejected with a 400** on Fable 5 / Sonnet 5 / Opus 4.8 / 4.7. Pre-4.6 models still use `budget_tokens`. |
| Web search / web fetch tool type | `web_search_20250305`, `web_fetch_20250910` | `web_search_20260209`, `web_fetch_20260209` (dynamic filtering) on Opus 4.8/4.7/4.6, Sonnet 5, and Sonnet 4.6. Older models keep the basic variants; on Vertex AI only basic `web_search_20250305` is available (web fetch is not on Vertex) — see the Server Tools QR below. |
| PHP parameter names | snake_case wire names as named args (`max_tokens`) | Top-level named args are camelCase (`maxTokens`). Nested array keys vary by feature (e.g. `'taskBudget'`, `'skillID'`, `'mcp_server_name'`) — copy the exact key from the documented example; do not bulk-convert. |

The `{lang}/` files in this skill are authoritative over recalled patterns.

---

## Subcommands

If the User Request at the bottom of this prompt is a bare subcommand string (no prose), search every **Subcommands** table in this document — including any in sections appended below — and follow the matching Action column directly. This lets users invoke specific flows via `/claude-api <subcommand>`. If no table in the document matches, treat the request as normal prose.

| Subcommand | Action |
|---|---|
| `migrate` | Migrate existing Claude API code to a newer model. **Read `shared/model-migration.md` immediately** and follow it in order: Step 0 (confirm scope — ask which files/directories before any edit), Step 1 (classify each file), then the per-target breaking-changes section. Do not summarize the guide — execute it. If the user did not name a target model, ask which model to migrate to in the same turn as the scope question. |

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

| Language   | Tool Runner | Managed Agents | Notes                                 |
| ---------- | ----------- | -------------- | ------------------------------------- |
| Python     | Yes (beta)  | Yes (beta)     | Full support — `@beta_tool` decorator |
| TypeScript | Yes (beta)  | Yes (beta)     | Full support — `betaZodTool` + Zod    |
| Java       | Yes (beta)  | Yes (beta)     | Beta tool use with annotated classes  |
| Go         | Yes (beta)  | Yes (beta)     | `BetaToolRunner` in `toolrunner` pkg  |
| Ruby       | Yes (beta)  | Yes (beta)     | `BaseTool` + `tool_runner` in beta    |
| C#         | Yes (beta)  | Yes (beta)     | `BetaToolRunner` + raw JSON schema    |
| PHP        | Yes (beta)  | Yes (beta)     | `BetaRunnableTool` + `toolRunner()`   |
| cURL       | N/A         | Yes (beta)     | Raw HTTP, no SDK features             |

> **Managed Agents code examples**: dedicated language-specific READMEs are provided for Python, TypeScript, Go, Ruby, PHP, Java, and cURL (`{lang}/managed-agents/README.md`, `curl/managed-agents.md`). Read your language's README plus the language-agnostic `shared/managed-agents-*.md` concept files. **Agents are persistent — create once, reference by ID.** Store the agent ID returned by `agents.create` and pass it to every subsequent `sessions.create`; do not call `agents.create` in the request path. The Anthropic CLI (`ant`) is one convenient way to create agents and environments from version-controlled YAML — see `shared/anthropic-cli.md`. If a binding you need isn't shown in the README, WebFetch the relevant entry from `shared/live-sources.md` rather than guess. C# has beta Managed Agents support via `client.Beta.Agents` and related namespaces.

---

## Which Surface Should I Use?

> **Start simple.** Default to the simplest tier that meets your needs. Single API calls and workflows handle most use cases — only reach for agents when the task genuinely requires open-ended, model-driven exploration.

| Use Case                                        | Tier            | Recommended Surface       | Why                                                          |
| ----------------------------------------------- | --------------- | ------------------------- | ------------------------------------------------------------ |
| Classification, summarization, extraction, Q&A  | Single LLM call | **Claude API**            | One request, one response                                    |
| Batch processing or embeddings                  | Single LLM call | **Claude API**            | Specialized endpoints                                        |
| Multi-step pipelines with code-controlled logic | Workflow        | **Claude API + tool use** | You orchestrate the loop                                     |
| Custom agent with your own tools                | Agent           | **Claude API + tool use** | Maximum flexibility                                          |
| Server-managed stateful agent with workspace    | Agent           | **Managed Agents**        | Anthropic runs the loop and hosts the tool-execution sandbox |
| Persisted, versioned agent configs              | Agent           | **Managed Agents**        | Agents are stored objects; sessions pin to a version         |
| Long-running multi-turn agent with file mounts  | Agent           | **Managed Agents**        | Per-session containers, SSE event stream, Skills + MCP       |

> **Note:** Managed Agents is the right choice when you want Anthropic to run the agent loop *and* host the container where tools execute — file ops, bash, code execution all run in the per-session workspace. If you want to host the compute yourself or run your own custom tool runtime, Claude API + tool use is the right choice — use the tool runner for automatic loop handling, or the manual loop for fine-grained control (approval gates, custom logging, conditional execution).

> **Cloud-provider access.** **Claude Platform on AWS** is Anthropic-operated with same-day API parity — see `shared/claude-platform-on-aws.md` for client setup. For per-feature availability on **Claude Platform on AWS**, **Amazon Bedrock**, **Google Vertex AI**, and **Microsoft Foundry**, see `shared/platform-availability.md` — that table is the single source of truth in this skill; do not infer availability from anywhere else.

### Decision Tree

```
What does your application need?

0. Which provider?
   ├── First-party API or Claude Platform on AWS → continue (full surface available; per-feature exceptions in shared/platform-availability.md).
   └── Amazon Bedrock, Google Vertex AI, or Microsoft Foundry → Claude API (+ tool use for agents); see shared/platform-availability.md for per-feature support.

1. Single LLM call (classification, summarization, extraction, Q&A)
   └── Claude API — one request, one response

2. Do you want Anthropic to run the agent loop and host a per-session
   container where Claude executes tools (bash, file ops, code)?
   └── Yes → Managed Agents — server-managed sessions, persisted agent configs,
       SSE event stream, Skills + MCP, file mounts.
       Examples: "stateful coding agent with a workspace per task",
                 "long-running research agent that streams events to a UI",
                 "agent with persisted, versioned config used across many sessions"

3. Workflow (multi-step, code-orchestrated, with your own tools)
   └── Claude API with tool use — you control the loop

4. Open-ended agent (model decides its own trajectory, your own tools, you host the compute)
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

**Supporting endpoints** — Batches (`POST /v1/messages/batches`), Files (`POST /v1/files`), Token Counting (`POST /v1/messages/count_tokens` — see `shared/token-counting.md`), and Models (`GET /v1/models`, `GET /v1/models/{id}` — live capability/context-window discovery) feed into or support Messages API requests.

---

## Current Models (cached: 2026-06-24)

| Model             | Model ID            | Context        | Input $/1M | Output $/1M |
| ----------------- | ------------------- | -------------- | ---------- | ----------- |
| Claude Fable 5    | `claude-fable-5`      | 1M             | $10.00     | $50.00      |
| Claude Mythos 5 (Project Glasswing only) | `claude-mythos-5` | 1M | $10.00     | $50.00      |
| Claude Opus 4.8   | `claude-opus-4-8`   | 1M             | $5.00      | $25.00      |
| Claude Opus 4.7   | `claude-opus-4-7`   | 1M             | $5.00      | $25.00      |
| Claude Opus 4.6   | `claude-opus-4-6`   | 1M             | $5.00      | $25.00      |
| Claude Sonnet 5   | `claude-sonnet-5`   | 1M             | $3.00 ($2.00 intro through 2026-08-31) | $15.00 ($10.00 intro) |
| Claude Sonnet 4.6 | `claude-sonnet-4-6` | 1M             | $3.00      | $15.00      |
| Claude Haiku 4.5  | `claude-haiku-4-5`  | 200K           | $1.00      | $5.00       |

**ALWAYS use `claude-opus-4-8` unless the user explicitly names a different model.** This is non-negotiable. Do not use `claude-sonnet-5`, `claude-sonnet-4-6`, or any other model unless the user literally says "use sonnet" or "use haiku". Never downgrade for cost — that's the user's decision, not yours. Use `claude-fable-5` only when the user explicitly asks for Claude Fable 5, "fable", or Anthropic's most capable model — it has different API behavior than the Opus family (see below) and pricing that exceeds Opus-tier.

### Claude Fable 5 (`claude-fable-5`) — most capable widely released model

Claude Fable 5 is Anthropic's most capable widely released model, for the most demanding reasoning and long-horizon agentic work. **Claude Mythos 5** (`claude-mythos-5`) offers the same capabilities, pricing, and API surface through Project Glasswing (participation is the only way to access it), succeeding the invitation-only Claude Mythos Preview (`claude-mythos-preview`) — everything below applies to both models. 1M context window (the maximum is also the default), 128K max output. Key API differences from Opus-tier — see `shared/model-migration.md` → Migrating to Claude Fable 5 for details:

- **Thinking is always on** — omit the `thinking` parameter entirely (or send `{type: "adaptive"}`). Any other explicit configuration is rejected: `{type: "disabled"}` and `{type: "enabled", budget_tokens: N}` both return a 400. Control depth with `output_config.effort` (supports `low` through `xhigh` and `max`).
- **The raw chain of thought is never returned** — responses carry regular `thinking` blocks (not `redacted_thinking`): `display: "summarized"` returns a readable summary, `"omitted"` (the default) leaves the `thinking` field as an empty string. Replay rules: pass thinking blocks back exactly as received on the same model (including empty-text blocks — the API rejects *modified* blocks, not read ones); a **different** model **drops** them from the prompt (typically silently — not an error; the drop happens before pricing, so dropped blocks aren't billed and there's nothing to strip). Regular thinking blocks from other models replay across models freely.
- **Tokenizer** — same tokenizer as Opus 4.8 (introduced with Opus 4.7). Token counts are roughly unchanged when migrating from Opus 4.7/4.8; per-token pricing differs. Coming from Opus 4.6, Sonnet, Haiku, or older, re-baseline with `count_tokens`.
- **`refusal` stop reason — handle it, and opt into fallbacks by default** — safety classifiers may decline a request (HTTP 200, `stop_reason: "refusal"`, with a `stop_details` category). A pre-output refusal has an empty `content` array and is not billed at all; a mid-stream refusal bills the already-streamed output — discard the partial output. Always check `stop_reason` before reading `content`. Recovery is **opt-in on the API**: most Claude consumer surfaces ship with built-in Claude Opus 4.8 fallbacks, but an API request that doesn't opt in simply stops on a refusal — and false positives on benign adjacent work (security tooling, life-sciences tasks) do happen. **When you write `claude-fable-5` code, include the server-side `fallbacks` parameter by default** (`betas: ["server-side-fallback-2026-06-01"]` + `fallbacks: [{"model": "claude-opus-4-8"}]`; Claude API and Claude Platform on AWS): a declined request is transparently re-served by the fallback model inside the same call, with credit-style repricing applied automatically (a decline before any output isn't billed; the rescue bills at the fallback model's own rates). Tell the user you've enabled it; drop it only if they decline. The GA SDKs' client-side `BetaRefusalFallbackMiddleware` + `BetaFallbackState` handle retry everywhere server-side fallbacks aren't supported (incl. Amazon Bedrock, Vertex AI, Microsoft Foundry); fallback credit refunds the cache-switch cost of client-side retries. Code examples: the Refusal Fallbacks section of your language's claude-api doc; full semantics in the migration guide's refusal section.
- **No assistant prefill** — same as the rest of the 4.6+ family.
- **30-day data retention required** — Claude Fable 5 is not available under zero data retention; requests from an org whose retention configuration doesn't meet the requirement return `400 invalid_request_error`.
- **Longer turns, different prompting** — single requests on hard tasks can run many minutes (plan timeouts/streaming/progress UX); effort sweeps should include low/medium for routine work; prompts written for prior models are often too prescriptive and reduce output quality. See `shared/model-migration.md` → Migrating to Claude Fable 5 → Behavioral shifts (prompt-tunable) for the recommended prompt snippets (anti-overplanning, no-tidying, grounded progress claims, boundaries, async sub-agents, memory, `send_to_user`).

**CRITICAL: Use only the exact model ID strings from the table above — they are complete as-is. Do not append date suffixes.** For example, use `claude-sonnet-4-6`, never `claude-sonnet-4-6-20251114` or any other date-suffixed variant you might recall from training data. If the user requests an older model not in the table (e.g., "opus 4.5", "sonnet 3.7"), read `shared/models.md` for the exact ID — do not construct one yourself.

A note: if any of the model strings above look unfamiliar to you, that's to be expected — that just means they were released after your training data cutoff. Rest assured they are real models; we wouldn't mess with you like that.

**Live capability lookup:** The table above is cached. When the user asks "what's the context window for X", "does X support vision/thinking/effort", or "which models support Y", query the Models API (`client.models.retrieve(id)` / `client.models.list()`) — see `shared/models.md` for the field reference and capability-filter examples.

---

## Authentication (Quick Reference)

**An unset `ANTHROPIC_API_KEY` does NOT mean there are no credentials.** The SDKs and the `ant` CLI resolve credentials in this order (first match wins): `ANTHROPIC_API_KEY` → `ANTHROPIC_AUTH_TOKEN` → the `ANTHROPIC_PROFILE`-selected or active OAuth profile from `ant auth login` → Workload Identity Federation env vars → the default profile on disk. A bare `Anthropic()` / `new Anthropic()` / `anthropic.NewClient()` works after `ant auth login` with no env var set.

**When you need to call the API and `ANTHROPIC_API_KEY` is unset, don't ask the user for a key.** First run `ant auth status` — it shows which credential source and profile is active. If it reports an active profile:

- **SDK code or `ant` CLI:** just run it. The zero-arg client constructor and every `ant …` subcommand pick up the profile automatically — no env var needed.
- **Raw `curl` / HTTP:** get a short-lived token with `ant auth print-credentials --access-token` and send it as `Authorization: Bearer <token>` **plus** the header `anthropic-beta: oauth-2025-04-20` (OAuth tokens go on `Authorization: Bearer`, not `x-api-key:` — converting a curl from an API key is a header change, not a key swap). Always pass `--access-token`; the no-flag form prints JSON, not a bare token.

Only ask the user for a key if `ant auth status` reports no active credential source (or `ant` itself isn't installed). Suggest `ant auth login` as the first option — it stores a profile under `~/.config/anthropic/` that the SDKs read automatically — and an exported `ANTHROPIC_API_KEY` as the alternative.

Full auth details (named profiles, scopes, the API-key-shadows-profile trap, refresh-token expiry): `shared/anthropic-cli.md`.

---

## Thinking & Effort (Quick Reference)

**Fable 5 / Opus 4.8 / 4.7 / Sonnet 5 — Adaptive thinking only:** Use `thinking: {type: "adaptive"}`. `thinking: {type: "enabled", budget_tokens: N}` returns a 400 — adaptive is the only on-mode. On Opus 4.8, Opus 4.7, and Sonnet 5, `{type: "disabled"}` and omitting `thinking` both work (on Sonnet 5, omitting runs adaptive; on Opus 4.7/4.8, omitting runs without thinking — set `{type: "adaptive"}` explicitly); on Fable 5, an explicit `{type: "disabled"}` returns a 400 — omit the `thinking` param entirely instead. Sampling parameters (`temperature`, `top_p`, `top_k`) are also removed and will 400. Opus 4.8 keeps the same request surface as 4.7 (no new breaking changes) — see `shared/model-migration.md` → Migrating to Opus 4.8 for the behavioral re-tuning, and → Migrating to Opus 4.7 for the full breaking-change list when coming from 4.6 or earlier. Note: with `thinking` disabled, Opus 4.8 may write longer reasoning into the visible response — leave adaptive thinking on, or add a final-answer-only instruction (see the migration guide).
**Opus 4.6 — Adaptive thinking (recommended):** Use `thinking: {type: "adaptive"}`. Claude dynamically decides when and how much to think. No `budget_tokens` needed — `budget_tokens` is deprecated on Opus 4.6 and Sonnet 4.6 and should not be used for new code. Adaptive thinking also automatically enables interleaved thinking (no beta header needed). **When the user asks for "extended thinking", a "thinking budget", or `budget_tokens`: always use Fable 5, Opus 4.8, 4.7, or 4.6 with `thinking: {type: "adaptive"}`. The concept of a fixed token budget for thinking is deprecated — adaptive thinking replaces it. Do NOT use `budget_tokens` for new 4.6/4.7/4.8 code and do NOT switch to an older model.** *Gradual-migration carve-out:* `budget_tokens` is still functional on Opus 4.6 and Sonnet 4.6 as a transitional escape hatch — if you're migrating existing code and need a hard token ceiling before you've tuned `effort`, see `shared/model-migration.md` → Transitional escape hatch. Note: this carve-out does **not** apply to Fable 5, Opus 4.7 or 4.8 — `budget_tokens` is fully removed there.
**Effort parameter (GA, no beta header):** Controls thinking depth and overall token spend via `output_config: {effort: "low"|"medium"|"high"|"max"}` (inside `output_config`, not top-level). Default is `high` (equivalent to omitting it). `max` is supported on Fable 5, Opus 4.6 and later, Sonnet 5, and Sonnet 4.6 (not Haiku or earlier Sonnets). Opus 4.7 added `"xhigh"` (between `high` and `max`) — the best setting for most coding and agentic use cases on Fable 5 / Opus 4.7/4.8 / Sonnet 5, and the default in Claude Code; use a minimum of `high` for most intelligence-sensitive work. Works on Fable 5, Opus 4.5, Opus 4.6, Opus 4.7, Opus 4.8, Sonnet 5, and Sonnet 4.6. Will error on Sonnet 4.5 / Haiku 4.5. On Fable 5, Opus 4.7/4.8, and Sonnet 5, effort matters more than on any prior model in their tier — re-tune it when migrating, and run long-horizon/agentic tasks at `high`/`xhigh` with the full task spec given up front. Combine with adaptive thinking for the best cost-quality tradeoffs. Lower effort means fewer and more-consolidated tool calls, less preamble, and terser confirmations — `high` is often the sweet spot balancing quality and token efficiency; use `max` when correctness matters more than cost; use `low` for subagents or simple tasks.

**Thinking display — `"omitted"` by default on Fable 5 / Mythos 5 / Opus 4.8 / 4.7 / Sonnet 5:** `display: "summarized"` returns a readable summary of the reasoning; `"omitted"` (the default on all five — a silent change from Opus 4.6 and Sonnet 4.6, where it was `"summarized"`) streams `thinking` blocks with empty text. `display` controls visibility only — thinking happens and is billed the same under every setting; the raw chain of thought is never exposed on any model. If you stream reasoning to users, the default looks like a long pause before output — set `thinking: {type: "adaptive", display: "summarized"}` explicitly. (Independent of display, echo thinking blocks back unchanged when continuing on the same model; other models silently ignore them — see the migration guide.)

**Task Budgets (beta, Fable 5 / Opus 4.7 / 4.8 / Sonnet 5):** `output_config: {task_budget: {type: "tokens", total: N}}` tells the model how many tokens it has for a full agentic loop — it sees a running countdown and self-moderates (minimum 20,000; beta header `task-budgets-2026-03-13`). Distinct from `max_tokens`, which is an enforced per-response ceiling the model is not aware of. See `shared/model-migration.md` → Task Budgets.

**Sonnet 4.6:** Supports adaptive thinking (`thinking: {type: "adaptive"}`). `budget_tokens` is deprecated on Sonnet 4.6 — use adaptive thinking instead.

**Older models (only if explicitly requested):** If the user specifically asks for Sonnet 4.5 or another older model, use `thinking: {type: "enabled", budget_tokens: N}`. `budget_tokens` must be less than `max_tokens` (minimum 1024). Never choose an older model just because the user mentions `budget_tokens` — use Opus 4.8 with adaptive thinking instead.

---

## Compaction (Quick Reference)

**Beta, Fable 5, Opus 4.8, Opus 4.7, Opus 4.6, Sonnet 5, and Sonnet 4.6.** For long-running conversations that may exceed the 1M context window, enable server-side compaction. The API automatically summarizes earlier context when it approaches the trigger threshold (default: 150K tokens). Requires beta header `compact-2026-01-12`.

**Critical:** Append `response.content` (not just the text) back to your messages on every turn. Compaction blocks in the response must be preserved — the API uses them to replace the compacted history on the next request. Extracting only the text string and appending that will silently lose the compaction state.

See `{lang}/claude-api/README.md` (Compaction section) for code examples. Full docs via WebFetch in `shared/live-sources.md`.

---

## Prompt Caching (Quick Reference)

**Prefix match.** Any byte change anywhere in the prefix invalidates everything after it. Render order is `tools` → `system` → `messages`. Keep stable content first (frozen system prompt, deterministic tool list), put volatile content (timestamps, per-request IDs, varying questions) after the last `cache_control` breakpoint.

**Mid-conversation operator instructions** (Claude Opus 4.8 only; no beta header): append `{"role": "system", ...}` to `messages[]` instead of editing top-level `system`. Preserves the cached history prefix and is the prompt-injection-safe operator channel. See `shared/prompt-caching.md` § Mid-conversation system messages.

**Top-level auto-caching** (`cache_control: {type: "ephemeral"}` on `messages.create()`) is the simplest option when you don't need fine-grained placement. Max 4 breakpoints per request. Minimum cacheable prefix is ~1024 tokens — shorter prefixes silently won't cache.

**Verify with `usage.cache_read_input_tokens`** — if it's zero across repeated requests, a silent invalidator is at work (`datetime.now()` in system prompt, unsorted JSON, varying tool set).

For placement patterns, architectural guidance, and the silent-invalidator audit checklist: read `shared/prompt-caching.md`. Language-specific syntax: `{lang}/claude-api/README.md` (Prompt Caching section).

---

## Fast Mode (Quick Reference)

**Research preview, Opus 4.8 / 4.7 only.** Opus 4.7 fast mode is deprecated — after removal, `speed: "fast"` on 4.7 returns an error. Opus 4.8 is the durable fast-capable tier. Fast mode runs the same model at up to 2.5x higher output tokens per second, at premium pricing. Three things are required on every request: use the **beta** messages endpoint (`client.beta.messages.…`), pass the beta flag `fast-mode-2026-02-01`, and set `speed: "fast"` as a top-level request parameter (not a header, not in `extra_body`).

```python
client.beta.messages.create(
    model="claude-opus-4-8", max_tokens=4096,
    speed="fast", betas=["fast-mode-2026-02-01"],
    messages=[...],
)
```

| Language | Beta flag | Speed parameter |
|---|---|---|
| Python | `betas=["fast-mode-2026-02-01"]` | `speed="fast"` |
| TypeScript / Ruby | `betas: ["fast-mode-2026-02-01"]` | `speed: "fast"` |
| Go | `[]anthropic.AnthropicBeta{anthropic.AnthropicBetaFastMode2026_02_01}` | `Speed: anthropic.BetaMessageNewParamsSpeedFast` |
| Java | `.addBeta(AnthropicBeta.FAST_MODE_2026_02_01)` | `.speed(MessageCreateParams.Speed.FAST)` |
| C# | `Betas = ["fast-mode-2026-02-01"]` | `Speed = Speed.Fast` (`Anthropic.Models.Beta.Messages`) |
| PHP | `betas: ['fast-mode-2026-02-01']` | `speed: 'fast'` |
| cURL | `anthropic-beta: fast-mode-2026-02-01` header | `"speed": "fast"` in body |

`response.usage.speed` reports which speed was used. Fast mode has its own rate limit separate from standard Opus; on 429, either retry after the `retry-after` delay or drop `speed` and fall back to standard (note: switching speed invalidates prompt cache). Not available with Batch API, Priority Tier, Claude Platform on AWS, or third-party platforms.

---

## Task Budgets (Quick Reference)

**Beta, Fable 5 / Sonnet 5 / Opus 4.8 / 4.7.** A task budget gives Claude a token ceiling for an agentic loop so it paces itself and finishes gracefully instead of being cut off. Set `task_budget` inside `output_config` on `client.beta.messages.stream(...)` with beta flag `task-budgets-2026-03-13` — use streaming so the large `max_tokens` doesn't hit HTTP timeouts:

```python
with client.beta.messages.stream(
    model="claude-opus-4-8", max_tokens=128000,
    output_config={"effort": "high", "task_budget": {"type": "tokens", "total": 64000}},
    betas=["task-budgets-2026-03-13"],
    messages=[...], tools=[...],
) as stream:
    response = stream.get_final_message()
```

`task_budget` fields: `type` (always `"tokens"`), `total`, and optional `remaining` (defaults to `total`). The server injects a countdown marker Claude sees during generation; the budget counts what Claude generates and the tool results it reads this turn — **not** the full history you resend each request.

**Observing spend:** accumulate `response.usage.output_tokens` (plus the token count of the tool-result blocks you append) across loop iterations if you want to display progress. Leave `remaining` unset in the normal loop — the server tracks the countdown itself, and passing a client-computed `remaining` while also resending full history under-reports the budget. **Only pass `remaining`** when you compact or rewrite history between requests and the server can no longer derive prior spend.

---

## Provider Clients (Quick Reference)

When targeting Claude on a third-party platform, use that platform's dedicated client class — not the first-party `Anthropic()` client with a `base_url` override. After construction the client exposes the same `messages.create` / `.stream` surface as the first-party SDK.

### Amazon Bedrock

Use the **Mantle** client (Messages-API Bedrock endpoint). Bedrock model IDs take an `anthropic.` prefix (e.g. `"anthropic.claude-opus-4-8"`). Region is required.

| Language | Client |
|---|---|
| Python | `from anthropic import AnthropicBedrockMantle` → `AnthropicBedrockMantle(aws_region="…")` |
| TypeScript | `import { AnthropicBedrockMantle } from "@anthropic-ai/bedrock-sdk"` → `new AnthropicBedrockMantle({ awsRegion: "…" })` |
| Go | `bedrock.NewMantleClient(ctx, bedrock.MantleClientConfig{ AWSRegion: "…" })` |
| Java | `AnthropicOkHttpClient.builder().backend(BedrockMantleBackend.fromEnv()).build()` (from `com.anthropic.bedrock.backends`) |
| C# | `new AnthropicBedrockMantleClient(new() { AwsRegion = "…" })` (package `Anthropic.Bedrock`) |
| PHP | `use Anthropic\Bedrock\MantleClient;` → `new MantleClient(awsRegion: '…')` |
| Ruby | `Anthropic::BedrockMantleClient.new(aws_region: "…")` |

`AnthropicBedrock` / `BedrockClient` / `BedrockBackend` (without `Mantle`) are the legacy `bedrock-runtime` InvokeModel path — prefer the Mantle client for new code.

### Microsoft Foundry

| Language | Client |
|---|---|
| Python | `from anthropic import AnthropicFoundry` → `AnthropicFoundry(api_key=…, resource="…")` |
| TypeScript | `import AnthropicFoundry from "@anthropic-ai/foundry-sdk"` → `new AnthropicFoundry({ … })` |
| Java | `AnthropicOkHttpClient.builder().backend(FoundryBackend.fromEnv()).build()` (from `com.anthropic.foundry.backends`) |
| C# | `new AnthropicFoundryClient(new AnthropicFoundryApiKeyCredentials(…))` (package `Anthropic.Foundry`) |
| PHP | `Foundry\Client::withCredentials(…)` |

The Go and Ruby SDKs do not currently support Foundry. For Ruby, use the standard `Anthropic::Client.new(base_url: "<foundry endpoint>")` as a fallback (Entra ID auth is not built in). For Claude Platform on AWS, see `shared/claude-platform-on-aws.md`.

### Google Cloud Vertex AI

Two required constructor args: GCP `project_id` and `region`. Vertex model IDs take **no prefix** — current-generation models (Opus 4.8/4.7/4.6, Sonnet 5, Sonnet 4.6) use the bare first-party ID (e.g. `"claude-opus-4-8"`); dated-snapshot models use an `@` version separator (e.g. `claude-opus-4-5@20251101`, **not** `claude-opus-4-5-20251101`). Auth is GCP ADC (`gcloud auth application-default login`); no Anthropic API key. `region` can be `"global"` (recommended), a multi-region (`"us"`/`"eu"`), or a specific region. After construction, use the same `messages.create` / `.stream` surface.

| Language | Client |
|---|---|
| Python | `from anthropic import AnthropicVertex` → `AnthropicVertex(project_id="…", region="…")` (install `"anthropic[vertex]"`) |
| TypeScript | `import { AnthropicVertex } from "@anthropic-ai/vertex-sdk"` → `new AnthropicVertex({ projectId, region })` |
| Go | `import "github.com/anthropics/anthropic-sdk-go/vertex"` → `anthropic.NewClient(vertex.WithGoogleAuth(ctx, region, projectID))` |
| Java | `AnthropicOkHttpClient.builder().backend(VertexBackend.builder().region("…").project("…").build()).build()` (from `com.anthropic.vertex.backends`) |
| C# | `new AnthropicClient { Backend = new VertexBackend(projectId, region) }` (package `Anthropic.Vertex`) |
| PHP | `use Anthropic\Vertex;` → `Vertex\Client::fromEnvironment(location: '…', projectId: '…')` — note `location`, not `region` |
| Ruby | `Anthropic::VertexClient.new(region: "…", project_id: "…")` |

---

## Context Editing (Quick Reference)

**Beta.** Context editing **clears** old tool results or thinking blocks from the conversation before the model sees it; it is **not compaction** (which summarizes). On `client.beta.messages.*` with beta `context-management-2025-06-27`, pass `context_management.edits` with a strategy type:

```python
client.beta.messages.create(
    model="claude-opus-4-8", max_tokens=4096,
    betas=["context-management-2025-06-27"],
    context_management={"edits": [{"type": "clear_tool_uses_20250919"}]},
    tools=[...], messages=[...],
)
```

Strategy types: `clear_tool_uses_20250919` (clears old tool results; optional `clear_tool_inputs: true` also clears the tool_use params) and `clear_thinking_20251015` (clears thinking blocks). Do **not** use `compact_20260112` or beta `compact-2026-01-12` — those are the separate compaction feature.

---

## Mid-Conversation System Messages (Quick Reference)

**Claude Opus 4.8 only; no beta header.** Append `{"role": "system", "content": "…"}` to the `messages` array (not the top-level `system` field) to add an operator instruction mid-conversation without invalidating the cached prefix. Use the regular `client.messages.create` — there is no beta. A mid-conversation system message must follow a `user` message (or an `assistant` message ending in server-tool use), and must be either the last entry in `messages` or be followed by an `assistant` turn — it cannot be `messages[0]`. Availability: `shared/platform-availability.md`. See `shared/prompt-caching.md` § Mid-conversation system messages.

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

**Reading guide:** Start with `shared/managed-agents-overview.md`, then the topical `shared/managed-agents-*.md` files (core, environments, tools, events, outcomes, multiagent, webhooks, memory, scheduled-deployments, client-patterns, onboarding, api-reference). For Python, TypeScript, Go, Ruby, PHP, and Java, read `{lang}/managed-agents/README.md` for code examples. For cURL, read `curl/managed-agents.md`. **Agents are persistent — create once, reference by ID.** Store the agent ID returned by `agents.create` and pass it to every subsequent `sessions.create`; do not call `agents.create` in the request path. The Anthropic CLI (`ant`) is one convenient way to create agents and environments from version-controlled YAML — see `shared/anthropic-cli.md`. If a binding you need isn't shown in the language README, WebFetch the relevant entry from `shared/live-sources.md` rather than guess. C# has beta Managed Agents support via `client.Beta.Agents` and related namespaces.

**When the user wants to set up a Managed Agent from scratch** (e.g. "how do I get started", "walk me through creating one", "set up a new agent"): read `shared/managed-agents-onboarding.md` and run its interview — same flow as the `managed-agents-onboard` subcommand.

**When the user asks "how do I write the client code for X":** reach for `shared/managed-agents-client-patterns.md` — covers lossless stream reconnect, `processed_at` queued/processed gate, interrupt, `tool_confirmation` round-trip, the correct idle/terminated break gate, post-idle status race, stream-first ordering, file-mount gotchas, keeping credentials host-side via custom tools, etc.

**When the user wants the agent to run on a schedule** (cron, "every night", "weekly report"): read `shared/managed-agents-scheduled-deployments.md` — deployments fire sessions autonomously on a cron cadence, with per-firing run records and lifecycle controls (pause/unpause/archive).

---

## Server Tools (Quick Reference)

Server-side tools run on Anthropic's infrastructure — no client-side execution loop. Declare in `tools`; results arrive as content blocks in the same response. **No beta header** unless noted. **Prefer the latest type variant your model supports.** The `_20260209` web search / web fetch variants below (dynamic filtering) require Opus 4.8/4.7/4.6, Sonnet 5, or Sonnet 4.6; the basic variants for older models are listed after the table.

| Tool | `type` | `name` | Key optional params | Result block type |
|---|---|---|---|---|
| Web search | `web_search_20260209` | `web_search` | `max_uses`, `allowed_domains`/`blocked_domains`, `user_location` | `web_search_tool_result` → `.content` is a list of `web_search_result` |
| Web fetch | `web_fetch_20260209` | `web_fetch` | `max_uses`, `allowed_domains`/`blocked_domains`, `citations`, `max_content_tokens` | `web_fetch_tool_result` → `.content` is a `web_fetch_result` with a `document` block |
| Code execution | `code_execution_20260521` | `code_execution` | none | `bash_code_execution_tool_result` → `.content.stdout` / `.stderr` / `.return_code` |
| Tool search (regex) | `tool_search_tool_regex_20251119` | `tool_search_tool_regex` | mark other tools `defer_loading: true` | `tool_search_tool_result` |
| Tool search (BM25) | `tool_search_tool_bm25_20251119` | `tool_search_tool_bm25` | mark other tools `defer_loading: true` | `tool_search_tool_result` |

`web_search_20260209` / `web_fetch_20260209` have built-in dynamic filtering — code execution runs under the hood, so do **not** separately declare `code_execution` in `tools` (a second execution environment confuses the model). For models older than Opus 4.6 / Sonnet 4.6, use the basic variants `web_search_20250305` / `web_fetch_20250910` instead; on Vertex AI only basic `web_search_20250305` is available. `code_execution_20260120` (REPL persistence + programmatic tool calling) runs on Opus 4.5+ / Sonnet 4.5+. **Go SDK only**: `code_execution_20260521` lives under `client.Beta.Messages.New` with `Betas: []anthropic.AnthropicBeta{"code-execution-2025-08-25"}` (other languages use plain `client.messages.create`); `code_execution_20260120` uses the non-beta `client.Messages.New` in Go like everywhere else. Web fetch only fetches URLs already present in the conversation. Provider availability varies by tool — see `shared/platform-availability.md`. See `shared/tool-use-concepts.md` for `pause_turn` handling.

## Document & File Input (Quick Reference)

**PDF (base64, no beta):** `{"type": "document", "source": {"type": "base64", "media_type": "application/pdf", "data": <b64 string>}}` in user content, placed before the text block. Base64 string must have no newlines. Limits: 32 MB request, 600 pages (100 for 200k-context models). Java: `ContentBlockParam.ofDocument(DocumentBlockParam... Base64PdfSource.builder().data(...))`.

**Files API (beta `files-api-2025-04-14`):** upload via `client.beta.files.upload(...)` → response `id` is the `file_id`. Reference it as `{"type": "document", "source": {"type": "file", "file_id": "..."}}` for PDF/text, or `{"type": "image", ...}` for images — the content-block type must match the file's MIME type. The beta header is required on **both** the upload and the `messages.create` that references the file. Availability: `shared/platform-availability.md`.

**Citations (no beta):** set `citations: {enabled: true}` on each `document` content block (all or none). Response splits into multiple `text` blocks; cited blocks carry a `citations` array. Each citation has `cited_text`, `document_index`, `document_title`, and a location by `type`: `char_location` (`start_char_index`/`end_char_index`) for plain text, `page_location` (`start_page_number`/`end_page_number`, 1-indexed) for PDF, `content_block_location` for custom content. Incompatible with `output_config.format`.

## Tool Use Patterns (Quick Reference)

**Strict tool use (no beta):** set `strict: true` as a top-level field on the tool definition (alongside `name`/`description`/`input_schema`), **not** on `tool_choice`. Schema must have `additionalProperties: false` + `required`. Guarantees `tool_use.input` validates exactly. Go: `Strict: anthropic.Bool(true)` + `additionalProperties` via `InputSchema.ExtraFields`; Java: `.strict(true)` + `.putAdditionalProperty("additionalProperties", JsonValue.from(false))`.

**Parallel tool use (default on):** one assistant message may contain multiple `tool_use` blocks. Execute them concurrently, then return **all** `tool_result` blocks in a **single** user message (don't split across multiple messages). For a failed tool, return `tool_result` with `is_error: true` — don't drop it.

**Tool Runner (SDK beta helper):** drives the tool-call loop for you via `client.beta.messages.*`. Python: `@beta_tool` decorator + `client.beta.messages.tool_runner(...)` → `runner.until_done()`. TypeScript: `betaZodTool({...})` from `@anthropic-ai/sdk/helpers/beta/zod` + `client.beta.messages.toolRunner(...)` → `await runner`. Go: `toolrunner.NewBetaToolFromJSONSchema(...)` + `client.Beta.Messages.NewToolRunner(...)` → `.RunToCompletion(ctx)`. Java requires `.addBeta("structured-outputs-2025-11-13")`. Ruby: `Anthropic::BaseTool` subclass + `client.beta.messages.tool_runner(...)`. PHP: `BetaRunnableTool` + `->toolRunner(...)`. C#: raw JSON-schema tools + `BetaToolRunner` via `client.Beta.Messages.ToolRunner(...)`.

**Programmatic tool calling (no beta header):** Claude calls your custom tool from inside code execution. Add `{"type": "code_execution_20260120", "name": "code_execution"}` **and** set `"allowed_callers": ["code_execution_20260120"]` on your custom tool. Opus 4.5+ / Sonnet 4.5+ (availability: `shared/platform-availability.md`). When responding to a pending programmatic call, the user message must contain **only** `tool_result` blocks (no text). Not compatible with `strict: true`, `disable_parallel_tool_use`, forced `tool_choice`, or MCP tools.

## Other API Surfaces (Quick Reference)

**Message Batches (no beta; availability: `shared/platform-availability.md`):** `client.messages.batches.create(requests=[{custom_id, params}, ...])` → poll `client.messages.batches.retrieve(id).processing_status` until `"ended"` → stream `client.messages.batches.results(id)`. Each result has `.custom_id` + `.result.type` (`succeeded`/`errored`/`canceled`/`expired`); on success read `.result.message.content`. Python wraps requests as `Request(custom_id=..., params=MessageCreateParamsNonStreaming(...))`. Results arrive in **any order** — key by `custom_id`, never by position.

**Models API (no beta; availability: `shared/platform-availability.md`):** `client.models.list()` (auto-paginates) and `client.models.retrieve("claude-opus-4-8")`. Each model object has `id`, `display_name`, `created_at`, and — since Mar 2026 — `max_input_tokens` (the context window), `max_tokens` (the output cap), and `capabilities`. There is no `context_window` field.

**Stop details (GA, Opus 4.7+):** `response.stop_details` is populated **only when `stop_reason == "refusal"`** (fields: `type: "refusal"`, `category: "cyber"|"bio"|null`, `explanation`). It is `null` for every other `stop_reason` (`end_turn`, `max_tokens`, `tool_use`, `pause_turn`, …) — always guard before reading.

**Client config (no beta):** `timeout` default 10 min; **units differ by SDK** — Python/Ruby: seconds; TypeScript: **milliseconds**; Go `option.WithRequestTimeout(time.Duration)`; Java `Duration`; C# `TimeSpan`. TS scales the default up to 60 min for large `max_tokens` on non-streaming requests; Java does so for streaming requests (Java non-streaming scales 30s–10 min). `max_retries`/`maxRetries` default 2 (retries 408/409/429/5xx + connection errors). `base_url` (or `ANTHROPIC_BASE_URL` env). Per-request override: Python `client.with_options(timeout=5.0).messages.create(...)`; TS `client.messages.create({...}, {timeout: 5_000})`; Ruby `request_options: {timeout: 5}`. Timeouts are retried — wall-clock can reach `timeout × (max_retries+1)`.

## Workload Identity Federation (Quick Reference)

**GA, no beta header.** Construct the normal zero-arg client (`Anthropic()` / `new Anthropic()` / `anthropic.NewClient()` / `AnthropicOkHttpClient.fromEnv()`); the SDK auto-detects WIF when **all** of `ANTHROPIC_FEDERATION_RULE_ID`, `ANTHROPIC_ORGANIZATION_ID`, `ANTHROPIC_SERVICE_ACCOUNT_ID`, and `ANTHROPIC_IDENTITY_TOKEN_FILE` (or `ANTHROPIC_IDENTITY_TOKEN`) are set, exchanges the JWT at `/v1/oauth/token`, and auto-refreshes. `ANTHROPIC_WORKSPACE_ID` does not gate activation — required only when the federation rule spans multiple workspaces (else 400 `workspace_id_required`), optional for single-workspace rules. `ANTHROPIC_API_KEY` or `ANTHROPIC_AUTH_TOKEN` (even empty) outrank WIF, and a set `ANTHROPIC_PROFILE` also wins over the federation env vars (a missing named profile is an error, not a fall-through) — unset all three.

---

## Reading Guide

After detecting the language, read the relevant files based on what the user needs.

**All SDK languages use the same multi-file layout** — directory `{lang}/claude-api/` containing `README.md` (install, client init, basic request, thinking, caching, stop details, misc), `tool-use.md` (tool definitions, agentic loop, Anthropic-defined tools, structured outputs), `streaming.md`, `batches.md`, `files-api.md`. Not every language has every file (e.g., Ruby has no `batches.md`); if a file is absent, that feature's example is not yet documented for that language — fall back to the cURL shape or WebFetch the SDK repo from `shared/live-sources.md`. **cURL** → `curl/examples.md`.

The Quick Task Reference below uses the `{lang}/claude-api/FILE.md` path notation for all languages.

### Quick Task Reference

**Single text classification/summarization/extraction/Q&A:**
→ Read only `{lang}/claude-api/README.md`

**Chat UI or real-time response display:**
→ Read `{lang}/claude-api/README.md` + `{lang}/claude-api/streaming.md`

**Long-running conversations (may exceed context window):**
→ Read `{lang}/claude-api/README.md` — see Compaction section
**Migrating to a newer model (Fable 5 / Opus 4.8 / Opus 4.7 / Opus 4.6 / Sonnet 5 / Sonnet 4.6) or replacing a retired model:**
→ Read `shared/model-migration.md`
**Prompting or tuning Fable 5 (long turns, effort, verbosity, autonomous runs, sub-agents):**
→ Read `shared/model-migration.md` → Migrating to Fable 5 → Behavioral shifts (prompt-tunable) + Long-running agent recommendations
**Prompt caching / optimize caching / "why is my cache hit rate low":**
→ Read `shared/prompt-caching.md` + `{lang}/claude-api/README.md` (Prompt Caching section)
**Count tokens in a file / prompt / diff ("how many tokens is X"):**
→ Read `shared/token-counting.md` — use `messages.count_tokens`, never `tiktoken`

**Function calling / tool use / agents:**
→ Read `{lang}/claude-api/README.md` + `shared/tool-use-concepts.md` + `{lang}/claude-api/tool-use.md`

**Agent design (tool surface, context management, caching strategy):**
→ Read `shared/agent-design.md`

**Batch processing (non-latency-sensitive):**
→ Read `{lang}/claude-api/README.md` + `{lang}/claude-api/batches.md`

**File uploads across multiple requests:**
→ Read `{lang}/claude-api/README.md` + `{lang}/claude-api/files-api.md`

**Managed Agents (server-managed stateful agents with workspace):**
→ Read `shared/managed-agents-overview.md` + the rest of the `shared/managed-agents-*.md` files. For Python, TypeScript, Go, Ruby, PHP, and Java, read `{lang}/managed-agents/README.md` for code examples. For cURL, read `curl/managed-agents.md`. **Agents are persistent — create once, reference by ID.** Store the agent ID returned by `agents.create` and pass it to every subsequent `sessions.create`; do not call `agents.create` in the request path. The Anthropic CLI (`ant`) is one convenient way to create agents and environments from version-controlled YAML — see `shared/anthropic-cli.md`. If a binding you need isn't shown in the language README, WebFetch the relevant entry from `shared/live-sources.md` rather than guess. C# has beta Managed Agents support — see `csharp/claude-api/README.md` for details, or `curl/managed-agents.md` for raw HTTP reference.

### Claude API (Full File Reference)

Read the **language-specific Claude API source** — `{language}/claude-api/` for every SDK language, `curl/examples.md` for cURL:

1. **`{language}/claude-api/README.md`** — **Read this first.** Installation, quick start, common patterns, error handling.
2. **`shared/tool-use-concepts.md`** — Read when the user needs function calling, code execution, memory, or structured outputs. Covers conceptual foundations.
3. **`shared/agent-design.md`** — Read when designing an agent: bash vs. dedicated tools, programmatic tool calling, tool search/skills, context editing vs. compaction vs. memory, caching principles.
4. **`{language}/claude-api/tool-use.md`** — Read for language-specific tool use code examples (tool runner, manual loop, code execution, memory, structured outputs).
5. **`{language}/claude-api/streaming.md`** — Read when building chat UIs or interfaces that display responses incrementally.
6. **`{language}/claude-api/batches.md`** — Read when processing many requests offline (not latency-sensitive). Runs asynchronously at 50% cost.
7. **`{language}/claude-api/files-api.md`** — Read when sending the same file across multiple requests without re-uploading.
8. **`shared/prompt-caching.md`** — Read when adding or optimizing prompt caching. Covers prefix-stability design, breakpoint placement, and anti-patterns that silently invalidate cache.
9. **`shared/error-codes.md`** — Read when debugging HTTP errors or implementing error handling. Includes the per-SDK typed exception class table and the Go `errors.As` pattern.
10. **`shared/model-migration.md`** — Read when upgrading to newer models, replacing retired models, or translating `budget_tokens` / prefill patterns to the current API.
11. **`shared/live-sources.md`** — WebFetch URLs for fetching the latest official documentation.

Not every language has every file (e.g., Ruby has no `batches.md`); if a file is absent, that feature's example is not yet documented for that language.

> **Note:** For the Managed Agents file reference, see the `## Managed Agents (Beta)` section above — it lists every `shared/managed-agents-*.md` file and the language-specific READMEs.

---

## When to Use WebFetch

Use WebFetch to get the latest documentation when:

- User asks for "latest" or "current" information
- Cached data seems incorrect
- User asks about features not covered here

Live documentation URLs are in `shared/live-sources.md`.

## Common Pitfalls

- **No `ANTHROPIC_API_KEY` ≠ no credentials.** Don't bail or ask the user for a key just because the env var is unset — run `ant auth status` first. After `ant auth login`, a bare `Anthropic()` client and `ant …` work with no env var; for raw curl, use `Authorization: Bearer $(ant auth print-credentials --access-token)` plus header `anthropic-beta: oauth-2025-04-20`. See the Authentication quick reference above and `shared/anthropic-cli.md`.
- Don't truncate inputs when passing files or content to the API. If the content is too long to fit in the context window, notify the user and discuss options (chunking, summarization, etc.) rather than silently truncating.
- **Fable 5 / Sonnet 5 / Opus 4.8 / 4.7 thinking:** Adaptive only. `thinking: {type: "enabled", budget_tokens: N}` returns 400 — `budget_tokens` is fully removed (along with `temperature`, `top_p`, `top_k`). Use `thinking: {type: "adaptive"}`. Opus 4.8 inherits this surface from 4.7 with no new breaking changes; Fable 5 adds one — an explicit `thinking: {type: "disabled"}` returns a 400 (accepted on Sonnet 5 / 4.7 / 4.8); omit the param instead.
- **Opus 4.6 / Sonnet 4.6 thinking:** Use `thinking: {type: "adaptive"}` — do NOT use `budget_tokens` for new 4.6 code (deprecated on both Opus 4.6 and Sonnet 4.6; for gradual migration of existing code, see the transitional escape hatch in `shared/model-migration.md` — note this carve-out does not apply to Fable 5, Opus 4.7 or 4.8). For older models, `budget_tokens` must be less than `max_tokens` (minimum 1024). This will throw an error if you get it wrong.
- **Prefill removed (Fable 5 and the 4.6/4.7/4.8 family):** Assistant message prefills (last-assistant-turn prefills) return a 400 error on Fable 5, Opus 4.6, Opus 4.7, Opus 4.8, and Sonnet 4.6. Use structured outputs (`output_config.format`) or system prompt instructions to control response format instead. (One exception: the fallback-credit prefill claim — when redeeming a credit with `fallback_has_prefill_claim: true`, the server accepts the echoed assistant message; see the migration guide's refusal section.)
- **Fable 5 `refusal` stop reason:** Safety classifiers may decline a request — a successful HTTP 200 with `stop_reason: "refusal"` (pre-output: empty `content`, nothing billed; mid-stream: partial output billed — discard it). Check `stop_reason` before reading `response.content[0]`, or you'll hit index errors on refused requests. To retry on another model, replay the history as-is — other models drop the refused model's thinking blocks from the prompt, unbilled; no stripping needed (and a fallback-credit redemption must echo the refused body exactly anyway, thinking blocks included). Fallbacks are **opt-in** — new `claude-fable-5` code should include the server-side `fallbacks` parameter by default so a refusal doesn't fail the request outright; see the Claude Fable 5 section above.
- **Fable 5 tokenizer:** Same tokenizer as Opus 4.8 — token counts are roughly unchanged when migrating from Opus 4.7/4.8. Coming from Opus 4.6, Sonnet, Haiku, or older, token counts differ (the Opus 4.7 tokenizer uses ~1×–1.35× as many tokens) — re-measure by calling `count_tokens` once with each model and comparing `input_tokens`.
- **Confirm migration scope before editing:** When a user asks to migrate code to a newer Claude model without naming a specific file, directory, or file list, **ask which scope to apply first** — the entire working directory, a specific subdirectory, or a specific set of files. Do not start editing until the user confirms. Imperative phrasings like "migrate my codebase", "move my project to X", "upgrade to Sonnet 4.6", or bare "migrate to Opus 4.8" are **still ambiguous** — they tell you what to do but not where, so ask. Proceed without asking only when the prompt names an exact file, a specific directory, or an explicit file list ("migrate `app.py`", "migrate everything under `services/`", "update `a.py` and `b.py`"). See `shared/model-migration.md` Step 0.
- **`max_tokens` defaults:** Don't lowball `max_tokens` — hitting the cap truncates output mid-thought and requires a retry. For non-streaming requests, default to `~16000` (keeps responses under SDK HTTP timeouts). For streaming requests, default to `~64000` (timeouts aren't a concern, so give the model room). Only go lower when you have a hard reason: classification (`~256`), cost caps, deliberately short outputs, or **`max_tokens: 0`** for cache pre-warming (see `shared/prompt-caching.md` → Pre-warming).
- **128K output tokens:** Fable 5, Opus 4.6, Opus 4.7, Opus 4.8, Sonnet 5, and Sonnet 4.6 support up to 128K `max_tokens`, but the SDKs require streaming for values that large to avoid HTTP timeouts. Use `.stream()` with `.get_final_message()` / `.finalMessage()`.
- **Tool call JSON parsing (Fable 5 and the 4.6/4.7/4.8 family):** Fable 5, Opus 4.6, Opus 4.7, Opus 4.8, and Sonnet 4.6 may produce different JSON string escaping in tool call `input` fields (e.g., Unicode or forward-slash escaping). Always parse tool inputs with `json.loads()` / `JSON.parse()` — never do raw string matching on the serialized input.
- **Structured outputs (all models):** Use `output_config: {format: {...}}` instead of the deprecated `output_format` parameter on `messages.create()`. This is a general API change, not 4.6-specific.
- **Don't reimplement SDK functionality:** The SDK provides high-level helpers — use them instead of building from scratch. Specifically: use `stream.finalMessage()` instead of wrapping `.on()` events in `new Promise()`; use typed exception classes (`Anthropic.RateLimitError`, etc.) instead of string-matching error messages; use SDK types (`Anthropic.MessageParam`, `Anthropic.Tool`, `Anthropic.Message`, etc.) instead of redefining equivalent interfaces.
- **Error handling — catch a chain, not one broad class.** A single `except APIStatusError` / `catch (AnthropicServiceException)` / `rescue APIError` loses the distinction between retryable (429, ≥500, network) and non-retryable (400/404) failures. Write a most-specific-first chain — e.g. `NotFoundError` → `RateLimitError` → `APIStatusError` → `APIConnectionError` (or the Go equivalent: `errors.As` into `*anthropic.Error` then `switch apierr.StatusCode { case 404: …; case 429: …; default: … }`). Per-language class names and namespaces are in `shared/error-codes.md`.
- **Don't research SDK types — write first.** If a type name isn't shown in the documentation included in this skill, write the code file from the namespace/package tables in the language-specific doc and let the compiler's error point you to the right name. Do not spend turns on WebFetch, SDK-repo clones, or compiling-and-running a separate reflection program to discover type names before writing — produce the source file first, then fix what the compiler reports. A quick `strings` / `jar tf` / `javap` against the installed SDK is acceptable for locating names (it returns in seconds), but don't escalate beyond that. A file with a wrong type name is recoverable; a session spent on discovery with no file written is not.
- **Bash and text editor tools are Anthropic-defined, schema-less.** Declare `{"type": "bash_20250124", "name": "bash"}` / `{"type": "text_editor_20250728", "name": "str_replace_based_edit_tool"}` — no `input_schema`. A custom tool with your own schema named `"bash"` is a different tool. Handler paths and security checks are in `shared/tool-use-concepts.md` § Client-Side Tools.
- **Advisor tool model pairing.** The advisor tool's `model` must be at least as capable as the request's top-level `model` — e.g. executor `claude-sonnet-5` → advisor `claude-opus-4-8` or `claude-opus-4-7`. An invalid pair returns 400. Pairing table in `shared/tool-use-concepts.md` § Advisor. Availability: `shared/platform-availability.md`.
- **Agent Skills ≠ Managed Agents.** To have Claude generate a `.pptx`/`.xlsx`/etc. via Agent Skills, call `client.beta.messages.create` with `container={"skills": [...]}`, the `code_execution_20260521` tool, and both `code-execution-2025-08-25` + `skills-2025-10-02` betas. Do not use `client.beta.agents` / `sessions` / `environments` here — those are the Managed Agents surface, not Agent Skills.
- **MCP connector needs both halves.** `mcp_servers=[{type:"url", url, name}]` alone is rejected as a validation error — also add `tools=[{type:"mcp_toolset", mcp_server_name:<same name>}]` with beta `mcp-client-2025-11-20`. Availability: `shared/platform-availability.md`.
- **Context editing ≠ compaction.** Context editing *clears* tool results and thinking blocks; compaction *summarizes* history. For context editing, use `context_management.edits` with type `clear_tool_uses_20250919` (or `clear_thinking_20251015`) on `client.beta.messages.*` with beta `context-management-2025-06-27` — not the `compact_20260112` type or `compact-2026-01-12` beta, which are compaction.
- **`inference_geo` is a direct top-level request parameter** — `client.messages.create(..., inference_geo="us")` / `.inferenceGeo("us")`. Do not put it in `extra_body` / `putAdditionalBodyProperty`. Supported on Opus 4.6 / Sonnet 4.6 and later; availability: `shared/platform-availability.md`. `response.usage.inference_geo` reports where inference ran.
- **Fine-grained tool streaming is not a beta feature.** Set `eager_input_streaming: true` on the tool definition and call the regular `client.messages.stream(...)`. There is no beta header and no `client.beta.*` path.
- **Cache diagnostics is beta.** Use `client.beta.messages.*` with beta `cache-diagnosis-2026-04-07`. Pass `diagnostics: {previous_message_id: null}` on the first turn and `diagnostics: {previous_message_id: <previous response id>}` on subsequent turns; the result is on `response.diagnostics`. Availability: `shared/platform-availability.md`.
- **Memory tool type is `memory_20250818`.** Declare `{"type": "memory_20250818", "name": "memory"}`. Go uses the beta-namespace type `{OfMemoryTool20250818: &anthropic.BetaMemoryTool20250818Param{}}` on `client.Beta.Messages.New`; Python/TypeScript/Ruby/PHP/C# use the non-beta `client.messages.create`; Java has both a non-beta `MemoryTool20250818` and a beta tool-runner path. Python/TypeScript provide `BetaAbstractMemoryTool` / `betaMemoryTool` helpers for implementing the backend.
- **Use a model the feature actually supports.** Some features are restricted to specific model tiers — fast mode is Opus 4.8 / 4.7 only, task budgets are Fable 5 / Sonnet 5 / Opus 4.8 / 4.7 only, and the advisor tool requires a valid executor↔advisor pair. If the user's prompt names a model that the feature doesn't support, use a supported model instead and note the substitution in the output.
- **Bedrock / Foundry: use the platform client class.** For Bedrock use the `…BedrockMantle…` client (e.g. Python `AnthropicBedrockMantle`, Java `BedrockMantleBackend`) with `anthropic.`-prefixed model IDs; `AnthropicBedrock`/`BedrockBackend` without `Mantle` is the legacy path. For Foundry use `AnthropicFoundry` / `FoundryBackend` / `AnthropicFoundryClient` where the SDK supports it (C#, Java, PHP, Python, TypeScript); Go and Ruby have no Foundry client — Ruby's documented fallback is the first-party client with a custom `base_url`. Per-language table above.
- **Don't define custom types for SDK data structures:** The SDK exports types for all API objects. Use `Anthropic.MessageParam` for messages, `Anthropic.Tool` for tool definitions, `Anthropic.ToolUseBlock` / `Anthropic.ToolResultBlockParam` for tool results, `Anthropic.Message` for responses. Defining your own `interface ChatMessage { role: string; content: unknown }` duplicates what the SDK already provides and loses type safety.
- **Report and document output:** For tasks that produce reports, documents, or visualizations, the code execution sandbox has `python-docx`, `python-pptx`, `matplotlib`, `pillow`, and `pypdf` pre-installed. Claude can generate formatted files (DOCX, PDF, charts) and return them via the Files API — consider this for "report" or "document" type requests instead of plain stdout text.
- **Server-tool errors don't raise.** Web search and web fetch errors return HTTP 200 with a `web_search_tool_result` / `web_fetch_tool_result` block whose `content` is a single error object (e.g. `{error_code: "max_uses_exceeded"}`) — not a raised exception. For web search, a success `content` is a *list*; an error `content` is an *object* — branch on that before indexing.
- **Code execution output block type:** `code_execution_20260521` returns `bash_code_execution_tool_result` (with `.content.stdout`), **not** the legacy bare `code_execution_tool_result`. Iterate `response.content` and match on the correct type.
- **Tool search: never defer everything.** The search tool itself must not have `defer_loading: true`, and at least one tool in `tools` must be non-deferred, or the API returns 400 `All tools have defer_loading set`.
- **`strict: true` goes on the tool, not `tool_choice`.** Putting `strict` on `tool_choice` does nothing; it's a sibling of `name`/`description`/`input_schema` on the tool definition itself.
- **Parallel tool results go in ONE user message.** Splitting `tool_result` blocks across multiple user messages silently trains Claude to stop making parallel calls. One assistant message of `tool_use` blocks → one user message of `tool_result` blocks.
- **Citations + structured outputs are incompatible.** Enabling `citations: {enabled: true}` on a document while also setting `output_config.format` returns a 400.
- **Batch results are unordered.** Match by `custom_id`, never by position in the results stream.
- **Vertex model IDs have no prefix.** Unlike Bedrock's `anthropic.`-prefixed IDs, Vertex takes the bare first-party ID for current-generation models (e.g. `"claude-opus-4-8"`); dated-snapshot models use an `@` separator (e.g. `claude-haiku-4-5@20251001`).
- **`stop_details` is `null` unless `stop_reason == "refusal"`.** For `max_tokens`, `end_turn`, etc., `stop_details` is `null` — guard before reading `.category`.
- **WIF auth: unset `ANTHROPIC_API_KEY`, `ANTHROPIC_AUTH_TOKEN`, and `ANTHROPIC_PROFILE`.** `ANTHROPIC_API_KEY` and `ANTHROPIC_AUTH_TOKEN` (even set to `""`) outrank Workload Identity Federation in the SDK's precedence chain and silently win; a set `ANTHROPIC_PROFILE` also wins (a missing named profile is an error, not a fall-through). `unset` them, don't blank them.
