---
name: mcp-builder
description: Guide for creating high-quality MCP (Model Context Protocol) servers that enable LLMs to interact with external services through well-designed tools. Use when building MCP servers to integrate external APIs or services, whether in Python (FastMCP) or Node/TypeScript (MCP SDK).
license: Complete terms in LICENSE.txt
---

# MCP Server Development Guide

## Overview

Create MCP servers that let LLMs interact with external services through well-designed tools. Quality is measured by whether an LLM can reliably accomplish real tasks with your server — verified objectively by the Phase 4 evaluation suite.

**This file is a navigator.** Each phase points at a deeper reference file. Load references on demand; do not duplicate their content here.

---

# Process

Four phases, in order. Do not skip Phase 1 (research) or Phase 4 (evaluation).

## 🚀 High-Level Workflow

| Phase | Output | Primary Reference |
|---|---|---|
| 1. Research | API map, tool list, stack choice, auth plan | `reference/mcp_best_practices.md` + SDK README |
| 2. Implement | Working server with auth, errors, pagination | `reference/node_mcp_server.md` or `reference/python_mcp_server.md` |
| 3. Test | Build clean + functional tests pass + Inspector verified | this file §3 |
| 4. Evaluate | ≥ 8/10 evaluation pass rate | `reference/evaluation.md` + `scripts/evaluation.py` |

---

## ⚡ 5-Minute Hello World

Skip the phases for a first feel of MCP. The following stdio server exposes one tool.

```bash
npm init -y && npm i @modelcontextprotocol/sdk zod
```

`server.ts`:

```typescript
import { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import { z } from "zod";

const server = new McpServer({ name: "hello-mcp-server", version: "0.1.0" });

server.registerTool(
  "hello_greet",
  {
    title: "Greet a person",
    description: "Return a greeting for the given name.",
    inputSchema: { name: z.string().describe("Person to greet, e.g. 'Ada'") },
    outputSchema: { greeting: z.string() },
    annotations: { readOnlyHint: true, destructiveHint: false, idempotentHint: true, openWorldHint: false },
  },
  async ({ name }) => {
    const out = { greeting: `Hello, ${name}!` };
    return { content: [{ type: "text", text: JSON.stringify(out) }], structuredContent: out };
  },
);

await server.connect(new StdioServerTransport());
```

Run + inspect:

```bash
npx tsx server.ts &        # or compile and run
npx @modelcontextprotocol/inspector node server.ts
```

This is **not** a shippable server — it has no auth, no real API, no eval. Use it to confirm your toolchain works, then return to Phase 1.

---

### Phase 1: Research and Planning

#### 1.1 Modern MCP Design Principles

**API coverage vs. workflow tools — decision rule:**
- **Default: one tool per endpoint**, named after the endpoint. Gives agents flexibility to compose.
- **Add a workflow tool only when** a single user-facing task reliably requires ≥ 3 raw tool calls in a fixed sequence (e.g. `create_issue_with_labels_and_assignee` wrapping three GitHub calls).
- **Cap total tools at ~30 per server.** Beyond this, LLM tool-selection accuracy drops and per-turn token cost climbs. If you exceed the cap, split into multiple servers, or fold related endpoints behind one tool with an `action` discriminator.

**Tool naming — required pattern:** `{service}_{verb}_{resource}` in snake_case.
- Good: `github_create_issue`, `slack_list_channels`, `jira_update_ticket`
- Bad: `createIssue`, `issue`, `do_create`

**Context economy:**
- Tool descriptions ≤ 3 sentences. Push detail into per-parameter `description` fields.
- Default page sizes 20–50. Always accept `limit` and return `has_more` + `next_cursor`.
- Return only fields the agent needs. Offer a `fields` or `verbosity` parameter on heavy endpoints.

**Actionable errors:** every error message must answer "what went wrong" + "what to try next".
> `Repository "foo/bar" not found. Check the owner/name spelling, or call github_list_repos to see accessible repos.`

#### 1.2 Study the MCP Protocol

Start: `https://modelcontextprotocol.io/sitemap.xml`
Fetch pages with the `.md` suffix (e.g. `https://modelcontextprotocol.io/specification/draft.md`).

Required reading:
- Specification overview and architecture
- Transport mechanisms (streamable HTTP, stdio)
- Tool, resource, and prompt definitions

#### 1.3 Choose the Stack

**Default — do not deviate without reason:**
- **Language**: TypeScript. Strong SDK, MCPB packaging support, LLMs generate it reliably with good static typing.
- **Transport**: Streamable HTTP with stateless JSON for remote servers; stdio for local.
- **Avoid**: SSE (deprecated), stateful streaming sessions (harder to scale and maintain).

Load:
- [📋 MCP Best Practices](./reference/mcp_best_practices.md) — universal rules
- TypeScript SDK: `https://raw.githubusercontent.com/modelcontextprotocol/typescript-sdk/main/README.md` + [⚡ TypeScript Guide](./reference/node_mcp_server.md)
- Python SDK: `https://raw.githubusercontent.com/modelcontextprotocol/python-sdk/main/README.md` + [🐍 Python Guide](./reference/python_mcp_server.md)

#### 1.4 Plan the Tool Surface

**First decide which primitive(s) you need.** MCP has three:
- **Tools** — model-controlled actions (most of what this guide covers).
- **Resources** — app-controlled reference data the LLM should *read* (schemas, docs, knowledge files at known URIs).
- **Prompts** — user-controlled canned workflows (slash-command templates).

A complete server often uses all three. See [📋 best practices → MCP Primitives](./reference/mcp_best_practices.md#mcp-primitives-tools-resources-prompts) for the decision rule.

**Then produce a written plan before coding:**

1. **Endpoint inventory** — list every API endpoint relevant to the target use cases.
2. **Tool budget** — pick ≤ 30 tools; mark each as `read` or `write`.
3. **Resource candidates** — data that is read-only, addressable by URI, and shouldn't burn a tool slot.
4. **Auth mechanism** — one of: API key, OAuth 2.0, OAuth 2.0 PKCE, service account / signed JWT. Identify token lifetime and refresh path.
5. **Rate limits** — note per-endpoint limits; plan client-side throttling.
6. **Pagination model** — cursor vs. offset; document on each list tool.

---

### Phase 2: Implementation

#### 2.1 Project Structure
Follow the language guide:
- [⚡ TypeScript Guide](./reference/node_mcp_server.md)
- [🐍 Python Guide](./reference/python_mcp_server.md)

#### 2.2 Core Infrastructure

Build these before any tool:

- **API client** — single shared instance with base URL, timeouts (default 30s), retry on 429/5xx with exponential backoff (≤ 3 attempts).
- **Auth layer** — encapsulate credential loading, token refresh, and 401-retry-once. Never log secrets.
- **Error mapper** — convert HTTP/SDK errors to MCP errors with actionable messages (see §1.1).
- **Response formatter** — trim large payloads; offer JSON or Markdown per tool.
- **Pagination helper** — wrap cursor/offset logic so each tool does not reimplement it.

**Auth patterns — pick one and follow its key concern:**

| Pattern | Use when | Key concern |
|---|---|---|
| Static API key (env var) | Personal / single-tenant local server | Document var name; fail fast with clear message if missing |
| OAuth 2.0 + refresh token | Multi-user or rotating creds | Persist refresh token securely; on 401 refresh and retry once |
| OAuth 2.0 PKCE (browser flow) | Interactive desktop auth | First run opens browser; cache tokens in OS keychain |
| Service account / signed JWT | Server-to-server | Rotate keys on a schedule; never commit credentials |

#### 2.3 Implement Tools

For every tool, define all four pieces:

**Input schema** — Zod (TS) or Pydantic (Py). Each non-obvious field gets `.describe()` with one realistic example value.

**Output schema** — define `outputSchema` and return `structuredContent`. Clients use this to parse without scraping the text response.

**Tool description** — ≤ 3 sentences. Lead with the verb. State the user task it enables.
> "Search GitHub issues by repo, label, and state. Returns up to `limit` issues ordered by recency."

**Implementation** — async, paginated, fails with actionable error, never leaks secrets.

**Annotations — when each should be `true`:**

| Annotation | Set `true` when... | Examples |
|---|---|---|
| `readOnlyHint` | The tool performs no writes anywhere | `list_issues`, `get_user` |
| `destructiveHint` | The tool deletes, overwrites, or sends external messages | `delete_repo`, `send_email` |
| `idempotentHint` | Repeated identical calls produce the same end state | `upsert_record`, PUT-style updates |
| `openWorldHint` | The tool reaches external systems with unbounded state | Almost always `true` for API-backed tools |

Default to conservative: when uncertain, mark `destructiveHint: true` and `idempotentHint: false`.

#### 2.4 Security Essentials

Non-negotiable for every server:

- **Prompt injection is the #1 threat.** External text your tool returns (issues, messages, search results, file contents) is *untrusted input to the LLM*. Wrap it in delimiters, strip control sequences, and never auto-chain destructive actions based on returned content.
- **Validate every input** against the schema before passing it to the API. Never interpolate raw strings into URLs, SQL, or shell commands.
- **Never log secrets** — redact tokens, API keys, and auth headers before formatting errors or responses.
- **Least-privilege credentials** — request only the OAuth scopes the implemented tools actually need.
- **SSRF guard** on any tool that accepts a URL — block private IP ranges, `localhost`, and cloud metadata endpoints (`169.254.169.254`).
- **Client-side rate limiting** — throttle to stay under the API quota; do not rely on the API rejecting you.
- **Confirm destructive bulk ops** — pair `destructiveHint: true` with an explicit parameter (e.g. `confirm: true`) on tools that delete many items.

Full checklist with code (redaction, SSRF guard, rate limiter, prompt-injection defense): [📋 mcp_best_practices.md → Security Best Practices](./reference/mcp_best_practices.md#security-best-practices).

#### 2.5 Packaging and Distribution

- **TypeScript local** — build to `dist/`; publish as MCPB or as an npm package with a `bin` entry.
- **Python local** — package via `pyproject.toml`; expose a console script.
- **Remote (streamable HTTP)** — containerize; set `MCP_TRANSPORT=http`; document the URL and required auth header.
- Pin SDK versions in lockfiles. Tag releases with semver.

---

### Phase 3: Review and Test

Do not stop at "it builds." Functional testing is mandatory.

#### 3.1 Static Quality
- No duplicated code (DRY).
- Full type coverage; `tsc --noEmit` / `mypy --strict` clean.
- Lint clean: `eslint` / `ruff`.
- Every tool has input schema, output schema, description, and annotations.

#### 3.2 Build
- TypeScript: `npm run build` — zero warnings.
- Python: `python -m py_compile` on every module, or `uv run --check`.

#### 3.3 Functional Testing

For every tool, exercise three paths:

1. **Happy path** — valid input; output shape matches `outputSchema`.
2. **Validation failure** — invalid input rejected with a clear message; no API call issued.
3. **API failure** — simulate 401, 404, 429, 500; tool returns actionable error without leaking secrets.

Additionally verify:

- **Pagination** — call a list tool with `limit=2` and confirm `has_more` + cursor round-trip works.
- **Idempotency** — for tools marked idempotent, call twice and confirm the same end state.
- **Rate-limit behavior** — fire 10 calls in a tight loop; confirm the client throttles instead of triggering 429s.

#### 3.4 MCP Inspector

Run `npx @modelcontextprotocol/inspector` and manually invoke each tool. Confirm responses render correctly and that `structuredContent` is populated.

Language-specific quality checklists live in the implementation guides.

---

### Phase 4: Create AND Run Evaluations

Evaluations are the only objective measure of server quality. Creating them is not enough — **run them and act on failures.**

**Load [✅ Evaluation Guide](./reference/evaluation.md) before starting.**

#### 4.1 Purpose

Measure whether an LLM client can use your server to answer realistic, multi-step questions end-to-end. A passing eval suite is the ship criterion.

#### 4.2 Create 10 Questions

1. **Inspect tools** — list every tool and its schema.
2. **Explore content** — use read-only tools to map the live data the questions will probe.
3. **Generate 10 questions** — see §4.3 for requirements.
4. **Verify answers** — solve each question yourself with the tools; record the exact answer string.

#### 4.3 Question Requirements

Each question must be:
- **Independent** — no shared state across questions.
- **Read-only** — no destructive operations.
- **Complex** — requires ≥ 3 tool calls or non-trivial composition.
- **Realistic** — a real user would plausibly ask this.
- **Verifiable** — single canonical answer comparable by string match.
- **Stable** — answer is invariant to time, ordering, or unrelated data changes.

#### 4.4 XML Format

```xml
<evaluation>
  <qa_pair>
    <question>In the engineering Slack workspace, find the channel where the team coordinates on-call rotations. Of the users who posted there in the last 30 days, which display name appears most often as the author of messages that received an "incident" emoji reaction?</question>
    <answer>alice.chen</answer>
  </qa_pair>
  <!-- 9 more qa_pairs... -->
</evaluation>
```

Each question should force the LLM to (a) discover the right tool, (b) chain multiple calls, and (c) filter or aggregate results.

#### 4.5 Run the Suite

Use the bundled harness (`scripts/evaluation.py`). Examples:

```bash
# stdio server
python scripts/evaluation.py your_eval.xml \
  -t stdio -c node -a dist/index.js \
  -e API_TOKEN=xxx \
  -o report.json

# streamable HTTP server
python scripts/evaluation.py your_eval.xml \
  -t http -u https://your-server.example/mcp \
  -H "Authorization: Bearer xxx" \
  -o report.json
```

**Target: ≥ 8/10 pass.** Below this, the server is not ready to ship.

#### 4.6 Iterate on Failures

For each failed question, classify the root cause and fix it:

| Failure | Root cause | Fix |
|---|---|---|
| LLM picked wrong tool | Description gap | Rewrite tool description; clarify verb and use case |
| LLM couldn't construct call | Schema gap | Add `.describe()` with example values; tighten constraints |
| LLM got data but parsed wrong | Output gap | Add or refine `outputSchema`; restructure payload |
| LLM gave up on error | Error gap | Improve error message to point at the next action |
| Task genuinely impossible | Tool gap | Add the missing tool or parameter |

Fix, rebuild, re-run. Repeat until ≥ 8/10.

---

# Reference Files

## 📚 Documentation Library

Load on demand:

### Core (Phase 1)
- [📋 MCP Best Practices](./reference/mcp_best_practices.md) — naming, response formats, pagination, transport, security
- MCP Protocol sitemap: `https://modelcontextprotocol.io/sitemap.xml` (fetch pages with `.md` suffix)

### SDKs (Phase 1–2)
- Python SDK: `https://raw.githubusercontent.com/modelcontextprotocol/python-sdk/main/README.md`
- TypeScript SDK: `https://raw.githubusercontent.com/modelcontextprotocol/typescript-sdk/main/README.md`

### Implementation (Phase 2)
- [⚡ TypeScript Guide](./reference/node_mcp_server.md) — project layout, Zod patterns, `server.registerTool`, full example, checklist
- [🐍 Python Guide](./reference/python_mcp_server.md) — module layout, Pydantic, `@mcp.tool`, full example, checklist

### Evaluation (Phase 4)
- [✅ Evaluation Guide](./reference/evaluation.md) — question design, verification, XML schema, runner usage

### Tooling (Phase 4)
- `scripts/evaluation.py` — eval runner (stdio / sse / http)
- `scripts/connections.py` — server connection helpers
- `scripts/example_evaluation.xml` — reference XML
