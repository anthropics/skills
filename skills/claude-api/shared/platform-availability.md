# Platform Availability

Which features work on which provider platform. **This table is the single source of truth in this skill** — per-feature sections elsewhere point here instead of restating availability. When writing code for a third-party platform (Bedrock, Vertex, Foundry) or Claude Platform on AWS, check this table first; a feature not supported there means use the first-party Claude API surface or a different approach.

Columns: **1P** = first-party Claude API, **P-AWS** = Claude Platform on AWS (Anthropic-operated, same-day parity), **Bedrock** = Amazon Bedrock, **Vertex** = Google Cloud Vertex AI, **Foundry** = Microsoft Foundry. ✅ = GA, β = beta, ❌ = not supported.

| Feature | 1P | P-AWS | Bedrock | Vertex | Foundry | Notes |
|---|---|---|---|---|---|---|
| Messages, streaming, tool use | ✅ | ✅ | ✅ | ✅ | ✅ | Core API |
| PDF input | ✅ | ✅ | ✅ | ✅ | β | |
| Structured outputs / strict tool use | ✅ | ✅ | ✅ | ✅ | β | |
| Adaptive thinking / effort | ✅ | ✅ | ✅ | ✅ | β | |
| Extended thinking | ✅ | ✅ | ✅ | ✅ | β | |
| Prompt caching (5m, 1h) | ✅ | ✅ | ✅ | ✅ | β | |
| Automatic prompt caching | ✅ | ✅ | ❌ | ❌ | β | |
| Token counting | ✅ | ✅ | ✅ | ✅ | β | |
| Citations | ✅ | ✅ | ✅ | ✅ | β | |
| Search results content blocks | ✅ | ✅ | ✅ | ✅ | β | |
| Fine-grained tool streaming | ✅ | ✅ | ✅ | ✅ | ✅ | |
| Compaction | β | β | β | β | β | |
| Context editing | β | β | β | β | β | |
| Context windows (1M) | ✅ | ✅ | ✅ | ✅ | β | |
| `inference_geo` (data residency) | ✅ | ✅ | ❌ | ❌ | ❌ | |
| **Server-side tools** | | | | | | |
| &nbsp;&nbsp;Web search | ✅ | ✅ | ❌ | ✅ | β | Vertex: basic `web_search_20250305` only (no `_20260209` dynamic filtering) |
| &nbsp;&nbsp;Web fetch | ✅ | ✅ | ❌ | ❌ | β | |
| &nbsp;&nbsp;Code execution | ✅ | ✅ | ❌ | ❌ | β | |
| &nbsp;&nbsp;Tool search | ✅ | ✅ | ✅ | ✅ | β | Bedrock: InvokeModel API only, not Converse |
| &nbsp;&nbsp;Advisor tool | β | β | ❌ | ❌ | ❌ | |
| **Client-implemented tools** | | | | | | |
| &nbsp;&nbsp;Bash, text editor, memory | ✅ | ✅ | ✅ | ✅ | β | |
| &nbsp;&nbsp;Computer use | β | β | β | β | β | |
| **Agentic / orchestration** | | | | | | |
| &nbsp;&nbsp;Agent Skills (Messages API) | β | β | ❌ | ❌ | β | |
| &nbsp;&nbsp;Programmatic tool calling | ✅ | ✅ | ❌ | ❌ | β | |
| &nbsp;&nbsp;MCP connector | β | β | ❌ | ❌ | β | |
| &nbsp;&nbsp;Managed Agents | β | β | ❌ | ❌ | ❌ | Foundry ❌ inferred (not in Foundry docs either way) |
| &nbsp;&nbsp;Self-hosted sandboxes | β | β | ❌ | ❌ | ❌ | P-AWS: `GET /v1/environments/{id}/work` list endpoint not supported; other work endpoints OK |
| **API endpoints** | | | | | | |
| &nbsp;&nbsp;Message Batches | ✅ | ✅ | ❌ | ❌ | ❌ | |
| &nbsp;&nbsp;Files API | β | β | ❌ | ❌ | β | |
| &nbsp;&nbsp;Models API | ✅ | ✅ | ❌ | ❌ | ❌ | |
| **Other** | | | | | | |
| &nbsp;&nbsp;Mid-conversation system messages | ✅ | ✅ | ❌ | ❌ | ❌ | Claude Opus 5, Claude Opus 4.8, Claude Fable 5, Claude Mythos 5; not Claude Sonnet 5 |
| &nbsp;&nbsp;Server-side `fallbacks` | β | β | ❌ | ❌ | ❌ | `"default"` → beta `server-side-fallback-2026-07-01`; array form → beta `server-side-fallback-2026-06-01` |
| &nbsp;&nbsp;Fast mode | β | ❌ | ❌ | ❌ | ❌ | Research preview, beta `fast-mode-2026-02-01`, first-party API only |
| &nbsp;&nbsp;Cache diagnostics | β | ❌ | ❌ | ❌ | ❌ | First-party API only |
| &nbsp;&nbsp;Task budgets | β | β | ❌ | ❌ | ❌ | Beta header `task-budgets-2026-03-13`; 3P availability not documented — assume unsupported |
