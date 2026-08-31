# Platform Availability

Which features work on which provider platform. **This table is the single source of truth in this skill** - per-feature sections elsewhere point here instead of restating availability. When writing code for a third-party platform (Bedrock, Vertex, Foundry) or Claude Platform on AWS, check this table first; a feature not supported there means use the first-party Claude API surface or a different approach.

Columns: **1P** = first-party Claude API, **P-AWS** = Claude Platform on AWS (Anthropic-operated, same-day parity), **Bedrock** = Amazon Bedrock, **Vertex** = Google Cloud Vertex AI, **Foundry** = Microsoft Foundry. Yes = GA, beta = beta, No = not supported.

| Feature | 1P | P-AWS | Bedrock | Vertex | Foundry | Notes |
|---|---|---|---|---|---|---|
| Messages, streaming, tool use | Yes | Yes | Yes | Yes | Yes | Core API |
| PDF input | Yes | Yes | Yes | Yes | beta | |
| Structured outputs / strict tool use | Yes | Yes | Yes | Yes | beta | |
| Adaptive thinking / effort | Yes | Yes | Yes | Yes | beta | |
| Extended thinking | Yes | Yes | Yes | Yes | beta | |
| Prompt caching (5m, 1h) | Yes | Yes | Yes | Yes | Yes | |
| Automatic prompt caching | Yes | Yes | Yes | Yes | Yes | The legacy Bedrock integration (Opus 4.6 and earlier) rejects top-level `cache_control` with a 400 - explicit breakpoints only there |
| Token counting | Yes | Yes | Yes | Yes | beta | |
| Citations | Yes | Yes | Yes | Yes | beta | |
| Search results content blocks | Yes | Yes | Yes | Yes | beta | |
| Fine-grained tool streaming | Yes | Yes | Yes | Yes | Yes | |
| Compaction | beta | beta | beta | beta | beta | |
| Context editing | beta | beta | beta | beta | beta | |
| Context windows (1M) | Yes | Yes | Yes | Yes | beta | |
| `inference_geo` (data residency) | Yes | Yes | No | No | No | |
| **Server-side tools** | | | | | | |
| &nbsp;&nbsp;Web search | Yes | Yes | No | Yes | beta | Vertex: basic `web_search_20250305` only (no `_20260209` dynamic filtering) |
| &nbsp;&nbsp;Web fetch | Yes | Yes | No | No | beta | |
| &nbsp;&nbsp;Code execution | Yes | Yes | No | No | beta | |
| &nbsp;&nbsp;Tool search | Yes | Yes | Yes | Yes | beta | Bedrock: InvokeModel API only, not Converse |
| &nbsp;&nbsp;Advisor tool | beta | beta | No | No | No | |
| **Client-implemented tools** | | | | | | |
| &nbsp;&nbsp;Bash, text editor, memory | Yes | Yes | Yes | Yes | beta | |
| &nbsp;&nbsp;Computer use | beta | beta | beta | beta | beta | |
| **Agentic / orchestration** | | | | | | |
| &nbsp;&nbsp;Agent Skills (Messages API) | Yes | Yes | No | No | beta | |
| &nbsp;&nbsp;Programmatic tool calling | Yes | Yes | No | No | beta | |
| &nbsp;&nbsp;MCP connector | beta | beta | No | No | beta | |
| &nbsp;&nbsp;Managed Agents | beta | beta | No | No | No | Foundry: No (inferred; not in Foundry docs either way) |
| &nbsp;&nbsp;Self-hosted sandboxes | beta | beta | No | No | No | P-AWS: worker authenticates with IAM/SigV4 or an AWS-Console API key + `AnthropicSelfHostedEnvironmentAccess` (Console environment keys don't work there); sessions on self-hosted environments cannot attach memory stores; `GET /v1/environments/{id}/work` list endpoint not supported, other work endpoints OK |
| **API endpoints** | | | | | | |
| &nbsp;&nbsp;Message Batches | Yes | Yes | No | No | No | |
| &nbsp;&nbsp;Files API | Yes | Yes | No | No | beta | |
| &nbsp;&nbsp;Models API | Yes | Yes | No | No | No | |
| **Other** | | | | | | |
| &nbsp;&nbsp;Mid-conversation system messages | Yes | Yes | Yes | Yes | No | Claude Opus 5, Claude Opus 4.8, Claude Fable 5, Claude Fable 5.1, Claude Mythos 5, Claude Mythos 5.1; not Claude Sonnet 5. Bedrock: InvokeModel passthrough, not ARN-versioned models |
| &nbsp;&nbsp;Turn-scoped (`clear_at`) system messages | beta | beta | beta | beta | No | Same models as mid-conversation system messages; beta `mid-conversation-system-clear-at-2026-08-21` (on Bedrock/Vertex pass the value as a beta) |
| &nbsp;&nbsp;Per-message `effort` (system message `output_config`) | beta | No | No | No | No | Claude Fable 5.1, Claude Mythos 5.1, Claude Opus 5; beta `mid-conversation-output-config-2026-07-01`; Claude API at launch (Bedrock/Vertex/Foundry unconfirmed; Claude Opus 5 excluded on Bedrock) |
| &nbsp;&nbsp;`thinking.display: "updates"` | beta | beta | beta | beta | beta | Claude Fable 5.1, Claude Mythos 5.1, Claude Fable 5; beta `thinking-display-updates-2026-08-18` (pass the beta value per platform); without it `"updates"` is rejected as an unknown `display` value |
| &nbsp;&nbsp;Thinking block-binding controls | beta | beta | per model | per model | No | `thinking.block_binding` + `input_transformations`; beta `thinking-binding-controls-2026-08-01` (on Bedrock via the `anthropic_beta` body field); the controls beta arrives per model on Bedrock/Vertex - until then the header is rejected; the history-editing enforcement itself follows the account-age rule in `shared/model-migration.md` -> Migrating to Claude Fable 5.1 from Claude Fable 5 |
| &nbsp;&nbsp;Server-side `fallbacks` | beta | beta | No | No | No | `"default"` -> beta `server-side-fallback-2026-07-01`; array form -> beta `server-side-fallback-2026-06-01` |
| &nbsp;&nbsp;Fast mode | beta | No | No | No | No | Research preview, beta `fast-mode-2026-02-01`, first-party API only |
| &nbsp;&nbsp;Cache diagnostics | beta | No | No | No | No | First-party API only |
| &nbsp;&nbsp;Task budgets | beta | beta | No | No | No | Beta header `task-budgets-2026-03-13`; 3P availability not documented - assume unsupported |

