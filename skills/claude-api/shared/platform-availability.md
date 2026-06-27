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
| &nbsp;&nbsp;Mid-conversation system messages | ✅ | ✅ | ❌ | ❌ | ❌ | Claude Opus 4.8 only |
| &nbsp;&nbsp;Fast mode | β | ❌ | ❌ | ❌ | ❌ | Research preview, beta `fast-mode-2026-02-01`, first-party API only |
| &nbsp;&nbsp;Cache diagnostics | β | ❌ | ❌ | ❌ | ❌ | First-party API only |
| &nbsp;&nbsp;Task budgets | β | β | ❌ | ❌ | ❌ | Beta header `task-budgets-2026-03-13`; 3P availability not documented — assume unsupported |

<!--
GROUNDING (reviewer-only; stripped at runtime by processSkillMarkdown).
All paths are under docker_eval/resources/cdp-skill/public-docs/.

Primary source: build-with-claude/overview.mdx <PlatformAvailability> props
(claudeApi→1P, claudePlatformAws→P-AWS, bedrock→Bedrock, vertexAi→Vertex,
azureAi→Foundry; *Beta suffix→β; prop absent→❌). Per-row citations:

  Context windows          ov:44
  Adaptive thinking        ov:45
  Batch / Message Batches  ov:46; bed:360; vtx:381; fdy:507
  Citations                ov:47
  inference_geo            ov:48
  Effort                   ov:49
  Extended thinking        ov:50
  PDF input                ov:51
  Search results           ov:52
  Structured outputs       ov:53
  Advisor tool             ov:63
  Code execution           ov:64
  Web fetch                ov:65
  Web search               ov:66; agents-and-tools/tool-use/web-search-tool.mdx:41
  Bash/text-editor/memory  ov:72,75,74
  Computer use             ov:73
  Agent Skills             ov:83
  Fine-grained streaming   ov:84
  MCP connector            ov:85; agents-and-tools/mcp-connector.mdx:36
  Programmatic tool call   ov:86
  Tool search              ov:87; agents-and-tools/tool-use/tool-search-tool.mdx:24-30
  Compaction               ov:95
  Context editing          ov:96
  Automatic caching        ov:97
  Prompt caching 5m/1h     ov:98,99
  Token counting           ov:100
  Files API                ov:108; build-with-claude/files.mdx:17
  Managed Agents           managed-agents/overview.mdx:11,70-72; bed:360; vtx:381
  Self-hosted sandboxes    build-with-claude/claude-platform-on-aws.mdx:525,547
  Mid-convo system msgs    build-with-claude/mid-conversation-system-messages.mdx:15
  Fast mode                build-with-claude/fast-mode.mdx:23
  Cache diagnostics        build-with-claude/cache-diagnostics.mdx:15,1379
  Task budgets             build-with-claude/task-budgets.mdx:15
  Models API               bed:360; vtx:381; fdy:506

  ov  = build-with-claude/overview.mdx
  bed = build-with-claude/claude-in-amazon-bedrock.mdx
  vtx = build-with-claude/claude-on-vertex-ai.mdx
  fdy = build-with-claude/claude-in-microsoft-foundry.mdx
-->
