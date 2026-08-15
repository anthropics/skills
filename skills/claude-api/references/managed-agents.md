## Managed Agents (Beta) — Reading Guide & Routing

**Mandatory flow:** Agent (once) → Session (every run). `model`/`system`/`tools` live on the agent, never the session. See `shared/managed-agents-overview.md` for the full reading guide, beta headers, and pitfalls.

**Beta headers:** `managed-agents-2026-04-01` — the SDK sets this automatically for all `client.beta.{agents,environments,sessions,vaults,memory_stores,deployments,deployment_runs}.*` calls. Skills API uses `skills-2025-10-02` and Files API uses `files-api-2025-04-14`, but you don't need to explicitly pass those in for endpoints other than `/v1/skills` and `/v1/files`.

**Agents are persistent — create once, reference by ID.** Define agents and environments as version-controlled YAML applied with the `ant` CLI (see `shared/anthropic-cli.md`); your code owns the data plane (`sessions.create` with the stored agent ID). Never call `agents.create()` in the request path. If a binding you need isn't shown in the language README, WebFetch the relevant entry from `shared/live-sources.md` rather than guess.

**Reading guide:** Start with `shared/managed-agents-overview.md`, then the topical `shared/managed-agents-*.md` files (core, environments, tools, events, outcomes, multiagent, webhooks, memory, scheduled-deployments, client-patterns, onboarding, api-reference). For Python, TypeScript, Go, Ruby, PHP, and Java, read `{lang}/managed-agents/README.md` for code examples. For cURL, read `curl/managed-agents.md`. C# support via `client.Beta.Agents` — see `csharp/claude-api/README.md`.

**Route by intent, reading the topical file only when it applies:**

- **Set up from scratch / walk me through creating one** → `shared/managed-agents-onboarding.md` — run its interview (same flow as `managed-agents-onboard`).
- **Client code for X** → `shared/managed-agents-client-patterns.md` (stream reconnect, interrupt, `tool_confirmation` round-trip, idle/terminated break gate, file-mount gotchas).
- **Credentials** → lead with vault `environment_variable` credentials — secrets substituted at egress, never in the sandbox (`shared/managed-agents-tools.md` → Vaults); host-side custom tools are the fallback for self-hosted sandboxes.
- **Run on a schedule / cron / "every night"** → `shared/managed-agents-scheduled-deployments.md`.
- **Work fans out or one loop would fill its context with reading** → `shared/managed-agents-multiagent.md` — recommend a multiagent session, starting with `{"type": "self"}` and moving reading-heavy sub-tasks to a cheaper worker agent (e.g. Claude Haiku 4.5).
