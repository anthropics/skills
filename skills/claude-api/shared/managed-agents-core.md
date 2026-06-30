# Managed Agents — Core Concepts

## Architecture

Managed Agents is built around four core concepts:

| Concept | Endpoint | What it is |
|---|---|---|
| **Agent** | `/v1/agents` | A persisted, versioned object defining the agent's capabilities and persona: model, system prompt, tools, MCP servers, skills. **Must be created before starting a session.** See the Agents section below. |
| **Session** | `/v1/sessions` | A stateful interaction with an agent. References a pre-created agent by ID + an environment + initial instructions. Produces an event stream. |
| **Environment** | `/v1/environments` | A template defining the configuration for container provisioning. |
| **Container** | N/A | An isolated compute instance where the agent's **tools** execute (bash, file ops, code). The agent loop does not run here — it runs on Anthropic's orchestration layer and acts on the container via tool calls. |

```
                       ┌─────────────────────────────────────┐
                       │  Anthropic orchestration layer      │
Agent (config) ───────▶│  (agent loop: Claude + tool calls)  │
                       └──────────────┬──────────────────────┘
                                      │ tool calls
                                      ▼
Environment (template) ──▶ Container (tool execution workspace)
                                 │
                         Session ─┤
                                 ├── Resources (files, repos, memory stores — attached at startup)
                                 ├── Vault IDs (MCP credential references)
                                 └── Conversation (event stream in/out)
```

> **Agent creation is a prerequisite.** Sessions reference a pre-created agent by ID — `model`/`system`/`tools` live on the agent object, never on the session. Every flow starts with `POST /v1/agents`.

---

## Session Lifecycle

```
rescheduling → running ↔ idle → terminated
```

| Status         | Description                                                        |
| -------------- | ------------------------------------------------------------------ |
| `idle` | Agent has finished the current task, and is awaiting input. It's either waiting for input to continue working via a `user.message` or blocked awaiting a `user.custom_tool_result` or `user.tool_confirmation`. The `stop_reason` attached contains more information about why the Agent has stopped working. |
| `running` | Session has starting running, and the Agent is actively doing work. |
| `rescheduling` | Session is (re)scheduling after a retryable error has occurred, ready to be picked up by the orchestration system. |
| `terminated` | Session has terminated, entering an irreversible and unusable state.  |

- Events can be sent when the session is `running` or `idle`. Messages are queued and processed in order.
- The agent transitions `idle → running` when it receives a new event, then back to `idle` when done.
- Errors surface as `session.error` events in the stream, not as a status value.

Every session has a live trace view in the Anthropic Console at `https://platform.claude.com/workspaces/default/sessions/{session_id}`. Print this URL immediately after creating a session so the user can watch tool calls and messages stream in real time. The `default` workspace segment auto-resolves to the session's actual workspace on load, so you don't need the workspace id.

### Built-in session features

- **Context compaction** — if you approach max context, the API automatically condenses session history to keep the interaction going
- **Prompt caching** — historical repeated tokens are cached, reducing processing time and cost
- **Extended thinking** — on by default, returned as `agent.thinking` events

### Session operations

| Operation | Notes |
|---|---|
| List / fetch | Paginated list or single resource by ID |
| Update | Only `title` is updatable |
| Archive | Session becomes **read-only**. Not reversible. |
| Delete | Permanently deletes session, event history, container, and checkpoints. |

These are ops/inspection calls — typically made from a terminal, not application code. From the shell (see `shared/anthropic-cli.md`):

```sh
ant beta:sessions list --transform '{id,title,status,created_at}' --format jsonl
ant beta:sessions retrieve --session-id "$SID"
ant beta:sessions:events stream --session-id "$SID"   # watch events live
ant beta:sessions archive  --session-id "$SID"
ant beta:sessions delete   --session-id "$SID"
```

---

## Sessions

A session is a running agent instance inside an environment.

### Session Object

Key fields returned by the API:

| Field           | Type     | Description                                         |
| --------------- | -------- | --------------------------------------------------- |
| `type` | string | Always `"session"` |
| `id` | string | Unique session ID |
| `title` | string | Human-readable title |
| `status` | string | `idle`, `running`, `rescheduling`, `terminated` |
| `created_at` | string | ISO 8601 timestamp |
| `updated_at` | string | ISO 8601 timestamp |
| `archived_at` | string | ISO 8601 timestamp (nullable) |
| `environment_id` | string | Environment ID |
| `agent` | object | Agent configuration |
| `resources` | array | Attached files, repos, and memory stores |
| `metadata` | object | User-provided key-value pairs (max 8 keys) |
| `usage` | object | Token usage statistics |

### Creating a session

**A session is meaningless without an agent.** Sessions reference a pre-created agent by ID. Create the agent first via `agents.create()`, then reference it:

```ts
// 1. Create the agent (reusable, versioned)
const agent = await client.beta.agents.create(
  {
    name: "Coding Assistant",
    model: "claude-opus-4-8",
    system: "You are a helpful coding agent.",
    tools: [{ type: "agent_toolset_20260401"}],
  },
);

// 2. Start a session that references it
const session = await client.beta.sessions.create(
  {
    agent: agent.id,  // string shorthand → latest version. Or: { type: "agent", id: agent.id, version: agent.version }
    environment_id: environmentId,
    title: "Hello World Session",
  },
);
```

> 💡 **Watch it live in Console.** While developing, print a link so you can click through to the session UI instead of parsing the event stream: `https://platform.claude.com/workspaces/default/sessions/{session.id}`. The `default` workspace segment auto-resolves to the session's actual workspace on load, so you don't need to know the workspace id. Include this `print`/`console.log` in code you generate for users who are iterating locally.

**Session creation parameters:**

| Field           | Type     | Required | Description                                    |
| --------------- | -------- | -------- | ---------------------------------------------- |
| `agent`         | string or object | **Yes** | Three forms: string shorthand `"agent_abc123"` (latest version); pinned `{type: "agent", id, version}`; or `{type: "agent_with_overrides", id, version?, ...}` to override `model`/`system`/`tools`/`mcp_servers`/`skills` for this session only — see § Override agent configuration for a session |
| `environment_id`| string   | **Yes**  | Environment ID                                 |
| `title`         | string   | No       | Human-readable name (appears in logs/dashboards) |
| `resources`     | array    | No       | Files, GitHub repos, or memory stores, attached to the container at startup. Memory stores are session-create-only (not addable via `resources.add()`). |
| `vault_ids`     | array    | No       | Vault IDs (`vlt_*`) — MCP credentials with auto-refresh + `environment_variable` secrets substituted at egress. See `shared/managed-agents-tools.md` → Vaults. |
| `metadata`      | object   | No       | User-provided key-value pairs                  |

**Agent configuration fields** (passed to `agents.create()`, not `sessions.create()`):

| Field         | Type     | Required | Description                                    |
| ------------- | -------- | -------- | ---------------------------------------------- |
| `name`        | string   | **Yes**  | Human-readable name (1-256 chars)              |
| `model`       | string or object | **Yes** | Claude model ID (bare string, or `{id, speed}` object). All Claude 4.5+ models supported. |
| `system`      | string   | No       | System prompt — defines the agent's behavior (up to 100K chars) |
| `tools`       | array    | No       | Encompasses three kinds: (1) pre-built Claude Agent tools (`agent_toolset_20260401`), (2) MCP tools (`mcp_toolset`), and (3) custom client-side tools. Max 128. |
| `mcp_servers` | array    | No       | MCP server connections — standardized third-party capabilities (e.g. GitHub, Asana). Max 20, unique names. See `shared/managed-agents-tools.md` → MCP Servers. |
| `skills`      | array    | No       | Customized "best-practices" context with progressive disclosure. Max 20. See `shared/managed-agents-tools.md` → Skills. |
| `description` | string   | No       | Description of the agent (up to 2048 chars)    |
| `multiagent`  | object   | No       | `{type: "coordinator", agents: [...]}` — roster this agent may delegate to. See `shared/managed-agents-multiagent.md`. |
| `metadata`    | object   | No       | Arbitrary key-value pairs (max 16, keys ≤64 chars, values ≤512 chars) |

---

## Agents

**This is where every Managed Agents flow begins.** The agent object is a persisted, versioned configuration — you create it once, then reference it by ID every time you start a session. No agent → no session.

### Agent Object

The API is **flat** — `model`, `system`, `tools` etc. are top-level fields, not wrapped in an `agent:{}` sub-object.

| Field              | Type     | Required | Description                                        |
| ------------------ | -------- | -------- | -------------------------------------------------- |
| `name`             | string   | Yes      | Human-readable name                                |
| `model`            | string   | Yes      | Claude model ID                                    |
| `system`           | string   | No       | System prompt                                      |
| `tools`            | array    | No       | Agent toolset / MCP toolset / custom tools         |
| `mcp_servers`      | array    | No       | MCP server connections                             |
| `skills`           | array    | No       | Skill references (max 20)                          |
| `description`      | string   | No       | Description of the agent                           |
| `multiagent`       | object   | No       | Coordinator roster — see `shared/managed-agents-multiagent.md` |
| `metadata`         | object   | No       | Arbitrary key-value pairs                          |

### Lifecycle: create once, run many, update in place

The agent is a **persistent resource**, not a per-run parameter. The intended pattern:

```
┌─ setup (once) ─────────┐     ┌─ runtime (every invocation) ─┐
│ agents.create()        │     │ sessions.create(             │
│   → store agent_id     │ ──→ │   agent={type:..., id: ID}   │
│     in config/env/db   │     │ )                            │
└────────────────────────┘     └──────────────────────────────┘
```

**Anti-pattern:** calling `agents.create()` at the top of every script run. This accumulates orphaned agent objects, pays create latency on every invocation, and defeats the versioning model. If you see `agents.create()` in a function that's called per-request or per-cron-tick, that's wrong — hoist it to one-time setup and persist the ID.

> **Recommended — define agents and environments as YAML + apply via the `ant` CLI.** The split is **CLI for the control plane, SDK for the data plane**: agents and environments are relatively static resources you manage with `ant` (version-controlled YAML, applied from CI); sessions are dynamic and driven by your application through the SDK. See `shared/anthropic-cli.md` → *Version-controlled Managed Agents resources* for the `ant beta:agents create < agent.yaml` / `update --version N` flow. The SDK `agents.create()` call shown elsewhere in this doc is the in-code equivalent — use it when you need to provision programmatically, but prefer the YAML flow for anything a human maintains.

### Versioning

Each `POST /v1/agents/{id}` (update) creates a new immutable version (numeric timestamp, e.g. `1772585501101368014`). The agent's history is append-only — you can't edit a past version.

**Why version:**
- **Reproducibility** — pin a session to a known-good config: `{type: "agent", id, version: 3}`
- **Safe iteration** — update the agent without breaking sessions already running on the old version
- **Rollback** — if a new system prompt regresses, pin new sessions back to the prior version while you debug

**`version` is optional.** Omit it (or use the string shorthand `agent="agent_abc123"`) to get the latest version at session-creation time. Pass it explicitly (`{type: "agent", id, version: N}`) to pin for reproducibility.

**Getting the version to pin:** `agents.create()` and `agents.update()` both return `version` in the response. Store it alongside `agent_id`. To fetch the current latest for an existing agent: `GET /v1/agents/{id}` → `.version`.

**When to update vs create new:** Update (`POST /v1/agents/{id}`) when it's conceptually the same agent with tweaked behavior (better prompt, extra tool). Create a new agent when it's a different persona/purpose. Rule of thumb: if you'd give it the same `name`, update.

### Agent Endpoints

| Operation        | Method   | Path                                  |
| ---------------- | -------- | ------------------------------------- |
| Create           | `POST`   | `/v1/agents`                          |
| List             | `GET`    | `/v1/agents`                          |
| Get              | `GET`    | `/v1/agents/{id}`                     |
| Update           | `POST`   | `/v1/agents/{id}`                     |
| Archive          | `POST`   | `/v1/agents/{id}/archive`             |

> ⚠️ **Archive is permanent.** Archiving makes the agent read-only: existing sessions continue to run, but **new sessions cannot reference it**, and there is no unarchive. Since agents have no `delete`, this is the terminal lifecycle state. Never archive a production agent as routine cleanup — confirm with the user first.

### Using an Agent in a Session

Reference the agent by string ID (latest version) or by object with an explicit version:

```python
# String shorthand — uses the agent's latest version
session = client.beta.sessions.create(
    agent=agent.id,
    environment_id=environment_id,
)

# Or pin to a specific version (int)
session = client.beta.sessions.create(
    agent={"type": "agent", "id": agent.id, "version": agent.version},
    environment_id=environment_id,
)
```

### Override agent configuration for a session

The third `agent` form, `agent_with_overrides`, replaces parts of the agent's configuration for **a single session** — try a different model or grant an extra tool without versioning the agent. Pass `id` (and optionally `version`; omitted = latest, same default as the other two forms) plus any of `model`, `system`, `tools`, `mcp_servers`, `skills`:

```python
session = client.beta.sessions.create(
    agent={
        "type": "agent_with_overrides",
        "id": agent.id,
        "model": "claude-opus-4-8",   # replace the agent's model for this session
        "system": None,           # clear the system prompt for this session
    },
    environment_id=environment_id,
)
```

Each overridable field follows tri-state rules:
- **Omit** → the session inherits the value from the referenced agent version.
- **`null` (or `[]` for list fields)** → the session runs with that field cleared. Applies in full to `system`, `mcp_servers`, `skills`. Two exceptions: `model` is never clearable (`model: null` → 400 `agent_model_required`); clearing `tools` returns 400 when the session's effective `skills` is non-empty (skills require the `read` tool), otherwise `tools: null` / `tools: []` clears.
- **A value** → replaces the agent's value **in full**. Overrides never merge — a `tools` override must list every tool the session should have.

Overrides are session-local: they do **not** modify the agent resource or create a new agent version. The response's `agent` object reflects the post-override configuration, while its `id` and `version` still identify the base agent — so you can trace a session back to its base. In multiagent sessions, overrides apply to the coordinator and its `{type: "self"}` copies; roster agents referenced by ID always use their own as-created configuration (see `shared/managed-agents-multiagent.md`).

### Updating the agent configuration mid-session

`sessions.update()` can change `agent.tools`, `agent.mcp_servers` (including permission policies), and `vault_ids` on an **existing** session. This is a **session-local override** — it does not create a new agent version and does not propagate back to the agent object. The provided arrays are **full replacements**; to append one tool, `GET` the session, modify, and `POST` back. The session must be `idle` — interrupt first if running.

Only `tools` and `mcp_servers` can change after a session is created — to run with a `model`, `system`, or `skills` other than the agent's values, use `agent_with_overrides` at create time (above). The agent's configured `system` field is fixed for the session's lifetime; you can still **replace the effective system prompt between turns** by sending a `system.message` event (see `shared/managed-agents-events.md` § Updating the system prompt mid-session).

```python
client.beta.sessions.update(
    session.id,
    agent={
        "tools": [
            {"type": "agent_toolset_20260401"},
            {"type": "mcp_toolset", "mcp_server_name": "linear"},
        ],
        "mcp_servers": [{"type": "url", "name": "linear", "url": "https://mcp.linear.app/sse"}],
    },
    vault_ids=["vlt_..."],
)
```

