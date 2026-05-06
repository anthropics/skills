# Managed Agents — Multiagent Sessions

A coordinator agent can delegate to other agents within one session. All agents **share the container and filesystem**; each runs in its own **thread** — a context-isolated event stream with its own conversation history, model, system prompt, tools, MCP servers, and skills (from that agent's own config). Threads are persistent: the coordinator can send a follow-up to a subagent it called earlier and that subagent retains its prior turns.

The SDK sets the `managed-agents-2026-04-01` beta header automatically on all `client.beta.{agents,sessions}.*` calls; no additional header is required for multiagent.

---

## Declare the roster on the coordinator

`multiagent` is a **top-level field** on `agents.create()` / `agents.update()` — **not** a `tools[]` entry. `agents` lists 1–20 roster entries. Nothing changes on `sessions.create()` — the roster is resolved from the coordinator's config.

```python
orchestrator = client.beta.agents.create(
    name="Engineering Lead",
    model="{{OPUS_ID}}",
    system="You coordinate engineering work. Delegate code review to the reviewer and test writing to the test agent.",
    tools=[{"type": "agent_toolset_20260401"}],
    multiagent={
        "type": "coordinator",
        "agents": [
            reviewer.id,                                            # bare string — latest version
            {"type": "agent", "id": test_writer.id, "version": 4},  # pinned version
            {"type": "self"},                                       # the coordinator itself
        ],
    },
)

session = client.beta.sessions.create(agent=orchestrator.id, environment_id=env.id)
```

| Roster entry | Shape | Notes |
|---|---|---|
| String shorthand | `"agent_abc123"` | References the latest version of a stored agent. |
| Agent reference | `{type: "agent", id, version?}` | Omit `version` to pin the latest at coordinator save time. |
| Self | `{type: "self"}` | The coordinator can spawn copies of itself. |

Up to **20 unique agents** in the roster; the coordinator may spawn **multiple copies** of each. **One level of delegation only** — depth > 1 is ignored.

---

## Threads

The session-level event stream is the **primary thread** — it shows the coordinator's trace plus a condensed view of subagent activity (thread status transitions and cross-thread messages, not every subagent tool call). Drill into a specific subagent via the per-thread endpoints:

| Operation | HTTP | SDK (`client.beta.sessions.threads.*`) |
|---|---|---|
| List threads | `GET /v1/sessions/{sid}/threads` | `.list(session_id)` |
| Retrieve one | `GET /v1/sessions/{sid}/threads/{tid}` | `.retrieve(thread_id, session_id=...)` |
| Archive | `POST /v1/sessions/{sid}/threads/{tid}/archive` | `.archive(thread_id, session_id=...)` |
| List thread events | `GET /v1/sessions/{sid}/threads/{tid}/events` | `.events.list(thread_id, session_id=...)` |
| Stream thread events | `GET /v1/sessions/{sid}/threads/{tid}/stream` | `.events.stream(thread_id, session_id=...)` |

Each `SessionThread` carries `id`, `status` (`running` | `idle` | `rescheduling` | `terminated`), `agent` (a resolved snapshot of the agent config — `id`, `name`, `model`, `system`, `tools`, `skills`, `mcp_servers`, `version`), `parent_thread_id` (null for the primary thread, which is included in the list), `archived_at`, and optional `stats`/`usage`. **Session status aggregates thread statuses** — if any thread is `running`, `session.status` is `running`. Max **25 concurrent threads**. When draining a per-thread stream, break on `session.thread_status_idle` (and check its `stop_reason` as you would for the session-level idle).

---

## Multiagent events (on the session stream)

| Event | Payload highlights | Meaning |
|---|---|---|
| `session.thread_created` | `session_thread_id`, `agent_name` | A new thread was created. |
| `session.thread_status_running` | `session_thread_id`, `agent_name` | Thread started activity. |
| `session.thread_status_idle` | `session_thread_id`, `agent_name`, **`stop_reason`** | Thread is awaiting input. Inspect `stop_reason` (same shape as `session.status_idle.stop_reason`). |
| `session.thread_status_rescheduled` | `session_thread_id`, `agent_name` | Thread is rescheduling after a retryable error. |
| `session.thread_status_terminated` | `session_thread_id`, `agent_name` | Thread was archived or hit a terminal error. |
| `agent.thread_message_sent` | `to_session_thread_id`, `to_agent_name`, `content` | Coordinator sent a follow-up to another thread. |
| `agent.thread_message_received` | `from_session_thread_id`, `from_agent_name`, `content` | An agent delivered its result to the coordinator. |

---

## Tool permissions and custom tools from subagent threads

When a subagent needs your client (an `always_ask` confirmation, or a custom tool result), the request is **cross-posted to the primary thread** with `session_thread_id` identifying the originating thread — so you only need to watch the session stream. Reply with `user.tool_confirmation` (carrying `tool_use_id`) or `user.custom_tool_result` (carrying `custom_tool_use_id`), and **echo the `session_thread_id` from the originating event** (the SDK param type and docstring expect it). The server also routes by the tool-use ID, so the echo is belt-and-suspenders rather than load-bearing — but include it.

```python
for event_id in stop.event_ids:
    pending = events_by_id[event_id]
    confirmation = {
        "type": "user.tool_confirmation",
        "tool_use_id": event_id,
        "result": "allow",
    }
    if pending.session_thread_id is not None:
        confirmation["session_thread_id"] = pending.session_thread_id
    client.beta.sessions.events.send(session.id, events=[confirmation])
```

The same pattern applies to `user.custom_tool_result`.

---

## Pitfalls

- **Don't put the roster on `sessions.create()` or in `tools[]`.** `multiagent` is a top-level agent field; update the coordinator, then start a session that references it.
- **Don't assume shared context.** Threads share the filesystem but not conversation history or tools. If the coordinator needs a subagent to act on something, it must say so in the delegated message (or write it to disk).
- **Depth > 1 is ignored.** A subagent's own `multiagent` roster (if any) doesn't cascade — only the session's coordinator delegates.

For per-language bindings beyond Python, WebFetch `https://platform.claude.com/docs/en/managed-agents/multi-agent.md` (see `shared/live-sources.md`).
