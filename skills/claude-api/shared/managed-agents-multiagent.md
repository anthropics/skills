# Managed Agents — Multiagent Sessions

A coordinator agent can delegate to other agents within one session. All agents **share the container and filesystem**; each runs in its own **thread** — a context-isolated event stream with its own conversation history, model, system prompt, tools, MCP servers, and skills (from that agent's own config). Threads are persistent: the coordinator can send a follow-up to a subagent it called earlier and that subagent retains its prior turns.

The SDK sets the `managed-agents-2026-04-01` beta header automatically on all `client.beta.{agents,sessions}.*` calls; no additional header is required for multiagent.

---

## When to use it — start with `self`, then add cheaper workers

**If the agent's work splits into independent pieces** — several sources to research, many files or records to process, anything shaped like "look into N things, then summarize" — or one piece would fill its context with reading, **use a multiagent session instead of one long single-threaded loop.** Each delegated piece runs in its own thread with a fresh context window, threads run in parallel in the same container, and only each subagent's report comes back, so the coordinator's context stays small. There is no orchestration code to write: the coordinator is given delegation tools automatically and decides when to use them, and your client still creates one session and reads one stream.

**Step 1 — the smallest useful roster is the agent itself.** Add a `multiagent` block whose only entry is `{"type": "self"}`. The coordinator can then hand self-contained sub-tasks to copies of itself — same model, system prompt, and tools, minus the ability to delegate further — and combine what they report. Nothing else changes.

```python
agent = client.beta.agents.create(
    name="Research assistant",
    description="Researches a question end to end. A copy can be spawned to own one well-scoped sub-question.",
    model="claude-opus-5",
    system="You are a research assistant. When a request splits into independent sub-questions, delegate each to a copy of yourself, one self-contained task per copy, then verify and combine their reports.",
    tools=[{"type": "agent_toolset_20260401"}],
    multiagent={"type": "coordinator", "agents": [{"type": "self"}]},  # the only change vs. a single agent
)

session = client.beta.sessions.create(agent=agent.id, environment_id=env.id)  # unchanged
```

**Step 2 — move the reading-heavy work to a cheaper model.** Delegated research work is mostly searching, reading, and extracting: many input tokens, little hard reasoning. Create a second agent on a smaller model with a narrow `system` prompt and only the tools it needs, and list it next to `self`. A roster entry is only a reference: the worker runs on its own `model`, `system`, and `tools`, and its tokens are billed at its own model's rates. The large model spends its tokens on planning, checking, and synthesis; the small model does the bulk reading.

```python
worker = client.beta.agents.create(
    name="Web researcher",
    description="Fast, low-cost, read-only researcher. Give it one well-scoped question; it searches, reads, and reports findings with sources.",
    model="claude-haiku-4-5",
    system="Answer exactly the question you are given. Search and read as much as you need, then report concise findings with a source URL or file path for every claim.",
    tools=[{
        "type": "agent_toolset_20260401",
        "default_config": {"enabled": False},
        "configs": [{"name": n, "enabled": True} for n in ("read", "glob", "grep", "web_fetch", "web_search")],
    }],
)

lead = client.beta.agents.create(
    name="Research lead",
    description="Plans and synthesizes research. A copy can be spawned to own one large sub-analysis.",
    model="claude-opus-5",
    system="Plan the work. Delegate each independent, reading-heavy question to Web researcher, one self-contained task per spawn, several in parallel. Keep verification and the final synthesis for yourself; spawn a copy of yourself only for a sub-analysis that needs your full capability.",
    tools=[{"type": "agent_toolset_20260401"}],
    multiagent={"type": "coordinator", "agents": [worker.id, {"type": "self"}]},
)
```

**Step 3 — add dedicated specialists.** When the sub-tasks call for different skills, give each its own agent — its own model, a narrow `system` prompt, and only the tools it needs — and roster them by ID next to `self`. Here the lead makes a change itself, sends the same review brief to several read-only reviewer threads for independent passes (one rostered agent can be spawned many times), and hands a test writer a self-contained brief; it then de-duplicates the findings, checks each against the code, and keeps the fix and the summary for itself.

```python
reviewer = client.beta.agents.create(
    name="Concurrency reviewer",
    description="Read-only reviewer for race conditions, deadlocks, lost updates, and retry/idempotency bugs. Give it the changed file paths and the invariants that must hold; it reports findings with file:line evidence. Spawn several on the same change for independent reviews.",
    model="claude-sonnet-5",
    system="Review only the files you are pointed at. Look for concurrency bugs: unsynchronized shared state, lock ordering, non-atomic read-modify-write, retries without idempotency. Report each finding as file:line, the interleaving that triggers it, and a suggested fix; say plainly if you found none.",
    tools=[{"type": "agent_toolset_20260401", "default_config": {"enabled": False},
            "configs": [{"name": n, "enabled": True} for n in ("read", "glob", "grep")]}],
)
test_writer = client.beta.agents.create(
    name="Test writer",
    description="Writes and runs tests. Give it the module path, the behavior to pin down, and the test command; it adds test files, runs them, and reports results with output.",
    model="claude-sonnet-5",
    system="Write focused tests for the behavior you are given, run them with the command you are given, and report pass/fail, the relevant output, and the paths of files you added. Do not edit non-test code; if the code under test looks wrong, report that instead.",
    tools=[{"type": "agent_toolset_20260401", "default_config": {"enabled": True},
            "configs": [{"name": n, "enabled": False} for n in ("web_fetch", "web_search")]}],
)
lead = client.beta.agents.create(
    name="Engineering lead",
    description="Plans and makes code changes and integrates specialist reports. A copy can be spawned to own one independent change.",
    model="claude-opus-5",
    system="Make the change yourself. Then, in parallel, send the changed paths and invariants to three Concurrency reviewers and the module path and test command to Test writer. Merge and de-duplicate the reviewers' findings, check each against the code before acting on it, fix, and have Test writer re-run. Keep design decisions and the final summary for yourself.",
    tools=[{"type": "agent_toolset_20260401"}],
    multiagent={"type": "coordinator", "agents": [reviewer.id, test_writer.id, {"type": "self"}]},
)
```

The same shape fits a pipeline of different specialists: a fast document extractor (for example on Claude Haiku 4.5) that writes one JSON file per input document, a verifier that checks each file against its source, and a lead that applies the corrections and writes the final table to `/mnt/session/outputs/`. Put the input and output paths in every task: threads share the container's filesystem, not each other's conversation.

- **Good fits:** parallel research across sources; reading large amounts of material without filling the coordinator's context; specialists with narrow prompts and tool sets rather than one agent carrying every tool. **Poor fit:** a small single-step task — every delegation costs a round-trip and a re-briefing.
- **Write `name` and `description` for the coordinator to read.** The coordinator chooses whom to spawn from each roster entry's name and description (the `self` entry is listed under the coordinator's own name), so say what each agent is good at and what to hand it. Names must be unique across the roster; don't name an agent `self`.
- **Say how to delegate in the coordinator's `system` prompt** — what to hand off and to whom, how many at once, what to keep for itself, and what is too small to be worth delegating (the *Delegating to subagents* sample prompt in `shared/model-migration.md` is a starting point). Subagents see none of the coordinator's conversation, so each task must carry the paths, constraints, and report format it needs. Spawning returns immediately; the subagent's report arrives in a later coordinator turn.
- **Limits:** 1–20 roster entries (at most one `self`; each rostered agent can be spawned many times), one level of delegation (a roster member must not have its own `multiagent`), and at most 25 concurrent threads per session — archive finished threads if a long session needs more (see *Interrupting and archiving threads* below).

The sections below are the reference for rosters, threads, events, and client-side handling; the platform guide is `https://platform.claude.com/docs/en/managed-agents/multiagent-orchestration.md`.

---

## Declare the roster on the coordinator

`multiagent` is a **top-level field** on `agents.create()` / `agents.update()` — **not** a `tools[]` entry. `agents` lists 1–20 roster entries. Nothing changes on `sessions.create()` — the roster is resolved from the coordinator's config.

```python
orchestrator = client.beta.agents.create(
    name="Engineering lead",
    model="claude-opus-5",
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
| Advisor | `{type: "advisor", model}` | A model the session's primary thread can consult mid-turn. At most one per roster. See § Advisor below. |

If the session was created with `agent_with_overrides` (see `shared/managed-agents-core.md` → Override agent configuration for a session), those overrides apply to the **coordinator and its `self` copies**. Roster agents referenced by ID always use their own as-created configuration — overrides do not propagate to them.

The coordinator's thread receives delegation tools for working the roster: `list_agents` (see the roster) and `send_to_agent` (task or message a member). Up to **20 unique agents** in the roster; the coordinator may spawn **multiple copies** of each. **One level of delegation only** — and it is enforced rather than silently flattened: rostering an agent that itself carries a `multiagent.agents` roster fails the create or update with a validation error.

**Inference geo pins must be roster-uniform.** When agents pin an inference geography (`model.inference_geo` — see `shared/managed-agents-core.md` § Pinning inference geography), the coordinator's pin and every roster member's must all be the same value or all be unset. A mismatched roster is a 400 validation error, both when the agent is saved and when a session-create `model` override changes any of the pins.

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

Each `SessionThread` carries `id`, `status` (`running` | `idle` | `rescheduling` | `terminated`), `agent` (a resolved snapshot of the agent config — `id`, `name`, `model`, `system`, `tools`, `skills`, `mcp_servers`, `version` — except advisor threads, whose `agent` is the two-field advisor form `{"type": "advisor", "model": ...}` — see § Advisor), `parent_thread_id` (null for the primary thread, which is included in the list), `archived_at`, and optional `stats`/`usage`. Per-thread `usage.list_cost` figures do **not** sum to the session total — the session figure additionally includes session running time and each figure is rounded independently; the session-level `usage.list_cost` is authoritative. **Session status aggregates thread statuses** — if any thread is `running`, `session.status` is `running`. Max **25 concurrent threads** (advisor threads are exempt — see § Advisor). When draining a per-thread stream, break on `session.thread_status_idle` (and check its `stop_reason` as you would for the session-level idle).

**A session budget is one shared cap across all threads** — no per-thread caps. Each thread's consumption is priced at its own served model, and threads pause independently (`stop_reason: budget_reached`) as the shared cap is reached; one thread can pause while another finishes its in-flight request. A thread waiting on `requires_action` outranks the cap at the session level. See `shared/managed-agents-core.md` § Session budgets.

---

## Multiagent events (on the session stream)

| Event | Payload highlights | Meaning |
|---|---|---|
| `session.thread_created` | `session_thread_id`, `agent_name` | A new thread was created. |
| `session.thread_status_running` | `session_thread_id`, `agent_name` | Thread started activity. |
| `session.thread_status_idle` | `session_thread_id`, `agent_name`, **`stop_reason`** | Thread is awaiting input — or paused at the session's shared budget (`stop_reason: budget_reached`). Inspect `stop_reason` (same shape as `session.status_idle.stop_reason`). |
| `session.thread_status_rescheduled` | `session_thread_id`, `agent_name` | Thread is rescheduling after a retryable error. |
| `session.thread_status_terminated` | `session_thread_id`, `agent_name` | Thread ended — completed its work and self-terminated (advisor consultation threads — see § Advisor), was archived, or hit a terminal error. |
| `agent.thread_message_sent` | `to_session_thread_id`, `to_agent_name`, `content` | *This* thread sent a message to another thread. On the primary stream: the coordinator sent a task or follow-up to an agent. |
| `agent.thread_message_received` | `from_session_thread_id`, `from_agent_name`, `content` | A message arrived on *this* thread from another. On the primary stream: an agent sent a report or question to the coordinator. |

> **Direction is relative to the thread whose stream carries the event**, not to the coordinator. The same delegated task is an `agent.thread_message_sent` on the primary stream and an `agent.thread_message_received` on the child's own stream. Reading `_received` as "a subagent finished" is wrong once you're reading a child stream.

---

## Previewing a subagent's text

Each thread's stream accepts the same `event_deltas[]` parameter as the session-level stream, so you can watch a subagent's text as the model generates it:

```
GET /v1/sessions/{sid}/threads/{tid}/stream?event_deltas%5B%5D=agent.message
```

**Previews are thread-scoped.** A child's previews are delivered only on that child's stream and never cross-posted to the session-level stream, whose previews stay scoped to the primary thread. So watching a subagent live means opening its thread stream — the session stream will not show it, no matter what you pass.

> ⚠️ **Only plain assistant text previews.** A subagent's *reply to its coordinator* rides `agent.thread_message_sent` and is never previewed. A worker that does nothing but report back therefore streams no deltas at all, even with a correct opt-in on the right thread. To get a live preview out of a subagent, its prompt has to make it write the answer as a plain assistant message in its own thread first, and only then report to the coordinator. Run one accumulator per connection, and exit the read loop on `session.thread_status_idle`. Opt-in, accumulate, and reconcile details: `shared/managed-agents-events.md` → Live previews.

---

## Advisor

An `{"type": "advisor", "model": "<model id>"}` roster entry gives the session's **primary thread** an advisor: a model it can consult mid-turn for strategic guidance (planning an approach, getting unstuck, reviewing work before finishing). The entry has exactly two fields — `type` and `model` — and can sit alongside any other roster forms; a roster with no other entries works too. The advisor is also available as a server tool on the Messages API (`advisor_20260301` — see `shared/tool-use-concepts.md` → Advisor); the Managed Agents surface differs in configuration and delivery: the roster entry has **no `max_uses`, `max_tokens`, or `caching` fields**, and advice arrives through thread events rather than `advisor_tool_result` blocks.

```python
agent = client.beta.agents.create(
    name="Backend engineer",
    model="claude-sonnet-5",
    system="You implement backend features end to end.",
    multiagent={
        "type": "coordinator",
        "agents": [{"type": "advisor", "model": "claude-opus-5"}],
    },
)
```

(Claude Opus 5 is the default advisor choice. It is a redacted advisor — the agent reads its advice server-side, but the client sees `[{"type": "redacted"}]`; see *Plaintext vs redacted delivery* below. For client-readable advice, a plaintext advisor such as `claude-opus-4-8` is valid only when the agent's own model is `claude-opus-4-8` or below — agents on Claude Opus 5, Claude Fable 5, or Claude Mythos 5 can only pair with redacted advisors, so client-readable advice is not available for them (pairing table: `shared/tool-use-concepts.md`).)

**Rules:**
- **At most one advisor entry per roster.** The entry occupies the reserved roster name `anthropic.advisor` — a roster that also lists a member literally named `anthropic.advisor` is a 400. In responses, the advisor entry is echoed **last** in the roster regardless of submitted position.
- **Pairing is validated at agent save:** the advisor model must meet a minimum capability bar, and the agent's own model must not be more capable than its advisor (equals can pair). Invalid pairing → 400. The valid pairs mirror the Messages advisor tool's executor↔advisor table (`shared/tool-use-concepts.md`) — except Claude Fable 5, which is temporarily unavailable as a Managed Agents advisor; use claude-opus-5 instead. Claude Mythos 5 advisors are unaffected — the unavailability is specific to claude-fable-5, despite the two models' shared capabilities.
- **Only the primary thread consults it.** The advisor is not a roster agent: invisible to the coordinator's `list_agents` tool, unreachable via `send_to_agent`, and roster agents cannot consult it.

**How consultations work.** Each consultation runs as a platform-spawned thread named `anthropic.advisor` that terminates itself when done; the advice is delivered to the primary thread as an `agent.thread_message_received` event. Typical event order (the reserved name rides `agent_name` on lifecycle events and `from_agent_name` on the delivery):

1. `session.thread_created`
2. `session.thread_status_running`
3. `agent.thread_message_received` — the advice
4. `session.thread_status_idle` (`stop_reason: end_turn`)
5. `session.thread_status_terminated`

No `agent.tool_use` and no `agent.thread_message_sent` are emitted for a consultation, and **the advice delivery is not guaranteed to precede the advisor thread's idle/terminated events** — don't treat those as "advice already delivered."

**Plaintext vs redacted delivery.** Whether your client can read the advice is the advisor model's policy, mirroring the Messages advisor tool's result variants: models that return plaintext there deliver readable text content here; models that return redacted results deliver `[{"type": "redacted"}]` as the message content on every client surface, while the agent still reads the full advice server-side. Advisor thinking is never surfaced. Clients cannot send `redacted` blocks themselves — an event containing one is a 400.

**Failure and interruption.** A failed consultation — or one abandoned via a `user.interrupt` carrying the advisor thread's `session_thread_id` — never fails the agent's turn: the agent continues after a generic notice. A session-level `user.interrupt` during a consultation halts the whole session as usual (every thread, primary included), terminating the advisor thread with no advice delivered.

**Threads, billing, caching.** Advisor threads are **exempt from the 25-concurrent-thread limit**. They appear in the session's thread list with `agent` set to the advisor form as configured (`{"type": "advisor", "model": ...}`) and `parent_thread_id` set to the primary thread. Consultations are billed at the advisor model's rates; their tokens appear in the advisor thread's usage and the session's totals. Advisor-side prompt caching is automatic — nothing to configure.

**Removing the advisor:** update the agent with a roster that omits the entry; if the advisor is the roster's only entry, clear the roster with `"multiagent": null`.

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

## Interrupting and archiving threads

- **`user.interrupt` without `session_thread_id` interrupts every non-archived thread in the session, including the primary** — it is not a primary-only stop. Pass `session_thread_id` to target one thread.
- **Against a child thread blocked on `requires_action`**, the interrupt closes each pending tool call with an *error* tool result (`"Tool execution was interrupted before completion. Please retry."`) and re-emits `session.thread_status_idle` with `stop_reason: end_turn` directly — the model is not sampled. Against a thread already `idle`, the interrupt is a no-op.
- **Archive requires the thread to be idle, and `requires_action` counts as idle** — a thread parked on a pending tool call can be archived directly. Only a *running* thread must be interrupted first.

---

## Pitfalls

- **Don't put the roster on `sessions.create()` or in `tools[]`.** `multiagent` is a top-level agent field; update the coordinator, then start a session that references it.
- **Don't assume shared context.** Threads share the filesystem but not conversation history or tools. If the coordinator needs a subagent to act on something, it must say so in the delegated message (or write it to disk).
- **Depth > 1 is a validation error.** Rostering an agent that itself carries a `multiagent.agents` roster fails the create or update — only the session's coordinator delegates.

For per-language bindings beyond Python, WebFetch `https://platform.claude.com/docs/en/managed-agents/multiagent-orchestration.md` (see `shared/live-sources.md`).
