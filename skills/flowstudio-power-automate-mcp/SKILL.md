---
name: flowstudio-power-automate-mcp
description: >-
  Foundation skill for Power Automate via FlowStudio MCP — auth setup, the
  reusable MCP helper (Python + Node.js), tool discovery via `list_skills` /
  `tool_search`, and oversized-response handling. Load this skill first when
  connecting an agent to Power Automate. For specialized workflows, load
  `flowstudio-power-automate-build`, `flowstudio-power-automate-debug`, `flowstudio-power-automate-monitoring`
  (Pro+), or `flowstudio-power-automate-governance` (Pro+) — each contains the workflow
  narrative, this skill provides the plumbing they all rely on. Requires a
  FlowStudio MCP subscription or compatible server — see https://mcp.flowstudio.app
metadata:
  openclaw:
    requires:
      env:
        - FLOWSTUDIO_MCP_TOKEN
    primaryEnv: FLOWSTUDIO_MCP_TOKEN
    homepage: https://mcp.flowstudio.app
---

# Power Automate via FlowStudio MCP — Foundation

This skill is the **plumbing layer**. It gives an AI agent a reliable way to
talk to a FlowStudio MCP server, discover what tools are available, and handle
the responses cleanly. The actual workflow narratives live in four specialized
skills that all build on this one.

> **Real debugging examples**: [Expression error in child flow](https://github.com/ninihen1/power-automate-mcp-skills/blob/main/examples/fix-expression-error.md) |
> [Data entry, not a flow bug](https://github.com/ninihen1/power-automate-mcp-skills/blob/main/examples/data-not-flow.md) |
> [Null value crashes child flow](https://github.com/ninihen1/power-automate-mcp-skills/blob/main/examples/null-child-flow.md)

> **Requires:** A [FlowStudio](https://mcp.flowstudio.app) MCP subscription (or
> compatible Power Automate MCP server). You will need:
> - MCP endpoint: `https://mcp.flowstudio.app/mcp` (same for all subscribers)
> - API key / JWT token (`x-api-key` header — NOT Bearer)
> - Power Platform environment name (e.g. `Default-<tenant-guid>`)

---

## Which Skill to Use When

Skills are organized by **use-case intent**, not by which tools they call.
Multiple skills reuse the same underlying tools — pick by what the user is
trying to accomplish.

| The user wants to… | Load this skill |
|---|---|
| Make or change a flow (build new, modify existing, fix a bug, deploy) | **`flowstudio-power-automate-build`** |
| Diagnose why a flow failed (root cause analysis on a failing run) | **`flowstudio-power-automate-debug`** |
| See tenant-wide flow health, failure rates, asset inventory | **`flowstudio-power-automate-monitoring`** *(Pro+)* |
| Tag, audit, classify, score, or offboard flows | **`flowstudio-power-automate-governance`** *(Pro+)* |
| Just connect, set up auth, write the helper, parse responses | this skill (foundation) |

**Same tools, different lenses.** `flowstudio-power-automate-build` and `flowstudio-power-automate-debug`
both call `update_live_flow`, `get_live_flow`, and the run-error tools — they
differ in *direction* (forward vs backward) and *intent* (compose vs diagnose).
`flowstudio-power-automate-monitoring` and `flowstudio-power-automate-governance` both call the Store
tools — they differ in *audience* (ops vs compliance) and *outcome* (read
health vs write metadata). Don't try to memorize "which tools belong to which
skill"; pick the skill by what the user is doing.

---

## Source of Truth

| Priority | Source | Covers |
|----------|--------|--------|
| 1 | **Real API response** | Always trust what the server actually returns |
| 2 | **`tool_search` / `list_skills`** | Authoritative tool schemas, parameter names, types, required flags |
| 3 | **SKILL docs & reference files** | Workflow narrative, response shapes, non-obvious behaviors |

If documentation disagrees with a real API response, the API wins. Tool schemas
in this skill (or any other) may lag the server — call `tool_search` to confirm
the current shape before invoking a tool you haven't used recently.

---

## How Agents Discover Tools

The FlowStudio MCP server (v1.1.5+) exposes two **non-billable** meta-tools that
let an agent load only the tools relevant to the current task. Use these in
preference to `tools/list` (which loads all 30+ schemas at once) or guessing
tool names.

| Meta-tool | When to call |
|---|---|
| `list_skills` | Cold start — see the available bundles (`build-flow`, `create-flow`, `debug-flow`, `monitor-flow`, `discover`, `governance`) and pick one |
| `tool_search` with `query: "skill:<name>"` | Load the full schema set for one bundle (e.g. `skill:debug-flow`) |
| `tool_search` with `query: "select:tool1,tool2"` | Load specific tools by name (e.g. when chaining across bundles) |
| `tool_search` with `query: "<keywords>"` | Free-text search when the user request is ambiguous (e.g. `"cancel run"`) |

The server's `tool_search` bundles are intentionally **narrower than this
skill family** — they're starter packs of the most-likely-needed tools per
intent. A workflow skill (e.g. `flowstudio-power-automate-debug`) may pull a bundle and
then call `tool_search` again for additional tools as the workflow progresses.

```python
# Cold start — pick a bundle by intent
skills = mcp("list_skills", {})
# [{"name": "debug-flow", "description": "Investigate why a flow is failing...",
#   "tools": ["get_live_flow_runs", "get_live_flow_run_error", ...]}, ...]

# Load schemas for the bundle
debug_tools = mcp("tool_search", {"query": "skill:debug-flow"})
```

Current common bundles:

| Bundle | Use when |
|---|---|
| `create-flow` | Creating a brand-new flow; includes environment/connection discovery, connector description, dynamic options, and `update_live_flow` |
| `build-flow` | Reading or modifying an existing flow definition |
| `debug-flow` | Investigating failed runs and action-level inputs/outputs |
| `monitor-flow` | Starting/stopping, triggering, cancelling, or resubmitting runs |
| `discover` | Enumerating environments, flows, and connections |
| `governance` | Pro+ cached-store tagging, maker audit, and metadata updates |

---

## Recommended Language: Python or Node.js

All examples in this skill family use **Python with `urllib.request`**
(stdlib — no `pip install` needed). **Node.js** is an equally valid choice:
`fetch` is built-in from Node 18+, JSON handling is native, and async/await
maps cleanly onto the request-response pattern of MCP tool calls — making it
a natural fit for teams already working in a JavaScript/TypeScript stack.

| Language | Verdict | Notes |
|---|---|---|
| **Python** | Recommended | Clean JSON handling, no escaping issues, all skill examples use it |
| **Node.js (≥ 18)** | Recommended | Native `fetch` + `JSON.stringify`/`JSON.parse`; no extra packages |
| PowerShell | Avoid for flow operations | `ConvertTo-Json -Depth` silently truncates nested definitions; quoting and escaping break complex payloads. Acceptable for a quick connectivity smoke-test but not for building or updating flows. |
| cURL / Bash | Possible but fragile | Shell-escaping nested JSON is error-prone; no native JSON parser |

> **TL;DR — use the Core MCP Helper (Python or Node.js) below.** Both handle
> JSON-RPC framing, auth, and response parsing in a single reusable function.

---

## Core MCP Helper (Python)

Use this helper throughout all subsequent operations:

```python
import json, urllib.request

TOKEN = "<YOUR_JWT_TOKEN>"
MCP   = "https://mcp.flowstudio.app/mcp"

def mcp(tool, args, cid=1):
    payload = {"jsonrpc": "2.0", "method": "tools/call", "id": cid,
               "params": {"name": tool, "arguments": args}}
    req = urllib.request.Request(MCP, data=json.dumps(payload).encode(),
        headers={"x-api-key": TOKEN, "Content-Type": "application/json",
                 "User-Agent": "FlowStudio-MCP/1.0"})
    try:
        resp = urllib.request.urlopen(req, timeout=120)
    except urllib.error.HTTPError as e:
        body = e.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"MCP HTTP {e.code}: {body[:200]}") from e
    raw = json.loads(resp.read())
    if "error" in raw:
        raise RuntimeError(f"MCP error: {json.dumps(raw['error'])}")
    text = raw["result"]["content"][0]["text"]
    return json.loads(text)
```

> **Common auth errors:**
> - HTTP 401/403 → token is missing, expired, or malformed. Get a fresh JWT from [mcp.flowstudio.app](https://mcp.flowstudio.app).
> - HTTP 400 → malformed JSON-RPC payload. Check `Content-Type: application/json` and body structure.
> - `MCP error: {"code": -32602, ...}` → wrong or missing tool arguments. Call `tool_search` with `select:<toolname>` to confirm the schema.

---

## Core MCP Helper (Node.js)

Equivalent helper for Node.js 18+ (built-in `fetch` — no packages required):

```js
const TOKEN = "<YOUR_JWT_TOKEN>";
const MCP   = "https://mcp.flowstudio.app/mcp";

async function mcp(tool, args, cid = 1) {
  const payload = {
    jsonrpc: "2.0",
    method: "tools/call",
    id: cid,
    params: { name: tool, arguments: args },
  };
  const res = await fetch(MCP, {
    method: "POST",
    headers: {
      "x-api-key": TOKEN,
      "Content-Type": "application/json",
      "User-Agent": "FlowStudio-MCP/1.0",
    },
    body: JSON.stringify(payload),
  });
  if (!res.ok) {
    const body = await res.text();
    throw new Error(`MCP HTTP ${res.status}: ${body.slice(0, 200)}`);
  }
  const raw = await res.json();
  if (raw.error) throw new Error(`MCP error: ${JSON.stringify(raw.error)}`);
  return JSON.parse(raw.result.content[0].text);
}
```

> Requires Node.js 18+. For older Node, replace `fetch` with `https.request`
> from the stdlib or install `node-fetch`.

---

## Verify the Connection

A 3-line smoke test that confirms the token, endpoint, and helper all work:

```python
skills = mcp("list_skills", {})
print(f"Connected — {len(skills)} skill bundles available:",
      [s["name"] for s in skills])
```

Expected output:

```text
Connected — 6 skill bundles available: ['build-flow', 'create-flow', 'debug-flow', 'monitor-flow', 'discover', 'governance']
```

If this fails, see the **Common auth errors** note above. If it succeeds, hand
off to the workflow skill matching the user's intent.

---

## Handling Oversized Responses

Some MCP tool responses are large enough to overflow the agent's context window:

| Tool | Typical size | Cause |
|---|---|---|
| `describe_live_connector` | 100-600 KB | Full Swagger spec for a connector |
| `get_live_dynamic_properties` | 50-500 KB | Dynamic connector field schemas such as SharePoint list columns |
| `get_live_flow_run_action_outputs` (no `actionName`) | 50 KB – several MB | Top-level action outputs; with an action in a foreach, every repetition can be returned |
| `get_live_flow` (large flows) | 50-500 KB | Deeply nested branches |
| `list_live_flows` (large tenants) | 50-200 KB | Hundreds of flow records |

### When the harness spills to a file

Agent harnesses (Claude Code, VS Code Copilot, etc.) save oversized responses
to a temp file (e.g. `tool-results/mcp-flowstudio-describe_live_connector-NNNN.txt`)
and return the path instead of the inline JSON. The file is **double-wrapped** —
the outer MCP envelope plus the inner JSON-escaped payload:

```text
[{"type":"text","text":"<JSON-escaped payload>"}]
```

Two parses to reach a usable object:

```python
import json
with open(path) as f:
    raw = json.loads(f.read())
payload = json.loads(raw[0]["text"])
```

```powershell
$payload = ((Get-Content $path -Raw | ConvertFrom-Json)[0].text) | ConvertFrom-Json
```

### Rules of thumb

1. **Extract, don't echo.** Pull the specific field(s) you need (one `operationId`, one action's outputs) and discard the rest before reasoning about it.
2. **Always pass `actionName` to `get_live_flow_run_action_outputs`.** Omitting it fetches all top-level actions. For actions inside a foreach, passing `actionName` without `iterationIndex` can return every repetition of that action.
3. **Reuse the spill file within a session.** Refetching the same connector swagger costs 30+ seconds and produces another spill — cache the path.
4. **Don't grep the spill file for JSON keys directly.** Strings are JSON-escaped inside the file (`\"OperationId\":`), so a plain grep for `"OperationId":` will not match. Parse first, then filter.
5. **Summarize tool output to the user.** Echo `name + state + trigger` for flow lists and `actionName + status + code` for run errors — not raw JSON, unless asked.

```python
# Good — drill into one operation in a connector swagger
conn = mcp("describe_live_connector", {"environmentName": ENV, "connectorName": "shared_sharepointonline"})
op = conn["properties"]["swagger"]["paths"]["/datasets/{dataset}/tables/{table}/items"]["get"]
print(op["operationId"], "—", op.get("summary"))

# Bad — keeping the whole 500 KB swagger in context
print(json.dumps(conn, indent=2))   # don't do this
```

---

## Auth & Connection Notes

| Field | Value |
|---|---|
| Auth header | `x-api-key: <JWT>` — **not** `Authorization: Bearer` |
| Token format | Plain JWT — do not strip, alter, or prefix it |
| Timeout | Use ≥ 120 s for `get_live_flow_run_action_outputs` (large outputs) |
| Environment name | `Default-<tenant-guid>` (find it via `list_live_environments` or `list_live_flows` response) |

---

## Reference Files

- [MCP-BOOTSTRAP.md](references/MCP-BOOTSTRAP.md) — endpoint, auth, request/response format (read this first)
- [tool-reference.md](references/tool-reference.md) — response shapes and behavioral notes (parameters are in `tool_search`)
- [action-types.md](references/action-types.md) — Power Automate action type patterns
- [connection-references.md](references/connection-references.md) — connector reference guide
