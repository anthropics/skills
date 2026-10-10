# Mock connectors — design now, wire later

When the founder wants a connector (Slack, email, an issue tracker, their own backend, a brokerage) that can't be wired in this session — credential not on hand, OAuth too slow, or they just want to keep moving — don't drop the capability and don't pretend it exists. **Mock it, visibly**, so v0 already behaves as if the connector were there and the later version is a swap, not a redesign.

## Two mock styles

**1. Outbox mock — the default; works unattended and on deployments.**
The agent writes each would-be action as a JSON file to `/mnt/session/outputs/outbox/<seq>-<action>.json`, using the same payload shape the real call would take (schemas below). One line in the system prompt: *"You cannot send/post X directly yet. For each action you would take, write the exact payload to the outbox instead."* Add a rubric criterion that every outbox payload is complete and matches the schema. The founder can read the outbox like a queue of "what it would have done."
Swap to real (v1): add the MCP server to `mcp_servers` + a vault credential + an `always_ask` gate, remove the outbox instruction. The payloads the agent already produces map 1:1 onto the real tool's arguments.

**2. Custom-tool mock — when the founder wants to feel the interaction live.**
Define a `custom` tool on the agent with a realistic `input_schema` (below). The agent's calls surface as `requires_action`; answer them in-session with a stubbed `user.custom_tool_result` (e.g. `{"ok": true, "id": "mock_123"}`). Good for shaping tool-call behaviour while the founder watches; **not** suitable for unattended schedules — every call blocks until something answers it. Swap to real: replace the custom tool with the real `mcp_toolset` entry.

Either way: tell the founder which mock you used and why, and write the swap-to-real route into NEXT-DIRECTIONS (which MCP server, which vault credential type, which gate).

## Typical endpoint schemas

Use these as the outbox payload shape and/or the custom tool `input_schema`. Trimmed to the fields that matter; extend per the founder's real system.

```jsonc
// slack.post_message
{"type":"object","required":["channel","text"],"properties":{
  "channel":{"type":"string","description":"Channel name or ID"},
  "text":{"type":"string","description":"Message body (markdown)"},
  "thread_ts":{"type":"string","description":"Optional thread to reply in"}}}

// email.create_draft / email.send
{"type":"object","required":["to","subject","body_markdown"],"properties":{
  "to":{"type":"array","items":{"type":"string"}},
  "cc":{"type":"array","items":{"type":"string"}},
  "subject":{"type":"string"},
  "body_markdown":{"type":"string"},
  "attachments":{"type":"array","items":{"type":"string"},"description":"Paths under /mnt/session/outputs/"}}}

// issue.create  (Linear / Jira / GitHub Issues)
{"type":"object","required":["title","description_markdown"],"properties":{
  "title":{"type":"string"},
  "description_markdown":{"type":"string"},
  "labels":{"type":"array","items":{"type":"string"}},
  "assignee":{"type":"string"},
  "priority":{"type":"string","enum":["urgent","high","medium","low"]}}}

// webhook.post  (the founder's own backend)
{"type":"object","required":["url","json_body"],"properties":{
  "url":{"type":"string"},
  "method":{"type":"string","enum":["POST","PUT","PATCH"],"default":"POST"},
  "headers":{"type":"object","additionalProperties":{"type":"string"}},
  "json_body":{"type":"object"}}}

// calendar.create_event
{"type":"object","required":["title","start_iso","end_iso"],"properties":{
  "title":{"type":"string"},
  "start_iso":{"type":"string","description":"ISO 8601 with timezone"},
  "end_iso":{"type":"string"},
  "attendees":{"type":"array","items":{"type":"string"}},
  "description":{"type":"string"}}}

// crm.create_note
{"type":"object","required":["entity","note_markdown"],"properties":{
  "entity":{"type":"string","description":"Company/contact name or CRM ID"},
  "note_markdown":{"type":"string"}}}

// broker.place_order  (mock / paper only — real execution is always a gated later version)
{"type":"object","required":["ticker","side","quantity","order_type"],"properties":{
  "ticker":{"type":"string"},
  "side":{"type":"string","enum":["buy","sell"]},
  "quantity":{"type":"number"},
  "order_type":{"type":"string","enum":["market","limit"]},
  "limit_price":{"type":"number"},
  "time_in_force":{"type":"string","enum":["day","gtc"],"default":"day"}}}
```
