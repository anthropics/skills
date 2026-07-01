# CMA API — verified command shapes

> Source: platform.claude.com/docs/en/managed-agents/* (read 2026-06-14). If a call fails on a field name, the **live docs win** — check, adapt, retry once.
> Two equivalent surfaces: `ant` CLI (`brew install anthropics/tap/ant`) and curl. The Python/TS SDKs mirror these exactly (`client.beta.<resource>.<verb>`).

## Setup (every terminal)

The key lives in `./my-agent/.env` (chmod 600, in `.gitignore`) — never pasted into the chat, echoed, or inlined into a command (it would land in the transcript / shell history). Easiest flow: check whether `ANTHROPIC_API_KEY` is already set in the shell env (skip the ask entirely if so — copy it into `.env` without printing it); otherwise pre-create `.env` with a placeholder, chmod 600 it, and have the founder paste the key into the file via its **absolute path** (their terminal's cwd isn't yours). If a key ever does end up in chat or an exported transcript, tell the founder to rotate it.

```bash
set -a; source .env; set +a      # ANTHROPIC_API_KEY=sk-ant-...  (founder-created at platform.claude.com → API keys)
BASE=https://api.anthropic.com/v1
H=(-H "x-api-key: $ANTHROPIC_API_KEY" -H "anthropic-version: 2023-06-01" \
   -H "anthropic-beta: managed-agents-2026-04-01" -H "content-type: application/json")
```

When the founder creates the key, have them note **which workspace it belongs to** — every object created with it lands in that workspace, and the Console only shows the workspace currently selected (this is the answer to "I can't see it in the Console").

Save every returned id into `IDS.env` immediately (`echo "AGENT_ID=..." >> IDS.env`); load it with `set -a; source IDS.env; set +a` so child processes (python parsers, scripts) see the variables, and make every launch step read `IDS.env` first and skip objects that already exist, so a failed step can be re-run without creating duplicates. Pattern for readable errors: `-o /tmp/resp.json -w '%{http_code}\n'`. **Parse responses with python, not jq** — session payloads embed the agent's `system` prompt with literal newlines/control characters that jq rejects:

```bash
python3 -c "import json,sys; d=json.JSONDecoder(strict=False).decode(open('/tmp/resp.json').read()); print(d['id'])"
```

## Pick a model

```bash
curl -sS "$BASE/models" "${H[@]:0:4}" | jq -r '.data[].id'
```
Default: newest Opus-class. Sonnet-class only if the founder explicitly wants cheaper/faster runs. Fast mode: pass model as `{"id":"claude-opus-4-8","speed":"fast"}`.

## 1. Agent (versioned; create once)

```bash
# curl
curl -sS --fail-with-body "$BASE/agents" "${H[@]}" -d @agent.json
# ant
ant beta:agents create --name "..." --model '{id: claude-opus-4-8}' \
  --system "..." --tool '{type: agent_toolset_20260401}'
```
`agent.json` fields: `name`*, `model`*, `system`, `tools`, `mcp_servers`, `skills`, `multiagent`, `description`, `metadata`.
Response: save `id` AND `version` (starts at 1).

**Update** (new version; pass current version as concurrency guard; arrays are FULL replacement, omitted fields preserved):
```bash
curl -sS --fail-with-body "$BASE/agents/$AGENT_ID" "${H[@]}" \
  -d '{"version": '$AGENT_VERSION', "system": "...new instructions..."}'
ant beta:agents update --agent-id "$AGENT_ID" --version "$AGENT_VERSION" --system "..."
```
Then bump `AGENT_VERSION` in IDS.env to the returned version.
Versions list: `GET $BASE/agents/$AGENT_ID/versions` · Archive: `POST $BASE/agents/$AGENT_ID/archive`.

### Tool config patterns

```jsonc
"tools": [
  {"type": "agent_toolset_20260401"},                                  // all 8 tools, always_allow
  {"type": "agent_toolset_20260401",                                   // gate bash behind approval
   "default_config": {"permission_policy": {"type": "always_allow"}},
   "configs": [{"name": "bash", "permission_policy": {"type": "always_ask"}}]},
  {"type": "mcp_toolset", "mcp_server_name": "linear",                 // MCP tools (default always_ask)
   "default_config": {"permission_policy": {"type": "always_allow"}}},
  {"type": "custom", "name": "get_weather", "description": "...",      // client-executed
   "input_schema": {"type": "object", "properties": {...}, "required": [...]}}
]
"mcp_servers": [{"type": "url", "name": "linear", "url": "https://mcp.linear.app/sse"}]
"skills": [{"type": "anthropic", "skill_id": "xlsx"},                  // xlsx | docx | pptx | pdf
           {"type": "custom", "skill_id": "skill_abc123", "version": "latest"}]
"multiagent": {"type": "coordinator", "agents": [{"type": "agent", "id": "agent_..."}]}
```
Built-in tool names: `bash read write edit glob grep web_fetch web_search`. Disable one: `configs:[{"name":"web_fetch","enabled":false}]`.

## 2. Environment (reusable; not versioned)

```bash
curl -sS --fail-with-body "$BASE/environments" "${H[@]}" -d '{
  "name": "<name>-env",
  "config": {"type": "cloud", "networking": {"type": "unrestricted"},
             "packages": {"pip": ["pandas"], "npm": []}}}'
ant beta:environments create --name "<name>-env" --config '{type: cloud, networking: {type: unrestricted}}'
```
Limited networking: `{"type":"limited","allowed_hosts":["api.example.com","*.example.com"],"allow_mcp_servers":true,"allow_package_managers":true}` (booleans default false; hostnames only, no scheme).
Package managers: `apt cargo gem go npm pip` (cached across sessions). Names unique per workspace.
List/retrieve/archive/delete: standard verbs on `$BASE/environments[/:id][/archive]` (delete only if no sessions reference it).

## 3. Session (one run; sandbox provisioned at create, work starts on first event)

```bash
curl -sS --fail-with-body "$BASE/sessions" "${H[@]}" -d '{
  "agent": "'$AGENT_ID'",                         // string = latest version
  "environment_id": "'$ENV_ID'",
  "title": "first run",
  "vault_ids": [],                                 // optional
  "resources": []                                  // optional: memory_store / file / repository
}'
ant beta:sessions create --agent "$AGENT_ID" --environment-id "$ENV_ID" --title "first run"
```
Pin a version: `"agent": {"type":"agent","id":"...","version":1}`.
Attach memory: `"resources":[{"type":"memory_store","memory_store_id":"memstore_...","access":"read_write","instructions":"..."}]` (creation-time only).

Statuses: `idle` (waiting — sessions start here) · `running` · `rescheduling` · `terminated`.
Retrieve: `GET $BASE/sessions/$SESSION_ID` (read `.status`, `.usage`, `.outcome_evaluations[]`).
List: `GET $BASE/sessions?agent_id=$AGENT_ID` · Archive: `POST .../archive` (not while running — interrupt first) · Delete: `DELETE $BASE/sessions/$SESSION_ID`.
Mid-session you can update a session's `agent.tools`/`agent.mcp_servers` (session-local, full replacement, must be idle): `POST $BASE/sessions/$SESSION_ID` with `{"agent":{"tools":[...],"mcp_servers":[...]}}`.

## 4. Kickoff events

**Outcome kickoff (default)** — task + definition of done + retry budget in one move; agent starts immediately:
```bash
EVT=$(jq -n --rawfile task first_prompt.txt --rawfile rubric outcome.md \
  '{type:"user.define_outcome", description:$task,
    rubric:{type:"text", content:$rubric}, max_iterations:3}')      # default 3, max 20
curl -sS --fail-with-body "$BASE/sessions/$SESSION_ID/events" "${H[@]}" -d "{\"events\":[$EVT]}"
ant beta:sessions:events send --session-id "$SESSION_ID" <<YAML
events:
  - type: user.define_outcome
    description: <task>
    rubric: {type: text, content: "<rubric markdown>"}
    max_iterations: 3
YAML
```
File rubric instead: `"rubric":{"type":"file","file_id":"file_..."}` (upload needs extra header `files-api-2025-04-14`).

**Plain message kickoff / steering / resume** (steering mid-run is allowed; agent picks it up at the next turn boundary):
```bash
curl -sS --fail-with-body "$BASE/sessions/$SESSION_ID/events" "${H[@]}" \
  -d '{"events":[{"type":"user.message","content":[{"type":"text","text":"..."}]}]}'
```

**Interrupt + redirect:** send `{"type":"user.interrupt"}` then a `user.message` in the same `events` array.
**Tool confirmation** (when status_idle has `stop_reason.type == "requires_action"`):
`{"type":"user.tool_confirmation","tool_use_id":"<event id>","result":"allow"|"deny","deny_message":"..."}`.
**Custom tool result:** `{"type":"user.custom_tool_result","custom_tool_use_id":"<id>","content":[{"type":"text","text":"..."}]}`.

## 5. Watch the run

```bash
# SSE stream — open BEFORE sending events; only post-open events are delivered. -N = don't buffer.
curl -sS -N --fail-with-body "$BASE/sessions/$SESSION_ID/events/stream" "${H[@]}" -H "accept: text/event-stream"
# Poll instead (python, NOT jq — the embedded system prompt breaks jq):
curl -sS "$BASE/sessions/$SESSION_ID" "${H[@]}" -o /tmp/sess.json
python3 -c "import json; d=json.JSONDecoder(strict=False).decode(open('/tmp/sess.json').read()); print(d['status'], [e.get('result') for e in d.get('outcome_evaluations',[])])"
# Full history (filterable): GET $BASE/sessions/$SESSION_ID/events?types[]=agent.tool_use
```
Run the first poll in the foreground and confirm it parses before putting the loop in a background task — a poller that errors silently every iteration looks like "still running" for ten minutes.
Narrate: `agent.message` (text), `agent.tool_use` (name), `span.outcome_evaluation_end` (`result` + `explanation`), `session.status_idle` (`stop_reason`: `end_turn` = done, `requires_action` = answer it), `session.error`.
Outcome results: `satisfied` · `needs_revision` · `max_iterations_reached` · `failed` · `interrupted`.
Runs of 8–10+ minutes are normal — say so. Also hand the founder the Console sessions view for the key's workspace so they can watch it there.

## 6. Outputs

Agent writes to `/mnt/session/outputs/`. Fetch:
```bash
curl -sS "$BASE/files?scope_id=$SESSION_ID" "${H[@]}" | jq -r '.data[] | "\(.id) \(.filename)"'
curl -sS "$BASE/files/$FILE_ID/content" "${H[@]}" -o output.md
ant beta:files list --scope-id "$SESSION_ID" ; ant beta:files download --file-id "$FILE_ID" --output output.md
```

## 7. Memory store (optional)

```bash
curl -sS "$BASE/memory_stores" "${H[@]}" -d '{"name":"<name>-memory","description":"<what it holds — shown to the agent>"}'
# seed: POST $BASE/memory_stores/$MEMSTORE_ID/memories  {"path":"/context.md","content":"..."}
# attach: session/deployment "resources" array (see §3). Mounted at /mnt/memory/.
```
Limits: 100kB/memory, 2,000 memories/store, 8 stores/session. Use `read_only` for reference material.

## 8. Vault + credential (optional; only when a credential is in hand)

```bash
VAULT_ID=$(curl -sS "$BASE/vaults" "${H[@]}" -d '{"display_name":"<founder name>"}' | jq -r .id)
# MCP bearer:   {"display_name":"Linear key","auth":{"type":"static_bearer","mcp_server_url":"https://mcp.linear.app/mcp","token":"..."}}
# MCP OAuth:    {"auth":{"type":"mcp_oauth","mcp_server_url":"...","access_token":"...","expires_at":"...","refresh":{...}}}
# Env var:      {"auth":{"type":"environment_variable","secret_name":"NOTION_API_KEY","secret_value":"...",
#                "networking":{"type":"limited","allowed_hosts":["api.notion.com"]}}}
curl -sS "$BASE/vaults/$VAULT_ID/credentials" "${H[@]}" -d @cred.json
# use: pass "vault_ids": ["'$VAULT_ID'"] at session/deployment creation
```
Secrets are write-only. Credential `mcp_server_url` must match the agent's `mcp_servers[].url` exactly (scheme + trailing slash).

## 9. Scheduled deployment (the "runs without you" finale)

```bash
curl -sS --fail-with-body "$BASE/deployments?beta=true" "${H[@]}" -d '{
  "name": "<human name>",
  "agent": "'$AGENT_ID'",
  "environment_id": "'$ENV_ID'",
  "initial_events": [ <the same kickoff event(s) as §4> ],
  "schedule": {"type": "cron", "expression": "0 7 * * 1", "timezone": "America/Los_Angeles"}
}'
ant beta:deployments create <<YAML ... YAML
```
**`initial_events` are replayed verbatim every run** — the kickoff text must use relative dates ("today", "the last N days as of this run"), never a literal date; re-read it for hard-coded dates before sending.
Response includes `schedule.upcoming_runs_at` — read it back to the founder to confirm.
Optional on the same body: `vault_ids`, memory/file/GitHub `resources`.
**Test now:** `curl -X POST -d '{}' "$BASE/deployments/$DEPLOYMENT_ID/run?beta=true" "${H[@]}"` (manual run, creates a session immediately — the explicit `-X POST` matters; a bodyless curl defaults to GET and 405s).
Runs history: `GET $BASE/deployment_runs?deployment_id=...&has_error=true`.
Pause / unpause / archive: `POST $BASE/deployments/$DEPLOYMENT_ID/{pause|unpause|archive}?beta=true`.
Cron = 5-field POSIX, minute granularity, IANA timezone, wall-clock DST. Limit 1,000/org.

## Cost & cleanup

- Session `usage` (input/output/cache tokens) on `GET /sessions/:id` — read it after each run.
- Rate limits: creates 300/min, reads 600/min per org.
- End of session hygiene: archive sessions you're done with; never leave one `running`.

## Console links (paste these proactively whenever something is ready to review)

Deep links work — link the specific object that just became reviewable, not only the list page:

- Agent: `https://platform.claude.com/workspaces/<workspace>/agents/<AGENT_ID>` (confirmed in use)
- Deployments list (+ cron builder): `https://platform.claude.com/workspaces/<workspace>/deployments` (documented); a created deployment: `…/deployments/<DEPLOYMENT_ID>` (same pattern — confirm on first click)
- Session: `…/workspaces/<workspace>/sessions/<SESSION_ID>` (same pattern — confirm on first click; fall back to the sessions list if it 404s)

The `<workspace>` segment: use `default` until known — it resolves when the key lives in the default workspace; otherwise add a one-time "switch workspaces with the picker (Settings → API Keys shows which workspace the key belongs to)". Once the founder pastes any Console URL, lift the workspace ID from it and use it in every link after.

## Troubleshooting quick hits

- **401/403** → key not in `.env` / typo'd / billing issue. Fix `.env`, re-`source`, retry once.
- **400 on agent create ("tools")** → built-in tools were listed individually. Use the toolset wrapper: `"tools": [{"type": "agent_toolset_20260401"}]` (with `configs` overrides if needed) — never `{"type":"bash"}` etc.
- **404 on a path** → check the live docs for the exact resource path before assuming the feature doesn't exist (e.g. deployments live at `/v1/deployments`, docs page is `scheduled-deployments`).
- **405 on deployment manual run** → the curl defaulted to GET; use an explicit `-X POST` with a `{}` body.
- **jq: "control characters … not allowed"** → the response embeds the agent `system` prompt with literal newlines. Parse with `python3` + `json.JSONDecoder(strict=False)` instead of jq.
- **Stream looks hung** → you forgot `-N`, or the run is just long (8–10 min is normal). Poll `.status` instead.
- **`requires_action`** → the agent is waiting on YOU: a tool confirmation or a custom tool result. Read the last events and answer.
- **"I can't see it in the Console"** → the Console only shows the currently selected workspace; the objects live in the workspace the API key belongs to. Settings → API Keys → find the key → switch to that workspace → Claude Managed Agents.
- **Vault MCP auth fails** → credential `mcp_server_url` doesn't exactly match the agent's `mcp_servers[].url`.
- **Update rejected (version conflict)** → re-fetch the agent, retry with the current `version`.
