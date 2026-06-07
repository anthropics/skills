# Managed Agents — Onboarding Flow

> **Invoked via `/claude-api managed-agents-onboard`?** You're in the right place. Run the interview below — don't summarize it back to the user, ask the questions.

Use this when a user wants to set up a Managed Agent from scratch: **branch on know-vs-explore → configure the template → set up the session → pre-flight viability check → emit working code.** The pre-flight check (§3) is not optional — a setup missing a tool, credential, or data access it needs will fail mid-run, and the gap is usually visible at setup time.

> Read `shared/managed-agents-core.md` alongside this — it has full detail for each knob. This doc is the interview script, not the reference.

---

Claude Managed Agents is a hosted agent: Anthropic runs the agent loop on its orchestration layer and provisions a sandboxed container per session where the agent's tools execute (or, with a `self_hosted` environment, your own worker runs the tools — see `shared/managed-agents-self-hosted-sandboxes.md`). You supply the agent config and the environment config; the harness — event stream, sandbox orchestration, prompt caching, context compaction, and extended thinking — is handled for you.

**What you supply:**
- **An agent config** — tools, skills, model, system prompt. Reusable and versioned.
- **An environment config** — the sandbox your agent's tools execute in (`cloud`: networking, packages; or `self_hosted`: your own infra). Reusable across agents.

Each run of the agent is a **session**.

---

## 1. Know or explore?

Ask the user:

> Do you already know the agent you want to build, or would you like to explore some common patterns first?

### Explore path — show the patterns

Four shapes, same runtime code path (`sessions.create()` → `sessions.events.send()` → stream). Only the trigger and sink differ.

| Pattern | Trigger | Example |
|---|---|---|
| Event-triggered | Webhook | GitHub PR push → CMA (GitHub tool) → Slack |
| Scheduled | Cron | Daily brief: browser + GitHub + Jira → CMA → Slack |
| Fire-and-forget PR | Human | Slack slash-command → CMA (GitHub tool) → PR passing CI |
| Research + dashboard | Human | Topic → CMA (web search + `frontend-design` skill) → HTML dashboard |

Ask which shape fits, then continue with the Know path using it as the reference.

### Know path — configure template

Three rounds. Batch the questions in each round; don't ask them one at a time.

**Round A — Tools.** Start here; it's the most concrete part. Three types; ask which the user wants (any combination):

| Type | What it is | How to guide |
|---|---|---|
| **Prebuilt Claude Agent tools** (`agent_toolset_20260401`) | Ready-to-use: `bash`, `read`, `write`, `edit`, `glob`, `grep`, `web_fetch`, `web_search`. Enable all at once, or individually via `enabled: true/false`. | Recommend enabling the full toolset. List the 8 tools so the user knows what they're getting. Full detail: `shared/managed-agents-tools.md` → Agent Toolset. |
| **MCP tools** | Third-party integrations (GitHub, Linear, Asana, etc.) via `mcp_toolset`. Credentials live in a vault, not inline. | Ask which services. For each, walk through MCP server URL + vault credentials. Full detail: `shared/managed-agents-tools.md` → MCP Servers + Vaults. |
| **Custom tools** | The user's own app handles these tool calls — agent fires `agent.custom_tool_use`, the app sends a result message back. | Ask for each tool: name, description, input schema. The app code that handles the event is *their* code — don't generate it. Full detail: `shared/managed-agents-tools.md` → Custom Tools. |

**Round B — Skills, files, and repos.** What the agent has on hand when it starts.

*Skills* — two types; both work the same way — Claude auto-uses them when relevant. Max 20 per agent.
- [ ] **Pre-built Agent Skills**: `xlsx`, `docx`, `pptx`, `pdf`. Reference by name.
- [ ] **Custom Skills**: skills uploaded to the user's org via the Skills API. Reference by `skill_id` + optional `version`. If the skill doesn't exist yet, walk the user through `POST /v1/skills` + `POST /v1/skills/{id}/versions` (beta header `skills-2025-10-02`). Full detail: `shared/managed-agents-tools.md` → Skills + Skills API.

*GitHub repositories* — any repos the agent needs on-disk? For each:
- [ ] Repo URL (`https://github.com/org/repo`)
- [ ] `authorization_token` (PAT or GitHub App token scoped to the repo)
- [ ] Optional `mount_path` (defaults to `/workspace/<repo-name>`) and `checkout` (branch or SHA)

Emit as `resources: [{type: "github_repository", url, authorization_token, ...}]`. Full detail: `shared/managed-agents-environments.md` → GitHub Repositories.

> ‼️ **PR creation needs the GitHub MCP server too.** `github_repository` gives filesystem access only — to open PRs, also attach the GitHub MCP server in Round A and credential it via a vault. The workflow is: edit files in the mounted repo → push branch via `bash` → create PR via the MCP `create_pull_request` tool.

*Files* — any local files to seed the session with? For each:
- [ ] Upload via the Files API → persist `file_id`
- [ ] Choose a `mount_path` — absolute, e.g. `/workspace/data.csv` (parents auto-created; files mount read-only)

Emit as `resources: [{type: "file", file_id, mount_path}]`. Max 999 file resources. Agent working directory defaults to `/workspace`. Full detail: `shared/managed-agents-environments.md` → Files API.

**Round C — Identity, success criteria, environment:**
- [ ] Name?
- [ ] Job (one or two sentences — becomes the system prompt)?
- [ ] **What does "done" look like?** Push for concrete, checkable success criteria — not "a good report" but "a CSV with a numeric `price` column per SKU." Explicit criteria give the agent a clear target and let you verify the result; vague ones leave it guessing what "done" means. If they're gradeable, plan to wire an **Outcome** in §2 so the harness grades-and-revises against them. See `shared/managed-agents-outcomes.md`.
- [ ] Networking: unrestricted internet from the container, or lock egress to specific hosts? (If locked, MCP server domains must be in `allowed_hosts` or tools silently fail.)
- [ ] Model? (default `claude-opus-4-8`)

---

## 2. Set up the session

Per-run. Points at the agent + environment, attaches credentials, kicks off.

**Vault credentials** (if the agent declared MCP servers):
- [ ] Existing vault, or create one? (`client.beta.vaults.create()` + `vaults.credentials.create()`)

Credentials are write-only, matched to MCP servers by URL, auto-refreshed. See `shared/managed-agents-tools.md` → Vaults.

**Kickoff — pick one:**
- [ ] **Conversational:** a first `user.message` to the agent.
- [ ] **Outcome-graded** (recommended when §Round C produced checkable criteria): send a `user.define_outcome` with a rubric *instead of* a `user.message` — the harness iterates and grades against the rubric until satisfied. Don't send both. See `shared/managed-agents-outcomes.md`.

Session creation blocks until all resources mount. Open the event stream before sending the kickoff. Stream is SSE; break on `session.status_terminated`, or on `session.status_idle` with a terminal `stop_reason` — i.e. anything except `requires_action`, which fires transiently while the session waits on a tool confirmation or custom-tool result (see `shared/managed-agents-client-patterns.md` Pattern 5). Usage lands on `span.model_request_end`. Agent-written artifacts end up in `/mnt/session/outputs/` — download via `files.list({scope_id: session.id, betas: ["managed-agents-2026-04-01"]})`.

**Console escape hatch.** In the runtime block you emit, print the session's Console URL right after `sessions.create()` so the user can watch it in the UI while iterating: `print(f"Watch in Console: https://platform.claude.com/workspaces/default/sessions/{session.id}")` (swap `default` for the user's workspace slug if they named one).

---

## 3. Pre-flight viability check — reconcile the job against the resources

**Do this before emitting any code.** A common, avoidable failure is an under-resourced run: the ask is clear, but the agent is missing a tool, a credential, data access, or the context to act. The agent discovers the gap a few turns in, flails, and gives up — burning the budget to produce nothing. The gap is usually visible at setup time. Catch it here, not after the session fails.

Walk the stated job clause by clause. For each action the agent must take, confirm a resource covers it — and name the gap out loud if one doesn't:

| Gap class | Check | If missing |
|---|---|---|
| **Tool / integration** (most catchable upfront — config is statically inspectable) | Every verb in the job maps to an enabled tool or MCP server. "Triage tickets" → a ticketing MCP server; "open a PR" → GitHub MCP server (a `github_repository` mount alone can't open PRs); "search the web" → `web_search` enabled in the toolset. | Add the tool/MCP server in §Round A, or cut the ask from the job. |
| **Credential / access** | Every MCP server has a vault credential attached (§2). Every external host the job touches is reachable — networking `unrestricted`, or the host is in `allowed_hosts`. | Create/attach the vault; widen `allowed_hosts`. These don't fail until runtime — the smoke-test in §4 is how you surface them cheaply. |
| **Data** | Every file, dataset, or repo the job references is mounted as a `resource` (file, `github_repository`, or memory store). | Upload + mount it in §Round B, or tell the agent where to fetch it from. |
| **Prompt quality / criteria** | The job is specific enough to act on, and "done" is checkable (§Round C). | Tighten the job; wire an Outcome. |

State any unmet gaps to the user and resolve them before generating code. Don't emit a config you already know is under-resourced — an agent can't complete a task it lacks the tools, credentials, or data for.

---

## 4. Emit the code

Go straight from the last interview answer to the code — no preamble about the setup-vs-runtime split, no "the critical thing to internalize…", no lecture about `agents.create()` being one-time. The two-block structure below already shows that; don't narrate it. Generate **two clearly-separated blocks**:

**Block 1 — Setup (run once, store the IDs).** Prefer emitting this as **YAML files + `ant` CLI commands** — agents and environments are version-controlled definitions, and the CLI flow is what users should check into their repo and run from CI. Fall back to SDK code only if the user explicitly wants setup in-language or the `ant` CLI is unavailable.

Emit:
1. `<name>.agent.yaml` with everything from §Round A–C (flat: `name`, `model`, `system`, `tools`, `mcp_servers`, `skills`)
2. `<name>.environment.yaml` with §Round C networking
3. The apply commands:
   ```sh
   AGENT_ID=$(ant beta:agents create < <name>.agent.yaml --transform id -r)
   ENV_ID=$(ant beta:environments create < <name>.environment.yaml --transform id -r)
   # CI sync: ant beta:agents update --agent-id "$AGENT_ID" --version N < <name>.agent.yaml
   ```

See `shared/anthropic-cli.md` for the full CLI reference. If emitting SDK code instead, label it `# ONE-TIME SETUP — run once, save the IDs to config/.env` and call `environments.create()` → `agents.create()`.

**Block 2 — Runtime (run on every invocation).** This is SDK code in the detected language (Python/TS/cURL — see SKILL.md → Language Detection). The runtime path needs to react programmatically to events (tool confirmations, custom tool results, reconnect), which is SDK territory — don't emit shell loops here.
1. Load `env_id` + `agent_id` from config/env
2. `sessions.create(agent=AGENT_ID, environment_id=ENV_ID, resources=[...], vault_ids=[...])` — this blocks until resources mount, so a bad file/repo mount surfaces *here*, before any tokens are spent.
3. **Smoke-test first when the job depends on MCP servers, credentials, or reachable hosts.** Credential and MCP-connectivity failures don't surface at `sessions.create()` — only when the agent first tries to use them. Send one cheap probe turn ("Confirm you can reach <service> and list 1–2 items; don't start the task yet"), check it succeeded, *then* send the real kickoff. A few hundred tokens here beats a runaway session that flails on a missing credential and gives up. Skip for agents with no external dependencies.
4. Open stream, `events.send()` the kickoff (a `user.message`, or a `user.define_outcome` if §2 chose the outcome-graded path), loop until `session.status_terminated` or `session.status_idle && stop_reason.type !== 'requires_action'` (see `shared/managed-agents-client-patterns.md` Pattern 5 for the full gate — do not break on bare `session.status_idle`)

> ⚠️ **Never emit `agents.create()` and `sessions.create()` in the same unguarded block.** That teaches the user to create a new agent on every run — the #1 anti-pattern. If they need a single script, wrap agent creation in `if not os.getenv("AGENT_ID"):`.

Pull exact syntax from `python/managed-agents/README.md`, `typescript/managed-agents/README.md`, or `curl/managed-agents.md`. Don't invent field names.
