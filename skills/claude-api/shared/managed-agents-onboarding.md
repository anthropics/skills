# Managed Agents — Onboarding Flow

> **Invoked via `/claude-api managed-agents-onboard`?** You're in the right place. Run the interview below — don't summarize it back to the user, ask the questions.

Claude Managed Agents is a hosted agent: Anthropic runs the agent loop and provisions a sandboxed container per session where the agent's tools execute (or your own worker, with a `self_hosted` environment — see `shared/managed-agents-self-hosted-sandboxes.md`). You supply an **agent config** (tools, skills, model, system prompt — reusable, versioned) and an **environment config** (the sandbox — reusable across agents). Each run is a **session**.

The flow is four beats — **describe → agent → environment → session** — the same arc as the Console quickstart, and the same philosophy: **value before credentials**. The user goes from idea to a runnable session before any auth ask; each credential is *flagged* at the moment the design makes it relevant (§2) and *collected* once, at session setup (§4), where it binds (`sessions.create()`) and gets exercised (smoke-test). Read `shared/managed-agents-core.md` alongside this — it has full detail for each knob; this doc is the interview script.

---

## 1. Describe the task

**Open with a one-breath signpost and a single open prompt — don't guess, don't questionnaire.** In your own words:

> Managed Agents is hosted — Anthropic runs the agent loop, the sandbox, and the infrastructure; you just define the agent. We'll do this in three moves: the agent, the environment it runs in, then a live test session. So: describe the agent you want — what should it do, and what kicks it off (a person, an event, a schedule)?

Let them answer in full before configuring anything.

## 2. Configure the agent — propose, don't interrogate

Their description does the interview's work. Draft the agent config from it and **present it as a proposal with your suggestions inline** — the user reacts to a concrete config instead of answering a question list. At most one batched follow-up for true gaps. Suggest where the description gives you an opening:

- **Tools** — enable the full prebuilt toolset by default (`agent_toolset_20260401`: `bash`, `read`, `write`, `edit`, `glob`, `grep`, `web_fetch`, `web_search`). **Suggest MCP servers** for any third-party service the job names (GitHub, Linear, Slack, …) — and flag the credential each one implies as you suggest it ("Linear MCP → you'll need a Linear API token at kickoff"), so §4's auth step is a formality, not a surprise. Collection itself waits for §4. Custom tools only if the user's own app must answer calls (name, description, input schema — their handler code is theirs; don't generate it).
- **Skills** — **suggest** prebuilt `xlsx`/`docx`/`pptx`/`pdf` when the job produces those artifacts; custom by `skill_id` (max 20 total per agent, prebuilt + custom combined).
- **Outcome** — if the description implies checkable "done" criteria (or you can elicit them in the follow-up: not "a good report" but "a CSV with a numeric `price` column per SKU"), **suggest an Outcome kickoff** — the harness grades and iterates against a rubric (`shared/managed-agents-outcomes.md`).
- **On-hand resources** — repos on disk (`github_repository`: URL, optional `mount_path`/`checkout`; token comes in §4), files to seed (Files API upload → `{type: "file", file_id, mount_path}`; read-only), if the job references them.
- **Model** — default `claude-opus-4-8`; `claude-fable-5` for the hardest long-horizon work (`shared/model-migration.md` → Migrating to Claude Fable 5).

> ‼️ **PR creation needs the GitHub MCP server too** — a `github_repository` mount is filesystem-only. Edit in the mount → push branch via `bash` → open the PR via the MCP `create_pull_request` tool.

Full detail per knob: `shared/managed-agents-tools.md` (toolset, MCP, custom tools, skills), `shared/managed-agents-environments.md` (repos, files).

## 3. Environment

Usually zero or one question:

- **Reuse or create?** Environments are shared across agents — check for an existing one first.
- **Networking** — default unrestricted egress. Switch to `limited` only if the user wants egress control — then set `allow_mcp_servers: true` or list every MCP server domain in `allowed_hosts`, or those tools fail silently.
- **Suggest `self_hosted`** when the signals are there: tools must run on their own infra, secrets can't leave it, or they need binaries/data the cloud container won't have (`shared/managed-agents-self-hosted-sandboxes.md`; not available on Claude Platform on AWS). Otherwise `cloud` — don't raise it unprompted for simple jobs.

## 4. Session — auth, then test run

**Auth happens here — collect the credentials flagged in §2, now that the config is settled:** a vault (existing or `vaults.create()`) + `vaults.credentials.create()` for each MCP server declared in §2, `environment_variable` credentials for API keys the job uses (substituted at egress; the sandbox sees a placeholder), and the `authorization_token` for each repo mount. Credentials are write-only; MCP credentials match servers by URL and auto-refresh. See `shared/managed-agents-tools.md` → Vaults.

**Silent viability gate — run this yourself before emitting anything; surface only the gaps.** Walk the job clause by clause: every verb maps to an enabled tool or MCP server ("open a PR" → GitHub MCP, not just the mount); every MCP server and repo mount has its credential from the auth step; every external host is reachable under the networking choice; every file/repo/dataset the job references is mounted; "done" is checkable. If something's missing, say so and resolve it — don't emit a config you already know is under-resourced.

**Kickoff — pick one, never both:**
- `user.message` — conversational.
- `user.define_outcome` + rubric — when §2 settled on an Outcome; the harness iterates and grades until the rubric passes.
- **Scheduled shape?** Skip per-session kickoff entirely — create a **deployment** (`deployments.create()` with `schedule` + `initial_events`); each firing creates the session autonomously. See `shared/managed-agents-scheduled-deployments.md`.

Mechanics to bake into the runtime code: session creation blocks until resources mount (bad mounts surface there, before tokens); open the event stream *before* sending the kickoff; break on `session.status_terminated`, or `session.status_idle` with a terminal `stop_reason` — anything except `requires_action` (`shared/managed-agents-client-patterns.md` Pattern 5); usage lands on `span.model_request_end`; artifacts land in `/mnt/session/outputs/` (`files.list({scope_id: session.id, ...})`).

## 5. Integrate — emit the code

Go straight from the last answer to the code — no preamble, no lecture about setup-vs-runtime; the two-block structure shows it. Generate **two clearly-separated blocks**:

**Block 1 — Setup (run once, store the IDs).** Prefer **YAML files + `ant` CLI** — agents and environments are version-controlled definitions users should check in and apply from CI:

1. `<name>.agent.yaml` (flat: `name`, `model`, `system`, `tools`, `mcp_servers`, `skills`) and `<name>.environment.yaml`
2. ```sh
   AGENT_ID=$(ant beta:agents create < <name>.agent.yaml --transform id -r)
   ENV_ID=$(ant beta:environments create < <name>.environment.yaml --transform id -r)
   # CI sync: ant beta:agents update --agent-id "$AGENT_ID" --version N < <name>.agent.yaml
   ```

SDK fallback if the user asks — and **required on Claude Platform on AWS**, where auth is SigV4 and the `ant` CLI has no SigV4 mode (use the platform client from `shared/claude-platform-on-aws.md`): label it `# ONE-TIME SETUP — run once, save the IDs` and call `environments.create()` → `agents.create()`.

> ⚠️ **Deployments are newer than the rest of the MA surface.** Before emitting `ant beta:deployments …` or `client.beta.deployments` / `client.beta.deployment_runs` calls, verify the user's installed CLI/SDK exposes them (`ant beta:deployments --help`; `hasattr(client.beta, "deployments")`). If not, emit raw HTTP against `POST /v1/deployments` with the `managed-agents-2026-04-01` beta header (plus `oauth-2025-04-20` when authenticating with a Bearer token from `ant auth print-credentials`), and leave an upgrade note marking what simplifies to SDK calls.

**Scheduled shape? The deployment is setup, not runtime.** Create it in Block 1, after the agent/environment IDs exist (`deployments.create()` with `schedule` + `initial_events`). Block 2 is then **not** a session loop — there is no per-run kickoff to send. Emit instead: a manual-run trigger (`POST /v1/deployments/{id}/run`) so the user can test now rather than wait for the first firing — the manual run doubles as the smoke test — plus a fetch helper (latest `deployment_runs` entry → `session_id` → Console URL + `files.list(scope_id=session_id)` for the artifacts).

**Block 2 — Runtime (every invocation; conversational and Outcome shapes).** SDK code in the detected language (Python/TS/cURL — SKILL.md → Language Detection); don't emit shell loops here:

1. Load `agent_id` + `env_id` from config/env
2. `sessions.create(agent=AGENT_ID, environment_id=ENV_ID, resources=[...], vault_ids=[...])`, then print the Console URL so the user can watch live: `https://platform.claude.com/workspaces/default/sessions/{session.id}` (swap `default` for their workspace slug)
3. **Smoke-test when the job depends on MCP servers, credentials, or locked-down hosts** — those failures don't surface at `sessions.create()`, only on first use. One cheap probe turn ("Confirm you can reach <service> and list 1–2 items; don't start the task"), verify, then send the real kickoff. Skip when there are no external dependencies.
4. Open stream → send the §4 kickoff → loop with the terminal gate from §4.

> ⚠️ **Never emit `agents.create()` and `sessions.create()` in the same unguarded block** — that teaches creating a new agent per run, the #1 anti-pattern. Single-script requests: wrap creation in `if not os.getenv("AGENT_ID"):`.

Pull exact syntax from `{lang}/managed-agents/README.md` for your detected language (cURL and C#: use `curl/managed-agents.md` as the wire-level reference). Don't invent field names.
