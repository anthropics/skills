# Founder interview → Claude Managed Agent config

> How the skill turns a short, iterative interview with a technical founder into a concrete, launchable CMA configuration.
> Companion to `cma-primitives.md` (the inventory of what we can configure).

## The shape of the thing

The interview is not a form — it's a **mapping exercise**. Every answer locks in one or more primitive decisions. The output is a **build sheet** (`build-sheet.json` + human-readable files) that fully determines:

| Decision | Primitive(s) |
|---|---|
| Who the agent is, what it does, what it must never do | Agent: `name`, `system`, `model` |
| What "done" looks like | Outcome: `description`, rubric, `max_iterations` |
| What it needs to read/know | Tools (web), Files, GitHub resource, MCP servers + Vault creds, Memory store |
| What it produces and where | Skills (xlsx/docx/pptx/pdf), output conventions, custom tools |
| When it runs | Session (on-demand) vs Scheduled deployment (cron) vs their-app-triggered |
| What software the task needs | Environment: `packages`, runtime |
| What it's allowed to touch | Permission policies, networking allowlist, `read_only` memory |
| One worker or several | Single agent vs multiagent coordinator + roster |
| Whether it gets smarter | Memory store(s) + (later) Dreams |
| Who interacts with it, and how | Their interface: terminal / internal dashboard / their product (→ vault-per-user pattern) |

**Start from the defaults, build what the job needs.** The interview's job is to find what the founder's v0 actually requires beyond the starting point — not to ask about every primitive, and not to gatekeep the ones the job genuinely needs.

## How CMA's architecture maps onto our constructs

Anthropic's own framing of the architecture (from the engineering blog) is **brain / hands / session**: the *brain* is the model + harness (system prompt, decision logic, tool routing), the *hands* are the sandboxed execution environment, and the *session* is the persistent event log of everything that happened. Our constructs sit on top of that one-to-one:

- **Brain** ↔ what the interview's Q1/Q4/Q6/Q8 produce → `agent.json` → the **Agent**, **Tools**, **Skills** cards.
- **Hands** ↔ Q3 (packages) + Q6 (networking) → `environment.json` → the **Environment** card.
- **Session** ↔ each run; Q5 decides who starts it (the founder, a cron, or their app) → `LAUNCH.md` / `deployment.json` → the **Deployment** card + the header's Planned/Launched status.
- The thing CMA adds beyond brain/hands/session — the **Outcome grader** — is what our Q2/Q2b feed, and it's why the build kit treats `outcome.md` + `evals/` as first-class files rather than prompt text.

### Primitive-by-primitive map

| CMA primitive | Decided by | Lands in the build kit as | Card on agent-overview.html | API call at launch | Official example to lift from |
|---|---|---|---|---|---|
| **Agent** (name, model, system) | Q1 job, Q6 behavioral never-dos, Q8 model/budget | `agent.json` / `agent.yaml` | Agent | `POST /v1/agents` (versioned; updates = new version) | Quickstart "Coding Assistant" |
| **Tools + permission policies** | Q3 inputs, Q4 outputs, Q6 approvals | `tools[]` in agent.json | Tools | part of agent create | Tools + Permission-policies docs |
| **Skills** (xlsx/docx/pptx/pdf, custom) | Q4 outputs | `skills[]` in agent.json | Skills | part of agent create | Skills docs "Financial Analyst" |
| **MCP servers + Vaults** | Q3 inputs behind logins, Q8 per-user pattern | `mcp_servers[]` + vault setup in LAUNCH.md | Connectors & vaults | `POST /v1/vaults` + `/credentials`; `vault_ids` at session/deployment | CMA_operate_in_production; Vaults docs "Alice" |
| **Custom tools** | Q4 "trigger something in *their* product" | `tools[]` (`type: custom`) + a note in their interface plan | Tools | part of agent create; results via `user.custom_tool_result` | CMA_gate_human_in_the_loop |
| **Multiagent** (coordinator + roster) | Q8 shape | `multiagent` in agent.json (only when earned) | Agent (roster note) | part of agent create | CMA_coordinate_specialist_team |
| **Environment** (packages, networking) | Q3 heavy inputs, Q6 hardening | `environment.json` | Environment | `POST /v1/environments` | Environments docs "data-analysis" |
| **Session** | Q5 = on-demand; also every eval run | `LAUNCH.md`, IDs in `IDS.env` | header status | `POST /v1/sessions` | Quickstart |
| **Events** (kickoff, steering, interrupts, confirmations) | Q2 (kickoff content), Q6 (confirmations) | `kickoff.json`, watch section of LAUNCH.md | — (live view stays in Console) | `POST /sessions/:id/events`, SSE stream | Events-and-streaming docs |
| **Outcome** (rubric + grader + iteration bound) | Q2 done, Q2b evidence | `outcome.md`, `first_prompt.txt`, `kickoff.json` | Outcome | `user.define_outcome` event | CMA_verify_with_outcome_grader; DCF example |
| **Files API** | Q2b eval cases, Q3 on-hand inputs, Q4 output retrieval | `evals/` inputs, output-fetch lines in LAUNCH.md | Evals | `/v1/files` (upload, `?scope_id=` list, download) | Outcomes docs "Retrieving deliverables" |
| **Memory stores** | Q7 learning | memory section of build sheet; seed calls in LAUNCH.md | Memory store | `POST /v1/memory_stores` + session `resources[]` | CMA_remember_user_preferences |
| **Scheduled deployment** | Q5 = recurring | `deployment.json` | Deployment | `POST /v1/deployments` (+ manual `/run` test) | Scheduled-deployments docs "weekly compliance scan" |
| **Webhooks** | Q5 = event-driven, or unattended monitoring | NEXT-DIRECTIONS entry (their backend subscribes) | Next directions | — | CMA_operate_in_production |
| **Dreams** | Q7 when memory will grow messy | NEXT-DIRECTIONS entry | Next directions | — | Dreams docs |
| **Self-hosted sandbox** | Q6 compliance/residency | NEXT-DIRECTIONS entry | Next directions | — | Self-hosted-sandboxes docs |

Reading the table by column: the **interview** column is where the decision gets made, the **build kit** column is the founder's editable copy, the **card** column is how it shows up on the overview page, and the **API** column is what Phase 2 of the skill actually executes. Anything that ends up in the Next-directions column of the page never becomes an API call today — that's the definition of "deferred."

### The starting point (what every build begins from)

- **One agent**, newest Opus-class model, full `agent_toolset_20260401`, `always_allow`
- **One cloud environment**, `unrestricted` networking, no extra packages
- **Outcome kickoff** (`user.define_outcome`), text rubric, `max_iterations: 3`
- Outputs written to `/mnt/session/outputs/`, fetched via Files API

From there, **build what the job needs — scoped into versions, not gatekept by primitive**. Any primitive (MCP connector, vault, memory store, custom tool, document/custom skill, schedule, even multiagent) belongs in v0 if the core job doesn't work without it and it's wireable now (e.g. the credential is on hand). Everything the job wants but doesn't need on the first pass is laid out explicitly as **v1, v2, …** in NEXT-DIRECTIONS — a numbered sequence of planned increments, each with its mechanism — so "not in v0" reads as "scheduled for v1", never "cut".

The standing recommendation (not a rule): v0 is **read/analyze/draft only** — write-actions into external systems (send/post/merge/delete/place orders) usually ship in a later version behind an `always_ask` gate, once the founder trusts the output. If the founder explicitly wants a write-action in v0, wire it gated (`always_ask`, or a sandbox/paper variant) rather than refusing — say what the recommendation is and why, then build what they choose.

---

## The interview

Eight question clusters, run **iteratively** — never as a form. Open light: a couple of warm sentences, 2–3 archetype examples from the examples bank, then Q1 — no boundaries block, no process talk. After their first answer, let them keep explaining (one open follow-up) before any suggestions or option menus; a founder telling their story usually answers 2–4 clusters at once, so only ask what's still open. Whenever the answer space is enumerable (which task, sources, schedule time, scope options, connector now vs later), use AskUserQuestion with concrete options; keep open-ended questions to one per turn. Boundaries and caveats are raised in context, briefly, when they matter. For each cluster below: what to ask, what you're listening for, and the mapping rules.

### Q1. The job — "Tell me about yourself and what you'd like to build."

Open and unrestrictive — they can bring anything an agent can do: their own task, a piece of their product, a customer-facing worker, an experiment. Listening for: a job with (a) real judgment+tool work in it and (b) inputs they can actually provide. Whether it recurs only decides the cadence question later (Q5) — it is not a requirement, and "this is for my product / my users" is just as good a starting point as "this eats my week".

**Maps to:** agent `name`, the core of `system`, and the archetype (ops chore / research-analyst / product probe / customer-facing worker).

Rules:
- **Let them explain first.** One open follow-up ("what would it actually do? what does a great first version look like to you?") before any reshaping, boundaries, or AskUserQuestion menus — respond to their picture, don't pre-empt it.
- If the ask needs things agents truly can't do (live phone calls, controlling desktop GUIs, sub-second real-time reaction) → say so honestly and reshape to the nearest can-do. Keep hard limits separate from defaults: gated write-actions (send/post/place orders behind `always_ask`, or paper/sandbox variants) are possible, even in v0 if they want them — don't undersell.
- If they describe a *pipeline* of many jobs → capture the whole pipeline, build **stage one** today; the rest goes into Next directions (and may justify multiagent later, see Q8).

### Q2. Done — "Show me what a good result looks like. Concretely. What would you check to know it's right?"

Ask this **after** the job is understood, under its own clearly-named step ("Outcome & evals") — never in the opening message.

Listening for: checkable, binary-ish criteria. Push past "a useful summary" to "a markdown file with the 5 most important items, each with a link and one line of why".

**Maps to:** the **Outcome** — `description` (the task) + rubric (markdown, per-criterion checks) + `max_iterations`.

Rules:
- 3–6 explicit criteria; each independently gradeable. Vague criteria → noisy grading.
- If they have a known-good past example → use it: derive the rubric from what makes that example good (the docs explicitly recommend this).
- `max_iterations`: default 3. Raise toward 5–10 only when the task is genuinely hard to nail and run cost is acceptable. (Max 20.)
- The rubric lives in the kickoff, **not** the system prompt — so sharpening it later is free (no agent version bump).

### Q2b. Evidence — "Do you have real examples we can test against? Past cases where you know what the right answer was?"

Asked in the same "Outcome & evals" step as Q2, not upfront. Listening for: real historical inputs **with known-good outputs** — last month's actual emails and how they triaged them, a competitor report they wrote by hand, the spreadsheet a contractor produced, tickets they already answered. This is the founder's eval set, and most founders have one without realizing it.

**Maps to:** the test/eval harness for v0 and beyond.

| What they have | What we do with it |
|---|---|
| 2–5 real past cases with known-good results | **Golden set.** Use one as the v0 kickoff input; hold the rest back. After the rubric passes on case 1, run the held-back cases as additional sessions and compare against what they actually did. |
| One known-good artifact, no inputs | Derive the rubric *from* it (per the Outcomes docs guidance) and use it as the reference when grading run #1. |
| Real inputs but no "right answers" | The founder is the grader: run it, they mark each rubric criterion pass/fail by hand on run #1 — that judgment becomes sharper rubric criteria for run #2. |
| Nothing real on hand (stealth, no data yet) | Synthesize 2–3 plausible test inputs *with them* during the interview; flag in NEXT-DIRECTIONS that the first week of real usage is the eval. |
| Fresh-data recurring task (news, raises, monitoring) — golden answers age out by design | The rubric IS the eval. Today's first verified output gets saved as `evals/case-01/expected.md` at close — it's the regression baseline for the next agent version, not a permanent golden answer. |
| Sensitive real data | Use it only if they're comfortable (no ZDR); otherwise have them hand-redact or synthesize look-alikes — the structure matters more than the values. |

How evals actually run on CMA (no separate eval product needed):
- **The Outcome rubric IS the per-run eval** — the grader scores every session against it and the verdict (`satisfied` / `needs_revision` / …) plus explanation is recorded on the session (`outcome_evaluations[]`).
- **A golden-set pass = N sessions, same agent version, one per test case** (cheap to script: loop over cases, create session, kickoff with the case as input, collect verdicts + outputs). Pin the agent `version` so results are comparable.
- **Regression check after iteration:** after any agent update (v2, v3…), re-run the golden set against the new version and diff verdicts — catches "fixed one case, broke another".
- Session `usage` gives cost-per-case alongside quality.

Rules:
- Don't gate v0 on a big eval set — **one real case to build against + 2–4 held back** is plenty; more goes in Next directions.
- If they picked a scheduled deployment (Q5), the golden set re-run becomes the pre-flight check before changing the deployed agent version.
- Record in the build sheet: where the eval cases live, which session IDs were the eval runs, and the verdict per case.

### Q3. Inputs — "What does it need to read or know to do this well?"

Triage every input they name into one of these buckets (this is the heart of the config):

| Input type | Maps to |
|---|---|
| Content they have on hand (docs, samples, exports) | **Files** attached to the session/deployment, or pasted into the kickoff |
| Live public information (sites, competitors, news, docs) | `web_search` / `web_fetch` (already in the toolset) |
| Their code | **GitHub resource** on the session/deployment |
| A SaaS behind a login that has a remote MCP server (Slack, Linear, Notion, GitHub…) | `mcp_servers` entry + `mcp_toolset` + **Vault `mcp_oauth`/`static_bearer` credential** |
| Any API/CLI keyed by an API key (their own backend, Stripe, Airtable…) | **Vault `environment_variable` credential** (+ host allowlisting on the credential) |
| Internal-only services not reachable from the internet | **MCP tunnel** (research preview) — flag, don't promise |
| Knowledge that should accumulate across runs (preferences, past decisions, what worked) | **Memory store** (see Q7) |

Rules:
- **Credential test:** if the key/token isn't available *right now*, v0 does without it — substitute public web or pasted samples, or **mock the connector** (outbox / custom-tool pattern + endpoint schemas in `mock-connectors.md`) so the agent's behaviour is already shaped for the real thing; the credentialed version is the swap, with a vault.
- Anything sensitive: remind them the sandbox + Anthropic store session data (no ZDR) — synthesized data is fine for v0.
- If an input requires heavy parsing libraries (PDFs, spreadsheets, specific SDKs) → **environment `packages`** (pip/npm/apt…).

### Q4. Outputs — "What artifact comes out, and where does it need to land?"

| Output | Maps to |
|---|---|
| Markdown / text / JSON report | default — `/mnt/session/outputs/`, fetched via Files API |
| Spreadsheet, deck, doc, PDF | **Anthropic skill**: `xlsx`, `pptx`, `docx`, `pdf` |
| A draft inside another system (PR, ticket, email draft, CRM note) | MCP write tool — **gated `always_ask`** in v0, or draft-text-only output |
| Triggering something in *their* product/backend | **Custom tool** (they execute it; define `input_schema`; their app returns `user.custom_tool_result`) |
| Something a human must review before it goes anywhere | keep agent draft-only; the review step lives in their interface (Q6/Q8) |
| A repeatable house format or procedure (report template, triage checklist, brand voice) | **Custom skill** for the agent — author it now if small, otherwise NEXT-DIRECTIONS with the skill outline |

Rules:
- v0 never *sends/posts/merges/deletes* in external systems. Drafting is the deliverable; the send button stays human (or `always_ask`-gated) until they trust it. **Say what the guardrail actually is** — "the agent drafts; sending is wired later through a connector with an ask-before-send gate" — not just "it can't email".
- When the founder names a delivery destination, name the connector route back: which MCP server, what credential it needs (vault), and whether it's wireable today or Next direction #1. If email delivery is awkward (OAuth, no Gmail MCP credential on hand), **offer Slack as the easier first delivery target** — a Slack MCP webhook/connector is usually a faster path to "it shows up where I look every morning".
- Can't wire it now but they want the behaviour? **Mock it** (`mock-connectors.md`): the agent writes schema-true payloads to an outbox (or calls a stubbed custom tool), and the real connector becomes a one-step swap in v1.
- When delivery is the point of the agent, **the v0 deliverable is the message itself** — the exact Slack message / email / ticket text (or schema-true payload) as the output file, ready to paste or send by hand. The next version then only adds the sending; the content and format are already proven.

### Q5. Cadence — "When should this run: when you ask, on a schedule, or when something happens?"

| Answer | Maps to |
|---|---|
| "When I ask" | Plain **sessions** (create + kickoff). Fine for v0 and for testing. |
| "Every Monday at 7" / "nightly" / "weekly" | **Scheduled deployment**: cron `expression` + IANA `timezone`, `initial_events` carrying the kickoff. Test instantly with the manual `run` endpoint before trusting the cron. |
| "When a customer signs up / when a PR opens / when an email arrives" | Event-driven: **their app calls the API** (create session or `deployments/run`) from their own webhook handler. CMA webhooks notify them of session lifecycle the other direction. |

Rules:
- Even for scheduled work, run everything as ad-hoc sessions first; the deployment is created **last**, once a session has passed the rubric.
- Capture the cron line + timezone verbatim in the build sheet; warn about the 1–3am DST window only if they pick it.
- **Cadence vs lookback consistency check:** if the run frequency and the data window disagree (e.g. daily run, 14-day lookback → mostly repeated content every run), resolve it now with one question (shorter window, less frequent run, or a memory store that tracks what's already been reported) rather than deferring it silently.
- Anything reused on a schedule (kickoff text, system prompt) must use **relative dates** ("today", "the last N days as of this run"), never a literal date — the deployment replays the same `initial_events` every run.

### Q6. Boundaries — "What must it never do? What's it allowed to spend?"

Two things are handled quietly, as defaults — not a discussion:
- **Iteration bound** via the Outcome's `max_iterations` (default 3) — the built-in stop condition. Mention once that a run costs cents; don't require any Console spend configuration.
- Behavioral never-dos ("never contact anyone", "never present guesses as facts") → lines in `system`. Cheap, do them now.

Everything else a founder raises here is **hardening, not v0** — capture it in **Next directions** (see below) with the exact mechanism so they can apply it after the session:

| Concern raised | Next-direction entry (mechanism) |
|---|---|
| "Only touch these specific sites/APIs" | Environment `networking: limited` + `allowed_hosts` (+ `allow_mcp_servers` / `allow_package_managers`) |
| "Ask me before it runs commands / posts anywhere" | Permission policy `always_ask` on `bash` or the relevant `mcp_toolset` (MCP already defaults to ask) — needs an interface that surfaces confirmations |
| "Don't let it rewrite our reference docs" | Memory store attached `read_only` |
| Compliance / data residency | Self-hosted sandbox environment on their infra |

### Q7. Learning — "Should run #10 be smarter than run #1? What should it remember?"

| Answer | Maps to |
|---|---|
| "No, each run is independent" | No memory store. Simpler. Done. |
| "It should remember my preferences / past decisions / what it already processed" | One **memory store**, `read_write`, attached to every session/deployment; seed it with 2–3 starter memories at launch |
| "There's reference material it should always consult but never change" | Second store, `read_only` (cheap insurance against prompt-injection poisoning) |
| "Per-customer memory" (their product) | One store **per end user/customer**, attached per session — pairs with vault-per-user (Q8) |
| "Memory will get messy over time" | Roadmap note: **Dreams** consolidation (research preview) |

Limits to respect silently: ≤8 stores/session, ≤2,000 memories/store, small focused files.

### Q8. Shape & surface — "Who uses this — just you, your team, or your customers? And where do they interact with it?"

This determines two things: **multiagent or not**, and **what their interface is** (the founder's own product surface — see note at bottom).

Multiagent rules (default is NO):
- One job, one context → **single agent**. Always start here.
- Genuinely separable specializations (different tools/credentials/models per role), or fan-out over many independent items, or an escalation tier → **coordinator + roster** (`multiagent`), depth 1, ≤20 roster / ≤25 threads. Build the single most valuable subagent first; the coordinator comes after at least one subagent works alone.

Interface mapping:
| "Who/where" | What it implies |
|---|---|
| Just the founder, terminal is fine | The launch scripts + `ant`/curl ARE the interface; nothing more to build |
| Founder + small team, want visibility | Console (sessions/tracing) + the **agent-overview page** we generate. A **generated interface** (Claude Code builds it in a follow-up session — graphical output, results viewer over the Files/Sessions API, or a way to interact with the agent) is the standard tailored-extension offer here when it suits the need — v1, not v0. |
| Their customers, inside their product | Their app calls the CMA API: session-per-user(or per-job), **vault per end user** (`metadata.external_user_id`), webhooks for completion, their own UI streams events / shows outputs / surfaces `always_ask` confirmations |

Also captured here: model & budget posture — default newest Opus-class (quality first; runs still cost cents); drop to Sonnet-class only if they explicitly want cheaper/faster runs; `speed: fast` only if they ask about latency.

---

## Output of the interview: the build sheet

Everything above lands in `./my-agent/`:

| File | Contents |
|---|---|
| `build-sheet.json` | The full structured mapping (every primitive decision + rationale) — **this is what the primitives UI renders** |
| `agent.json` / `agent.yaml` | The agent config (name, model, system, tools+policies, mcp_servers, skills, multiagent if any) |
| `environment.json` | Env config (packages, networking) |
| `outcome.md` | The rubric |
| `kickoff.json` | The `user.define_outcome` (or `user.message`) event payload |
| `deployment.json` | Cron schedule + initial events (only if Q5 = scheduled) |
| `evals/` | The golden set: one folder per test case (`input.*` + `expected.md` or known-good artifact), plus `run-evals.sh` (loop: session per case, kickoff, collect `outcome_evaluations[]` verdicts + usage into `evals/results-<agent-version>.json`) |
| `agent-overview.html` | The "spec sheet" page: a static, self-contained view of every primitive in use (agent, rubric, tools, connections, memory, schedule, evals, next directions). **Claude Code generates and regenerates it directly** — it's a workflow step in the skill (after the interview, after launch when IDs exist, after every iteration), not a script the founder runs. Template/example: `references/overview-template.html`. Live observability stays in the Console. |
| `launch.sh` / `LAUNCH.md` | The exact create-calls in order, saving IDs to `IDS.env` |
| `NEXT-DIRECTIONS.md` | The version plan. **Whenever something doesn't belong in v0 — at any point in the session — it goes here, in the moment**, slotted into a numbered later version (v1, v2, …) with the exact mechanism + doc link: write-actions with approval gates, network allowlists, read-only memory, vault creds not in hand, multiagent stages, self-hosted sandboxes, Dreams, the founder's productized interface. It reads as a sequence of planned releases, not a list of cuts. |

`IDS.env` accumulates real IDs as objects are created (`AGENT_ID`, `AGENT_VERSION`, `ENV_ID`, `SESSION_ID`, `MEMSTORE_ID`, `VAULT_ID`, `DEPLOYMENT_ID`) — the bridge between "planned" and "live" that the UI uses.

## Sequencing (v0 first, upgrades after)

1. **Light open + interview** → warm welcome, 2–3 examples, the open question, then let them explain before steering; the iterative interview with boundaries raised only in context; the design read back as the brief (primitives table · v1/v2 section · eval table) and approved via AskUserQuestion; **agent-overview.html generated and opened immediately on approval** (something to look at while the rest is built), then build sheet + files emitted. Eval cases (Q2b) collected into `evals/` — case 1 becomes the v0 input, the rest are held back.
2. **Stage** → validate payloads, write the resumable launch sequence and LAUNCH.md, `ant`/curl check — all without the key. The brief already told them what credentials to go grab and where (API key; any connector token/webhook), so by now they're fetching in parallel. Then the key step, made as easy as possible: check the shell env first (skip the ask if it's already set); otherwise pre-create `my-agent/.env` (chmod 600) and have the founder paste the key into it via its absolute path — never into the chat. Keep staging/explaining while they do. Model pick happens at launch (newest Opus-class; show the full slug from then on).
3. **Launch v0** → env → agent → session → outcome kickoff **on eval case 1**. Watch the stream; hand them the Console link for the key's workspace.
4. **While it runs** → regenerate agent-overview.html with live IDs; draft NEXT-DIRECTIONS; seed memory store if planned.
5. **Grade & iterate** → read grader verdict + outputs against rubric *and against the known-good answer for case 1* (grading table); pick the next move via AskUserQuestion; change ONE thing (rubric edit = free; system/tool change = agent v2); re-kickoff. Once a version passes, fire the held-back eval cases (`run-evals.sh`) against the winning version as parallel background tasks while talking.
6. **Make it theirs** → if scheduled: create the deployment (relative dates only in `initial_events`) + manual `run` test; eval results recorded per agent version; Next directions finalized (incl. "re-run evals before promoting any new agent version to the deployment"); then invoke `/wrap-up` — it owns the close: overview page reopened, primitives recap table, run log, 1–2 tailored extensions, hygiene sweep.

---

## Note on the founder's *own* interface (the FYI)

The thing built here is the **worker**. How the founder (or their users) talk to it afterwards is a separate, deliberate choice captured in Q8 and written into NEXT-DIRECTIONS:

- **Terminal-only** is legitimate and complete for a solo founder (scripts + `ant` + Console).
- **Internal surface**: the agent-overview page we generate doubles as a minimal spec/status view; a **generated interface** is offered as a tailored extension when it suits the need — graphical output, a results viewer over the Files/Sessions API, or a way to interact with the agent — built by Claude Code in a follow-up session.
- **Productized**: their app owns the UX — creating sessions/vaults per user, streaming events, rendering outputs, surfacing tool confirmations. That's their build, not ours; the build sheet gives them the API map for it.
