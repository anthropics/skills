---
name: conversational-ai-quickstarts
description: |
  Locked quickstart flow for Agora Conversational AI. Use when no working baseline exists.
  BLOCKING: Do not write code, create files, scaffold projects, or propose custom architecture until the quickstart state machine reaches `complete`. Use the Agora CLI directly to verify and fix project readiness — do not ask the user to self-report. One decision group per turn. Before every reply, check: baseline_resolved? cli_readiness_done? vendor_gate_done? If any is false, stay in the current gate.
  SAMPLE INTEGRITY: After cloning the official sample, the default allowed actions are: install dependencies, populate env with CLI-extracted credentials, and start the app using the commands documented in the sample's README. Do NOT substitute your own startup commands or replace the sample with a self-built implementation. If a documented command is blocked by sandbox or permissions, re-run that exact command with escalation if available; otherwise stop and report an environment constraint. If the failure is localized to the official sample itself, a minimal upstream-shaped workaround is allowed, but not a custom architecture or repo rewrite.
license: MIT
metadata:
  author: agora
  version: '1.3.0'
---

# Conversational AI Quickstart

Use this file for `quickstart` and `integration` mode from [README.md](README.md).

## Working-Baseline Rule

A **working ConvoAI baseline** means the developer has already started an Agora ConvoAI agent successfully and the client can join the same RTC channel and interact with it.

The following do **not** count as a working baseline:

- only RTC code exists
- a sample repo is cloned but the agent has never started successfully
- environment variables are present but unverified
- the user only knows the desired backend language or framework

If the user already has a working baseline, exit this file and route back through [README.md](README.md).

## Sequence

Follow this exact user-visible order:

1. Product intro in plain language
2. Environment check — verify runtime dependencies are installed
3. Project-readiness checkpoint — use the CLI directly to verify and fix
4. Vendor-path confirmation — **skip if the user has not mentioned BYOK, providers, or Studio Agent ID; defaults apply automatically**
5. Vendor selection, only if the user asks for the current provider list or chooses a non-default path
6. Studio Agent ID confirmation, only if the user wants to reuse an agent configured in Agora Studio
7. Structured quickstart spec

There is no baseline-path or backend-path selection. The default path is always the Python server + React frontend quickstart (`agent-quickstart-python`). Do not offer alternatives before first success.

## Interaction Rules

- One decision group per turn. Do not ask credentials and vendor path in the same reply.
- Skip anything the user already answered.
- **Auto-skip `vendor_defaults`**: if the user has not mentioned BYOK, vendor API keys, a specific provider, or a Studio Agent ID, skip the vendor gate entirely and use the defaults. Do not ask about providers when the user just wants the fastest path.
- Infer obvious context from the user's stack or repository description.
- Mirror the user's language.
- While quickstart is unresolved, do **not** generate `/join` payloads, SDK code, custom file structures, clone commands, or repo adaptation plans.
- While quickstart is unresolved, read only this file and [README.md](README.md).
- If the user asks to use the CLI to speed up onboarding, keep the request inside this quickstart flow. The CLI is already the default readiness path, so continue normally.
- Unless the user explicitly asks for BYOK (bring your own key) or a different provider stack, anchor on the defaults first — no vendor API keys needed.
- For non-default provider selection, fetch the official current provider docs before confirming support or generating config details.
- If the user already has an **Agora Studio Agent ID** from `https://console.agora.io/studio/agents`, treat that as a separate quickstart branch. Do not re-ask STT/LLM/TTS provider choices unless the user explicitly wants to replace the Studio-managed config.
- Do not offer baseline-path choices. The default is always `agent-quickstart-python` (Python server + React frontend). Other demos are referenced only after first success.

## Command Integrity Under Environment Restrictions

For the first-success gate, treat the sample README commands as exact.

If a documented command fails because of sandbox, permission, port-binding, filesystem, or network restrictions:

1. Do **not** replace the command with an equivalent variant.
2. Do **not** add flags, env vars, host overrides, alternate entrypoints, or custom wrappers.
3. Re-run the exact documented command with required escalation or approval if available.
4. If escalation is unavailable or denied, stop and report that the baseline is blocked by the execution environment, not by the sample itself.
5. Do **not** continue to customization until the sample has been validated with the documented command.

Forbidden substitutions include:

- `pnpm dev` → `pnpm exec next dev ...`
- `npm run dev` → `next dev ...`
- README clone/start commands → custom shell variants that change the command semantics

## Failure Attribution

If the documented sample command fails before app code runs and the error indicates a local execution restriction, classify it as an environment constraint.

Typical signals include:

- `EPERM`
- `EACCES`
- blocked `listen` / `bind`
- blocked `chmod` / filesystem permission errors
- sandbox-denied network or local resource access

Do **not** reinterpret these failures as sample misconfiguration and do **not** change the command to work around them.

## First-Success Readiness Layers

Use three readiness layers during quickstart:

- **Control-plane ready** — login works, the project resolves, App ID exists, App Certificate can be exported through the verified CLI surface, required features are enabled, and `agora project doctor` is not blocking.
- **Runtime ready** — services are actually usable. In practice, RTM enablement may lag behind control-plane state; after enablement, allow bounded wait/retry for up to about 5 minutes before deciding the project still needs intervention.
- **Sample ready** — the official sample installs, env is populated, the app starts, the browser can open, the user can press `Try it now`, the agent joins the RTC channel, and the frontend does not crash.

`agora project doctor` only proves **control-plane ready**. It does not prove runtime or sample readiness.

## CLI-Driven Readiness Check

The project readiness step requires the agent to directly execute Agora CLI commands to verify and fix prerequisites. Do not ask the user to run CLI commands themselves, do not offer manual alternatives, and do not present choices. The agent checks, the agent fixes.

The CLI covers:

- login / auth status
- current project selection
- project env export
- feature enablement
- App ID presence, App Certificate presence, and other basic project checks
- `agora project doctor` readiness checks

Use `agora project env --with-secrets --json` as the primary source of truth for App ID and App Certificate during quickstart. Use `project show --json` only when project metadata inspection is needed.

Do **not** treat a healthy doctor result as a proven ConvoAI baseline.

For command details, route to the CLI references:

- [../cli/README.md](../cli/README.md)
- [../cli/projects.md](../cli/projects.md)
- [../cli/doctor.md](../cli/doctor.md)

After the CLI readiness step is resolved, return to this quickstart and continue from the same readiness checkpoint.

## Default Quickstart Path

There is one default quickstart path. Do not offer alternatives before first success.

**Repo:** <https://github.com/AgoraIO-Conversational-AI/agent-quickstart-python> *(Python server + React frontend)*

1. Runtime prerequisites
   1.1 Bun (package manager & script runner)
   1.2 Python 3.8+
2. CLI preflight
   2.1 Log in: `agora login`
   2.2 Prefer the current selected project only if it is directly usable for first-success
   2.3 Otherwise select another directly usable project or create a new dedicated token-ready project
   2.4 Ensure `rtc`, `rtm`, and `convoai` are enabled for the first-success path
   2.5 Export App ID + App Certificate with `agora project env --with-secrets --json`
   2.6 Check `agora project doctor`
   2.7 If RTM was just enabled, allow bounded wait/retry before concluding runtime failure
3. Official sample baseline
   3.1 Clone `agent-quickstart-python`
   3.2 Run `bun install`
   3.3 Copy `server/.env.example` to `server/.env.local`
   3.4 Set `APP_ID` and `APP_CERTIFICATE` in `server/.env.local`
   3.5 Start with `bun run dev` (auto-creates venv, installs deps, starts both services)
4. Success gate
   4.1 Frontend loads at http://localhost:3000
   4.2 Backend runs at http://localhost:8000
   4.3 The user can start a conversation
   4.4 The agent joins the RTC channel
   4.5 The user can speak to the agent and hear TTS back
   4.6 Only after this counts as a working baseline

## First-Success Vendor Defaults

The official `agent-quickstart-nextjs` sample works out of the box with just Agora credentials.
Vendor API calls (STT, LLM, TTS) go through Agora by default — no vendor API keys needed.

Default pipeline:

- **STT:** Deepgram nova-3
- **LLM:** OpenAI gpt-4o-mini
- **TTS:** MiniMax speech_2_6_turbo

BYOK (Bring Your Own Key) is supported but optional. The sample includes commented-out
BYOK blocks for Deepgram, OpenAI, and ElevenLabs. Users who want to use their own vendor
API keys can uncomment those blocks and provide them.

BYOK provider families visible in the current sample and SDK docs:

- **STT:** Deepgram (BYOK)
- **LLM:** OpenAI (BYOK)
- **TTS:** ElevenLabs (BYOK), Microsoft
- **MLLM:** OpenAI Realtime, Google Gemini Live

Use this rule during quickstart:

- For the first end-to-end success path, prefer the **default pipeline** (no vendor keys).
- Only switch to BYOK during quickstart if the user explicitly asks for it or names a specific vendor key they want to use.
- Only switch away from the default cascading pipeline if the user explicitly asks for MLLM.
- For the current provider matrix or vendor-specific configs, fetch the official live docs before claiming support or listing parameters.

## Env Name Policy

### Default sample path (`agent-quickstart-python`)

Keep the official sample's env names as the source of truth.

Default (no vendor keys needed):

```bash
APP_ID=
APP_CERTIFICATE=
PORT=8000
```

Do **not** prompt for vendor API keys unless the user explicitly asks for BYOK.
Do **not** rename these env vars to a different custom scheme during quickstart.

### Custom-code path

If the user is no longer sample-aligned and needs provider-specific config layout, fetch the current official ConvoAI provider docs and use those as the source of truth.

## Baseline Path

The default and only quickstart baseline is `agent-quickstart-python` (Python server + React frontend).

After first success, the user can explore other demos:

| Demo | Description | Reference |
|------|-------------|-----------|
| `agent-quickstart-nextjs` | Full-stack Next.js (single app with API routes) | [See below](#other-demo-references) |
| `agent-samples` | Decomposed backend + multiple client apps | [agent-samples.md](agent-samples.md) |

## State Machine

The quickstart is a blocking state machine. While a state is unresolved, the only allowed action is to send the next prompt for that state and wait for the user's reply.

| State | Allowed | Forbidden | Next prompt | Advance when |
|---|---|---|---|---|
| `intro` | Give a short plain-language intro to what ConvoAI is | Code, repo plans, framework recommendations | Product intro text | Intro delivered |
| `environment_check` | Check Node.js, Bun, Python, Agora CLI versions. Install or update missing tools. | Code, repo inspection, implementation | Environment check commands | All four dependencies are installed and meet minimum versions |
| `project_readiness` | Execute CLI commands directly to verify auth, project, App ID, App Certificate, feature activation, and fix missing prerequisites. Extract credentials from CLI env output. | Code, repo inspection, implementation | Readiness prompt | Control-plane readiness confirmed and credentials captured |
| `vendor_defaults` | Ask whether to use the defaults (no vendor keys), BYOK, show the current official provider list, choose a non-default cascading / MLLM path, or reuse a Studio Agent ID. **Skip this gate entirely if the user has not mentioned BYOK, providers, or Studio Agent ID — defaults apply automatically.** | Code, implementation | Vendor-defaults prompt | User picks or gate is auto-skipped |
| `vendor_selection` | Collect only provider-mode and provider choices after checking the official current provider docs | Code, implementation, secret collection | Custom-provider prompt | Provider mode and provider names are resolved |
| `studio_agent_id` | Collect the Agora Studio Agent ID and confirm the user wants Studio to remain the source of truth for agent config | Code, re-asking provider setup from scratch | Studio-Agent-ID prompt | The Studio Agent ID path is resolved |
| `complete` | Emit structured spec and continue to execution | Re-open resolved gates | None | Spec emitted |

### Pre-Action Self-Check

Before every tool call or user-visible reply:

1. What is the current state?
2. Is the intended action allowed in that state?
3. If not, send the state prompt instead.

### Failure Branches

- If the user says they cloned a repo but never got an agent running, stay in quickstart.
- If the user asks for code before quickstart resolves, answer with the next gate instead of generating code.
- If a reply only partially resolves the current gate, ask a narrow follow-up for the missing field only.
- If the user asks for the fastest onboarding path or mentions setup during the readiness gate, proceed directly with the CLI verification sequence and then return to the quickstart once readiness is confirmed.
- If the user asks for the full fastest onboarding flow, proceed with the default quickstart path directly.
- If the user names a provider that is not in the current official provider docs, say this clearly: it is **not currently documented as supported in the official Agora ConvoAI provider docs**, so do not proceed as if it is supported. Offer the documented default combo or a live-doc verification path.
- If the user asks to see the provider list, fetch the current official provider docs and stay in the vendor gate until they accept the default combo or choose a documented alternative.
- If the user says they already have an Agora Studio Agent ID, switch to the `studio_agent_id` state and stop re-asking provider-vendor questions unless they explicitly say they want to replace the Studio-managed config.

## Prompt Templates

### Product Intro

Keep it short. Explain that ConvoAI is a server-managed voice agent that joins an RTC channel, speaks through TTS, and usually pairs an RTC client with a backend that starts the agent.

Use a natural transition into quickstart. Preferred tone:

- Avoid saying "run the baseline flow" or "anchor on a proven baseline" to the user.
- Prefer "let's first use the official sample to get the whole link working once" language.

Suggested transition line:

```text
Before we jump into custom code, let's first use the official sample to get the whole flow working once. Once the agent can join the channel and finish one real conversation, we can turn that working version into your demo.
```

### Environment Check

Before starting the CLI readiness flow, verify that all runtime dependencies are installed. Run these checks and fix any missing tools automatically. Do not ask the user to install them manually.

| Dependency | Check command | Minimum version | Install if missing |
|-----------|--------------|----------------|-------------------|
| Node.js | `node --version` | 18+ | Direct the user to https://nodejs.org or use `nvm install 22` |
| Bun | `bun --version` | 1.0+ | `npm install -g bun` |
| Python | `python3 --version` | 3.8+ | Direct the user to https://python.org |
| Agora CLI | `npm list -g agoraio-cli` | 0.1.3+ | `npm install -g agoraio-cli@latest` |

Execution rules:
- Check all four in order. If any is missing or below minimum version, install/update it before continuing.
- For Node.js and Python, if they are not installed, tell the user what to install and wait — do not attempt to install system-level runtimes.
- For Bun and Agora CLI, install them directly via npm.
- If Agora CLI is installed but outdated, run `npm install -g agoraio-cli@latest` to update.
- Only proceed to project readiness after all four checks pass.

### Project Readiness

Do not ask the user to self-report readiness or choose between manual and CLI paths. The agent must directly execute CLI commands to check each prerequisite and, when something is missing, fix it on the spot.

Tell the user what you are about to check, then execute the commands yourself:

```text
Let me check your project readiness — I'll use the Agora CLI to verify login, project, App ID, App Certificate, and ConvoAI activation. If anything is missing I'll fix it directly. Once the control-plane checks out I'll grab the credentials and fill in .env.local for you automatically.
```

#### Agent execution sequence

Run these commands in order. Use `--json` where available so you can parse the output programmatically.

1. **Auth check** — `agora auth status --json`
   - If not logged in → run `agora login` and wait for the user to complete the browser OAuth flow.

2. **Current project suitability** — check the currently selected project first.
   - Inspect the selected project with `agora project show --json`.
   - Treat it as directly usable only if the project resolves, App ID exists, App Certificate is exportable, and the required first-success features are present.
   - If the current project is directly usable → keep it.
   - If the current project is not directly usable → continue to project discovery.

3. **Project discovery and selection**
   - If the user explicitly named a project, inspect that exact project first and try to repair it with documented CLI commands.
   - If the user did **not** name a project and the current selected project is not directly usable, inspect existing projects and look for a directly usable candidate.
   - If a directly usable candidate is found, select it and explicitly tell the user which project was chosen before continuing.
   - If no directly usable candidate exists, create a new dedicated first-success project with the required features already enabled, then select it.

4. **Credential export** — use `agora project env --with-secrets --json`
   - Extract App ID and App Certificate from the CLI env output, not from Agora Console.
   - Keep these values for later sample env population.
   - If `--with-secrets` fails because the project is still not token-ready, treat that as a project-readiness failure and keep fixing or replace the project according to the selection rules above.

5. **Doctor** — `agora project doctor --json`
   - If `healthy` or `warning` → control-plane readiness is confirmed, not runtime/sample readiness.
   - If `not_ready` → read the reported issues and fix them directly:
     - ConvoAI not enabled → `agora project feature enable convoai`, then re-run doctor.
     - RTM or related service just enabled → allow bounded wait/retry for up to about 5 minutes before concluding the project still needs intervention.
     - Other issues → run the matching recovery command (see [doctor.md](../cli/doctor.md)), then re-run doctor.
   - Repeat until doctor passes at the control-plane layer.

6. **Auto-populate env** — once control-plane readiness passes, the agent has both App ID and App Certificate from step 4. When the sample repo is cloned and `.env.local` is created, the agent writes these values directly into the file. No manual copy-paste needed.

7. **Sample-ready gate**
   - Install dependencies and start the official sample using the documented commands.
   - The quickstart is only fully ready when the app opens, the user can press `Try it now`, the agent joins, and the frontend stays up.
   - If a failure is localized to the official sample itself rather than the environment or project readiness, a minimal upstream-shaped workaround is allowed. Do not replace the sample with a self-built implementation.

For CLI command details, route to:

- [../cli/README.md](../cli/README.md)
- [../cli/projects.md](../cli/projects.md)
- [../cli/doctor.md](../cli/doctor.md)

### Vendor Defaults

Use this only if the user has mentioned BYOK, vendor API keys, a specific provider, or a Studio Agent ID. If none of these were mentioned, skip this prompt entirely and use the defaults.

```text
The official quickstart works out of the box with just Agora credentials — no vendor API keys needed.

Default pipeline:
- STT: Deepgram nova-3
- LLM: OpenAI gpt-4o-mini
- TTS: MiniMax speech_2_6_turbo

A. Use the defaults (no vendor keys needed — fastest path)
B. I want to use my own vendor API keys (BYOK)
C. Show me the current official provider list first
D. I want to choose a non-default cascading or MLLM path
E. I already have an Agora Studio Agent ID and want to reuse that Studio-managed agent
```

### Custom Provider Prompt

Use only after the user picks `C` or directly asks for non-default providers.

```text
First check the current official ConvoAI provider docs, then choose from the documented provider modes:
- Cascading path: STT + LLM + TTS
- MLLM path: OpenAI Realtime or Google Gemini Live

Then choose the documented providers for that mode using the current official docs as the source of truth.

Reply in one line, for example:
- `TTS: Microsoft`
- `MLLM: OpenAI Realtime`
- `STT: Deepgram, LLM: OpenAI, TTS: Microsoft`
```

### Studio Agent ID Prompt

Use only when the user picks `D` or directly says they already have an Agora Studio Agent ID.

```text
If you already configured the agent in Agora Studio, we can treat Studio as the source of truth for the agent configuration instead of rebuilding the provider stack here.

Open `https://console.agora.io/studio/agents`, find the agent you want to reuse, and copy its **Agent ID**.

Important:
- This **Studio Agent ID** is different from the runtime `agent_id` returned by `/join`.
- The Studio Agent ID identifies the Studio-managed agent configuration and maps to the request field `pipeline_id`.
- The runtime `agent_id` identifies a live started session.

Reply with one of these:
A. I have the Studio Agent ID — here it is: `<agent-id>`
B. I need to look it up in Studio first
C. Go back — I want to use the default/provider path instead
```

### Unsupported Provider Prompt

Use this when the user names a provider that is not in the current official provider docs.

```text
That provider is not in the current official Agora ConvoAI provider docs, so I should not proceed as if it is supported.

You can choose one of these paths:
A. Use the documented default combo to get the first demo working
B. Show the current official provider list first
C. Re-check the latest official docs to verify whether that provider is supported now
```

## Output: Structured Quickstart Spec

After all gates are resolved, normalize the result into a short spec and continue automatically.

```yaml
use_case: [text]
mode: quickstart
proven_working_baseline: no
project_readiness:
  app_id: [ready | missing | unknown]
  app_certificate: [ready | missing | unknown]
  convoai_activation: [ready | missing | unknown]
key_mode: [default | byok | unknown]
providers:
  pipeline: [cascading | mllm | unknown]
  stt: [deepgram | user-specified-supported | unknown]
  llm: [openai | user-specified-supported | unknown]
  tts: [minimax | elevenlabs | microsoft | user-specified-supported | unknown]
  mode: [default | byok-default | user-specified-cascading | mllm | unknown]
studio_agent:
  use_existing_agent_id: [yes | no | unknown]
  agent_id: [text | missing | unknown]
```

Notes:

- `stt` is the SDK-facing name in this quickstart spec. Platform docs may call the same stage `ASR`.
- `studio_agent.agent_id` means the **Agora Studio Agent ID** from `https://console.agora.io/studio/agents`, not the runtime `agent_id` returned by `/join`.
- When this Studio path is used, that Studio Agent ID maps to the request field `pipeline_id`.

## After Collection

Execute the default quickstart path (clone `agent-quickstart-python`, configure, run, verify first success).

After first success, route by user's next request:

- existing Agora Studio Agent ID → use [conversational-ai-studio.md](conversational-ai-studio.md)
- provider selection or parameter confirmation → fetch the current official ConvoAI provider docs
- custom LLM backend → [server-custom-llm.md](server-custom-llm.md)
- direct REST API (non-SDK languages) → [auth-flow.md](auth-flow.md)
- other demos → see "After the Baseline Works" section below

## Other Demo References

These are available after the first success baseline is proven. Do not use these as the default quickstart path.

### Full-Stack Next.js (`agent-quickstart-nextjs`)

**Repo:** <https://github.com/AgoraIO-Conversational-AI/agent-quickstart-nextjs>

Single Next.js app with built-in API routes for token generation and agent lifecycle. Includes React UI with live transcription. Requires Node.js 22+ and pnpm 8+. See the repo README for setup.

### Decomposed Samples (`agent-samples`)

Multiple backend + client combinations. See [agent-samples.md](agent-samples.md).

## After the Baseline Works

Once the first end-to-end ConvoAI session works, route by task:

| Next step | Reference |
|---|---|
| Customize LLM, TTS, ASR vendor or model | Fetch `https://docs-md.agora.io/en/conversational-ai/develop/custom-llm.md` |
| Add transcript rendering or agent state to a custom UI | [agent-toolkit.md](agent-toolkit.md) |
| Use React hooks (`useTranscript`, `useAgentState`) | [agent-client-toolkit-react.md](agent-client-toolkit-react.md) |
| Swap in pre-built React UI components | [agent-ui-kit.md](agent-ui-kit.md) |
| Add a custom LLM backend (RAG, tool calling) | [server-custom-llm.md](server-custom-llm.md) |
| Production token generation | [../server/tokens.md](../server/tokens.md) |
| Full REST API reference | [README.md](README.md#rest-api-endpoints) |
