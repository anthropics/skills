# Agora Conversational AI Engine

REST API-driven voice AI agents. Create agents that join RTC channels and converse with users via speech. Front-end clients connect via RTC+RTM.

> **HARD GATE:** If the user does not have a working ConvoAI baseline, route to [quickstarts.md](quickstarts.md) and stay there. Do not generate code, scaffold projects, propose custom architecture, or write files until the quickstart state machine reaches `complete`. This is not a suggestion — it is a blocking constraint.

> **OFFICIAL DEMO FIRST:** When the user wants to try ConvoAI, build a demo, or prototype a voice AI agent, always clone and run the official sample repo first. Use the official repo and the official documented startup commands for the first-success gate. Do not replace the flow with a self-built implementation. Do not use web search for Agora integration details — use only the skill reference files.

## Routing: Classify the Request

The key question: does the user already have a **working ConvoAI baseline**?

- **Working baseline** = an Agora ConvoAI agent has already been started successfully end to end, and the client can join the same RTC channel and interact with it.
- **Not a working baseline** = only RTC code exists, a sample repo is cloned but not proven, env vars are present, or the user only knows the target backend language.

| Mode | When | Route to |
|---|---|---|
| `quickstart` | Starting from scratch, first demo, wants the official baseline | [quickstarts.md](quickstarts.md) |
| `integration` | Has an app or repo, but the ConvoAI path is not proven end to end yet | [quickstarts.md](quickstarts.md) |
| `backend-implementation` | Working baseline confirmed, now needs server code or lifecycle/auth changes | [server-sdks.md](server-sdks.md), [python-sdk.md](python-sdk.md), [go-sdk.md](go-sdk.md), or [auth-flow.md](auth-flow.md) |
| `client-customization` | Working baseline confirmed, now needs transcripts, hooks, UI, or mobile client work | [agent-toolkit.md](agent-toolkit.md), [agent-client-toolkit-react.md](agent-client-toolkit-react.md), [agent-ui-kit.md](agent-ui-kit.md), [agent-toolkit-ios.md](agent-toolkit-ios.md), [agent-toolkit-android.md](agent-toolkit-android.md) |
| `studio-agent` | The user already has an Agora Studio Agent ID and wants to reuse that Studio-managed agent config | [quickstarts.md](quickstarts.md), then [conversational-ai-studio.md](conversational-ai-studio.md) |
| `advanced-feature` / `debugging` / `ops-hardening` | Working baseline confirmed, wants custom LLM, memory, webhooks, production hardening, or error diagnosis | Start in this file, then route to the relevant reference below |

### Routing Rules

- If the user does **not** have a working baseline yet, read only this file and [quickstarts.md](quickstarts.md).
- While quickstart is unresolved, do **not** generate `/join` payloads, propose a custom project structure, or jump straight into SDK code.
- Existing RTC code or a checked-out repo is not enough to skip quickstart; the ConvoAI path must already work once.
- If the user explicitly says the baseline already works, skip quickstart and route directly to the relevant implementation file.
- If the user explicitly says they already have an **Agora Studio Agent ID** from `https://console.agora.io/studio/agents`, treat that as a dedicated ConvoAI path rather than re-running the provider-choice flow.
- If the user needs Java, Ruby, PHP, C#, or another non-SDK backend language, use [auth-flow.md](auth-flow.md) after the quickstart path is chosen.
- If the user asks to use the CLI to speed up ConvoAI onboarding, keep the request in the ConvoAI path first. Use the CLI only as a readiness helper for login, project selection, feature enablement, and `project doctor`, then continue the ConvoAI quickstart.
- For the first-success gate, treat the sample README commands as exact. If a documented command fails because of sandbox, permission, port-binding, filesystem, or network restrictions, re-run the exact documented command with escalation if available. Do not add flags, host overrides, alternate entrypoints, or equivalent replacement commands.

## Fast Onboarding With Agora CLI

For `quickstart` and `integration` mode, the fastest first-mile path is often:

1. use the Agora CLI to verify login, current project, `convoai` feature readiness, and other basic project checks such as App ID presence
2. run `project doctor` to catch missing setup early
3. then continue the official ConvoAI sample path until the agent joins a real RTC channel and completes one end-to-end conversation

Use the CLI references as the source of truth for command details:

- [../cli/README.md](../cli/README.md)
- [../cli/projects.md](../cli/projects.md)
- [../cli/doctor.md](../cli/doctor.md)

Important:

- a healthy CLI readiness check does **not** replace a working ConvoAI baseline
- the CLI can help verify login, project context, feature readiness, App Certificate presence, and basic project config, but it does **not** by itself prove RTM runtime availability or sample-ready status
- for the full combined onboarding flow, use the matching path in [quickstarts.md](quickstarts.md) once the baseline path is clear

## SDK vs. Direct REST API

**Default to the SDK for the user's backend language.** The TypeScript, Go, and Python SDKs wrap the REST API and handle auth, token generation, and session lifecycle automatically.

| Backend language | Path |
|---|---|
| TypeScript / Node.js | `agora-agent-server-sdk` — see [server-sdks.md](server-sdks.md) |
| Python | `agora-agent` — see [python-sdk.md](python-sdk.md) |
| Go | `agora-agent-server-sdk-go` — see [go-sdk.md](go-sdk.md) |
| Java, Ruby, PHP, C#, other | Call the REST API directly — see [auth-flow.md](auth-flow.md) |

Direct REST API use is fully supported for languages without an SDK. The [auth-flow.md](auth-flow.md) file covers the end-to-end auth and token flow for REST API implementors. If the user has an SDK available, start with that instead — the SDK eliminates the need to manually build tokens for the ConvoAI server.
The live OpenAPI spec is the authoritative source for request/response schemas:

```
GET https://docs-md.agora.io/api/conversational-ai-api-v2.x.yaml
```

## Architecture

```text
Your Server (REST API calls)
    ↓ POST /join with config
Agora ConvoAI Engine
    ↓ creates agent
Agent joins RTC channel ←→ Front-end client (RTC + RTM)
    ↓                           ↓
ASR → LLM → TTS             Receives audio + transcripts
```

1. Your server calls the REST API to create an agent with LLM/TTS/ASR config
2. The agent joins an Agora RTC channel and subscribes to the user's audio
3. ASR converts speech to text → LLM generates response → TTS converts to speech
4. The agent publishes audio back to the channel; transcripts arrive via RTC data channel or RTM

## Documentation Lookup

The bundled references in this file cover gotchas, generation rules, and the stable
behavioral contracts. Read the relevant local ConvoAI reference first, then use Level 2 only
if the local file does not cover the detail needed.

For vendor/provider questions, use the official current provider docs as the source of truth
once the question moves beyond the default quickstart combo. The bundled quickstart references
are still the right source for the first-success default path, but the current provider matrix,
vendor availability, beta status, and vendor-specific configs should come from live docs.

For content that still needs live docs after the local check, use Level 2:

1. Fetch `https://docs.agora.io/en/llms.txt`
2. Scan for a URL matching your topic (e.g., `conversational-ai`, `quick-start`, `rest-api`)
3. Fetch that URL

Common topics to fetch via Level 2 after the local reference check: quick-start code (Python, Go, Java), provider matrices, vendor-specific configs, full request/response schemas, newly changed vendor configs, error code listings.

For full request/response schemas, fetch the OpenAPI spec directly — it is always
current and covers every endpoint and field:
`https://docs-md.agora.io/api/conversational-ai-api-v2.x.yaml`

See [../doc-fetching.md](../doc-fetching.md) for the full procedure.

## Authentication (Direct REST API)

This section covers auth for implementors calling the REST API directly (non-SDK languages). **If the user has a TypeScript/Python/Go SDK available, skip this — the SDK handles auth automatically in App Credentials mode.** See [server-sdks.md](server-sdks.md) instead.

Two methods are supported for direct REST API calls. **Token-based auth is preferred** — it avoids storing long-lived Customer Secret credentials on your server.

### Option A: Agora Token (recommended)

Use a combined RTC + RTM token generated with `RtcTokenBuilder.buildTokenWithRtm` from the [`agora-token`](https://www.npmjs.com/package/agora-token) npm package:

```javascript
import { RtcTokenBuilder, RtcRole } from 'agora-token';

const token = RtcTokenBuilder.buildTokenWithRtm(
  appId, appCertificate, channelName, account, RtcRole.PUBLISHER,
  tokenExpire, privilegeExpire
);

const response = await fetch(
  `${baseUrl}/${appId}/join`,
  {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
      Authorization: `agora token=${token}`,
    },
    body: JSON.stringify(requestBody),
  }
);
```

> **Rule:** Use token auth (`Authorization: agora token=<RTC+RTM token>`) as the default for new direct REST implementations. Basic Auth remains available, but grants broader account-level access.

See [../server/tokens.md](../server/tokens.md) for `buildTokenWithRtm` parameter reference.

### Option B: HTTP Basic Auth (Customer ID + Secret)

- Credentials: Customer ID + Customer Secret from [Agora Console](https://console.agora.io) → Developer Toolkit → RESTful API
- Header: `Authorization: Basic <base64(customerID:customerSecret)>`
- HTTPS required (TLS 1.0/1.1/1.2)

## Base URL

```text
https://api.agora.io/api/conversational-ai-agent/v2/projects/{appid}
```

## Agent Lifecycle

| Status     | Code | Description                |
| ---------- | ---- | -------------------------- |
| IDLE       | 0    | Ready, not active          |
| STARTING   | 1    | Initialization in progress |
| RUNNING    | 2    | Active, processing audio   |
| STOPPING   | 3    | Shutdown in progress       |
| STOPPED    | 4    | Exited channel             |
| RECOVERING | 5    | Error recovery             |
| FAILED     | 6    | Execution failure          |

## Gotchas & Quirks

Things the official docs don't emphasize that cause frequent mistakes:

- **`agent_rtc_uid` is a string, not an int** — pass `"0"` (string) for auto-assignment, not `0`. Passing an integer will cause a type error at the API boundary.
- **`remote_rtc_uids` is an array of strings** — use `["*"]` to subscribe to all users, not `"*"` or `["0"]`. The wildcard must be in array form.
- **Agent name must be unique per project** — collisions return HTTP 409. Use a short UUID suffix: `agent_{uuid[:8]}`. On 409, generate a new name and retry; do not retry with the same name.
- **Use token auth as the default for new direct REST integrations.** The ConvoAI REST API accepts `Authorization: agora token=<token>` using a combined RTC + RTM token from `RtcTokenBuilder.buildTokenWithRtm`. This is **safer than Basic Auth**: tokens are scoped to a single App ID + channel, while Customer ID/Secret grants access to every project on the account. Use Basic Auth only when a user explicitly needs that mode.
- **POST `/join` success does not mean the agent is already in the RTC channel** — the request was accepted and the agent is starting. The client should wait for the RTC `user-joined` event before expecting agent audio or querying media state.
- **`/update` overwrites `params` entirely** — sending `{ "llm": { "params": { "max_tokens": 2048 } } }` erases `model` and everything else in `params`. Always send the full object.
- **Agora Studio Agent ID is not the same thing as the runtime `agent_id` returned by `/join`** — the Studio Agent ID comes from the Studio Agents page and identifies a Studio-managed agent configuration. In the Studio-managed start path, that value maps to the request field `pipeline_id`. The runtime `agent_id` identifies a started live session returned by the REST API. Do not use one in place of the other.
- **`/speak` priority enum** — `"INTERRUPT"` (immediate, default), `"APPEND"` (queued after current speech), `"IGNORE"` (skip if agent is busy). `interruptable: false` prevents users from cutting in.
- **20 PCU default limit** — max 20 concurrent agents per App ID. Exceeding returns error on `/join`. Contact Agora support to increase.
- **Event notifications require two flags** — `advanced_features.enable_rtm: true` AND `parameters.data_channel: "rtm"` in the join config. Without both, `onAgentStateChanged`/`onAgentMetrics`/`onAgentError` won't fire. Additionally: `parameters.enable_metrics: true` for metrics, `parameters.enable_error_message: true` for errors.
- **RTM channel name matches the RTC channel name** — the agent publishes transcripts and state events to the RTM channel with the same name as the RTC channel it joined. Subscribe the RTM client to the same channel name you passed to the agent's `properties.channel`.
- **RTM login identity must match the RTM token subject** — if the RTM token was minted for `String(rtcUid)`, the RTM client must log in with that same identity. Do not mint a token for one user identity and then log in RTM with another random user ID; this can surface as generic startup failures such as "Failed to start conversation".
- **RTM enablement can lag behind control-plane state** — after enabling RTM or related project capabilities, CLI/control-plane checks may report the feature as enabled before the RTM service is actually usable. For first-success flows, treat RTM availability as a bounded wait/retry condition for up to about 5 minutes before concluding the project still needs intervention.
- **Custom LLM interruptable metadata** — the first SSE chunk can be `{"object": "chat.completion.custom_metadata", "metadata": {"interruptable": false}}` to prevent user speech from interrupting critical responses (e.g., compliance disclaimers). Subsequent chunks use standard `chat.completion.chunk` format.
- **Error response format** — non-200 responses return `{ "detail": "...", "reason": "..." }`.
- **MLLM `location` not `region`** — use `params.location: "us-central1"`, not `region`. The field name is `location` at every level (join payload and backend env vars).

For test setup and mocking patterns, see [references/testing-guidance/SKILL.md](../testing-guidance/SKILL.md).

## REST API Endpoints

| Method | Path                          | Description                      |
| ------ | ----------------------------- | -------------------------------- |
| POST   | `/join`                       | Start agent — joins channel      |
| POST   | `/agents/{agentId}/leave`     | Stop agent — leaves channel      |
| POST   | `/agents/{agentId}/update`    | Update agent config (token, LLM) |
| GET    | `/agents/{agentId}`           | Query agent status               |
| GET    | `/agents`                     | List agents (with filters)       |
| POST   | `/agents/{agentId}/speak`     | Broadcast TTS message            |
| POST   | `/agents/{agentId}/interrupt` | Interrupt agent speech           |
| GET    | `/agents/{agentId}/history`   | Get conversation history         |

## Reference Files

Use the file that matches what the user is building:

| User's question / task | Read this file |
|---|---|
| No working ConvoAI baseline yet — choose the baseline path, setup order, and readiness gates | [quickstarts.md](quickstarts.md) |
| Node.js/Python/Go backend — starting agent, auth, session lifecycle | [server-sdks.md](server-sdks.md) |
| Python SDK specifics (async, deprecations, debug) | [python-sdk.md](python-sdk.md) |
| Go SDK specifics (context, builder, status constants) | [go-sdk.md](go-sdk.md) |
| Supported vendors and current vendor-specific configs | Fetch the official ConvoAI provider docs after reading this file |
| Existing Agora Studio Agent ID from `console.agora.io/studio/agents` | [conversational-ai-studio.md](conversational-ai-studio.md) |
| Auth flow, token types, direct REST API (non-SDK languages) | [auth-flow.md](auth-flow.md) |
| Full working demo app architecture, profiles, MLLM/Gemini | [agent-samples.md](agent-samples.md) |
| Web/React client: transcripts, agent state, sendText, interrupt | [agent-toolkit.md](agent-toolkit.md) |
| React hooks in depth (useTranscript, useAgentState, provider) | [agent-client-toolkit-react.md](agent-client-toolkit-react.md) |
| React UI components (voice visualizer, chat UI, video) | [agent-ui-kit.md](agent-ui-kit.md) |
| iOS client: ConversationalAIAPIImpl, Swift | [agent-toolkit-ios.md](agent-toolkit-ios.md) |
| Android client: ConversationalAIAPIImpl, Kotlin | [agent-toolkit-android.md](agent-toolkit-android.md) |
| Custom LLM backend: RAG, tool calling, conversation memory | [server-custom-llm.md](server-custom-llm.md) |
| Persistent per-user memory via MCP | [server-mcp.md](server-mcp.md) |

## REST API Reference

Full request/response details for all endpoints — **always fetch these; do not answer from memory:**

- **[Start Agent (Join)](https://docs-md.agora.io/en/conversational-ai/rest-api/agent/join.md)** — POST /join: start agent with LLM/TTS/ASR config
- **[Stop Agent (Leave)](https://docs-md.agora.io/en/conversational-ai/rest-api/agent/leave.md)** — POST /leave: stop agent
- **[Update Agent](https://docs-md.agora.io/en/conversational-ai/rest-api/agent/update.md)** — POST /update: update token, LLM config
- **[Query Agent Status](https://docs-md.agora.io/en/conversational-ai/rest-api/agent/query.md)** — GET /agents/{id}: query status
- **[List Agents](https://docs-md.agora.io/en/conversational-ai/rest-api/agent/list.md)** — GET /agents: list with filters
- **[Broadcast Message (Speak)](https://docs-md.agora.io/en/conversational-ai/rest-api/agent/speak.md)** — POST /speak: broadcast TTS
- **[Interrupt Agent](https://docs-md.agora.io/en/conversational-ai/rest-api/agent/interrupt.md)** — POST /interrupt
- **[Conversation History](https://docs-md.agora.io/en/conversational-ai/rest-api/agent/history.md)** — GET /history

## Production: Platform Webhooks

The ConvoAI platform can POST event notifications to your server endpoint when agent state changes. These are distinct from:
- The SDK's in-process `session.on()` events (fire in your Node.js/Python/Go process)
- The client toolkit's `AGENT_STATE_CHANGED` event (fires in the browser via RTM)

Webhooks are the correct pattern for **production stateless deployments** where you do not hold the `AgentSession` object in memory between requests. Your server receives a POST when agent state changes, correlates using the agent ID (returned by `session.start()` / the `/join` response), and updates your application state accordingly.

Webhook payload schemas and registration are REST API surface — do not rely on inline content here. Fetch from the Agora docs:

```
GET https://docs-md.agora.io/en/conversational-ai/rest-api/agent/join.md
```

or via MCP: search for "conversational AI webhook" in the Agora docs tool.

## Agent Configuration (join payload `properties` object)

Fetch these before answering questions about vendor configs, model names, or join payload fields:

- **[Custom LLM Guide](https://docs-md.agora.io/en/conversational-ai/develop/custom-llm.md)** — LLM vendor, model, url, api_key, system prompt, greeting, style; TTS vendor, model, voice settings; ASR vendor, language, model
- **[Gemini Live MLLM](https://docs-md.agora.io/en/conversational-ai/models/mllm/gemini.md)** — Multimodal: vendor, model, credentials, location
- **[Join Endpoint (full schema)](https://docs-md.agora.io/en/conversational-ai/rest-api/agent/join.md)** — Complete properties schema: channel, token, turn detection, VAD, tools, avatars, encryption, filler words
- **[Release Notes](https://docs-md.agora.io/en/conversational-ai/overview/release-notes.md)** — New parameters and features
