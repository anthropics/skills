# ConvoAI Studio Agent ID

Use this file when the user already has an **Agora Studio Agent ID** from:

<https://console.agora.io/studio/agents>

This is the Agora-version analogue of a preconfigured agent path: the Studio-managed agent
configuration already exists, so quickstart should avoid rebuilding the provider stack from
scratch unless the user explicitly asks to replace it.

## What It Is

- **Studio Agent ID**: identifies an agent configuration created or managed in Agora Studio.
- **Runtime `agent_id`**: identifies a live started agent session returned by the ConvoAI REST API.
- **Request field mapping**: when reusing an Agora Studio-managed agent in the start flow, pass the Studio Agent ID via the request field `pipeline_id`.

These are **not** interchangeable.

## When to Use This Path

Use the Studio Agent ID path when:

- the user explicitly says they already have an Agent ID from the Studio Agents page
- the user wants to reuse an agent configured in Studio
- the user does not want to re-enter STT / LLM / TTS provider details during quickstart

Do **not** use this path when:

- the user only has the runtime `agent_id` returned by `/join`
- the user still needs to choose or build the provider stack from scratch

## Quickstart Rules

If the Studio Agent ID path is chosen:

1. Treat Agora Studio as the source of truth for the agent configuration.
2. Do not re-ask provider-vendor questions unless the user explicitly wants to replace the Studio-managed config.
3. Keep the client and auth path aligned with the chosen quickstart baseline (`full-stack-nextjs`, `separate-backend-frontend`, or `existing-app-integration`).
4. Use the Studio Agent ID as `pipeline_id` in the request body.
5. Before generating exact request code, still verify the current official ConvoAI docs for any other request-shape changes. Do not fabricate undocumented fields beyond the confirmed `pipeline_id` mapping.

## Goal

Reuse the official sample repo as the structural baseline, but replace the default provider-selection path with the user's existing Studio-managed agent path.

This flow is for implementation after quickstart confirms the user already has a Studio Agent ID. Do not send the user back to provider selection unless they explicitly want to replace the Studio-managed config.

## User-Facing Guidance

Suggested explanation:

```text
If you already configured the agent in Agora Studio, we can treat Studio as the source of truth for the agent configuration and avoid rebuilding the provider stack from scratch here.

Open `https://console.agora.io/studio/agents`, find the agent you want to reuse, and copy its Agent ID.
```

## Request Shape Rule

For this Studio path, use the same request-field convention as the parallel preconfigured-agent flow:

- copy the **Agent ID** from `https://console.agora.io/studio/agents`
- pass that value as `pipeline_id` in the request body

In other words:

- **Studio UI name**: `Agent ID`
- **Request field name**: `pipeline_id`

## Current Request Shape

Current fixed request shape for the Studio Agent ID path:

```text
POST https://api.agora.io/api/conversational-ai-agent/v2/projects/{AGORA_APP_ID}/join
Authorization: agora token={RTC_HEADER_TOKEN}
Content-Type: application/json

{
  "name": "{channel}",
  "pipeline_id": "{AGORA_STUDIO_AGENT_ID}",
  "properties": {
    "agent_rtc_uid": "{agent_rtc_uid}",
    "channel": "{channel}",
    "remote_rtc_uids": ["*"],
    "token": "{RTC_AGENT_TOKEN}"
  }
}
```

Field mapping rules:

| Request field | Source |
|---|---|
| URL project segment | Existing `AGORA_APP_ID` |
| `Authorization` header token | RTC token generated with the caller/user UID using the sample's existing token-generation path |
| `name` | Same value as `channel` |
| `pipeline_id` | `AGORA_STUDIO_AGENT_ID` copied from `https://console.agora.io/studio/agents` |
| `properties.agent_rtc_uid` | Runtime RTC UID string |
| `properties.channel` | Runtime channel value |
| `properties.remote_rtc_uids` | `["*"]` unless the user asks for specific UIDs |
| `properties.token` | Separate RTC token generated with the agent UID using the sample's existing token-generation path |

Do not reintroduce the old provider-based `llm`, `tts`, or `asr` request blocks in this Studio-managed path.
Do not reuse one RTC token for both the `Authorization` header and `properties.token`.

## Expected Success Response

Code generated for this flow should expect and preserve the standard live-agent response fields:

- `agent_id`
- `create_ts`
- `status`

## Minimum Contract

For the Studio-managed path, the skill may assume:

- the Studio Agent ID value is supplied by the user
- that value maps to `pipeline_id`
- the runtime `agent_id` is still returned by the live start/join flow and must not be confused with the Studio Agent ID

## Env and Config Rules

- Prefer `AGORA_STUDIO_AGENT_ID` as the config key / placeholder name in code or env templates.
- Reuse the sample's existing `AGORA_APP_ID` and token-generation path.
- Remove or bypass provider-only config when it is only used for the old three-stage selection flow.
- Keep the sample's existing config style; do not invent a second config-loading layer just for `AGORA_STUDIO_AGENT_ID`.
- Treat `AGORA_STUDIO_AGENT_ID` as a user-filled config value. Add the placeholder, but do not ask the user to paste the live value into the conversation after it has already been identified.

## Implementation Guardrails

- Do not confuse the Studio Agent ID with the runtime `agent_id`.
- Do not replace `pipeline_id` with `agent_id` in request generation.
- Do not hardcode the `Authorization` token or the RTC `properties.token`; both must come from the runtime token path.
- Before code generation, fetch the current official ConvoAI docs / OpenAPI and verify:
  - any other required body fields around `pipeline_id`
  - whether Studio-managed agents require additional prerequisites or restrictions
  - the current response shape

## Implementation Workflow

1. Keep the chosen quickstart baseline (`full-stack-nextjs`, `separate-backend-frontend`, or `existing-app-integration`) as the structural baseline.
2. Inspect the repo's actual env/config files and the current request path that starts the agent.
3. Replace only the provider-selection-specific request/config path with the fixed Studio Agent ID request shape in this file.
4. Generate the new request code from the fixed shape above, preserving:
   - `POST /api/conversational-ai-agent/v2/projects/{appId}/join`
   - `Authorization: agora token=...`
   - JSON body with `name`, `pipeline_id`, and `properties`
5. Map dynamic fields to runtime/config sources:
   - `name` → same value as `channel`
   - `pipeline_id` → `AGORA_STUDIO_AGENT_ID`
   - URL project segment → `AGORA_APP_ID`
   - `Authorization` header token → RTC token generated with the caller/user UID
   - `properties.token` → separate RTC token generated with the agent UID
   - `channel` / `agent_rtc_uid` → runtime values
6. Parse and preserve `agent_id`, `create_ts`, and `status` from the response.
7. Keep the rest of the repo structure and RTC/UI flow as close to the sample as possible.

## After This Step

Once the Studio Agent ID is collected:

- keep quickstart in the selected baseline path
- use the official current ConvoAI docs to verify the exact start flow
- then continue with the appropriate backend/client reference:
  - [server-sdks.md](server-sdks.md)
  - [python-sdk.md](python-sdk.md)
  - [go-sdk.md](go-sdk.md)
  - [agent-samples.md](agent-samples.md)
