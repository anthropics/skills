# Agent Samples

Backend + frontend clients for Agora Conversational AI.

**Repo:** <https://github.com/AgoraIO-Conversational-AI/agent-samples>
**Coding Guide:** <https://github.com/AgoraIO-Conversational-AI/agent-samples/blob/main/AGENT.md>

## Prerequisites

- **Node.js >= 20.9.0** — required by Next.js 16 (used by both React clients). The repo includes `.nvmrc`. Run `nvm install` (or `nvm use`) in the repo root to auto-select the correct version. If nvm sourcing fails in non-interactive shells, use the full binary path: `$NVM_DIR/versions/node/v<VERSION>/bin/node`.
- **Python 3.x** — required by simple-backend

## Local Setup Steps

1. Clone: `git clone https://github.com/AgoraIO-Conversational-AI/agent-samples.git`
2. Node.js: `cd agent-samples && nvm install` (reads `.nvmrc`, installs if needed)
3. Backend: `cd simple-backend && python3 -m venv venv && source venv/bin/activate && pip install -r requirements-local.txt && cp .env.example .env`
4. Configure `.env` with `VOICE_*` or `VIDEO_*` credentials (see [Profile System](#profile-system) below)
5. Start backend: `python3 local_server.py` (port 8082)
6. Frontend (voice): `cd react-voice-client && npm install --legacy-peer-deps && npm run dev` (port 8083)
7. Frontend (video+avatar): `cd react-video-client-avatar && npm install --legacy-peer-deps && npm run dev` (port 8084)

> **[AGENT.md — Local Development Quick Start](https://github.com/AgoraIO-Conversational-AI/agent-samples/blob/main/AGENT.md#local-development-quick-start)** — Full details
> **[README — Backend Sample](https://github.com/AgoraIO-Conversational-AI/agent-samples#backend-sample)** — Setup overview

## Backend (simple-backend/)

- Python Flask server on port 8082
- Profile-based config system (`<PROFILE>_<VARIABLE>`)
- Agent lifecycle management, token generation
- `AGENT_AUTH_HEADER` — sets the `Authorization` header on ConvoAI REST API calls. Now optional: if not set, the backend auto-generates an Agora token (`agora token=<AccessToken2>`) from `APP_ID` + `APP_CERTIFICATE`. Override only if you need Basic Auth (`Basic <base64(customerId:secret)>`) or lack an App Certificate. See [ConvoAI Authentication](./README.md#authentication) for context.

> **[AGENT.md — Backend Configuration](https://github.com/AgoraIO-Conversational-AI/agent-samples/blob/main/AGENT.md#backend-configuration)** — Profile system, variable naming, active profiles

## Profile System

- Default profiles: `VOICE` (Rime TTS + OpenAI), `VIDEO` (ElevenLabs + GPT-4o + HeyGen)
- Profile names are case-insensitive
- Client sends `profile=VOICE` → backend loads all `VOICE_*` env vars
- `NEXT_PUBLIC_DEFAULT_PROFILE` env var overrides the client's default profile
- URL params: `?profile=VOICE` overrides profile selection, `?autoconnect=true` auto-starts conversation

> **[AGENT.md — Profile System Mechanics](https://github.com/AgoraIO-Conversational-AI/agent-samples/blob/main/AGENT.md#profile-system-mechanics)**

## MLLM / Gemini Live Configuration

- Required vars: `VOICE_ENABLE_MLLM`, `VOICE_MLLM_VENDOR`, `VOICE_MLLM_MODEL`, `VOICE_MLLM_LOCATION` (NOT REGION!)
- `MLLM_LOCATION` not `MLLM_REGION` — the backend expects LOCATION

> **[AGENT.md — Required MLLM Variables](https://github.com/AgoraIO-Conversational-AI/agent-samples/blob/main/AGENT.md#required-mllm-variables-for-gemini-live)**
> **[AGENT.md — Configuration Translation Guide](https://github.com/AgoraIO-Conversational-AI/agent-samples/blob/main/AGENT.md#configuration-translation-guide)**

## OpenAI Realtime MLLM

Alternative to Gemini Live for multimodal voice:
- `MLLM_VENDOR=openai`, `MLLM_MODEL=gpt-4o-realtime-preview`
- Built-in TTS (no separate TTS vendor needed), set voice with `MLLM_VOICE=alloy`

> **[AGENT.md — MLLM Configuration](https://github.com/AgoraIO-Conversational-AI/agent-samples/blob/main/AGENT.md#required-mllm-variables-for-gemini-live)**

## React Voice Client (react-voice-client/)

- Next.js voice AI client, port 8083
- Uses `@agora/conversational-ai` + `@agora/agent-ui-kit`

## React Video Client (react-video-client-avatar/)

- Next.js video+avatar client, port 8084
- HeyGen/Anam avatar integration

## Simple HTML Clients

- `simple-voice-client-no-backend/` — standalone, no backend needed
- `simple-voice-client-with-backend/` — uses simple-backend

## Debugging Agent Failures

- RTM error `-11033: user offline` → agent failed to create (400 from Agora API)
- Check backend logs for `Response status: 400`
- Common: missing `location` field in MLLM config

> **[AGENT.md — Debugging Agent Creation Failures](https://github.com/AgoraIO-Conversational-AI/agent-samples/blob/main/AGENT.md#debugging-agent-creation-failures)**

## Production Deployment (EC2 + nginx)

- Gotcha: `NEXT_PUBLIC_*` env vars must be set at both **build time** AND runtime for Next.js

> **[AGENT.md — Production Deployment](https://github.com/AgoraIO-Conversational-AI/agent-samples/blob/main/AGENT.md#production-deployment-ec2--nginx-on-port-443)** — nginx config, PM2 ecosystem, basePath, gotchas

## Companion Servers

- **server-custom-llm** → see [server-custom-llm.md](server-custom-llm.md)
- **server-mcp** → see [server-mcp.md](server-mcp.md)

## Port Reference

| Server | Port |
|--------|------|
| simple-backend | 8082 |
| react-voice-client | 8083 |
| react-video-client-avatar | 8084 |
