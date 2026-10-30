---
name: agora-server-sdk-python
description: |
  Python SDK for Agora Conversational AI server-side integration. Use when the user is
  building a Python backend to start/stop/manage ConvoAI agents. Triggers on:
  agora-agent Python, agent_server_sdk_python, AsyncAgora, AsyncAgentSession, pip install
  agora-agent, Python ConvoAI server, agora_agent.
license: MIT
metadata:
  author: agora
  version: '1.1.0'
---

# ConvoAI Server SDK — Python

Python SDK for managing Agora Conversational AI agents from a server-side application. Wraps the ConvoAI REST API.

**Package:** `agora-agent`
**Repo:** <https://github.com/AgoraIO-Conversational-AI/agent-server-sdk-python>

## Installation

```bash
pip install agora-agent
# or with Poetry:
poetry add agora-agent
```

## Sync vs Async

Two parallel APIs exist:

| Use case | Classes |
|----------|---------|
| Sync (scripts, Flask, Django) | `Agora`, `AgentSession` |
| Async (FastAPI, aiohttp, asyncio apps) | `AsyncAgora`, `AsyncAgentSession` |

**Rule:** use the async variants in any async framework. Mixing sync calls into an async event loop blocks it.

## Async Example

```python
import asyncio
from agora_agent import AsyncAgora, Agent
from agora_agent.agentkit import OpenAI, ElevenLabsTTS, DeepgramSTT

async def main():
    client = AsyncAgora(
        app_id="YOUR_APP_ID",
        app_certificate="YOUR_APP_CERTIFICATE",  # App Credentials mode
    )

    agent = (
        Agent(name="my_agent", instructions="You are a helpful voice assistant.")
        .with_stt(DeepgramSTT(api_key="DEEPGRAM_KEY"))
        .with_llm(OpenAI(api_key="OPENAI_KEY"))
        .with_tts(ElevenLabsTTS(api_key="ELEVENLABS_KEY"))
    )

    session = agent.create_session(channel="my-channel", agent_uid=0)

    agent_id = await session.start()
    print(f"Agent started: {agent_id}")

    # Later — stop from the same process
    await session.stop()

    # Or stop from a stateless handler (different request)
    await client.stop_agent(agent_id)

asyncio.run(main())
```

For the first-success default combo, use the quickstart guidance in [quickstarts.md](quickstarts.md). For the current provider matrix and vendor-specific configuration details, use the official live ConvoAI provider docs rather than maintaining a local copy in this SDK usage file.

## Naming Conventions

All method names are snake_case — same API surface as TypeScript but with Python naming:

| TypeScript | Python |
|-----------|--------|
| `session.start()` | `session.start()` |
| `session.stop()` | `session.stop()` |
| `session.getHistory()` | `session.get_history()` |
| `session.getInfo()` | `session.get_info()` |
| `client.generateRtcToken()` | `client.generate_rtc_token()` |

## Deprecation Warnings

Three patterns generate `DeprecationWarning` at runtime. Suppress them by migrating to the replacement:

| Deprecated | Replacement |
|-----------|-------------|
| `TurnDetection.type` field | Use `config.start_of_speech` / `config.end_of_speech` directly |
| `InterruptMode` on standard LLM sessions | Only valid for MLLM with `server_vad` or `semantic_vad` |
| `Eagerness` parameter | MLLM-only — remove from standard LLM configs |

## Debug Logging

```python
client = AsyncAgora(
    app_id="YOUR_APP_ID",
    app_certificate="YOUR_APP_CERTIFICATE",
    debug=True,  # enables request/response logging
)
# Auth headers are redacted automatically — logs show "Basic ***", not the actual value
```

## Auth Modes

Same three modes as TypeScript. Pass exactly one:

```python
# App Credentials (recommended) — SDK generates ConvoAI token per request
client = AsyncAgora(app_id="...", app_certificate="...")

# Token Auth — you supply a pre-built combined RTC+RTM token; reused until replaced
client = AsyncAgora(app_id="...", auth_token="YOUR_TOKEN")

# Basic Auth — Customer ID + Secret; for testing only
client = AsyncAgora(app_id="...", customer_id="...", customer_secret="...")
```
