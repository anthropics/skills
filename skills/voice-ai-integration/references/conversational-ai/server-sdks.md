---
name: agora-convoai-server-sdks
description: |
  Server-side SDKs for Agora Conversational AI: TypeScript, Python, and Go wrappers around the
  ConvoAI REST API. Use when the user is building a backend to start/stop/manage ConvoAI agents.
  Triggers on: agora-agent-server-sdk, AgoraClient, AgentSession, session.start, session.stop,
  agent server SDK, ConvoAI backend, ConvoAI server, withStt, withLlm, withTts.
license: MIT
metadata:
  author: agora
  version: '1.0.0'
---

# ConvoAI Server SDKs

TypeScript, Go, and Python SDKs — convenience wrappers around the ConvoAI REST API. For any other backend language, call the REST API directly. Fetch the live OpenAPI spec for the full schema: `https://docs-md.agora.io/api/conversational-ai-api-v2.x.yaml`

## TypeScript — `agora-agent-server-sdk`

```bash
npm install agora-agent-server-sdk
```

Builder pattern — configure the AI pipeline then create sessions:

```typescript
import { AgoraClient, Agent, Area } from 'agora-agent-server-sdk';

const client = new AgoraClient({
  area: Area.US,
  appId: process.env.AGORA_APP_ID,
  appCertificate: process.env.AGORA_APP_CERTIFICATE,
});

const agent = new Agent({
  name: `agent_${crypto.randomUUID().slice(0, 8)}`, // must be unique per project
  instructions: 'You are a helpful voice assistant.',
  greeting: 'Hello! How can I help you today?',
})
  .withStt(new DeepgramSTT({ apiKey: process.env.DEEPGRAM_API_KEY }))
  .withLlm(new OpenAI({ apiKey: process.env.OPENAI_API_KEY }))
  .withTts(new ElevenLabsTTS({ apiKey: process.env.ELEVENLABS_API_KEY }));

// Start a session (joins the agent to a channel)
const session = agent.createSession({ channel: 'my-channel', agentUid: 0 });
const sessionId = await session.start();

// Stop from the same process
await session.stop();

// Stop from a stateless server (e.g. a different request handler)
await client.stopAgent(sessionId);
```

Token auth is handled automatically when `appCertificate` is provided. For vendor-specific STT/LLM/TTS import paths and MLLM (OpenAI Realtime, Gemini Live) config, see the [SDK README](https://github.com/AgoraIO-Conversational-AI/agent-server-sdk-ts).

## Auth Modes

Three modes, in order of recommendation:

- **App Credentials** (`appId` + `appCertificate`): SDK generates a fresh ConvoAI token per REST call. No token management needed. The App Certificate never leaves your server. Recommended for production.
- **Token Auth** (`authToken`): A pre-built combined RTC+RTM token you supply. This token is **reused for every request** until you replace the SDK instance — the SDK does not refresh it. You are responsible for refreshing before expiry. Max token validity is 24 hours.
- **Basic Auth** (`customerId` + `customerSecret`): Credentials never expire but are long-lived secrets that grant access to every project on your account. Use for local testing only; do not ship to production.

## Session State Machine

Sessions follow a strict state sequence. Calling methods outside the valid states throws an error:

| State | `start()` | `stop()` | `say()` / `interrupt()` / `update()` |
|-------|-----------|----------|---------------------------------------|
| `idle` | ✅ | ❌ | ❌ |
| `starting` | ❌ | ❌ | ❌ |
| `running` | ❌ | ✅ | ✅ |
| `stopping` | ❌ | ❌ | ❌ |
| `stopped` | ✅ | ❌ | ❌ |
| `error` | ✅ | ❌ | ❌ |

`stop()` on a 404 (agent already stopped on the platform) resolves without throwing — the SDK treats it as already stopped.

## In-Process Events (TypeScript)

`AgentSession` emits events within your Node.js process — these are not HTTP webhooks:

```typescript
session.on('started', () => {
  // Agent has connected to the RTC channel and is ready
  // session.id is now set; session.status === 'running'
});

session.on('stopped', () => {
  // Agent has left the channel
});

session.on('error', (err) => {
  // Non-recoverable error; session.status === 'error'
  // Safe to call session.start() again from this state
});
```

## Avatar + TTS Sample Rate

HeyGen and Akool avatars require a specific TTS sample rate. The SDK validates this at `session.start()` and throws if mismatched. The error message identifies the avatar config as the problem — the root cause is actually the TTS sample rate.

| Avatar vendor | Required TTS sample rate |
|--------------|--------------------------|
| HeyGen | **24000 Hz** |
| Akool | **16000 Hz** |

Whenever an avatar vendor is set, explicitly configure the TTS sample rate to match. Do not rely on defaults.

```typescript
// HeyGen — must pair with 24 kHz TTS
const agent = new Agent({ ... })
  .withAvatar(new HeyGen({ ... }))
  .withTts(new ElevenLabsTTS({ sampleRate: 24000, ... }));

// Akool — must pair with 16 kHz TTS
const agent = new Agent({ ... })
  .withAvatar(new Akool({ ... }))
  .withTts(new ElevenLabsTTS({ sampleRate: 16000, ... }));
```

## Python and Go SDKs

- **[python-sdk.md](python-sdk.md)** — Python SDK: sync vs async, deprecation warnings, debug logging.
- **[go-sdk.md](go-sdk.md)** — Go SDK: context.Context pattern, builder syntax, SessionStatus constants, token helpers.
