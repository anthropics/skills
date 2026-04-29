---
name: agora-agent-client-toolkit
description: |
  Client-side TypeScript SDK for adding Agora Conversational AI features to applications
  already using the Agora RTC SDK. Use when the user needs to integrate agora-agent-client-toolkit
  or agora-agent-client-toolkit-react, receive transcripts, track agent state, send messages
  to an AI agent, handle agent events, or build a ConvoAI front-end client. Triggers on
  agora-agent-client-toolkit, AgoraVoiceAI, useConversationalAI, useTranscript, useAgentState,
  agent transcript, agent state, TRANSCRIPT_UPDATED, AGENT_STATE_CHANGED, ConversationalAIProvider.
license: MIT
metadata:
  author: agora
  version: '1.0.0'
---

# Agent Client Toolkit

Client-side SDK for adding Agora Conversational AI features to applications already using the Agora RTC SDK. Runs in the browser — adds transcript rendering, agent state tracking, and RTM-based messaging controls on top of `agora-rtc-sdk-ng`.

**npm:** `agora-agent-client-toolkit` (core) · `agora-agent-client-toolkit-react` (React hooks)
**Repo:** <https://github.com/AgoraIO-Conversational-AI/agent-client-toolkit-ts>

> This toolkit is a **client add-on** — it does not start agents. Start agents via the ConvoAI REST API first. See [README.md](README.md) for the REST API.

## Installation

```bash
npm install agora-agent-client-toolkit agora-rtc-sdk-ng agora-rtm

# React
npm install agora-agent-client-toolkit-react agora-rtc-react
```

## Initialization

`AgoraVoiceAI.init()` is **async** — always `await` it. Pass the RTC client you already have.

```typescript
import AgoraRTC from 'agora-rtc-sdk-ng';
import AgoraRTM from 'agora-rtm';
import { AgoraVoiceAI } from 'agora-agent-client-toolkit';

// Your existing RTC + RTM setup
const rtcClient = AgoraRTC.createClient({ mode: 'rtc', codec: 'vp8' });
const rtmClient = new AgoraRTM.RTM('APP_ID', 'RTM_USER_ID'); // must match the RTM token subject; often String(rtcUid)
await rtmClient.login({ token: 'RTM_TOKEN' });

// Initialize the toolkit — pass your existing clients
const ai = await AgoraVoiceAI.init({
  rtcEngine: rtcClient,
  rtmConfig: { rtmEngine: rtmClient }, // optional — needed for sendText/interrupt
});

// Join + publish via RTC directly (toolkit does not wrap join/publish)
await rtcClient.join('APP_ID', 'CHANNEL', 'RTC_TOKEN', null);
const micTrack = await AgoraRTC.createMicrophoneAudioTrack();
await rtcClient.publish([micTrack]);

// Start receiving agent messages
ai.subscribeMessage('CHANNEL');
```

## Configuration

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `rtcEngine` | `IAgoraRTCClient` | Yes | Your existing Agora RTC client |
| `rtmConfig` | `{ rtmEngine: RTMClient }` | No | Pass your RTM client for sendText/interrupt |
| `renderMode` | `TranscriptHelperMode` | No | `TEXT`, `WORD`, `CHUNK`, `AUTO` (default: `AUTO`) — see table below |
| `enableLog` | `boolean` | No | Debug logging (default: `false`) |
| `enableAgoraMetrics` | `boolean` | No | Load `@agora-js/report` for usage metrics |

### Render Modes

| Mode | Update cadence | Word timing in metadata | PTS required | When to use |
|------|---------------|------------------------|--------------|-------------|
| `TEXT` | Per sentence (`final: true`) | No | No | Lowest overhead; subtitles |
| `WORD` | Per word | Yes (`words[].start_ms`, `duration_ms`) | **Yes** (before RTC client creation) | Karaoke-style highlight |
| `CHUNK` | When all parts reassembled | No | No | Fragmented transport |
| `AUTO` | Detected from first message | Depends on detected mode | If WORD detected | Default; fine unless you need WORD and must pre-configure PTS |

## Events

Register handlers before calling `subscribeMessage()`. All 9 events:

```typescript
import { AgoraVoiceAIEvents } from 'agora-agent-client-toolkit';

// Transcript — delivers FULL history every time, replace don't append
ai.on(AgoraVoiceAIEvents.TRANSCRIPT_UPDATED, (transcript) => {
  renderTranscript(transcript);
});

// Agent state — requires RTM + enable_rtm: true in agent start config
ai.on(AgoraVoiceAIEvents.AGENT_STATE_CHANGED, (agentUserId, event) => {
  // event.state: 'idle' | 'listening' | 'thinking' | 'speaking' | 'silent'
  updateStatusUI(event.state);
});

// Agent interrupted (user cut off agent's response)
ai.on(AgoraVoiceAIEvents.AGENT_INTERRUPTED, (agentUserId, event) => {
  // event: { turnID: number, timestamp: number }
});

// Performance metrics — requires enable_metrics: true in agent start config
ai.on(AgoraVoiceAIEvents.AGENT_METRICS, (agentUserId, metrics) => {
  // metrics: { type: ModuleType, name: string, value: number, timestamp: number }
  // ModuleType: 'llm' | 'mllm' | 'tts' | 'context' | 'unknown'
});

// Agent pipeline error — requires enable_error_message: true in agent start config
ai.on(AgoraVoiceAIEvents.AGENT_ERROR, (agentUserId, error) => {
  // error: { type: ModuleType, code: number, message: string, timestamp: number }
  showErrorToast(error.message);
});

// Message delivery receipt — requires RTM
ai.on(AgoraVoiceAIEvents.MESSAGE_RECEIPT_UPDATED, (agentUserId, receipt) => {});

// RTM message delivery failure
ai.on(AgoraVoiceAIEvents.MESSAGE_ERROR, (agentUserId, error) => {});

// Speech Activity Level registration status — requires RTM
ai.on(AgoraVoiceAIEvents.MESSAGE_SAL_STATUS, (agentUserId, salStatus) => {});

// Internal debug log
ai.on(AgoraVoiceAIEvents.DEBUG_LOG, (message) => {});
```

## Sending Messages & Interrupting

Requires `rtmConfig` — throws `RTMRequiredError` if called without RTM.

```typescript
import { ChatMessageType, ChatMessagePriority } from 'agora-agent-client-toolkit';

// Send text to the agent
await ai.sendText(agentUserId, {
  messageType: ChatMessageType.TEXT,
  text: 'What is the weather like today?',
  priority: ChatMessagePriority.INTERRUPTED, // interrupts current agent speech
  responseInterruptable: true,
});

// Send image to the agent
await ai.sendImage(agentUserId, {
  messageType: ChatMessageType.IMAGE,
  uuid: crypto.randomUUID(), // caller-generated unique ID for receipt correlation
  url: 'https://example.com/image.png', // or: base64: '<inline data>'
});

// Interrupt the agent's current speech
await ai.interrupt(agentUserId);
```

### `ChatMessagePriority` values

| Value | Behavior |
|-------|----------|
| `INTERRUPTED` | Sends the message and immediately interrupts any speech the agent is currently producing |
| `APPEND` | Queues the message to be processed after the agent finishes its current speech turn |
| `IGNORE` | Drops the message silently if the agent is busy — use for low-priority updates only relevant when idle |

`responseInterruptable: boolean` on `ChatMessageText` — when `true`, the agent's response to this message can itself be interrupted by subsequent user input.

### `ChatMessageImage` fields

| Field | Required | Description |
|-------|----------|-------------|
| `messageType` | Yes | Must be `ChatMessageType.IMAGE` |
| `uuid` | Yes | Caller-generated unique ID for receipt correlation via `MESSAGE_RECEIPT_UPDATED` |
| `url` | One of url/base64 | Publicly accessible image URL |
| `base64` | One of url/base64 | Inline image data |

## Cleanup

```typescript
ai.unsubscribe(); // stop receiving channel messages
ai.destroy();     // remove all event handlers, clear singleton

await rtmClient.logout(); // you manage RTM lifecycle
```

## Critical Rules

1. **`init()` is async** — always `await AgoraVoiceAI.init()`. Missing the await causes `getInstance()` to throw `NotInitializedError`.
2. **Register events before `subscribeMessage()`** — events from messages already in the stream will be missed otherwise.
3. **Transcript replaces, never appends** — `TRANSCRIPT_UPDATED` delivers the complete history every time. Set state to the full array, not `prev.concat(next)`.
4. **`AgoraVoiceAI` is a singleton** — calling `init()` twice replaces the first instance. Call `destroy()` before re-initializing.
5. **RTM is optional but required for several features** — `sendText`, `sendImage`, and `interrupt` throw `RTMRequiredError` without `rtmConfig`. `AGENT_STATE_CHANGED`, `MESSAGE_RECEIPT_UPDATED`, `MESSAGE_ERROR`, `MESSAGE_SAL_STATUS` only fire with RTM.
6. **Agent start config flags are required for some events** — `AGENT_STATE_CHANGED` requires `advanced_features.enable_rtm: true` AND `parameters.data_channel: "rtm"`. `AGENT_METRICS` requires `parameters.enable_metrics: true`. `AGENT_ERROR` requires `parameters.enable_error_message: true`.
7. **Toolkit does not wrap join/publish** — call `rtcClient.join()` and `rtcClient.publish()` yourself before `subscribeMessage()`.
8. **WORD mode requires PTS metadata enabled before RTC client creation** — if `renderMode` is `TranscriptHelperMode.WORD`, call `AgoraRTC.setParameter('ENABLE_AUDIO_PTS_METADATA', true)` before calling `AgoraRTC.createClient()`. Setting it after client creation produces no error — word-level timing data simply never arrives. This also applies when using `AUTO` mode if WORD is detected; prefer explicit `WORD` mode when karaoke display is required so the pre-configuration step is obvious.
9. **RTM identity must match the RTM token subject** — if your RTM token was minted for `String(rtcUid)`, create or log in the RTM client with that same identity. Do not mint an RTM token for one user and log in RTM with another random ID; that can show up as generic conversation-start failures instead of a clear auth error.

## React Hooks

For React integration, see **[agent-client-toolkit-react.md](agent-client-toolkit-react.md)**.
