---
name: agora-agent-client-toolkit-react
description: |
  React hooks for Agora Conversational AI client integration. Use when the user is building
  a React app with Agora ConvoAI and needs agora-agent-client-toolkit-react hooks.
  Triggers on useTranscript, useAgentState, useAgentError, useAgentMetrics,
  ConversationalAIProvider, agora-agent-client-toolkit-react, React ConvoAI hooks,
  agent transcript React, agent state React hook.
license: MIT
metadata:
  author: agora
  version: '1.0.0'
---

# Agent Client Toolkit — React

React hooks for `agora-agent-client-toolkit`. Wraps the `AgoraVoiceAI` singleton into React state and effects. Must be used alongside `agora-rtc-react` — this package handles ConvoAI concerns only, not RTC primitives (mic tracks, camera, remote users).

**npm:** `agora-agent-client-toolkit-react`
**Requires:** `agora-agent-client-toolkit`, `agora-rtc-react`, React >= 18

## Installation

```bash
npm install agora-agent-client-toolkit-react agora-agent-client-toolkit agora-rtc-react agora-rtm
```

## Usage

Use `ConversationalAIProvider` + standalone hooks. The provider manages the `AgoraVoiceAI` lifecycle — standalone hooks connect via context so only the components that need updates re-render.

> For simple single-component cases, `useConversationalAI` is available as a batteries-included alternative. See the [package README](https://github.com/AgoraIO-Conversational-AI/agent-client-toolkit-ts/blob/main/packages/react/README.md) for details.

```tsx
import { useMemo } from 'react';
import AgoraRTC, { AgoraRTCProvider, useJoin, useLocalMicrophoneTrack, usePublish } from 'agora-rtc-react';
import AgoraRTM from 'agora-rtm';
import {
  ConversationalAIProvider,
  useTranscript,
  useAgentState,
  useAgentError,
  useAgentMetrics,
} from 'agora-agent-client-toolkit-react';

const rtcClient = AgoraRTC.createClient({ mode: 'rtc', codec: 'vp8' });
const rtmClient = new AgoraRTM.RTM('APP_ID', 'RTM_USER_ID'); // must match the RTM token subject; often String(rtcUid)
await rtmClient.login({ token: 'RTM_TOKEN' });

function App() {
  const config = useMemo(() => ({
    channel: 'my-channel',
    rtmConfig: { rtmEngine: rtmClient },
  }), []);

  return (
    // AgoraRTCProvider (outer) → ConversationalAIProvider (inner)
    <AgoraRTCProvider client={rtcClient}>
      <ConversationalAIProvider config={config}>
        <VoiceSession />
      </ConversationalAIProvider>
    </AgoraRTCProvider>
  );
}

function VoiceSession() {
  // Agora RTC hooks — your existing integration
  useJoin({ appid: 'APP_ID', channel: 'my-channel', token: 'RTC_TOKEN' });
  const { localMicrophoneTrack } = useLocalMicrophoneTrack();
  usePublish([localMicrophoneTrack]);

  // ConvoAI hooks — added on top
  const transcript = useTranscript();
  const { agentState } = useAgentState();
  const { error, clearError } = useAgentError();
  const { metrics } = useAgentMetrics();

  return (
    <div>
      <p>Agent: {agentState ?? 'idle'}</p>
      {error && <p onClick={clearError}>Error: {error.error.message}</p>}
      <ul>{transcript.map((t) => <li key={t.turn_id}>{t.text}</li>)}</ul>
    </div>
  );
}
```

## Hooks Reference

### `useTranscript()`

Subscribe to transcript updates. Returns the full conversation history — replace, don't append.

```typescript
const transcript = useTranscript();
// transcript: TranscriptHelperItem[]
// Each item: { uid, turn_id, text, status, metadata }
```

### `useAgentState()`

Subscribe to `AGENT_STATE_CHANGED` events.

```typescript
const { agentState, stateEvent, agentUserId } = useAgentState();
// agentState: 'idle' | 'listening' | 'thinking' | 'speaking' | 'silent' | null
// stateEvent: { state, turnID, timestamp, reason } | null
```

Only fires when RTM is configured and agent start config includes `advanced_features.enable_rtm: true` + `parameters.data_channel: "rtm"`.

### `useAgentError()`

Subscribe to `AGENT_ERROR` and `MESSAGE_ERROR` events. Returns a discriminated union.

```typescript
const { error, clearError } = useAgentError();
// error: { source: 'agent', agentUserId, error: ModuleError }
//      | { source: 'message', agentUserId, error: { type, code, message, timestamp } }
//      | null
```

Call `clearError()` after dismissing (e.g. closing a toast).

### `useAgentMetrics()`

Subscribe to `AGENT_METRICS` events.

```typescript
const { metrics, agentUserId } = useAgentMetrics();
// metrics: { type: ModuleType, name: string, value: number, timestamp: number } | null
// ModuleType: 'llm' | 'mllm' | 'tts' | 'context' | 'unknown'
```

Only fires when agent start config includes `parameters.enable_metrics: true`.

## `useConversationalAI` — Batteries-Included Alternative

For simple single-page apps or demos where all ConvoAI state is consumed in one component, `useConversationalAI` is a drop-in alternative to the full Provider + hooks pattern. If multiple components need transcript, agent state, or errors independently, use `ConversationalAIProvider` + standalone hooks instead.

```tsx
import { useConversationalAI } from 'agora-agent-client-toolkit-react';
import { useMemo } from 'react';

function VoiceSession() {
  const config = useMemo(() => ({
    channel: 'my-channel',
    rtmConfig: { rtmEngine: rtmClient },
  }), []);

  const {
    transcript,
    agentState,
    isConnected,
    error,
    interrupt,
    sendMessage,
    metrics,
  } = useConversationalAI(config);

  return (
    <div>
      <p>Agent: {agentState ?? 'idle'}</p>
      <button onClick={() => interrupt(agentUserId)}>Interrupt</button>
      <ul>{transcript.map((t) => <li key={t.turn_id}>{t.text}</li>)}</ul>
    </div>
  );
}
```

**Config stability rule** — same as `ConversationalAIProvider`: wrap config in `useMemo`. The hook re-initializes if the config object identity changes.

The hook internally calls `AgoraVoiceAI.init()`, `subscribeMessage()`, and `destroy()` automatically. No manual lifecycle management needed.

## Critical Rules

1. **Wrap `config` in `useMemo`** — `ConversationalAIProvider` depends on `config.channel`. An inline object creates a new reference every render, causing unnecessary re-init cycles.
2. **`AgoraRTCProvider` must be the outer wrapper** — `ConversationalAIProvider` calls `useRTCClient()` internally and will throw if rendered outside `AgoraRTCProvider`.
3. **All standalone hooks require `ConversationalAIProvider`** — `useTranscript`, `useAgentState`, `useAgentError`, and `useAgentMetrics` won't receive events without it.
4. **Use `agora-rtc-react` for RTC primitives** — mic tracks, camera, remote users, join, and publish are handled by `agora-rtc-react` hooks. This package covers ConvoAI concerns only.
5. **RTM must be logged in before passing to config** — call `rtmClient.login()` before passing `rtmEngine` into the provider config. The provider does not manage RTM login/logout.
6. **RTM userId must match the RTM token subject** — if your server minted the RTM token for `String(rtcUid)`, do not construct `new AgoraRTM.RTM(appId, ...)` with a different user ID. In first-success flows, identity mismatches can bubble up as generic startup failures instead of a clean RTM auth error.
