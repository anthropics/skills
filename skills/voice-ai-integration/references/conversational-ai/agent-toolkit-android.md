# ConvoAI Agent Toolkit — Android (Kotlin)

The Android agent toolkit (`ConversationalAIAPIImpl`) wraps RTC + RTM to deliver AI transcripts, agent state, interrupts, and metrics. It is sourced from the Conversational AI Demo repo — not from the Agora SDK packages.

Source: `convoaiApi/IConversationalAIAPI.kt` and `ConversationalAIAPIImpl.kt` in the demo repo.

## Table of Contents

- [Setup](#setup)
- [Initialization](#initialization)
- [Audio Configuration](#audio-configuration)
- [Subscribing to Events](#subscribing-to-events)
- [Sending Messages to the Agent](#sending-messages-to-the-agent)
- [Interrupting the Agent](#interrupting-the-agent)
- [Handling Events](#handling-events)
- [Cleanup](#cleanup)

## Setup

The toolkit takes an existing `RtcEngine` and `RtmClient` — initialize both SDKs first.

```kotlin
import io.agora.rtc2.RtcEngine
import io.agora.rtm.RtmClient
// Copy or import from the demo repo:
// io.agora.scene.convoai.convoaiApi.*
```

## Initialization

```kotlin
// 1. Create your RTC engine and RTM client first (standard SDK init)
val rtcEngine: RtcEngine = // ... your existing engine
val rtmClient: RtmClient = // ... your existing RTM client (already logged in)

// 2. Create the toolkit config
val config = ConversationalAIAPIConfig(
    rtcEngine = rtcEngine,
    rtmClient = rtmClient,
    renderMode = TranscriptRenderMode.Word,   // Word (word-by-word) or Text (full sentence)
    enableLog = true,
    enableRenderModeFallback = true           // fall back to Text if server lacks word timestamps
)

// 3. Create the API instance
val api = ConversationalAIAPIImpl(config)

// 4. Register your event handler
api.addHandler(eventHandler)
```

## Audio Configuration

**Must be called before `rtcEngine.joinChannel()`** to configure optimal AI audio settings.

```kotlin
// Standard ConvoAI mode
api.loadAudioSettings()
// Equivalent to: api.loadAudioSettings(Constants.AUDIO_SCENARIO_AI_CLIENT)

// If using Avatar (requires audio mixing)
api.loadAudioSettings(Constants.AUDIO_SCENARIO_DEFAULT)

// Then join RTC channel
rtcEngine.joinChannel(token, channelName, uid, channelMediaOptions)
```

## Subscribing to Events

Subscribe after logging in to RTM and before the agent starts speaking.

```kotlin
api.subscribeMessage(channelName) { error ->
    if (error != null) {
        Log.e("ConvoAI", "Subscribe failed: ${error.errorMessage}")
        return@subscribeMessage
    }
    Log.d("ConvoAI", "Subscribed — ready to receive agent events")
}

// When done
api.unsubscribeMessage(channelName) { error -> }
```

## Sending Messages to the Agent

```kotlin
// Text message (default priority: INTERRUPT)
val textMsg = TextMessage(
    text = "What is the weather today?",
    priority = Priority.INTERRUPT,
    responseInterruptable = true
)
api.chat(agentUserId, textMsg) { error ->
    if (error != null) Log.e("ConvoAI", "Chat failed: ${error.errorMessage}")
}

// Text with APPEND priority (queue after current response)
val appendMsg = TextMessage(text = "And tomorrow?", priority = Priority.APPEND)
api.chat(agentUserId, appendMsg) { }

// Image message (URL-based; keep base64 under 32KB total)
val imageMsg = ImageMessage(uuid = UUID.randomUUID().toString(), imageUrl = "https://example.com/photo.jpg")
api.chat(agentUserId, imageMsg) { error -> }
```

## Interrupting the Agent

```kotlin
api.interrupt(agentUserId) { error ->
    if (error != null) Log.e("ConvoAI", "Interrupt failed: ${error.errorMessage}")
}
```

## Handling Events

Implement `IConversationalAIAPIEventHandler`:

```kotlin
val eventHandler = object : IConversationalAIAPIEventHandler {

    // Agent state: IDLE | SILENT | LISTENING | THINKING | SPEAKING | UNKNOWN
    override fun onAgentStateChanged(agentUserId: String, event: StateChangeEvent) {
        Log.d("ConvoAI", "Agent $agentUserId state: ${event.state}, turn: ${event.turnId}")
        runOnUiThread { updateStateIndicator(event.state) }
    }

    // Transcript update (fires frequently — dedup by turnId if needed)
    override fun onTranscriptUpdated(agentUserId: String, transcript: Transcript) {
        // transcript.type: TranscriptType.AGENT or .USER
        // transcript.status: IN_PROGRESS | END | INTERRUPTED | UNKNOWN
        // transcript.renderMode: Word or Text
        runOnUiThread { updateTranscriptUI(transcript) }
    }

    // Agent interrupted mid-speech
    override fun onAgentInterrupted(agentUserId: String, event: InterruptEvent) {
        Log.d("ConvoAI", "Interrupted turn: ${event.turnId}")
    }

    // Performance metrics (LLM/TTS latency)
    override fun onAgentMetrics(agentUserId: String, metric: Metric) {
        Log.d("ConvoAI", "Metric: ${metric.type} ${metric.name} = ${metric.value}ms")
    }

    // Agent-side error (LLM/TTS failure)
    override fun onAgentError(agentUserId: String, error: ModuleError) {
        Log.e("ConvoAI", "Agent error: ${error.type} code=${error.code} ${error.message}")
    }

    // Message send error (e.g., image too large)
    override fun onMessageError(agentUserId: String, error: MessageError) {
        Log.e("ConvoAI", "Message error: ${error.chatMessageType} code=${error.code}")
    }

    // Message receipt (server acknowledged image/text)
    override fun onMessageReceiptUpdated(agentUserId: String, receipt: MessageReceipt) {
        Log.d("ConvoAI", "Receipt: ${receipt.type} turnId=${receipt.turnId}")
    }

    // Voiceprint registration status (technical preview)
    override fun onAgentVoiceprintStateChanged(agentUserId: String, event: VoiceprintStateChangeEvent) {
        Log.d("ConvoAI", "Voiceprint: ${event.status}")
    }

    // Internal debug messages — useful during development
    override fun onDebugLog(log: String) {
        Log.v("ConvoAI", log)
    }
}
```

## Cleanup

```kotlin
fun cleanup() {
    api.unsubscribeMessage(channelName) { }
    api.removeHandler(eventHandler)
    api.destroy()
}
```

Call `destroy()` when the conversation session ends. After this call the instance cannot be reused.

## Key Types Reference

| Type | Purpose |
|------|---------|
| `ConversationalAIAPIConfig` | Init config: `rtcEngine`, `rtmClient`, `renderMode`, `enableLog` |
| `ConversationalAIAPIImpl` | Concrete implementation — create one per session |
| `IConversationalAIAPIEventHandler` | Interface for receiving all events |
| `TextMessage` | Text to send: `text`, `priority`, `responseInterruptable` |
| `ImageMessage` | Image to send: `uuid`, `imageUrl` or `imageBase64` (≤32KB) |
| `Priority` | `INTERRUPT` / `APPEND` / `IGNORE` |
| `AgentState` | `IDLE` / `SILENT` / `LISTENING` / `THINKING` / `SPEAKING` |
| `Transcript` | `turnId`, `text`, `type` (AGENT/USER), `status`, `renderMode` |
| `TranscriptRenderMode` | `Word` (word-level) or `Text` (full sentence) |
| `StateChangeEvent` | `state`, `turnId`, `timestamp` |
| `Metric` | `type` (LLM/TTS), `name`, `value` (ms), `timestamp` |
| `ConversationalAIAPIError` | Sealed: `RtmError(code, msg)`, `RtcError(code, msg)`, `UnknownError(msg)` |

## Notes

- `onTranscriptUpdated` fires at high frequency. Deduplicate on `turnId` in your UI if needed.
- All callbacks are dispatched on the main thread — safe for UI updates.
- The `renderMode = Word` setting falls back to `Text` automatically if the server doesn't provide word timestamps (when `enableRenderModeFallback = true`).
- Agent state arrives via RTM presence events (REMOTE_STATE_CHANGED); transcripts arrive via RTM channel messages.
- Image payloads via `imageBase64` must keep the total JSON message under 32KB. Use `imageUrl` for larger images.
- Audio routing changes re-apply audio parameters automatically via `onAudioRouteChanged`.
