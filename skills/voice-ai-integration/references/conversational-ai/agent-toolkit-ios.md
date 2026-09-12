# ConvoAI Agent Toolkit — iOS (Swift)

The iOS agent toolkit (`ConversationalAIAPIImpl`) wraps RTC + RTM to deliver AI transcripts, agent state, interrupts, and metrics. It is sourced from the Conversational AI Demo repo — not from the Agora SDK packages.

Source: `ConversationalAIAPI/ConversationalAIAPI.swift` and `ConversationalAIAPIImpl.swift` in the demo repo.

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

The toolkit takes an existing `AgoraRtcEngineKit` and `AgoraRtmClientKit` — initialize both SDKs first.

```swift
import AgoraRtcKit
import AgoraRtmKit
import ConversationalAIAPI // or copy files directly from the demo repo
```

## Initialization

```swift
// 1. Create your RTC engine and RTM client first (standard SDK init)
let rtcEngine: AgoraRtcEngineKit = // ... your existing engine
let rtmKit: AgoraRtmClientKit = // ... your existing RTM client (already logged in)

// 2. Create the toolkit config
let config = ConversationalAIAPIConfig(
    rtcEngine: rtcEngine,
    rtmEngine: rtmKit,
    renderMode: .words,        // .words (word-by-word) or .text (full sentence)
    enableLog: true,
    enableRenderModeFallback: true // fall back to .text if server lacks word timestamps
)

// 3. Create the API instance
let api = ConversationalAIAPIImpl(config: config)

// 4. Register your event handler
api.addHandler(handler: self) // self implements ConversationalAIAPIEventHandler
```

## Audio Configuration

**Must be called before `joinChannel`** on every join to configure optimal AI audio settings.

```swift
// Standard ConvoAI mode
api.loadAudioSettings()
// Equivalent to: api.loadAudioSettings(secnario: .aiClient)

// If using Avatar (requires audio mixing)
api.loadAudioSettings(secnario: .default)

// Then join RTC channel
rtcEngine.joinChannel(byToken: token, channelId: channelName, info: nil, uid: userId)
```

## Subscribing to Events

Subscribe after logging in to RTM and before the agent starts speaking.

```swift
api.subscribeMessage(channelName: channelName) { error in
    if let error = error {
        print("Subscribe failed: \(error)")
        return
    }
    print("Subscribed — ready to receive agent events")
}

// When done
api.unsubscribeMessage(channelName: channelName) { error in }
```

## Sending Messages to the Agent

```swift
// Text message (default priority: INTERRUPT)
let textMsg = TextMessage(
    text: "What is the weather today?",
    priority: .interrupt,
    responseInterruptable: true
)
api.chat(agentUserId: agentUid, message: textMsg) { error in
    if let error = error { print("Chat failed: \(error)") }
}

// Text with APPEND priority (queue after current response)
let appendMsg = TextMessage(text: "And tomorrow?", priority: .append)
api.chat(agentUserId: agentUid, message: appendMsg) { _ in }

// Image message (URL-based; keep base64 under 32KB total)
let imageMsg = ImageMessage(uuid: UUID().uuidString, imageUrl: "https://example.com/photo.jpg")
api.chat(agentUserId: agentUid, message: imageMsg) { error in }
```

## Interrupting the Agent

```swift
api.interrupt(agentUserId: agentUid) { error in
    if let error = error { print("Interrupt failed: \(error)") }
}
```

## Handling Events

Implement `ConversationalAIAPIEventHandler`:

```swift
extension YourViewController: ConversationalAIAPIEventHandler {

    // Agent state: .silent | .listening | .thinking | .speaking | .idle | .unknown
    func onAgentStateChanged(agentUserId: String, event: StateChangeEvent) {
        print("Agent \(agentUserId) state: \(event.state), turn: \(event.turnId)")
        DispatchQueue.main.async {
            self.updateStateIndicator(event.state)
        }
    }

    // Transcript update (fires frequently — dedup by turnId if needed)
    func onTranscriptUpdated(agentUserId: String, transcript: Transcript) {
        // transcript.type: .agent or .user
        // transcript.status: .inProgress | .end | .interrupted | .unknown
        // transcript.renderMode: .words or .text
        DispatchQueue.main.async {
            self.updateTranscriptUI(transcript)
        }
    }

    // Agent interrupted mid-speech
    func onAgentInterrupted(agentUserId: String, event: InterruptEvent) {
        print("Interrupted turn: \(event.turnId)")
    }

    // Performance metrics (LLM/TTS latency)
    func onAgentMetrics(agentUserId: String, metrics: Metric) {
        print("Metric: \(metrics.type) \(metrics.name) = \(metrics.value)ms")
    }

    // Agent-side error (LLM/TTS failure)
    func onAgentError(agentUserId: String, error: ModuleError) {
        print("Agent error: \(error.type) code=\(error.code) \(error.message)")
    }

    // Message send error (e.g., image too large)
    func onMessageError(agentUserId: String, error: MessageError) {
        print("Message error: \(error.chatMessageType) code=\(error.code)")
    }

    // Message receipt (server acknowledged image/text)
    func onMessageReceiptUpdated(agentUserId: String, messageReceipt: MessageReceipt) {
        print("Receipt: \(messageReceipt.type) turnId=\(messageReceipt.turnId)")
    }

    // Voiceprint registration status (technical preview)
    func onAgentVoiceprintStateChanged(agentUserId: String, event: VoiceprintStateChangeEvent) {
        print("Voiceprint: \(event.status)")
    }

    func onDebugLog(log: String) {
        // Internal debug messages — useful during development
    }
}
```

## Cleanup

```swift
func cleanup() {
    api.unsubscribeMessage(channelName: channelName) { _ in }
    api.removeHandler(handler: self)
    api.destroy()
}
```

Call `destroy()` when the conversation session ends. After this call the instance cannot be reused.

## Key Types Reference

| Type | Purpose |
|------|---------|
| `ConversationalAIAPIConfig` | Init config: `rtcEngine`, `rtmEngine`, `renderMode`, `enableLog` |
| `ConversationalAIAPIImpl` | Concrete implementation — create one per session |
| `ConversationalAIAPIEventHandler` | Protocol for receiving all events |
| `TextMessage` | Text to send: `text`, `priority`, `responseInterruptable` |
| `ImageMessage` | Image to send: `uuid`, `imageUrl` or `imageBase64` (≤32KB) |
| `Priority` | `.interrupt` / `.append` / `.ignore` |
| `AgentState` | `.silent` / `.listening` / `.thinking` / `.speaking` |
| `Transcript` | `turnId`, `text`, `type` (agent/user), `status`, `renderMode` |
| `TranscriptRenderMode` | `.words` (word-level) or `.text` (full sentence) |
| `StateChangeEvent` | `state`, `turnId`, `timestamp` |
| `Metric` | `type` (LLM/TTS), `name`, `value` (ms), `timestamp` |

## Notes

- `onTranscriptUpdated` fires at high frequency. Deduplicate on `turnId` in your UI if needed.
- The `renderMode: .words` setting falls back to `.text` automatically if the server doesn't provide word timestamps (when `enableRenderModeFallback: true`).
- Agent state arrives via RTM presence events; transcripts arrive via RTM channel messages.
- Image payloads via `imageBase64` must keep the total JSON message under 32KB. Use `imageUrl` for larger images.
