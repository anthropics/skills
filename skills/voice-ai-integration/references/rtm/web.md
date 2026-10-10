# Agora Signaling SDK — Web (RTM)

## Table of Contents

- [Overview](#overview)
- [Installation](#installation)
- [RTM v2 (Web)](#rtm-v2-web)
- [RTM v1 (Legacy Web)](#rtm-v1-legacy-web)
- [Common Use Cases with RTC](#common-use-cases-with-rtc)
- [Stream Channels (Topics)](#stream-channels-topics)

## Overview

RTM provides signaling, text messaging, presence, and metadata capabilities alongside RTC audio/video. RTC and RTM are **independent systems** — RTC channels and RTM channels are separate namespaces.

**When to use RTM alongside RTC:**

- Text chat during video calls
- Signaling (call invitations, control messages)
- User presence/status tracking
- Custom data exchange (VAD signals, resolution requests)
- Sending text messages to AI agents (Conversational AI)

Package: `agora-rtm` (v2.x) on npm.

## Installation

```bash
npm install agora-rtm
```

## RTM v2 (Web)

### Initialization and Login

```typescript
import AgoraRTM from "agora-rtm"

let rtmClient: AgoraRTM.RTM;
try {
  rtmClient = new AgoraRTM.RTM("your-app-id", "user-id-string", {
    logLevel: "debug", // "debug" | "info" | "warn" | "error"
  });
} catch (status) {
  console.error("RTM init failed", status);
}

// Always login with a server-generated RTM token
await rtmClient.login({ token: 'YOUR_RTM_TOKEN' })
```

### Channel Subscription

```typescript
// Subscribe to a channel to receive messages and presence
await rtmClient.subscribe("channel-name", {
  withMessage: true,
  withPresence: true,
})

// Unsubscribe
await rtmClient.unsubscribe("channel-name")
```

### Sending Messages

```typescript
// Publish to channel (all subscribers receive)
await rtmClient.publish("channel-name", "Hello everyone!", {
  customType: "chat.message",
})

// Publish JSON data
await rtmClient.publish("channel-name", JSON.stringify({
  type: "control",
  action: "mute-all",
}), {
  customType: "control.message",
})

// Peer-to-peer (publish to user topic)
await rtmClient.publish("target-user-id", JSON.stringify({
  message: "Hello!",
  priority: "APPEND",
}), {
  customType: "user.transcription",
  channelType: "USER",
})
```

### Receiving Messages

```typescript
rtmClient.addEventListener("message", (event) => {
  console.log("Message from:", event.publisher)
  console.log("Channel:", event.channelName)
  console.log("Content:", event.message)      // string or Uint8Array
  console.log("Type:", event.customType)

  // Parse if JSON
  if (typeof event.message === "string") {
    try {
      const data = JSON.parse(event.message)
    } catch {}
  }
})
```

### Presence Events

```typescript
rtmClient.addEventListener("presence", (event) => {
  // event.eventType: "SNAPSHOT" | "INTERVAL" | "JOIN" | "LEAVE" | "TIMEOUT" | "STATE_CHANGED"

  switch (event.eventType) {
    case "SNAPSHOT":
      // Initial state on subscribe — event.snapshot is an array of {userId, states}
      for (const user of event.snapshot) {
        console.log("Online:", user.userId, user.states)
      }
      break
    case "JOIN":
      console.log("User joined:", event.publisher)
      break
    case "LEAVE":
    case "TIMEOUT":
      console.log("User left:", event.publisher)
      break
    case "INTERVAL":
      // Periodic batch update — contains joinedUsers[], leftUsers[], timeoutUsers[]
      for (const uid of event.joinedUsers ?? []) console.log("Joined:", uid)
      for (const uid of event.leftUsers ?? []) console.log("Left:", uid)
      break
    case "STATE_CHANGED":
      // User called setState — event.publisher, event.stateChanged (key-value pairs)
      console.log("State changed:", event.publisher, event.stateChanged)
      break
  }
})
```

### Connection Status

```typescript
rtmClient.addEventListener("status", (event) => {
  // event.state: "CONNECTED" | "CONNECTING" | "RECONNECTING" | "DISCONNECTED"
  console.log("RTM status:", event.state)
})
```

### Cleanup

```typescript
async function cleanupRTM() {
  await rtmClient.unsubscribe("channel-name")
  await rtmClient.logout()
}
```


## Common Use Cases with RTC

### Text Chat During Video Call

```typescript
// RTM for chat alongside RTC video
rtmClient.addEventListener("message", (event) => {
  if (event.customType === "chat.message") {
    displayChatMessage(event.publisher, event.message)
  }
})

function sendChatMessage(text: string) {
  rtmClient.publish(channelName, text, { customType: "chat.message" })
}
```

### Voice Activity Detection (VAD) Signaling

```typescript
// Notify other users when speaking (for prioritized video)
function notifyVAD(uid: number) {
  rtmClient.publish(channelName, JSON.stringify({
    type: "VAD",
    uid: uid,
  }), { customType: "signaling.vad" })
}
```

### Control Messages

```typescript
// Request resolution change, stop screen share, etc.
rtmClient.publish(channelName, JSON.stringify({
  type: "INCREASE_RESOLUTION",
  targetUid: uid,
}), { customType: "signaling.control" })
```

### Sending Text to Conversational AI Agent

```typescript
// Send a text message to an AI agent via RTM
async function sendMessageToAgent(message: string, agentUid: string) {
  const publishTarget = `${agentUid}-${channel}`

  await rtmClient.publish(publishTarget, JSON.stringify({
    message: message.trim(),
    priority: "APPEND", // or "REPLACE"
  }), {
    customType: "user.transcription",
    channelType: "USER",
  })
}
```

## Stream Channels (Topics)

Stream channels provide structured, topic-based messaging with lower latency than message channels. Users **join** a stream channel (rather than subscribing) and publish/subscribe to **topics** within it.

```typescript
// Create and join a stream channel
const streamChannel = await rtmClient.createStreamChannel("channel-name")
await streamChannel.join({
  token: "your-rtm-token", // or null for testing
  withPresence: true,
})

// Join a topic to publish messages
await streamChannel.joinTopic("chat")

// Publish to a topic
await streamChannel.publishTopicMessage("chat", "Hello from stream channel!")

// Subscribe to a topic to receive messages from specific publishers (or all)
await streamChannel.subscribeTopic("chat", {
  users: ["user-123", "user-456"], // optional: filter by publisher
})

// Receive messages (same "message" event as message channels)
rtmClient.addEventListener("message", (event) => {
  console.log("Topic:", event.topicName, "From:", event.publisher, ":", event.message)
})

// Leave topic and channel
await streamChannel.leaveTopic("chat")
await streamChannel.leave()
```

**When to use stream channels over message channels:**

- Lower latency needed (0.5s heartbeat vs 5s for message channels)
- Topic-based message routing within a channel
- Fine-grained publisher filtering per topic
- Max 64 users per stream channel, max 50 topics per channel

## Presence State and Metadata

### User State (setState / getState)

Set temporary key-value metadata on the current user that is broadcast to all subscribers:

```typescript
// Set user state (visible to all channel subscribers)
await rtmClient.presence.setState("channel-name", "MESSAGE", {
  displayName: "Alice",
  status: "available",
  typing: "false",
})

// Get a specific user's state
const result = await rtmClient.presence.getState("channel-name", "MESSAGE", "target-user-id")
console.log(result.states) // { displayName: "Alice", status: "available", ... }

// Remove state
await rtmClient.presence.removeState("channel-name", "MESSAGE", ["typing"])
```

State is ephemeral — it is cleared when the user leaves or disconnects. Other users receive `STATE_CHANGED` presence events when state is updated.

### Channel Metadata (Storage)

Store persistent metadata on a channel (survives user disconnect):

```typescript
// Set channel metadata
const metadata = new AgoraRTM.Metadata()
metadata.setMetadataItem({ key: "roomTitle", value: "Team Standup" })
metadata.setMetadataItem({ key: "maxParticipants", value: "10" })
await rtmClient.storage.setChannelMetadata("channel-name", "MESSAGE", metadata, {})

// Get channel metadata
const result = await rtmClient.storage.getChannelMetadata("channel-name", "MESSAGE")
for (const item of result.metadata.items) {
  console.log(item.key, item.value)
}

// Subscribe to metadata updates
await rtmClient.storage.subscribeChannelMetadata("channel-name", "MESSAGE")
rtmClient.addEventListener("storage", (event) => {
  console.log("Metadata updated:", event.data)
})
```

### Important Notes

- RTM does **not** echo published messages back to the sender. Your chat UI must add sent messages locally.
- RTM uses **string UIDs** while RTC uses numeric UIDs. A common mapping strategy: use `String(rtcUid)` as the RTM userId, or maintain a lookup table if usernames differ.
- `presenceTimeout` can be configured during RTM initialization:

```typescript
try {
  const rtmClient = new AgoraRTM.RTM(appId, userId, {
    presenceTimeout: 30, // seconds (5-1800), default 5
  });
} catch (status) {
  console.error("RTM init failed", status);
}
```

## Connection Management

### Heartbeat Configuration

- **MESSAGE channels**: Heartbeat interval defaults to **5 seconds**, customizable from 5–1800 seconds via `presenceTimeout` config.
- **STREAM channels**: Fixed heartbeat interval of **0.5 seconds** (not configurable).
- Set `presenceTimeout` appropriately to prevent excessive presence event floods during brief network reconnections.

### Connection Cleanup

- Always call `logout()` for MESSAGE channel connections.
- Always call `leave()` for STREAM channel connections before disconnecting.
- Failure to clean up properly causes ghost presence entries until heartbeat timeout.

### REST API Rate Limiting

When using RTM REST APIs, implement exponential back-off on rate limit responses:

- 1st retry: wait **1 second**
- 2nd retry: wait **3 seconds**
- 3rd retry: wait **6 seconds**

## Official Documentation

For APIs or features not covered above:

- API Reference: <https://docs.agora.io/en/signaling/reference/api?platform=web>
- Guides: <https://docs.agora.io/en/signaling/overview/product-overview>
