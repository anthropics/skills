# Agora Signaling SDK (RTM)

The Agora Signaling SDK (internally called RTM) provides signaling, text messaging, presence, and metadata — used alongside or independently from RTC. RTC and the Signaling SDK are **independent systems**: their channels are separate namespaces.

## When to Use RTM

- Text chat during video calls
- Signaling (call invitations, control messages, hang-up)
- User presence and status tracking
- Custom data exchange (VAD signals, resolution requests, state sync)
- Receiving transcripts from Conversational AI agents

## Channel Types

RTM has two channel types with different semantics:

|                     | Message Channel                          | Stream Channel                              |
| ------------------- | ---------------------------------------- | ------------------------------------------- |
| **Model**           | Pub/sub                                  | Join + topic subscribe                      |
| **Join required**   | No — subscribe to publish/receive        | Yes — must join before publishing           |
| **Topics**          | No                                       | Yes — messages published per topic          |
| **Use for**         | Signaling, chat, ConvoAI transcripts     | High-frequency data, custom media streams   |
| **Presence events** | Via `presence.getOnlineUsers()` or event | Built-in via channel join/leave events      |

**Default choice**: Use message channels for most use cases. Use stream channels only if you need topic-based filtering or high-frequency updates (e.g., cursor positions, sensor data).

## Key Concepts

- **Presence**: Track online users and their metadata per channel. Subscribe to `presence` events to detect joins, leaves, and state changes in real time.
- **Storage**: Channel and user metadata — key-value store with versioning and compare-and-set (CAS) for conflict resolution.
- **Lock**: Distributed locking for coordinating shared resources across users.
- **RTM UIDs are strings** — not numeric like RTC. When using RTC and RTM together, `String(rtcUid)` is the simplest default mapping, but it is a convention, not a protocol requirement.

## Gotchas & Critical Rules

- **UID type mismatch causes silent failures** — RTC UIDs are numbers; RTM UIDs are strings. If your app maps the same person across both systems, convert explicitly and consistently. `String(rtcUid)` is the default convention. Type mismatches don't throw errors — they silently break user lookups across both systems.
- **RTM token subject and RTM login userId must match** — if your server minted an RTM token for `String(rtcUid)` (or any other identity), the RTM client must log in with that exact same string. Logging in RTM with a different random identity can look like a generic startup failure instead of a clear auth error.
- **Namespace isolation** — RTC channels and RTM channels are completely separate. Joining RTC channel `"meeting-1"` does NOT auto-subscribe you to RTM channel `"meeting-1"`. Subscribe both explicitly.
- **Login before all operations** — `rtmClient.login()` must complete (connection reaches `CONNECTED`) before any subscribe, publish, or presence call. Operations called while still connecting are not guaranteed to succeed.
- **Subscribe before presence** — Presence events (joins/leaves) require an active channel subscription. Publishing to a channel without subscribing means you won't receive presence notifications or responses.
- **RTM v2 API is a full rewrite** — Do NOT apply v1 patterns (`AgoraRTM.createInstance()`, `.createChannel()`) to v2. The APIs are incompatible. The Web reference (`web.md`) covers v2 only.
- **ConvoAI transcript delivery requires two flags** — For AI agent transcripts to arrive via RTM, the ConvoAI `/join` payload must include both `advanced_features.enable_rtm: true` AND `parameters.data_channel: "rtm"`. One flag alone is not sufficient.
- **Recent enablement can lag behind runtime availability** — if RTM or a related capability was just enabled at the control-plane layer, allow bounded wait/retry for up to about 5 minutes before concluding the runtime path is still broken.

## RTC + RTM Coordination Pattern

When pairing RTC and RTM in the same app, the default recommendation is:

1. Join RTC channel with numeric UID (or `0` for auto-assignment)
2. After RTC join resolves, log in to RTM with `String(rtcUid)`
3. Subscribe to the RTM message channel
4. Use RTC for media (audio/video tracks), RTM for all signaling and metadata

```javascript
// RTC join resolves with the assigned numeric UID
const rtcUid = await rtcClient.join(appId, channelName, rtcToken, null);

// uid is set in the RTM constructor; login only needs the token
// new AgoraRTM.RTM(appId, String(rtcUid)) was already called at setup
await rtmClient.login({ token: rtmToken }); // RTM token from your server
await rtmClient.subscribe(channelName);
```

RTM channel name does not need to match the RTC channel name, but using the same name is the conventional approach.

If your app already has a stable user identity independent of the RTC UID, you can log in to RTM earlier and keep a separate RTC↔RTM mapping. That pattern is useful when you want signaling or presence before media starts, but it adds coordination complexity.

## Platform Scope

RTM is a **client-side SDK**. It runs in browsers, iOS apps, and Android apps. There is no server-side RTM SDK and no Electron/Windows/desktop variant. If a user needs server-to-channel messaging from a backend, they should use the ConvoAI REST API (`/speak`) or build their own signaling layer.

All three platform files below document **RTM v2**. Do not apply v1 patterns (`AgoraRTM.createInstance()`, `.createChannel()`) to any of them — the APIs are incompatible.

## Platform Reference Files

- **[web.md](web.md)** — `agora-rtm` v2 (JS/TS): client, messaging, presence, stream channels
- **[ios.md](ios.md)** — `AgoraRtmClientKit` (Swift): init, login, subscribe, publish, delegate
- **[android.md](android.md)** — `RtmClient` (Kotlin): init, login, subscribe, publish, event listener

For test setup and mocking patterns, see [references/testing-guidance/SKILL.md](../testing-guidance/SKILL.md).
