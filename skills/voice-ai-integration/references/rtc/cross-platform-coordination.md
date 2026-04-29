# RTC Cross-Platform Coordination

Patterns for apps where users on different platforms (Web, iOS, Android) join the same Agora RTC channel.

## UID Strategy

Agora assigns UIDs per channel. For multi-platform apps:

- **Auto-assign on all clients**: Pass `null`/`0` to `join()` — each platform auto-receives a unique numeric UID. Clients subscribe to all remote users regardless of platform.
- **Fixed UIDs**: Assign specific UIDs per user role (e.g., `1001` for host, `1002` for co-host) when you need deterministic lookup. Must be unique per channel — duplicates cause undefined behavior.
- **RTC + RTM coordination**: After RTC join, use `String(rtcUid)` as the RTM user ID to correlate users across both systems (see [../rtm/README.md](../rtm/README.md)).

## Codec Interoperability

Agora handles codec negotiation automatically for most scenarios. What to know:

| Codec | Notes |
|-------|-------|
| VP8 | Web default. Scales well in multi-user calls. Supported on Safari 13+. Recommended. |
| VP9 | Better compression than VP8. Scales well on desktop. **iOS Safari: hardware-only** — requires iPhone 15 Pro / M3 Mac or newer; software fallback degrades battery significantly on older devices. |
| H.264 | Default on iOS and Android native SDKs. Does not scale well beyond small groups — avoid for multi-user Web calls. |
| H.265 (HEVC) | Not universally supported on Web; avoid for cross-platform channels. |

**Recommendation**: `'vp8'` is the safest default for multi-user Web calls — scales well and works on all modern Safari (13+). Use `'vp9'` only if you can ensure participants are on modern hardware. Avoid `'h264'` for multi-user Web scenarios. If codecs differ between Web and native clients, Agora's server transcodes transparently, which adds latency and is billed separately.

## Screen Sharing (Cross-Platform)

Screen share is a separate track/stream, not a replacement for the camera track.

- **Web**: `AgoraRTC.createScreenVideoTrack()` — publishes as a second video track. See [web.md](web.md) for dual-stream setup.
- **iOS**: `AgoraRtcEngineKit.startScreenCapture(_:)` with broadcast extension — different lifecycle than camera.
- **Android**: `MediaProjection` API + `RtcEngine.startScreenCapture()`.

Remote users on any platform subscribe to the screen share UID as a normal remote user — the stream is just another video track from a different UID.

**Key rule**: Screen share uses a separate channel join with a different UID. Never publish camera and screen share from the same UID.

## Audio Routing Differences

| Platform | Default audio output | Override |
|----------|---------------------|---------|
| Web | Speaker (browser-controlled) | Not configurable via SDK |
| iOS | Earpiece for `rtc` mode | `setDefaultAudioRouteToSpeakerphone(true)` for speaker |
| Android | Earpiece by default | `setEnableSpeakerphone(true)` |

When a user plugs in headphones, iOS/Android switch automatically. Web relies on the browser and OS audio routing — the SDK cannot override this.

## Testing Multi-Platform Channels Locally

1. **Web + Simulator/Emulator**: Connect both to the same channel; verify remote tracks appear on both sides.
2. **Different UIDs on same machine**: Open two browser tabs or two simulator instances — each gets its own UID automatically.
3. **Cross-device**: Use the Agora [Web Demo](https://webdemo.agora.io) to join from a browser while testing your native app in the same channel.
4. **Codec check**: In the Agora Console → Real-time Monitoring, inspect active streams to confirm codec negotiation.

## Common Cross-Platform Bugs

- **Remote user appears then immediately disappears on iOS** — usually a token expiry or UID collision. Check `connectionStateChanged` delegate for the reason code.
- **No video from Android on Web** — codec mismatch. Android may be sending H.265; Web can't decode it. Force H.264 on Android via `VideoEncoderConfiguration`.
- **Audio works, video doesn't on mobile** — camera permission not granted. Check permission before calling `startPreview()`.
- **Web user sees mobile user but not vice versa** — `user-published` event not registered before `client.join()`. Event handlers must be set up before joining — see RTC critical rules in [README.md](README.md).
