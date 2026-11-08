# Agora RTC (Video/Voice SDK)

Real-time audio and video communication. Users join channels, publish local tracks, and subscribe to remote tracks.

## Critical Rules

1. **Register event handlers BEFORE joining** the channel, or you will miss events for users already present.
2. **`user-published` fires separately** for audio and video. A user publishing both triggers two events — handle each.
3. **Track cleanup**: Always `stop()` then `close()` local tracks before setting to null. Failure to clean up causes memory leaks and device locks. (React SDK hooks handle this automatically — see `react.md`.)
4. **HTTPS required** for Web SDK (except `localhost`).
5. **Token management is mandatory in production**. Handle `token-privilege-will-expire` (Web) / `onTokenPrivilegeWillExpire` (native) to renew tokens. UID in token must match UID used to join.
6. **Stream bombing prevention**: In production, generate tokens with subscriber role (`kRoleSubscriber` / `RtcRole.SUBSCRIBER`) for audience-only users to prevent unauthorized publishing.
7. **Audio autoplay (non-standard flows only)**: Browser autoplay policy is not an issue in typical RTC flows because the user has already clicked to join (satisfying the gesture requirement). However, if you auto-join on page load, trigger audio from a non-user event, or run in a headless/test environment, `audioTrack.play()` may be silently blocked. Wrap the join + publish sequence in a user gesture handler in these cases.

## Channel Profiles

- `rtc` (communication): All peers are equal. Best for video calls, conferencing.
- `live` (live streaming): Host/audience roles. Higher bitrate, lower latency for hosts.

## Video Encoder Profiles (Web)

```text
"120p_1"  → 160×120,   15fps, 65kbps
"180p_1"  → 320×180,   15fps, 140kbps
"360p_1"  → 640×360,   15fps, 400kbps
"480p_1"  → 640×480,   15fps, 500kbps
"720p_1"  → 1280×720,  15fps, 1130kbps
"720p_2"  → 1280×720,  30fps, 2000kbps
"1080p_1" → 1920×1080, 15fps, 2080kbps
"1080p_2" → 1920×1080, 30fps, 3000kbps
```

Or use custom config: `{ width: 640, height: 360, frameRate: 24, bitrateMin: 400, bitrateMax: 1000 }`

## Audio Encoder Profiles (Web)

```text
"speech_low_quality"      → mono, 16kHz, 24kbps
"speech_standard"         → mono, 32kHz, 24kbps
"high_quality"            → mono, 48kHz, 40kbps
"high_quality_stereo"     → stereo, 48kHz, 128kbps
```

## Dual Stream (Simulcast)

Send high+low quality streams simultaneously. Subscribers choose which to receive, enabling large-scale calls:

```javascript
// Web: Enable after joining
await client.enableDualStream();
client.setLowStreamParameter({
  width: 160,
  height: 90,
  framerate: 24,
  bitrate: 200,
});
// Switch remote user to low stream
client.setRemoteVideoStreamType(uid, 1); // 0=high, 1=low
```

## Screen Sharing (Web)

```javascript
const screenTrack = await AgoraRTC.createScreenVideoTrack(
  {
    optimizationMode: 'detail', // or "motion" for video content
    encoderConfig: { width: 1280, height: 720, frameRate: 15 },
  },
  'auto',
); // "auto" returns [videoTrack, audioTrack] if audio available
```

Screen share typically uses a separate client instance to avoid replacing the camera track.

## Cross-Platform Interop Notes

When Web, iOS, and Android clients share the same channel:

- **Codec**: `"vp8"` and `"vp9"` scale better in multi-user calls — prefer these over `"h264"`, which does not scale well beyond small groups. If codecs differ between Web and native clients, Agora's server transcodes transparently (works but adds latency).
- **UID types**: iOS uses `UInt` (unsigned 32-bit), Android uses `Int` (signed 32-bit), Web uses `number`. UIDs > 2,147,483,647 wrap to negative on Android. RTM uses **string UIDs** — use `String(rtcUid)` as a mapping convention.
- **Audio profiles**: Align encoder settings across platforms to avoid one side sending stereo 128kbps while another expects mono. Use `"speech_standard"` (Web) / `AUDIO_PROFILE_DEFAULT` (native) for voice calls.
- **Orientation**: Mobile uses adaptive orientation (rotates with device). Web cameras are typically landscape. Handle aspect ratio changes on the viewer side.
- **Dual stream**: Enable on all platforms for large calls, not just Web.

## Platform Reference Files

Read the file matching the user's platform:

- **[web.md](web.md)** — `agora-rtc-sdk-ng` (JS/TS): client creation, tracks, events, complete examples
- **[react.md](react.md)** — `agora-rtc-react` hooks and components
- **[nextjs.md](nextjs.md)** — Next.js / SSR dynamic import patterns (App Router + Pages Router)
- **[ios.md](ios.md)** — `AgoraRtcEngineKit` (Swift): engine setup, delegation, permissions
- **[android.md](android.md)** — `RtcEngine` (Kotlin/Java): engine setup, callbacks, permissions
- **[react-native.md](react-native.md)** — `react-native-agora`: engine init, events, video views, complete example
- **[flutter.md](flutter.md)** — `agora_rtc_engine` (Dart): engine init, events, AgoraVideoView, complete example
- **[cross-platform-coordination.md](cross-platform-coordination.md)** — UID strategy, codec interop, screen sharing across platforms, audio routing, common cross-platform bugs

For additional platforms and advanced features: <https://docs-md.agora.io/en/video-calling/get-started/get-started-sdk.md> — voice-only: <https://docs-md.agora.io/en/voice-calling/get-started/get-started-sdk.md>

For test setup and mocking patterns, see [references/testing-guidance/SKILL.md](../testing-guidance/SKILL.md).

## When to Fetch More

Always use Level 2 fetch for: encoder profile parameter details, error code listings, release notes, Windows/Electron/Unity platform quick-starts. See [../doc-fetching.md](../doc-fetching.md).
