# Agora RTC Flutter SDK

## Table of Contents

- [Installation](#installation)
- [Engine Initialization](#engine-initialization)
- [Joining a Channel](#joining-a-channel)
- [Video Setup](#video-setup)
- [Audio Setup](#audio-setup)
- [Event Handling](#event-handling)
- [Leaving and Cleanup](#leaving-and-cleanup)
- [Complete Example](#complete-example)

API Reference: <https://api-ref.agora.io/en/video-sdk/flutter/6.x/API/rtc_api_overview.html>

## Installation

Add to `pubspec.yaml`:

```yaml
dependencies:
  agora_rtc_engine: ^6.5.0
```

Run `flutter pub get`.

Add permissions to `AndroidManifest.xml`:

```xml
<uses-permission android:name="android.permission.INTERNET" />
<uses-permission android:name="android.permission.CAMERA" />
<uses-permission android:name="android.permission.RECORD_AUDIO" />
<uses-permission android:name="android.permission.MODIFY_AUDIO_SETTINGS" />
<uses-permission android:name="android.permission.ACCESS_NETWORK_STATE" />
<uses-permission android:name="android.permission.BLUETOOTH" />
<!-- Android 12+ (API 31+): required for Bluetooth audio headsets -->
<uses-permission android:name="android.permission.BLUETOOTH_CONNECT" />
```

Add to `Info.plist` (iOS):

```xml
<key>NSCameraUsageDescription</key>
<string>Camera access for video calls</string>
<key>NSMicrophoneUsageDescription</key>
<string>Microphone access for audio calls</string>
```

## Engine Initialization

```dart
import 'package:agora_rtc_engine/agora_rtc_engine.dart';

late RtcEngine _engine;

Future<void> initializeAgora() async {
  _engine = createAgoraRtcEngine();
  await _engine.initialize(const RtcEngineContext(
    appId: 'your-app-id',
    channelProfile: ChannelProfileType.channelProfileCommunication,
  ));
  await _engine.enableVideo();
}
```

## Joining a Channel

```dart
Future<void> joinChannel() async {
  await _engine.joinChannel(
    token: null, // null for testing
    channelId: 'channel-name',
    uid: 0,      // 0 for auto-assignment
    options: const ChannelMediaOptions(
      clientRoleType: ClientRoleType.clientRoleBroadcaster,
      publishMicrophoneTrack: true,
      publishCameraTrack: true,
      autoSubscribeAudio: true,
      autoSubscribeVideo: true,
    ),
  );
}
```

## Video Setup

```dart
// Local preview — use uid=0
AgoraVideoView(
  controller: VideoViewController(
    rtcEngine: _engine,
    canvas: const VideoCanvas(uid: 0),
  ),
)

// Remote video — use the remote user's uid
AgoraVideoView(
  controller: VideoViewController.remote(
    rtcEngine: _engine,
    canvas: VideoCanvas(uid: remoteUid),
    connection: const RtcConnection(channelId: 'channel-name'),
  ),
)
```

## Audio Setup

```dart
// Mute/unmute local audio
await _engine.muteLocalAudioStream(true)   // mute
await _engine.muteLocalAudioStream(false)  // unmute

// Mute/unmute local video
await _engine.muteLocalVideoStream(true)   // video off
await _engine.muteLocalVideoStream(false)  // video on

// Speaker vs earpiece
await _engine.setEnableSpeakerphone(true)  // speaker
await _engine.setEnableSpeakerphone(false) // earpiece
```

## Event Handling

Register handlers **before** joining the channel.

```dart
_engine.registerEventHandler(
  RtcEngineEventHandler(
    onJoinChannelSuccess: (RtcConnection connection, int elapsed) {
      print('Joined: ${connection.channelId}, uid: ${connection.localUid}');
    },
    onUserJoined: (RtcConnection connection, int remoteUid, int elapsed) {
      print('Remote user joined: $remoteUid');
      setState(() => _remoteUid = remoteUid);
    },
    onUserOffline: (RtcConnection connection, int remoteUid, UserOfflineReasonType reason) {
      print('Remote user left: $remoteUid');
      setState(() => _remoteUid = null);
    },
    onTokenPrivilegeWillExpire: (RtcConnection connection, String token) async {
      final newToken = await fetchTokenFromServer();
      await _engine.renewToken(newToken);
    },
    onError: (ErrorCodeType err, String msg) {
      print('Error: $err $msg');
    },
  ),
);
```

## Leaving and Cleanup

```dart
Future<void> leaveChannel() async {
  await _engine.leaveChannel();
}

// Full cleanup when widget is disposed
@override
void dispose() {
  _engine.leaveChannel();
  _engine.release();
  super.dispose();
}
```

Always call `release()` when the engine is no longer needed.

## Complete Example

```dart
import 'package:flutter/material.dart';
import 'package:agora_rtc_engine/agora_rtc_engine.dart';

const appId = 'your-app-id';
const token = null; // null for testing
const channel = 'test';

class VideoCallPage extends StatefulWidget {
  const VideoCallPage({super.key});
  @override
  State<VideoCallPage> createState() => _VideoCallPageState();
}

class _VideoCallPageState extends State<VideoCallPage> {
  late RtcEngine _engine;
  bool _joined = false;
  int? _remoteUid;

  @override
  void initState() {
    super.initState();
    _initAgora();
  }

  Future<void> _initAgora() async {
    _engine = createAgoraRtcEngine();
    await _engine.initialize(const RtcEngineContext(appId: appId));
    await _engine.enableVideo();

    _engine.registerEventHandler(RtcEngineEventHandler(
      onJoinChannelSuccess: (_, __) => setState(() => _joined = true),
      onUserJoined: (_, uid, __) => setState(() => _remoteUid = uid),
      onUserOffline: (_, uid, __) => setState(() => _remoteUid = null),
    ));
  }

  Future<void> _join() async {
    await _engine.startPreview();
    await _engine.joinChannel(
      token: token,
      channelId: channel,
      uid: 0,
      options: const ChannelMediaOptions(
        clientRoleType: ClientRoleType.clientRoleBroadcaster,
        publishMicrophoneTrack: true,
        publishCameraTrack: true,
      ),
    );
  }

  Future<void> _leave() async {
    await _engine.leaveChannel();
    setState(() {
      _joined = false;
      _remoteUid = null;
    });
  }

  @override
  void dispose() {
    _engine.release();
    super.dispose();
  }

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      body: Stack(
        children: [
          if (_joined)
            AgoraVideoView(
              controller: VideoViewController(
                rtcEngine: _engine,
                canvas: const VideoCanvas(uid: 0),
              ),
            ),
          if (_remoteUid != null)
            Positioned(
              right: 16, top: 16, width: 120, height: 160,
              child: AgoraVideoView(
                controller: VideoViewController.remote(
                  rtcEngine: _engine,
                  canvas: VideoCanvas(uid: _remoteUid!),
                  connection: const RtcConnection(channelId: channel),
                ),
              ),
            ),
          Positioned(
            bottom: 32, left: 0, right: 0,
            child: Center(
              child: ElevatedButton(
                onPressed: _joined ? _leave : _join,
                child: Text(_joined ? 'Leave' : 'Join'),
              ),
            ),
          ),
        ],
      ),
    );
  }
}
```

For test setup and mocking patterns, see [references/testing-guidance/SKILL.md](../testing-guidance/SKILL.md).

## Official Documentation

For APIs or features not covered above:

- Quick-start guide: <https://docs-md.agora.io/en/video-calling/get-started/get-started-sdk.md?platform=flutter>
- API Reference: <https://api-ref.agora.io/en/video-sdk/flutter/6.x/API/rtc_api_overview.html>
