# Agora RTC React Native SDK

## Table of Contents

- [Installation](#installation)
- [Engine Initialization](#engine-initialization)
- [Joining a Channel](#joining-a-channel)
- [Video Setup](#video-setup)
- [Audio Setup](#audio-setup)
- [Event Handling](#event-handling)
- [Leaving and Cleanup](#leaving-and-cleanup)
- [Complete Example](#complete-example)

API Reference: <https://api-ref.agora.io/en/video-sdk/react-native/4.x/API/rtc_api_overview.html>

## Installation

```bash
npm install react-native-agora
```

For iOS, run `pod install` in the `ios/` directory. Android requires no extra steps beyond Gradle sync.

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

Request runtime permissions before initializing (use `react-native-permissions` or the built-in `PermissionsAndroid`).

## Engine Initialization

```typescript
import {
  createAgoraRtcEngine,
  IRtcEngine,
  ChannelProfileType,
  ClientRoleType,
} from 'react-native-agora'

let agoraEngine: IRtcEngine

function initializeAgora() {
  agoraEngine = createAgoraRtcEngine()
  agoraEngine.initialize({
    appId: 'your-app-id',
    channelProfile: ChannelProfileType.ChannelProfileCommunication,
  })
  agoraEngine.enableVideo()
}
```

## Joining a Channel

```typescript
import { ChannelMediaOptions, ClientRoleType } from 'react-native-agora'

function joinChannel() {
  const options: ChannelMediaOptions = {
    clientRoleType: ClientRoleType.ClientRoleBroadcaster,
    publishMicrophoneTrack: true,
    publishCameraTrack: true,
    autoSubscribeAudio: true,
    autoSubscribeVideo: true,
  }
  agoraEngine.joinChannel(token, 'channel-name', uid, options)
  // token: null for testing, uid: 0 for auto-assignment
}
```

## Video Setup

```typescript
import { RtcSurfaceView, VideoCanvas, RenderModeType } from 'react-native-agora'

// Local preview — use uid=0
<RtcSurfaceView
  canvas={{ uid: 0, renderMode: RenderModeType.RenderModeHidden }}
  style={{ width: 320, height: 240 }}
/>

// Remote video — use the remote user's uid
<RtcSurfaceView
  canvas={{ uid: remoteUid, renderMode: RenderModeType.RenderModeHidden }}
  style={{ width: 320, height: 240 }}
/>
```

## Audio Setup

```typescript
import { AudioProfileType, AudioScenarioType } from 'react-native-agora'

// Mute/unmute local audio
agoraEngine.muteLocalAudioStream(true)   // mute
agoraEngine.muteLocalAudioStream(false)  // unmute

// Mute/unmute local video
agoraEngine.muteLocalVideoStream(true)   // video off
agoraEngine.muteLocalVideoStream(false)  // video on

// Speaker vs earpiece (Android/iOS)
agoraEngine.setEnableSpeakerphone(true)  // speaker
agoraEngine.setEnableSpeakerphone(false) // earpiece
```

## Event Handling

Register event handlers **before** joining the channel.

```typescript
import { IRtcEngineEventHandler } from 'react-native-agora'

const eventHandler: IRtcEngineEventHandler = {
  onJoinChannelSuccess: (connection, elapsed) => {
    console.log('Joined channel:', connection.channelId, 'uid:', connection.localUid)
  },

  onUserJoined: (connection, remoteUid, elapsed) => {
    console.log('Remote user joined:', remoteUid)
    // Update state to render <RtcSurfaceView canvas={{ uid: remoteUid }} />
  },

  onUserOffline: (connection, remoteUid, reason) => {
    console.log('Remote user left:', remoteUid)
  },

  onTokenPrivilegeWillExpire: (connection, token) => {
    // Fetch new token and renew
    fetchNewToken().then(newToken => {
      agoraEngine.renewToken(newToken)
    })
  },

  onError: (err, msg) => {
    console.error('Agora error:', err, msg)
  },
}

agoraEngine.registerEventHandler(eventHandler)
```

## Leaving and Cleanup

```typescript
function leaveChannel() {
  agoraEngine.leaveChannel()
}

// Full cleanup when component unmounts
function destroyAgora() {
  agoraEngine.leaveChannel()
  agoraEngine.unregisterEventHandler(eventHandler)
  agoraEngine.release()
}
```

Always call `release()` when the engine is no longer needed to free native resources.

## Complete Example

```typescript
import React, { useEffect, useState } from 'react'
import { View, Button } from 'react-native'
import {
  createAgoraRtcEngine,
  IRtcEngine,
  IRtcEngineEventHandler,
  ChannelProfileType,
  ClientRoleType,
  RtcSurfaceView,
  RenderModeType,
} from 'react-native-agora'

const APP_ID = 'your-app-id'
const TOKEN = null // null for testing
const CHANNEL = 'test'
const UID = 0

export default function VideoCall() {
  const [engine, setEngine] = useState<IRtcEngine | null>(null)
  const [joined, setJoined] = useState(false)
  const [remoteUid, setRemoteUid] = useState<number | null>(null)

  useEffect(() => {
    const rtcEngine = createAgoraRtcEngine()
    rtcEngine.initialize({
      appId: APP_ID,
      channelProfile: ChannelProfileType.ChannelProfileCommunication,
    })
    rtcEngine.enableVideo()

    const handler: IRtcEngineEventHandler = {
      onJoinChannelSuccess: () => setJoined(true),
      onUserJoined: (_, uid) => setRemoteUid(uid),
      onUserOffline: () => setRemoteUid(null),
    }
    rtcEngine.registerEventHandler(handler)
    setEngine(rtcEngine)

    return () => {
      rtcEngine.leaveChannel()
      rtcEngine.unregisterEventHandler(handler)
      rtcEngine.release()
    }
  }, [])

  const join = () => {
    engine?.joinChannel(TOKEN, CHANNEL, UID, {
      clientRoleType: ClientRoleType.ClientRoleBroadcaster,
      publishMicrophoneTrack: true,
      publishCameraTrack: true,
    })
  }

  const leave = () => {
    engine?.leaveChannel()
    setJoined(false)
    setRemoteUid(null)
  }

  return (
    <View style={{ flex: 1 }}>
      {joined && (
        <RtcSurfaceView
          canvas={{ uid: 0, renderMode: RenderModeType.RenderModeHidden }}
          style={{ width: '100%', height: 240 }}
        />
      )}
      {remoteUid !== null && (
        <RtcSurfaceView
          canvas={{ uid: remoteUid, renderMode: RenderModeType.RenderModeHidden }}
          style={{ width: '100%', height: 240 }}
        />
      )}
      <Button title={joined ? 'Leave' : 'Join'} onPress={joined ? leave : join} />
    </View>
  )
}
```

For test setup and mocking patterns, see [references/testing-guidance/SKILL.md](../testing-guidance/SKILL.md).

## Official Documentation

For APIs or features not covered above:

- Quick-start guide: <https://docs-md.agora.io/en/video-calling/get-started/get-started-sdk.md?platform=react-native>
- API Reference: <https://api-ref.agora.io/en/video-sdk/react-native/4.x/API/rtc_api_overview.html>
