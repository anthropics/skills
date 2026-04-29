# Agora RTC iOS SDK (Swift)

## Table of Contents

- [Installation](#installation)
- [Engine Initialization](#engine-initialization)
- [Joining a Channel](#joining-a-channel)
- [Video Setup](#video-setup)
- [Audio Setup](#audio-setup)
- [Event Handling (Delegate)](#event-handling-delegate)
- [Leaving and Cleanup](#leaving-and-cleanup)
- [Token Renewal](#token-renewal)
- [Complete Example: Video Call](#complete-example-video-call)

API Reference: <https://api-ref.agora.io/en/video-sdk/ios/4.x/API/rtc_api_overview_ng.html>

## Installation

### Swift Package Manager

```text
https://github.com/AgoraIO/AgoraRtcEngine_iOS
```

### CocoaPods

```ruby
pod 'AgoraRtcEngine_iOS', '~> 4.3'
```

Add to Info.plist:

```xml
<key>NSCameraUsageDescription</key>
<string>For video calling</string>
<key>NSMicrophoneUsageDescription</key>
<string>For voice calling</string>
```

## Engine Initialization

```swift
import AgoraRtcKit

let config = AgoraRtcEngineConfig()
config.appId = "your-app-id"
config.channelProfile = .communication  // or .liveBroadcasting

let agoraEngine = AgoraRtcEngineKit.sharedEngine(with: config, delegate: self)
```

## Joining a Channel

```swift
// Communication mode
let option = AgoraRtcChannelMediaOptions()
option.clientRoleType = .broadcaster  // .broadcaster or .audience
option.channelProfile = .communication

agoraEngine.joinChannel(
    byToken: token,      // nil for testing
    channelId: "channel-name",
    uid: 0,              // 0 = auto-assign
    mediaOptions: option
)
```

## Video Setup

```swift
// Enable video module
agoraEngine.enableVideo()

// Configure video encoder
let videoConfig = AgoraVideoEncoderConfiguration(
    size: CGSize(width: 640, height: 360),
    frameRate: .fps24,
    bitrate: AgoraVideoBitrateStandard,
    orientationMode: .adaptative
)
agoraEngine.setVideoEncoderConfiguration(videoConfig)

// Local video preview
let localView = UIView(frame: localVideoContainer.bounds)
let canvas = AgoraRtcVideoCanvas()
canvas.uid = 0  // 0 = local user
canvas.view = localView
canvas.renderMode = .hidden
agoraEngine.setupLocalVideo(canvas)
agoraEngine.startPreview()

// Remote video (call in didJoinedOfUid delegate)
let remoteCanvas = AgoraRtcVideoCanvas()
remoteCanvas.uid = remoteUid
remoteCanvas.view = remoteVideoView
remoteCanvas.renderMode = .hidden
agoraEngine.setupRemoteVideo(remoteCanvas)
```

## Audio Setup

```swift
// Enable audio (enabled by default)
agoraEngine.enableAudio()

// Audio profile
agoraEngine.setAudioProfile(.default)

// Mute/unmute local audio
agoraEngine.muteLocalAudioStream(true)   // mute
agoraEngine.muteLocalAudioStream(false)  // unmute

// Mute/unmute local video (stops sending video, camera stays active)
agoraEngine.muteLocalVideoStream(true)   // video off
agoraEngine.muteLocalVideoStream(false)  // video on

// Or disable video entirely (stops camera capture)
agoraEngine.enableLocalVideo(false)      // camera off
agoraEngine.enableLocalVideo(true)       // camera on

// Switch between speaker and earpiece
agoraEngine.setEnableSpeakerphone(true)  // speaker
agoraEngine.setEnableSpeakerphone(false) // earpiece

// Mute remote user
agoraEngine.muteRemoteAudioStream(remoteUid, mute: true)
```

## Event Handling (Delegate)

```swift
extension ViewController: AgoraRtcEngineDelegate {
    // Successfully joined channel
    func rtcEngine(_ engine: AgoraRtcEngineKit, didJoinChannel channel: String, withUid uid: UInt, elapsed: Int) {
        print("Joined channel: \(channel), uid: \(uid)")
    }

    // Remote user joined
    func rtcEngine(_ engine: AgoraRtcEngineKit, didJoinedOfUid uid: UInt, elapsed: Int) {
        // Setup remote video view
        let canvas = AgoraRtcVideoCanvas()
        canvas.uid = uid
        canvas.view = remoteVideoView
        canvas.renderMode = .hidden
        engine.setupRemoteVideo(canvas)
    }

    // Remote user left
    func rtcEngine(_ engine: AgoraRtcEngineKit, didOfflineOfUid uid: UInt, reason: AgoraUserOfflineReason) {
        // Clean up remote view
        let canvas = AgoraRtcVideoCanvas()
        canvas.uid = uid
        canvas.view = nil
        engine.setupRemoteVideo(canvas)
    }

    // Token expiring
    func rtcEngine(_ engine: AgoraRtcEngineKit, tokenPrivilegeWillExpire token: String) {
        // Fetch new token from server and renew
        fetchNewToken { newToken in
            engine.renewToken(newToken)
        }
    }

    // Error
    func rtcEngine(_ engine: AgoraRtcEngineKit, didOccurError errorCode: AgoraErrorCode) {
        print("Agora error: \(errorCode.rawValue)")
    }

    // Network quality
    func rtcEngine(_ engine: AgoraRtcEngineKit, networkQuality uid: UInt,
                   txQuality: AgoraNetworkQuality, rxQuality: AgoraNetworkQuality) {
        // 0=unknown, 1=excellent, 2=good, 3=poor, 4=bad, 5=very bad
    }
}
```

## Leaving and Cleanup

```swift
func leaveChannel() {
    agoraEngine.stopPreview()
    agoraEngine.leaveChannel(nil)
}

// Full cleanup (app termination)
func destroy() {
    agoraEngine.stopPreview()
    agoraEngine.leaveChannel(nil)
    AgoraRtcEngineKit.destroy()
}
```

## Token Renewal

```swift
func rtcEngine(_ engine: AgoraRtcEngineKit, tokenPrivilegeWillExpire token: String) {
    Task {
        let newToken = await fetchTokenFromServer(channel: channelName, uid: localUid)
        engine.renewToken(newToken)
    }
}
```

## Complete Example: Video Call

```swift
import UIKit
import AgoraRtcKit

class VideoCallViewController: UIViewController {
    private var agoraEngine: AgoraRtcEngineKit!
    private let appId = "your-app-id"
    private var token: String? = nil
    private let channelName = "test"

    @IBOutlet weak var localVideoView: UIView!
    @IBOutlet weak var remoteVideoView: UIView!

    override func viewDidLoad() {
        super.viewDidLoad()
        initializeAgora()
    }

    private func initializeAgora() {
        let config = AgoraRtcEngineConfig()
        config.appId = appId
        config.channelProfile = .communication

        agoraEngine = AgoraRtcEngineKit.sharedEngine(with: config, delegate: self)
        agoraEngine.enableVideo()
        agoraEngine.setVideoEncoderConfiguration(
            AgoraVideoEncoderConfiguration(
                size: CGSize(width: 640, height: 360),
                frameRate: .fps24,
                bitrate: AgoraVideoBitrateStandard,
                orientationMode: .adaptative
            )
        )
    }

    @IBAction func joinChannel(_ sender: Any) {
        // Setup local preview
        let localCanvas = AgoraRtcVideoCanvas()
        localCanvas.uid = 0
        localCanvas.view = localVideoView
        localCanvas.renderMode = .hidden
        agoraEngine.setupLocalVideo(localCanvas)
        agoraEngine.startPreview()

        // Join
        let option = AgoraRtcChannelMediaOptions()
        option.clientRoleType = .broadcaster
        option.channelProfile = .communication

        agoraEngine.joinChannel(
            byToken: token,
            channelId: channelName,
            uid: 0,
            mediaOptions: option
        )
    }

    @IBAction func leaveChannel(_ sender: Any) {
        agoraEngine.stopPreview()
        agoraEngine.leaveChannel(nil)
    }

    deinit {
        agoraEngine.stopPreview()
        agoraEngine.leaveChannel(nil)
        AgoraRtcEngineKit.destroy()
    }
}

extension VideoCallViewController: AgoraRtcEngineDelegate {
    func rtcEngine(_ engine: AgoraRtcEngineKit, didJoinedOfUid uid: UInt, elapsed: Int) {
        let remoteCanvas = AgoraRtcVideoCanvas()
        remoteCanvas.uid = uid
        remoteCanvas.view = remoteVideoView
        remoteCanvas.renderMode = .hidden
        agoraEngine.setupRemoteVideo(remoteCanvas)
    }

    func rtcEngine(_ engine: AgoraRtcEngineKit, didOfflineOfUid uid: UInt, reason: AgoraUserOfflineReason) {
        let canvas = AgoraRtcVideoCanvas()
        canvas.uid = uid
        canvas.view = nil
        agoraEngine.setupRemoteVideo(canvas)
    }

    func rtcEngine(_ engine: AgoraRtcEngineKit, tokenPrivilegeWillExpire token: String) {
        Task {
            let newToken = await fetchTokenFromServer()
            agoraEngine.renewToken(newToken)
        }
    }
}
```

## Official Documentation

For APIs or features not covered above:

- API Reference: <https://api-ref.agora.io/en/video-sdk/ios/4.x/API/rtc_api_overview_ng.html>
- Guides: <https://docs.agora.io/en/video-calling/overview/product-overview>
