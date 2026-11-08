# Testing Guidance — RTC iOS (Swift)

Use protocol-based injection. `AgoraRtcEngineKit.sharedEngine(withAppId:delegate:)`
is a singleton — wrap it behind a protocol to enable mocking.

Pattern:

```swift
protocol RtcEngineProtocol: AnyObject {
    func joinChannel(byToken token: String?,
                     channelId: String,
                     uid: UInt,
                     mediaOptions: AgoraRtcChannelMediaOptions) -> Int32
    func leaveChannel(_ leaveChannelBlock: ((AgoraChannelStats) -> Void)?) -> Int32
    func enableVideo() -> Int32
    func muteLocalAudioStream(_ mute: Bool) -> Int32
    func renewToken(_ token: String) -> Int32
}

extension AgoraRtcEngineKit: RtcEngineProtocol {}

class RtcManager {
    private let engine: RtcEngineProtocol
    init(engine: RtcEngineProtocol = AgoraRtcEngineKit.sharedEngine(
        withAppId: Config.appId, delegate: nil)) {
        self.engine = engine
    }
}
```

Mock:

```swift
class MockRtcEngine: RtcEngineProtocol {
    var joinChannelCallCount = 0
    var renewedToken: String?

    func joinChannel(byToken token: String?, channelId: String,
                     uid: UInt,
                     mediaOptions: AgoraRtcChannelMediaOptions) -> Int32 {
        joinChannelCallCount += 1
        return 0
    }

    func leaveChannel(_ leaveChannelBlock: ((AgoraChannelStats) -> Void)?) -> Int32 { 0 }
    func enableVideo() -> Int32 { 0 }
    func muteLocalAudioStream(_ mute: Bool) -> Int32 { 0 }
    func renewToken(_ token: String) -> Int32 {
        renewedToken = token
        return 0
    }
}
```

Token renewal:

```swift
func testRenewsTokenBeforeExpiry() {
    let mockEngine = MockRtcEngine()
    let manager = RtcManager(engine: mockEngine)

    manager.rtcEngine(mockEngine as! AgoraRtcEngineKit, tokenPrivilegeWillExpire: "expiring-token")

    XCTAssertNotNil(mockEngine.renewedToken)
}
```

Primary assertions:

- join called with correct channel/token/UID
- video/audio setup methods are invoked
- token renewal path runs before expiry
- leave/cleanup happens once
