# Agora Signaling SDK v2 — iOS (Swift)

## Table of Contents

- [Installation](#installation)
- [Initialization and Login](#initialization-and-login)
- [Channel Subscription](#channel-subscription)
- [Sending Messages](#sending-messages)
- [Receiving Messages](#receiving-messages)
- [Presence Events](#presence-events)
- [Cleanup](#cleanup)
- [Complete Example](#complete-example)

API Reference: <https://api-ref.agora.io/en/signaling/ios/2.x/API/rtm_api_overview.html>

## Installation

**CocoaPods** — add to your `Podfile`:

```ruby
pod 'AgoraRtm', '~> 2.2'
```

Run `pod install`.

**Swift Package Manager** — add `https://github.com/AgoraIO/AgoraRtm_iOS` as a package dependency.

## Initialization and Login

```swift
import AgoraRtmKit

var rtmKit: AgoraRtmClientKit?

// Initialize
let config = AgoraRtmClientConfig(appId: "your-app-id", userId: "user-id-string")
do {
    rtmKit = try AgoraRtmClientKit(config, delegate: self)
} catch {
    print("RTM init failed: \(error)")
}

// Login — always with a server-generated token
rtmKit?.login(token: "YOUR_RTM_TOKEN") { response, error in
    if let error = error {
        print("Login failed: \(error)")
        return
    }
    print("RTM logged in")
}
```

## Channel Subscription

```swift
// Subscribe to a channel
let options = AgoraRtmSubscribeOptions()
options.features = [.message, .presence]

rtmKit?.subscribe(channelName: "channel-name", option: options) { response, error in
    if let error = error {
        print("Subscribe failed: \(error)")
    }
}

// Unsubscribe
rtmKit?.unsubscribe("channel-name") { response, error in }
```

## Sending Messages

```swift
// Publish to a channel
let publishOptions = AgoraRtmPublishOptions()
publishOptions.customType = "chat.message"

rtmKit?.publish(channelName: "channel-name", message: "Hello!", option: publishOptions) { response, error in
    if let error = error { print("Publish failed: \(error)") }
}

// Publish JSON data
let payload = try! JSONSerialization.data(withJSONObject: ["type": "control", "action": "mute-all"])
let jsonString = String(data: payload, encoding: .utf8)!
rtmKit?.publish(channelName: "channel-name", message: jsonString, option: publishOptions) { _, _ in }

// Peer-to-peer (user channel)
let p2pOptions = AgoraRtmPublishOptions()
p2pOptions.customType = "user.transcription"
p2pOptions.channelType = .user

rtmKit?.publish(channelName: "target-user-id", message: message, option: p2pOptions) { _, _ in }
```

## Receiving Messages

Implement `AgoraRtmClientDelegate`:

```swift
extension YourClass: AgoraRtmClientDelegate {
    func rtmKit(_ rtmKit: AgoraRtmClientKit, didReceiveMessageEvent event: AgoraRtmMessageEvent) {
        print("From: \(event.publisher)")
        print("Channel: \(event.channelName)")
        print("Message: \(event.message.stringData ?? "")")
        print("Type: \(event.customType ?? "")")
    }
}
```

## Presence Events

```swift
func rtmKit(_ rtmKit: AgoraRtmClientKit, didReceivePresenceEvent event: AgoraRtmPresenceEvent) {
    switch event.type {
    case .snapshot:
        // Initial state on subscribe
        for user in event.snapshot {
            print("Online: \(user.userId), states: \(user.states)")
        }
    case .remoteJoinChannel:
        print("User joined: \(event.publisher ?? "")")
    case .remoteLeaveChannel, .remoteConnectionTimeout:
        print("User left: \(event.publisher ?? "")")
    case .remoteStateChanged:
        print("State changed: \(event.publisher ?? ""), \(event.states)")
    default:
        break
    }
}
```

## Connection Status

```swift
func rtmKit(_ rtmKit: AgoraRtmClientKit, channel: String, connectionChangedToState state: AgoraRtmClientConnectionState, reason: AgoraRtmClientConnectionChangeReason) {
    print("RTM connection state: \(state.rawValue)")
}
```

## Cleanup

```swift
func cleanup() {
    rtmKit?.unsubscribe("channel-name") { _, _ in }
    rtmKit?.logout { _, _ in }
    rtmKit?.destroy()
    rtmKit = nil
}
```

## Complete Example

```swift
import UIKit
import AgoraRtmKit

class SignalingViewController: UIViewController {
    var rtmKit: AgoraRtmClientKit?
    let channelName = "my-channel"

    override func viewDidLoad() {
        super.viewDidLoad()
        setupRTM()
    }

    func setupRTM() {
        let config = AgoraRtmClientConfig(appId: "your-app-id", userId: "user-123")
        do {
            rtmKit = try AgoraRtmClientKit(config, delegate: self)
        } catch {
            print("RTM init failed: \(error)")
            return
        }

        rtmKit?.login(token: "YOUR_RTM_TOKEN") { [weak self] _, error in
            guard error == nil else { return }
            self?.subscribeToChannel()
        }
    }

    func subscribeToChannel() {
        let options = AgoraRtmSubscribeOptions()
        options.features = [.message, .presence]

        rtmKit?.subscribe(channelName: channelName, option: options) { _, error in
            if let error = error {
                print("Subscribe failed: \(error)")
            }
        }
    }

    func sendMessage(_ text: String) {
        let options = AgoraRtmPublishOptions()
        options.customType = "chat.message"
        rtmKit?.publish(channelName: channelName, message: text, option: options) { _, _ in }
    }

    override func viewDidDisappear(_ animated: Bool) {
        super.viewDidDisappear(animated)
        rtmKit?.unsubscribe(channelName) { _, _ in }
        rtmKit?.logout { _, _ in }
        rtmKit?.destroy()
    }
}

extension SignalingViewController: AgoraRtmClientDelegate {
    func rtmKit(_ rtmKit: AgoraRtmClientKit, didReceiveMessageEvent event: AgoraRtmMessageEvent) {
        print("\(event.publisher ?? ""): \(event.message.stringData ?? "")")
    }

    func rtmKit(_ rtmKit: AgoraRtmClientKit, didReceivePresenceEvent event: AgoraRtmPresenceEvent) {
        if event.type == .remoteJoinChannel {
            print("User joined: \(event.publisher ?? "")")
        }
    }
}
```

## Notes

- iOS RTM UIDs are **strings**. When pairing with RTC (which uses `UInt`), use `String(rtcUid)` as the RTM userId.
- The RTM constructor can throw — always wrap in `do/catch`.
- Always call `login()` and wait for the callback before subscribing or publishing.

For test setup and mocking patterns, see [references/testing-guidance/SKILL.md](../testing-guidance/SKILL.md).

## Official Documentation

For APIs or features not covered above:

- Quick-start guide: <https://docs-md.agora.io/en/signaling/get-started/sdk-quickstart.md?platform=ios>
- API Reference: <https://api-ref.agora.io/en/signaling/ios/2.x/API/rtm_api_overview.html>
