# Agora Signaling SDK v2 — Android (Kotlin)

## Table of Contents

- [Installation](#installation)
- [Initialization and Login](#initialization-and-login)
- [Channel Subscription](#channel-subscription)
- [Sending Messages](#sending-messages)
- [Receiving Messages](#receiving-messages)
- [Presence Events](#presence-events)
- [Cleanup](#cleanup)
- [Complete Example](#complete-example)

API Reference: <https://api-ref.agora.io/en/signaling/android/2.x/API/rtm_api_overview.html>

## Installation

Add to `build.gradle`:

```groovy
dependencies {
    implementation 'io.agora:agora-rtm:2.2.+'
}
```

Add permissions to `AndroidManifest.xml`:

```xml
<uses-permission android:name="android.permission.INTERNET" />
<uses-permission android:name="android.permission.ACCESS_NETWORK_STATE" />
```

## Initialization and Login

```kotlin
import io.agora.rtm.RtmClient
import io.agora.rtm.RtmConfig
import io.agora.rtm.RtmEventListener
import io.agora.rtm.ResultCallback
import io.agora.rtm.ErrorInfo

val config = RtmConfig.Builder("your-app-id", "user-id-string")
    .eventListener(rtmEventListener)
    .build()

val rtmClient = RtmClient.create(config)

// Login — always with a server-generated token
rtmClient.login("YOUR_RTM_TOKEN", object : ResultCallback<Void> {
    override fun onSuccess(responseInfo: Void?) {
        Log.d("RTM", "Logged in")
    }
    override fun onFailure(errorInfo: ErrorInfo) {
        Log.e("RTM", "Login failed: ${errorInfo.errorReason}")
    }
})
```

## Channel Subscription

```kotlin
import io.agora.rtm.SubscribeOptions
import io.agora.rtm.RtmConstants

val options = SubscribeOptions().apply {
    withMessage = true
    withPresence = true
}

rtmClient.subscribe("channel-name", options, object : ResultCallback<Void> {
    override fun onSuccess(responseInfo: Void?) { }
    override fun onFailure(errorInfo: ErrorInfo) {
        Log.e("RTM", "Subscribe failed: ${errorInfo.errorReason}")
    }
})

// Unsubscribe
rtmClient.unsubscribe("channel-name", object : ResultCallback<Void> {
    override fun onSuccess(responseInfo: Void?) { }
    override fun onFailure(errorInfo: ErrorInfo) { }
})
```

## Sending Messages

```kotlin
import io.agora.rtm.PublishOptions
import io.agora.rtm.RtmConstants

// Publish to a channel
val options = PublishOptions().apply {
    customType = "chat.message"
}
rtmClient.publish("channel-name", "Hello!", options, object : ResultCallback<Void> {
    override fun onSuccess(responseInfo: Void?) { }
    override fun onFailure(errorInfo: ErrorInfo) { }
})

// Publish JSON data
val json = JSONObject().apply {
    put("type", "control")
    put("action", "mute-all")
}.toString()
rtmClient.publish("channel-name", json, options, object : ResultCallback<Void> {
    override fun onSuccess(responseInfo: Void?) { }
    override fun onFailure(errorInfo: ErrorInfo) { }
})

// Peer-to-peer (user channel)
val p2pOptions = PublishOptions().apply {
    setChannelType(RtmConstants.RtmChannelType.USER)
    customType = "user.transcription"
}
rtmClient.publish("target-user-id", message, p2pOptions, object : ResultCallback<Void> {
    override fun onSuccess(responseInfo: Void?) { }
    override fun onFailure(errorInfo: ErrorInfo) { }
})
```

## Receiving Messages

Implement `RtmEventListener`:

```kotlin
val rtmEventListener = object : RtmEventListener {
    override fun onMessageEvent(event: MessageEvent?) {
        event ?: return
        val message = event.message.data as? String ?: return
        Log.d("RTM", "From: ${event.publisherId}, Channel: ${event.channelName}, Message: $message")
        // Parse JSON if needed
        try {
            val json = JSONObject(message)
        } catch (e: Exception) { }
    }
}
```

## Presence Events

```kotlin
val rtmEventListener = object : RtmEventListener {
    override fun onPresenceEvent(event: PresenceEvent?) {
        event ?: return
        when (event.eventType) {
            RtmConstants.RtmPresenceEventType.SNAPSHOT -> {
                for (user in event.snapshot) {
                    Log.d("RTM", "Online: ${user.userId}, states: ${user.states}")
                }
            }
            RtmConstants.RtmPresenceEventType.REMOTE_JOIN -> {
                Log.d("RTM", "User joined: ${event.publisherId}")
            }
            RtmConstants.RtmPresenceEventType.REMOTE_LEAVE,
            RtmConstants.RtmPresenceEventType.REMOTE_TIMEOUT -> {
                Log.d("RTM", "User left: ${event.publisherId}")
            }
            RtmConstants.RtmPresenceEventType.REMOTE_STATE_CHANGED -> {
                Log.d("RTM", "State changed: ${event.publisherId}, ${event.stateItems}")
            }
            else -> {}
        }
    }
}
```

## Cleanup

```kotlin
fun cleanup() {
    rtmClient.unsubscribe("channel-name", object : ResultCallback<Void> {
        override fun onSuccess(responseInfo: Void?) {
            rtmClient.logout(object : ResultCallback<Void> {
                override fun onSuccess(responseInfo: Void?) {
                    rtmClient.release()
                }
                override fun onFailure(errorInfo: ErrorInfo) {
                    rtmClient.release()
                }
            })
        }
        override fun onFailure(errorInfo: ErrorInfo) { }
    })
}
```

## Complete Example

```kotlin
class SignalingActivity : AppCompatActivity() {
    private lateinit var rtmClient: RtmClient
    private val channelName = "my-channel"

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)

        val config = RtmConfig.Builder("your-app-id", "user-123")
            .eventListener(rtmEventListener)
            .build()
        rtmClient = RtmClient.create(config)

        rtmClient.login("YOUR_RTM_TOKEN", object : ResultCallback<Void> {
            override fun onSuccess(responseInfo: Void?) {
                subscribeToChannel()
            }
            override fun onFailure(errorInfo: ErrorInfo) {
                Log.e("RTM", "Login failed: ${errorInfo.errorReason}")
            }
        })
    }

    private fun subscribeToChannel() {
        val options = SubscribeOptions().apply {
            withMessage = true
            withPresence = true
        }
        rtmClient.subscribe(channelName, options, object : ResultCallback<Void> {
            override fun onSuccess(responseInfo: Void?) { }
            override fun onFailure(errorInfo: ErrorInfo) {
                Log.e("RTM", "Subscribe failed: ${errorInfo.errorReason}")
            }
        })
    }

    fun sendMessage(text: String) {
        val options = PublishOptions().apply { customType = "chat.message" }
        rtmClient.publish(channelName, text, options, object : ResultCallback<Void> {
            override fun onSuccess(responseInfo: Void?) { }
            override fun onFailure(errorInfo: ErrorInfo) { }
        })
    }

    private val rtmEventListener = object : RtmEventListener {
        override fun onMessageEvent(event: MessageEvent?) {
            event ?: return
            val message = event.message.data as? String ?: return
            runOnUiThread {
                Log.d("RTM", "${event.publisherId}: $message")
            }
        }

        override fun onPresenceEvent(event: PresenceEvent?) {
            event ?: return
            if (event.eventType == RtmConstants.RtmPresenceEventType.REMOTE_JOIN) {
                Log.d("RTM", "User joined: ${event.publisherId}")
            }
        }
    }

    override fun onDestroy() {
        super.onDestroy()
        rtmClient.unsubscribe(channelName, object : ResultCallback<Void> {
            override fun onSuccess(responseInfo: Void?) {
                rtmClient.logout(object : ResultCallback<Void> {
                    override fun onSuccess(responseInfo: Void?) { rtmClient.release() }
                    override fun onFailure(errorInfo: ErrorInfo) { rtmClient.release() }
                })
            }
            override fun onFailure(errorInfo: ErrorInfo) { }
        })
    }
}
```

## Notes

- Android RTM UIDs are **strings**. When pairing with RTC (which uses `Int`), use `rtcUid.toString()` as the RTM userId.
- Login must complete before any subscribe/publish operations.
- Call `release()` only after logout completes to avoid resource leaks.

For test setup and mocking patterns, see [references/testing-guidance/SKILL.md](../testing-guidance/SKILL.md).

## Official Documentation

For APIs or features not covered above:

- Quick-start guide: <https://docs-md.agora.io/en/signaling/get-started/sdk-quickstart.md?platform=android>
- API Reference: <https://api-ref.agora.io/en/signaling/android/2.x/API/rtm_api_overview.html>
