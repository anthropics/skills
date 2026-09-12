# Agora RTC Android SDK (Kotlin)

## Table of Contents

- [Installation](#installation)
- [Engine Initialization](#engine-initialization)
- [Joining a Channel](#joining-a-channel)
- [Video Setup](#video-setup)
- [Audio Setup](#audio-setup)
- [Event Handling (IRtcEngineEventHandler)](#event-handling)
- [Leaving and Cleanup](#leaving-and-cleanup)
- [Token Renewal](#token-renewal)
- [Complete Example: Video Call](#complete-example-video-call)

API Reference: <https://api-ref.agora.io/en/video-sdk/android/4.x/API/rtc_api_overview.html>

## Installation

Add to `build.gradle`:

```groovy
dependencies {
    implementation 'io.agora.rtc:full-sdk:4.3.+'
    // or for voice-only: implementation 'io.agora.rtc:voice-sdk:4.3.+'
}
```

Add permissions to `AndroidManifest.xml`:

```xml
<uses-permission android:name="android.permission.INTERNET" />
<uses-permission android:name="android.permission.CAMERA" />
<uses-permission android:name="android.permission.RECORD_AUDIO" />
<uses-permission android:name="android.permission.MODIFY_AUDIO_SETTINGS" />
<uses-permission android:name="android.permission.ACCESS_WIFI_STATE" />
<uses-permission android:name="android.permission.ACCESS_NETWORK_STATE" />
<uses-permission android:name="android.permission.BLUETOOTH" />
<!-- Android 12+ (API 31+): required for Bluetooth audio headsets -->
<uses-permission android:name="android.permission.BLUETOOTH_CONNECT" />
```

Request runtime permissions for `CAMERA` and `RECORD_AUDIO` before initializing.

## Engine Initialization

```kotlin
import io.agora.rtc2.RtcEngine
import io.agora.rtc2.RtcEngineConfig
import io.agora.rtc2.Constants

val config = RtcEngineConfig().apply {
    mContext = applicationContext
    mAppId = "your-app-id"
    mEventHandler = rtcEventHandler
    mChannelProfile = Constants.CHANNEL_PROFILE_COMMUNICATION
    // or Constants.CHANNEL_PROFILE_LIVE_BROADCASTING
}

val agoraEngine = RtcEngine.create(config)
```

## Joining a Channel

```kotlin
import io.agora.rtc2.ChannelMediaOptions

val options = ChannelMediaOptions().apply {
    clientRoleType = Constants.CLIENT_ROLE_BROADCASTER
    channelProfile = Constants.CHANNEL_PROFILE_COMMUNICATION
    publishMicrophoneTrack = true
    publishCameraTrack = true
    autoSubscribeAudio = true
    autoSubscribeVideo = true
}

agoraEngine.joinChannel(token, "channel-name", 0, options)
// token: null for testing, uid: 0 for auto-assignment
```

## Video Setup

```kotlin
// Enable video module
agoraEngine.enableVideo()

// Configure encoder
val videoConfig = VideoEncoderConfiguration().apply {
    dimensions = VideoEncoderConfiguration.VideoDimensions(640, 360)
    frameRate = VideoEncoderConfiguration.FRAME_RATE.FRAME_RATE_FPS_24.value
    bitrate = VideoEncoderConfiguration.STANDARD_BITRATE
    orientationMode = VideoEncoderConfiguration.ORIENTATION_MODE.ORIENTATION_MODE_ADAPTIVE
}
agoraEngine.setVideoEncoderConfiguration(videoConfig)

// Local preview
val localSurfaceView = SurfaceView(context)
localVideoContainer.addView(localSurfaceView)
agoraEngine.setupLocalVideo(
    VideoCanvas(localSurfaceView, VideoCanvas.RENDER_MODE_HIDDEN, 0)
)
agoraEngine.startPreview()

// Remote video (call in onUserJoined callback)
val remoteSurfaceView = SurfaceView(context)
remoteVideoContainer.addView(remoteSurfaceView)
agoraEngine.setupRemoteVideo(
    VideoCanvas(remoteSurfaceView, VideoCanvas.RENDER_MODE_HIDDEN, remoteUid)
)
```

## Audio Setup

```kotlin
// Enable audio (enabled by default)
agoraEngine.enableAudio()

// Audio profile (SDK 4.x: set profile and scenario separately)
agoraEngine.setAudioProfile(Constants.AUDIO_PROFILE_DEFAULT)
agoraEngine.setAudioScenario(Constants.AUDIO_SCENARIO_DEFAULT)

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
agoraEngine.muteRemoteAudioStream(remoteUid, true)
```

## Event Handling

```kotlin
private val rtcEventHandler = object : IRtcEngineEventHandler() {
    // Successfully joined channel
    override fun onJoinChannelSuccess(channel: String?, uid: Int, elapsed: Int) {
        runOnUiThread {
            Log.d("Agora", "Joined channel: $channel, uid: $uid")
        }
    }

    // Remote user joined
    override fun onUserJoined(uid: Int, elapsed: Int) {
        runOnUiThread {
            val remoteSurfaceView = SurfaceView(context)
            remoteVideoContainer.addView(remoteSurfaceView)
            agoraEngine.setupRemoteVideo(
                VideoCanvas(remoteSurfaceView, VideoCanvas.RENDER_MODE_HIDDEN, uid)
            )
        }
    }

    // Remote user left
    override fun onUserOffline(uid: Int, reason: Int) {
        runOnUiThread {
            agoraEngine.setupRemoteVideo(VideoCanvas(null, VideoCanvas.RENDER_MODE_HIDDEN, uid))
            // Remove remote view from container
        }
    }

    // Token expiring
    override fun onTokenPrivilegeWillExpire(token: String?) {
        // Fetch new token and renew
        fetchNewToken { newToken ->
            agoraEngine.renewToken(newToken)
        }
    }

    // Error
    override fun onError(err: Int) {
        Log.e("Agora", "Error code: $err")
    }

    // Network quality
    override fun onNetworkQuality(uid: Int, txQuality: Int, rxQuality: Int) {
        // 0=unknown, 1=excellent, 2=good, 3=poor, 4=bad, 5=very bad, 6=disconnected
    }
}
```

## Leaving and Cleanup

```kotlin
fun leaveChannel() {
    agoraEngine.stopPreview()
    agoraEngine.leaveChannel()
}

// Full cleanup (activity/app destruction)
fun destroy() {
    agoraEngine.stopPreview()
    agoraEngine.leaveChannel()
    RtcEngine.destroy()
}
```

## Token Renewal

```kotlin
override fun onTokenPrivilegeWillExpire(token: String?) {
    lifecycleScope.launch {
        val newToken = fetchTokenFromServer(channelName, localUid)
        agoraEngine.renewToken(newToken)
    }
}
```

## Complete Example: Video Call

```kotlin
class VideoCallActivity : AppCompatActivity() {
    private val appId = "your-app-id"
    private var token: String? = null
    private val channelName = "test"
    private var agoraEngine: RtcEngine? = null
    private var isJoined = false

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        setContentView(R.layout.activity_video_call)

        // Request permissions first
        if (checkPermissions()) {
            initializeAgora()
        } else {
            requestPermissions()
        }
    }

    private fun initializeAgora() {
        val config = RtcEngineConfig().apply {
            mContext = applicationContext
            mAppId = appId
            mEventHandler = rtcEventHandler
        }
        agoraEngine = RtcEngine.create(config)
        agoraEngine?.enableVideo()

        agoraEngine?.setVideoEncoderConfiguration(
            VideoEncoderConfiguration().apply {
                dimensions = VideoEncoderConfiguration.VideoDimensions(640, 360)
                frameRate = VideoEncoderConfiguration.FRAME_RATE.FRAME_RATE_FPS_24.value
                bitrate = VideoEncoderConfiguration.STANDARD_BITRATE
            }
        )
    }

    fun joinChannel() {
        // Setup local preview
        val localView = SurfaceView(this)
        findViewById<FrameLayout>(R.id.local_video_container).addView(localView)
        agoraEngine?.setupLocalVideo(VideoCanvas(localView, VideoCanvas.RENDER_MODE_HIDDEN, 0))
        agoraEngine?.startPreview()

        // Join channel
        val options = ChannelMediaOptions().apply {
            clientRoleType = Constants.CLIENT_ROLE_BROADCASTER
            channelProfile = Constants.CHANNEL_PROFILE_COMMUNICATION
            publishMicrophoneTrack = true
            publishCameraTrack = true
        }
        agoraEngine?.joinChannel(token, channelName, 0, options)
    }

    fun leaveChannel() {
        agoraEngine?.stopPreview()
        agoraEngine?.leaveChannel()
        isJoined = false
    }

    private val rtcEventHandler = object : IRtcEngineEventHandler() {
        override fun onJoinChannelSuccess(channel: String?, uid: Int, elapsed: Int) {
            runOnUiThread { isJoined = true }
        }

        override fun onUserJoined(uid: Int, elapsed: Int) {
            runOnUiThread {
                val remoteView = SurfaceView(this@VideoCallActivity)
                findViewById<FrameLayout>(R.id.remote_video_container).addView(remoteView)
                agoraEngine?.setupRemoteVideo(
                    VideoCanvas(remoteView, VideoCanvas.RENDER_MODE_HIDDEN, uid)
                )
            }
        }

        override fun onUserOffline(uid: Int, reason: Int) {
            runOnUiThread {
                agoraEngine?.setupRemoteVideo(VideoCanvas(null, VideoCanvas.RENDER_MODE_HIDDEN, uid))
            }
        }

        override fun onTokenPrivilegeWillExpire(token: String?) {
            lifecycleScope.launch {
                val newToken = fetchTokenFromServer(channelName, 0)
                agoraEngine?.renewToken(newToken)
            }
        }
    }

    override fun onDestroy() {
        super.onDestroy()
        agoraEngine?.stopPreview()
        agoraEngine?.leaveChannel()
        RtcEngine.destroy()
        agoraEngine = null
    }

    private fun checkPermissions(): Boolean {
        return ContextCompat.checkSelfPermission(this, Manifest.permission.CAMERA) ==
            PackageManager.PERMISSION_GRANTED &&
            ContextCompat.checkSelfPermission(this, Manifest.permission.RECORD_AUDIO) ==
            PackageManager.PERMISSION_GRANTED
    }

    private fun requestPermissions() {
        ActivityCompat.requestPermissions(
            this,
            arrayOf(Manifest.permission.CAMERA, Manifest.permission.RECORD_AUDIO),
            PERMISSION_REQUEST_CODE
        )
    }

    companion object {
        private const val PERMISSION_REQUEST_CODE = 22
    }
}
```

## Official Documentation

For APIs or features not covered above:

- API Reference: <https://api-ref.agora.io/en/video-sdk/android/4.x/API/rtc_api_overview.html>
- Guides: <https://docs.agora.io/en/video-calling/overview/product-overview>
