# Testing Guidance — RTC Android (Kotlin)

Use interface extraction with Mockito. `RtcEngine.create(context, appId, handler)`
is a factory method — wrap it behind an interface to enable mocking.

Pattern:

```kotlin
interface RtcEngineInterface {
    fun joinChannel(token: String?, channelName: String, uid: Int,
                    options: ChannelMediaOptions): Int
    fun leaveChannel(): Int
    fun enableVideo(): Int
    fun muteLocalAudioStream(mute: Boolean): Int
    fun renewToken(token: String): Int
}

class RtcEngineAdapter(private val engine: RtcEngine) : RtcEngineInterface {
    override fun joinChannel(token: String?, channelName: String, uid: Int,
                              options: ChannelMediaOptions) =
        engine.joinChannel(token, channelName, uid, options)
    override fun leaveChannel() = engine.leaveChannel()
    override fun enableVideo() = engine.enableVideo()
    override fun muteLocalAudioStream(mute: Boolean) = engine.muteLocalAudioStream(mute)
    override fun renewToken(token: String) = engine.renewToken(token)
}
```

Example:

```kotlin
@RunWith(MockitoJUnitRunner::class)
class RtcManagerTest {
    @Mock lateinit var mockEngine: RtcEngineInterface

    @Test
    fun `joins channel with correct parameters`() {
        whenever(mockEngine.joinChannel(anyOrNull(), any(), any(), any())).thenReturn(0)

        val manager = RtcManager(engine = mockEngine)
        manager.join(channel = "test", token = null, uid = 0)

        verify(mockEngine).joinChannel(eq(null), eq("test"), eq(0), any())
    }

    @Test
    fun `renews token when privilege will expire`() {
        val manager = RtcManager(engine = mockEngine)
        val handler = manager.getRtcEventHandler()

        handler.onTokenPrivilegeWillExpire("expiring-token")

        verify(mockEngine, timeout(500)).renewToken(any())
    }
}
```

Add to `build.gradle`:

```groovy
testImplementation 'org.mockito:mockito-kotlin:5.+'
testImplementation 'org.mockito:mockito-core:5.+'
```

Primary assertions:

- join called with correct token/channel/UID
- engine setup methods invoked in order
- token renewal path is wired
- cleanup/leave path runs on disconnect
