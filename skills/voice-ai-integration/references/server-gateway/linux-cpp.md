# Server Gateway SDK — Linux C++

## Initialization

```cpp
// Create and initialize IAgoraService — one instance per process
auto service = createAgoraService();
agora::base::AgoraServiceConfiguration scfg;
scfg.appId = appid;
scfg.enableAudioProcessor = true;
scfg.enableAudioDevice = false;  // servers don't use audio devices
scfg.enableVideo = true;
scfg.useStringUid = false;  // set true to use string UIDs
if (service->initialize(scfg) != agora::ERR_OK) {
    return nullptr;
}
```

## Create and Connect

```cpp
// Create connection — autoSubscribe must be false; set BROADCASTER role
agora::rtc::RtcConnectionConfiguration ccfg;
ccfg.autoSubscribeAudio = false;
ccfg.autoSubscribeVideo = false;
ccfg.clientRoleType = agora::rtc::CLIENT_ROLE_BROADCASTER;
agora::agora_refptr<agora::rtc::IRtcConnection> connection =
    service->createRtcConnection(ccfg);

// Register connection observer before connecting
auto connObserver = std::make_shared<SampleConnectionObserver>();
connection->registerObserver(connObserver.get());

// Connect to channel
if (connection->connect(appId, channelId, userId)) {
    AG_LOG(ERROR, "Failed to connect to Agora channel!");
    return -1;
}
```

## Sending Media

### Create senders

```cpp
agora::agora_refptr<agora::rtc::IMediaNodeFactory> factory =
    service->createMediaNodeFactory();

// PCM audio sender
agora::agora_refptr<agora::rtc::IAudioPcmDataSender> audioPcmDataSender =
    factory->createAudioPcmDataSender();

// YUV video sender
agora::agora_refptr<agora::rtc::IVideoFrameSender> videoFrameSender =
    factory->createVideoFrameSender();

// Encoded audio sender (AAC, Opus, etc.)
agora::agora_refptr<agora::rtc::IAudioEncodedFrameSender> audioFrameSender =
    factory->createAudioEncodedFrameSender();

// Encoded video sender (H.264, etc.)
agora::agora_refptr<agora::rtc::IVideoEncodedImageSender> videoEncodedFrameSender =
    factory->createVideoEncodedImageSender();
```

### Create and publish tracks

```cpp
// PCM audio track
agora::agora_refptr<agora::rtc::ILocalAudioTrack> customAudioTrack =
    service->createCustomAudioTrack(audioPcmDataSender);

// Encoded audio track
agora::agora_refptr<agora::rtc::ILocalAudioTrack> customAudioTrack =
    service->createCustomAudioTrack(audioFrameSender, agora::base::MIX_DISABLED);

// YUV video track
agora::agora_refptr<agora::rtc::ILocalVideoTrack> customVideoTrack =
    service->createCustomVideoTrack(videoFrameSender);

// Encoded video track
agora::agora_refptr<agora::rtc::ILocalVideoTrack> customVideoTrack =
    service->createCustomVideoTrack(videoEncodedFrameSender);

// Enable and publish
customAudioTrack->setEnabled(true);
connection->getLocalUser()->publishAudio(customAudioTrack);
customVideoTrack->setEnabled(true);
connection->getLocalUser()->publishVideo(customVideoTrack);
```

### Send PCM audio (10 ms intervals — required)

```cpp
// PCM must be sent in exactly 10 ms frames — use a pacer thread
static void SampleSendAudioTask(
    agora::agora_refptr<agora::rtc::IAudioPcmDataSender> audioFrameSender,
    bool& exitFlag) {
    PacerInfo pacer = {0, 10, std::chrono::steady_clock::now()};
    while (!exitFlag) {
        // samplesPer10ms = sampleRate / 100
        audioFrameSender->sendAudioPcmData(
            frameBuf, 0, samplesPer10ms,
            agora::rtc::TWO_BYTES_PER_SAMPLE,
            numOfChannels, sampleRate);
        waitBeforeNextSend(pacer);
    }
}
```

### Send encoded H.264 video

```cpp
static void sendOneH264Frame(
    int frameRate,
    std::unique_ptr<HelperH264Frame> h264Frame,
    agora::agora_refptr<agora::rtc::IVideoEncodedImageSender> videoH264FrameSender) {
    agora::rtc::EncodedVideoFrameInfo videoEncodedFrameInfo;
    videoEncodedFrameInfo.rotation = agora::rtc::VIDEO_ORIENTATION_0;
    videoEncodedFrameInfo.codecType = agora::rtc::VIDEO_CODEC_H264;
    videoEncodedFrameInfo.framesPerSecond = frameRate;
    videoEncodedFrameInfo.frameType =
        h264Frame->isKeyFrame
            ? agora::rtc::VIDEO_FRAME_TYPE_KEY_FRAME
            : agora::rtc::VIDEO_FRAME_TYPE_DELTA_FRAME;

    videoH264FrameSender->sendEncodedVideoImage(
        reinterpret_cast<uint8_t*>(h264Frame->buffer.get()),
        h264Frame->bufferLen,
        videoEncodedFrameInfo);
}
```

## Receiving Media

```cpp
// Register observers via SampleLocalUserObserver (wraps ILocalUserObserver)
auto localUserObserver =
    std::make_shared<SampleLocalUserObserver>(connection->getLocalUser());

// Audio: set PCM params before registering observer
connection->getLocalUser()->setPlaybackAudioFrameBeforeMixingParameters(
    numOfChannels, sampleRate);

auto pcmFrameObserver = std::make_shared<PcmFrameObserver>(outputFile);
localUserObserver->setAudioFrameObserver(pcmFrameObserver.get());

// Video (encoded H.264)
auto h264FrameReceiver = std::make_shared<H264FrameReceiver>(outputFile);
localUserObserver->setVideoEncodedImageReceiver(h264FrameReceiver.get());
```

### PCM receive callback

```cpp
bool PcmFrameObserver::onPlaybackAudioFrameBeforeMixing(
    const char* channelId,
    agora::media::base::user_id_t userId,
    AudioFrame& audioFrame) {
    size_t writeBytes =
        audioFrame.samplesPerChannel * audioFrame.channels * sizeof(int16_t);
    fwrite(audioFrame.buffer, 1, writeBytes, pcmFile_);
    return true;
}
```

### Encoded video receive callback

```cpp
class H264FrameReceiver : public agora::rtc::IVideoEncodedImageReceiver {
public:
    bool OnEncodedVideoImageReceived(
        const uint8_t* imageBuffer,
        size_t length,
        const agora::rtc::EncodedVideoFrameInfo& videoEncodedFrameInfo) override;
};
```

### YUV video receive callback

```cpp
class YuvFrameObserver : public agora::rtc::IVideoFrameObserver2 {
public:
    void onFrame(
        const char* channelId,
        agora::user_id_t remoteUid,
        const agora::media::base::VideoFrame* frame) override;
};
```

## Video Mixing

```cpp
// Create mixer and mixed video track
agora::agora_refptr<agora::rtc::IVideoMixerSource> videoMixer =
    factory->createVideoMixer();
agora::agora_refptr<agora::rtc::ILocalVideoTrack> mixVideoTrack =
    service->createMixedVideoTrack(videoMixer);

// Configure encoder
agora::rtc::VideoEncoderConfiguration encoderConfig;
encoderConfig.codecType = agora::rtc::VIDEO_CODEC_H264;
encoderConfig.dimensions.width = 1920;
encoderConfig.dimensions.height = 1080;
encoderConfig.frameRate = 15;
mixVideoTrack->setVideoEncoderConfiguration(encoderConfig);

// Add remote video tracks and set layout
videoMixer->addVideoTrack(userId, remote_video_track_);
videoMixer->setStreamLayout(userId, layout);  // position/size per user
videoMixer->setBackground(1920, 1080, 15);
videoMixer->refresh();  // apply layout changes
```

## Shutdown Sequence

Order matters — follow exactly:

```cpp
// 1. Unpublish tracks
connection->getLocalUser()->unpublishAudio(customAudioTrack);
connection->getLocalUser()->unpublishVideo(customVideoTrack);

// 2. Unregister observers
connection->unregisterObserver(connObserver.get());
local_user_->unregisterAudioFrameObserver(audio_frame_observer_);
local_user_->unregisterVideoFrameObserver(video_frame_observer_);

// 3. Disconnect
connection->disconnect();

// 4. Release objects (nullptr in this order)
connObserver.reset();
localUserObserver.reset();
audioPcmDataSender = nullptr;
videoFrameSender = nullptr;
customAudioTrack = nullptr;
customVideoTrack = nullptr;
factory = nullptr;
connection = nullptr;

// 5. Release service last
service->release();
service = nullptr;
```

## Official Documentation

- **[Send and Receive Media Streams](https://docs.agora.io/en/server-gateway/develop/send-receive-media-streams?platform=linux-cpp)**
- **[Video Mixing](https://docs.agora.io/en/server-gateway/develop/video-mixing?platform=linux-cpp)**
- **[API Reference](https://api-ref.agora.io/en/server-gateway-sdk/linux-cpp/4.x/index.html)**
