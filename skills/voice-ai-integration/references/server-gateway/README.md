# Agora Server Gateway SDK

Self-hosted SDK for transmitting audio and video streams between server-side applications and Agora's Voice and Video SDKs via the Agora SDRTN®.

## Critical Rules

1. **Video SDK channel must use `LIVE_BROADCASTING` mode** — standard `COMMUNICATION` mode is not supported when the remote peer is a Server Gateway client.
2. **PCM audio must be sent in 10 ms intervals** — the SDK only accepts PCM frames of exactly 10 ms length.
3. **AAC audio cannot use 44.1 kHz sampling** — use 16 kHz or 48 kHz instead.
4. **All SDK methods are async and non-blocking** — use event callbacks and observers; do not expect synchronous results.
5. **Server requires internet access to `*.agora.io` and `*.agoralab.co`** — ensure firewall rules allow outbound connections to these domains.
6. **This is a self-hosted SDK, not a REST API** — the SDK runs as a process on your Linux server, not as a cloud service you call.

## Key Concepts

- **IAgoraService** — root object. Create once per process, initialize with audio/video config before creating any connections.
- **IRtcConnection** — represents a connection to one RTC channel. Create one per channel. Manages join/leave lifecycle.
- **IMediaNodeFactory** — factory for creating senders and receivers (audio PCM sender, video YUV sender, encoded video sender, etc.).
- **Local tracks** — wrap senders/receivers and get published/subscribed via the connection.
- **Observers** — implement `ILocalUserObserver`, `IAudioFrameObserver`, `IVideoEncodedImageReceiver` to receive incoming media frames via callbacks.

## Architecture

```text
Your Server App (Server Gateway SDK)
    ↕  audio/video frames (PCM, YUV, encoded)
Agora SDRTN® (global real-time network)
    ↕
Video SDK clients (Web, iOS, Android, etc.)
```

Typical flow:
1. Initialize `IAgoraService` with audio/video support enabled
2. Create `IRtcConnection` and join channel
3. Create media senders via `IMediaNodeFactory`, wrap in local tracks, publish
4. Register observers to receive incoming frames via callbacks
5. On shutdown: unpublish → unregister observers → disconnect → release all objects (order matters)

## Supported Platforms

| Platform | Language | Min OS |
|----------|----------|--------|
| Linux x86-64 | C++ | Ubuntu 14.04+ / CentOS 7.0+ |
| Linux x86-64 | Java | Ubuntu 14.04+ / CentOS 7.0+ |
| Linux x86-64 | Go | Ubuntu 18.04+ / CentOS 7.0+ |
| Linux x86-64 | Python | Ubuntu 18.04+ / CentOS 7.0+ |
| arm64 | C++ | Ubuntu 14.04+ |

Hardware minimum: 8-core CPU 1.8 GHz, 2 GB RAM (4 GB recommended).

## Media Formats

| Type | Formats supported |
|------|------------------|
| Audio send | PCM (10 ms frames) |
| Audio receive | PCM |
| Video send | YUV, encoded (H.264, etc.) |
| Video receive | Encoded frames |

## Use Cases

- **Call centers** — server-side agent voice processing
- **AI interactive classes** — server processes audio/video for AI analysis
- **Network testing** — automated stream injection and validation
- **aPaaS** — application platform integrations that need server-side media

## Platform Reference Files

- **[linux-cpp.md](linux-cpp.md)** — C++ full implementation: init, senders, receivers, video mixing, shutdown sequence
- **Java, Go, Python** — Level 2 fetch required; use [../doc-fetching.md](../doc-fetching.md) or fetch directly from the links below

## When to Fetch More

Always use Level 2 fetch for Java, Go, and Python quick-starts, SDK download links, and any platform-specific method signatures. Direct fallback URLs:

- **Java** — <https://docs-md.agora.io/en/server-gateway/get-started/integrate-sdk?platform=java.md>
- **Go** — <https://docs-md.agora.io/en/server-gateway/get-started/integrate-sdk?platform=go.md>
- **Python** — <https://docs-md.agora.io/en/server-gateway/get-started/integrate-sdk?platform=python.md>
- **Product Overview** — <https://docs-md.agora.io/en/server-gateway/overview/product-overview.md>
- **SDK Downloads** — <https://docs.agora.io/en/sdks>
