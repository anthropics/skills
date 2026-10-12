# Events [Experimental]

{{ experimental_feature_warning() }}

Bidirectional streaming events enable real-time monitoring and processing of audio, text, and tool execution during persistent conversations. Unlike standard streaming which uses async iterators or callbacks, bidirectional streaming uses `send()` and `receive()` methods for explicit control over the conversation flow.

## Event Model

Bidirectional streaming uses a different event model than [standard streaming](../../streaming/index.md):

**Standard Streaming:**

- Uses `stream_async()` or callback handlers
- Request-response pattern (one invocation per call)
- Events flow in one direction (model → application)

**Bidirectional Streaming:**

- Uses `send()` and `receive()` methods
- Persistent connection (multiple turns per connection)
- Events flow in both directions (application ↔ model)
- Supports real-time audio and interruptions

```python
import asyncio
from strands.experimental.bidi import BidiAgent
from strands.experimental.bidi.models import BidiNovaSonicModel

async def main():
    model = BidiNovaSonicModel()
    
    async with BidiAgent(model=model) as agent:
        # Send input to model
        await agent.send("What is 2+2?")
        
        # Receive events from model
        async for event in agent.receive():
            print(f"Event: {event['type']}")

asyncio.run(main())
```

## Input Event Types

Events sent to the model via `agent.send()`.

### BidiTextInputEvent

Send text input to the model.

```python
await agent.send("What is the weather?")
# Or explicitly:
from strands.experimental.bidi.types.events import BidiTextInputEvent
await agent.send(BidiTextInputEvent(text="What is the weather?", role="user"))
```

### BidiAudioInputEvent

Send audio input to the model. Audio must be base64-encoded.

```python
import base64
from strands.experimental.bidi.types.events import BidiAudioInputEvent

audio_bytes = record_audio()  # Your audio capture logic
audio_base64 = base64.b64encode(audio_bytes).decode('utf-8')

await agent.send(BidiAudioInputEvent(
    audio=audio_base64,
    format="pcm",
    sample_rate=16000,
    channels=1
))
```

### BidiImageInputEvent

Send image input to the model. Images must be base64-encoded.

```python
import base64
from strands.experimental.bidi.types.events import BidiImageInputEvent

with open("image.jpg", "rb") as f:
    image_bytes = f.read()
    image_base64 = base64.b64encode(image_bytes).decode('utf-8')

await agent.send(BidiImageInputEvent(
    image=image_base64,
    mime_type="image/jpeg"
))
```

## Output Event Types

Events received from the model via `agent.receive()`.

### Connection Lifecycle Events

Events that track the connection state throughout the conversation.

#### BidiConnectionStartEvent

Emitted when the streaming connection is established and ready for interaction.

```python
{
    "type": "bidi_connection_start",
    "connection_id": "conn_abc123",
    "model": "amazon.nova-sonic-v1:0"
}
```

**Properties:**

- `connection_id`: Unique identifier for this streaming connection
- `model`: Model identifier (e.g., "amazon.nova-sonic-v1:0", "gemini-2.0-flash-live")

#### BidiConnectionRestartEvent

Emitted when the agent is restarting the model connection after a timeout. The conversation history is preserved and the connection resumes automatically.

```python
{
    "type": "bidi_connection_restart",
    "timeout_error": BidiModelTimeoutError(...)
}
```

**Properties:**

- `timeout_error`: The timeout error that triggered the restart

**Usage:**
```python
async for event in agent.receive():
    if event["type"] == "bidi_connection_restart":
        print("Connection restarting, please wait...")
        # Connection resumes automatically with full history
```

See [Connection Lifecycle](agent.md#connection-restart) for more details on timeout handling.

#### BidiConnectionCloseEvent

Emitted when the streaming connection is closed.

```python
{
    "type": "bidi_connection_close",
    "connection_id": "conn_abc123",
    "reason": "user_request"
}
```

**Properties:**

- `connection_id`: Unique identifier for this streaming connection
- `reason`: Why the connection closed
  - `"client_disconnect"`: Client disconnected
  - `"timeout"`: Connection timed out
  - `"error"`: Error occurred
  - `"complete"`: Conversation completed normally
  - `"user_request"`: User requested closure (via `stop_conversation` tool)

### Response Lifecycle Events

Events that track individual model responses within the conversation.

#### BidiResponseStartEvent

Emitted when the model begins generating a response.

```python
{
    "type": "bidi_response_start",
    "response_id": "resp_xyz789"
}
```

**Properties:**

- `response_id`: Unique identifier for this response (matches `BidiResponseCompleteEvent`)

#### BidiResponseCompleteEvent

Emitted when the model finishes generating a response.

```python
{
    "type": "bidi_response_complete",
    "response_id": "resp_xyz789",
    "stop_reason": "complete"
}
```

**Properties:**

- `response_id`: Unique identifier for this response
- `stop_reason`: Why the response ended
  - `"complete"`: Model completed its response
  - `"interrupted"`: User interrupted the response
  - `"tool_use"`: Model is requesting tool execution
  - `"error"`: Error occurred during generation

### Audio Events

Events for streaming audio input and output.

#### BidiAudioStreamEvent

Emitted when the model generates audio output. Audio is base64-encoded for JSON compatibility.

```python
{
    "type": "bidi_audio_stream",
    "audio": "base64_encoded_audio_data...",
    "format": "pcm",
    "sample_rate": 16000,
    "channels": 1
}
```

**Properties:**

- `audio`: Base64-encoded audio string
- `format`: Audio encoding format (`"pcm"`, `"wav"`, `"opus"`, `"mp3"`)
- `sample_rate`: Sample rate in Hz (`16000`, `24000`, `48000`)
- `channels`: Number of audio channels (`1` = mono, `2` = stereo)

**Usage:**
```python
import base64

async for event in agent.receive():
    if event["type"] == "bidi_audio_stream":
        # Decode and play audio
        audio_bytes = base64.b64decode(event["audio"])
        play_audio(audio_bytes, sample_rate=event["sample_rate"])
```

### Transcript Events

Events for speech-to-text transcription of both user and assistant speech.

#### BidiTranscriptStreamEvent

Emitted when speech is transcribed. Supports incremental updates for providers that send partial transcripts.

```python
{
    "type": "bidi_transcript_stream",
    "delta": {"text": "Hello"},
    "text": "Hello",
    "role": "assistant",
    "is_final": True,
    "current_transcript": "Hello world"
}
```

**Properties:**

- `delta`: The incremental transcript change
- `text`: The delta text (same as delta content)
- `role`: Who is speaking (`"user"` or `"assistant"`)
- `is_final`: Whether this is the final/complete transcript
- `current_transcript`: The accumulated transcript text so far (None for first delta)

**Usage:**
```python
async for event in agent.receive():
    if event["type"] == "bidi_transcript_stream":
        role = event["role"]
        text = event["text"]
        is_final = event["is_final"]
        
        if is_final:
            print(f"{role}: {text}")
        else:
            print(f"{role} (preview): {text}")
```

### Interruption Events

Events for handling user interruptions during model responses.

#### BidiInterruptionEvent

Emitted when the model's response is interrupted, typically by user speech detected via voice activity detection.

```python
{
    "type": "bidi_interruption",
    "reason": "user_speech"
}
```

**Properties:**

- `reason`: Why the interruption occurred
  - `"user_speech"`: User started speaking (most common)
  - `"error"`: Error caused interruption

**Usage:**
```python
async for event in agent.receive():
    if event["type"] == "bidi_interruption":
        print(f"Interrupted by {event['reason']}")
        # Audio output automatically cleared
        # Model ready for new input
```

!!! note "BidiInterruptionEvent vs Human-in-the-Loop Interrupts"
    `BidiInterruptionEvent` is different from [human-in-the-loop (HIL) interrupts](../interrupts.md). BidiInterruptionEvent is emitted when the model detects user speech during audio conversations and automatically stops generating the current response. HIL interrupts pause agent execution to request human approval or input before continuing, typically used for tool execution approval. BidiInterruptionEvent is automatic and audio-specific, while HIL interrupts are programmatic and require explicit handling.

### Tool Events

Events for tool execution during conversations. Bidirectional streaming reuses the standard `ToolUseStreamEvent` from Strands.

#### ToolUseStreamEvent

Emitted when the model requests tool execution. See [Tools Overview](../../tools/index.md) for details.

```python
{
    "type": "tool_use_stream",
    "current_tool_use": {
        "toolUseId": "tool_123",
        "name": "calculator",
        "input": {"expression": "2+2"}
    }
}
```

**Properties:**

- `current_tool_use`: Information about the tool being used
  - `toolUseId`: Unique ID for this tool use
  - `name`: Name of the tool
  - `input`: Tool input parameters

Tools execute automatically in the background and results are sent back to the model without blocking the conversation.

### Usage Events

Events for tracking token consumption across different modalities.

#### BidiUsageEvent

Emitted periodically to report token usage with modality breakdown.

```python
{
    "type": "bidi_usage",
    "inputTokens": 150,
    "outputTokens": 75,
    "totalTokens": 225,
    "modality_details": [
        {"modality": "text", "input_tokens": 100, "output_tokens": 50},
        {"modality": "audio", "input_tokens": 50, "output_tokens": 25}
    ]
}
```

**Properties:**

- `inputTokens`: Total tokens used for all input modalities
- `outputTokens`: Total tokens used for all output modalities
- `totalTokens`: Sum of input and output tokens
- `modality_details`: Optional list of token usage per modality
- `cacheReadInputTokens`: Optional tokens read from cache
- `cacheWriteInputTokens`: Optional tokens written to cache

### Error Events

Events for error handling during conversations.

#### BidiErrorEvent

Emitted when an error occurs during the session.

```python
{
    "type": "bidi_error",
    "message": "Connection failed",
    "code": "ConnectionError",
    "details": {"retry_after": 5}
}
```

**Properties:**

- `message`: Human-readable error message
- `code`: Error code (exception class name)
- `details`: Optional additional error context
- `error`: The original exception (accessible via property, not in JSON)

**Usage:**
```python
async for event in agent.receive():
    if event["type"] == "bidi_error":
        print(f"Error: {event['message']}")
        # Access original exception if needed
        if hasattr(event, 'error'):
            raise event.error
```

## Event Flow Examples

### Basic Audio Conversation

```python
import asyncio
from strands.experimental.bidi import BidiAgent, BidiAudioIO
from strands.experimental.bidi.models import BidiNovaSonicModel

async def main():
    model = BidiNovaSonicModel()
    agent = BidiAgent(model=model)
    audio_io = BidiAudioIO()
    
    await agent.start()
    
    # Process events from audio conversation
    async for event in agent.receive():
        if event["type"] == "bidi_connection_start":
            print(f"🔗 Connected to {event['model']}")
        
        elif event["type"] == "bidi_response_start":
            print(f"▶️ Response starting: {event['response_id']}")
        
        elif event["type"] == "bidi_audio_stream":
            print(f"🔊 Audio chunk: {len(event['audio'])} bytes")
        
        elif event["type"] == "bidi_transcript_stream":
            if event["is_final"]:
                print(f"{event['role']}: {event['text']}")
        
        elif event["type"] == "bidi_response_complete":
            print(f"✅ Response complete: {event['stop_reason']}")
    
    await agent.stop()

asyncio.run(main())
```

### Tracking Transcript State

```python
import asyncio
from strands.experimental.bidi import BidiAgent
from strands.experimental.bidi.models import BidiNovaSonicModel

async def main():
    model = BidiNovaSonicModel()
    
    async with BidiAgent(model=model) as agent:
        await agent.send("Tell me about Python")
        
        # Track incremental transcript updates
        current_speaker = None
        current_text = ""
        
        async for event in agent.receive():
            if event["type"] == "bidi_transcript_stream":
                role = event["role"]
                
                if role != current_speaker:
                    if current_text:
                        print(f"\n{current_speaker}: {current_text}")
                    current_speaker = role
                    current_text = ""
                
                current_text = event.get("current_transcript", event["text"])
                
                if event["is_final"]:
                    print(f"\n{role}: {current_text}")
                    current_text = ""

asyncio.run(main())
```

### Tool Execution During Conversation

```python
import asyncio
from strands.experimental.bidi import BidiAgent
from strands.experimental.bidi.models import BidiNovaSonicModel
from strands_tools import calculator

async def main():
    model = BidiNovaSonicModel()
    agent = BidiAgent(model=model, tools=[calculator])
    
    async with agent as agent:
        await agent.send("What is 25 times 48?")
        
        async for event in agent.receive():
            event_type = event["type"]
            
            if event_type == "bidi_transcript_stream" and event["is_final"]:
                print(f"{event['role']}: {event['text']}")
            
            elif event_type == "tool_use_stream":
                tool_use = event["current_tool_use"]
                print(f"🔧 Using tool: {tool_use['name']}")
                print(f"   Input: {tool_use['input']}")
            
            elif event_type == "bidi_response_complete":
                if event["stop_reason"] == "tool_use":
                    print("   Tool executing in background...")

asyncio.run(main())
```

### Handling Interruptions

```python
import asyncio
from strands.experimental.bidi import BidiAgent
from strands.experimental.bidi.models import BidiNovaSonicModel

async def main():
    model = BidiNovaSonicModel()
    
    async with BidiAgent(model=model) as agent:
        await agent.send("Tell me a long story about space exploration")
        
        interruption_count = 0
        
        async for event in agent.receive():
            if event["type"] == "bidi_transcript_stream" and event["is_final"]:
                print(f"{event['role']}: {event['text']}")
            
            elif event["type"] == "bidi_interruption":
                interruption_count += 1
                print(f"\n⚠️ Interrupted (#{interruption_count})")
            
            elif event["type"] == "bidi_response_complete":
                if event["stop_reason"] == "interrupted":
                    print(f"Response interrupted {interruption_count} times")

asyncio.run(main())
```

### Connection Restart Handling

```python
import asyncio
from strands.experimental.bidi import BidiAgent
from strands.experimental.bidi.models import BidiNovaSonicModel

async def main():
    model = BidiNovaSonicModel()  # 8-minute timeout
    
    async with BidiAgent(model=model) as agent:
        # Continuous conversation that handles restarts
        async for event in agent.receive():
            if event["type"] == "bidi_connection_restart":
                print("⚠️ Connection restarting (timeout)...")
                print("   Conversation history preserved")
                # Connection resumes automatically
            
            elif event["type"] == "bidi_connection_start":
                print(f"✅ Connected to {event['model']}")
            
            elif event["type"] == "bidi_transcript_stream" and event["is_final"]:
                print(f"{event['role']}: {event['text']}")

asyncio.run(main())
```

## Hook Events

Hook events are a separate concept from streaming events. While streaming events flow through `agent.receive()` during conversations, hook events are callbacks that trigger at specific lifecycle points (like initialization, message added, or interruption). Hook events allow you to inject custom logic for cross-cutting concerns like logging, analytics, and session persistence without processing the event stream directly.

For details on hook events and usage patterns, see the [Hooks](hooks.md) documentation.
