# MeloTTS LiveKit Plugin Documentation

Complete guide for using the MeloTTS plugin with LiveKit agents.

## Installation

```bash
cd plugin
pip install -r requirements.txt
```

Or install from the package:

```bash
cd plugin
pip install -e .
```

## Quick Start

```python
from melotts_plugin import TTS

# Initialize the plugin
tts = TTS(
    api_base_url="http://localhost:8000",
    language="EN",
    speaker="EN-US",
    speed=1.0
)

# Use in your agent
stream = tts.synthesize("Hello from LiveKit!")
```

## API Reference

### TTS Class

Main plugin class that extends `livekit.agents.tts.TTS`.

#### Constructor

```python
TTS(
    *,
    api_base_url: str = "http://localhost:8000",
    language: str = "EN",
    speaker: Optional[str] = "EN-US",
    speed: float = 1.0,
    timeout: float = 30.0,
    sample_rate: int = 44100,
    num_channels: int = 1,
)
```

**Parameters:**

- `api_base_url` (str): Base URL of the MeloTTS API server
  - Default: `"http://localhost:8000"`
  - Example: `"http://tts-server:8000"`

- `language` (str): Language code
  - Default: `"EN"`
  - Options: `"EN"`, `"ES"`, `"FR"`, `"ZH"`, `"JP"`, `"KR"`

- `speaker` (Optional[str]): Speaker/voice ID
  - Default: `"EN-US"`
  - English: `"EN-US"`, `"EN-BR"`, `"EN-AU"`, `"EN-IN"`
  - Spanish: `"ES"`
  - French: `"FR"`
  - Chinese: `"ZH"`
  - Japanese: `"JP"`
  - Korean: `"KR"`

- `speed` (float): Speech speed multiplier
  - Default: `1.0`
  - Range: `0.5` to `2.0`
  - Example: `1.5` for 1.5x speed

- `timeout` (float): Request timeout in seconds
  - Default: `30.0`
  - Increase for longer texts

- `sample_rate` (int): Audio sample rate in Hz
  - Default: `44100`
  - Must match API server output

- `num_channels` (int): Number of audio channels
  - Default: `1` (mono)

#### Methods

##### synthesize()

```python
def synthesize(
    self,
    text: str,
    *,
    conn_options: agents.APIConnectOptions = agents.DEFAULT_API_CONNECT_OPTIONS,
) -> ChunkedStream
```

Synthesize text to speech.

**Parameters:**
- `text` (str): Text to synthesize
- `conn_options` (APIConnectOptions): Connection options

**Returns:**
- `ChunkedStream`: Audio stream object

**Example:**
```python
stream = tts.synthesize("Hello world")
```

##### aclose()

```python
async def aclose(self) -> None
```

Close the aiohttp session and clean up resources.

**Example:**
```python
await tts.aclose()
```

#### Properties

##### model

```python
@property
def model(self) -> str
```

Returns the model identifier.

**Returns:** `"melotts"`

##### provider

```python
@property
def provider(self) -> str
```

Returns the provider name.

**Returns:** `"custom-melotts"`

##### capabilities

```python
@property
def capabilities(self) -> TTSCapabilities
```

Returns TTS capabilities.

**Returns:** `TTSCapabilities(streaming=True)`

### ChunkedStream Class

Handles streaming audio from the API.

**Note:** This class is used internally. You typically don't need to interact with it directly.

## Usage Examples

### Basic Usage

```python
from melotts_plugin import TTS

async def example():
    # Create TTS instance
    tts = TTS()

    # Synthesize text
    stream = tts.synthesize("Hello, this is a test.")

    # Process stream (handled by LiveKit framework)
    # ...

    # Clean up
    await tts.aclose()
```

### Custom Configuration

```python
tts = TTS(
    api_base_url="http://my-tts-server:8000",
    language="ES",
    speaker="ES",
    speed=1.2,
    timeout=60.0
)
```

### Different Languages

```python
# English
tts_en = TTS(language="EN", speaker="EN-US")

# Spanish
tts_es = TTS(language="ES", speaker="ES")

# French
tts_fr = TTS(language="FR", speaker="FR")
```

### Different Voices

```python
# American English
tts_us = TTS(language="EN", speaker="EN-US")

# British English
tts_uk = TTS(language="EN", speaker="EN-BR")

# Australian English
tts_au = TTS(language="EN", speaker="EN-AU")
```

### Variable Speed

```python
# Slow speech
tts_slow = TTS(speed=0.7)

# Fast speech
tts_fast = TTS(speed=1.5)
```

## Integration with LiveKit Agents

### Simple Agent

```python
from livekit import agents
from livekit.agents import JobContext, WorkerOptions, cli
from melotts_plugin import TTS

async def entrypoint(ctx: JobContext):
    # Initialize TTS
    tts = TTS(
        api_base_url="http://localhost:8000",
        language="EN",
        speaker="EN-US"
    )

    # Connect to room
    await ctx.connect()

    # Synthesize greeting
    greeting = "Hello! How can I help you today?"
    stream = tts.synthesize(greeting)

    # The stream integrates automatically with LiveKit
    # Audio will be sent to the room

    # Clean up when done
    await tts.aclose()

if __name__ == "__main__":
    cli.run_app(WorkerOptions(entrypoint_fnc=entrypoint))
```

### Voice Assistant

```python
from livekit import agents
from livekit.agents import JobContext, WorkerOptions, cli
from livekit.plugins import openai  # Or other STT/LLM providers
from melotts_plugin import TTS

async def entrypoint(ctx: JobContext):
    # Initialize components
    stt = openai.STT()
    llm = openai.LLM(model="gpt-4")
    tts = TTS(
        api_base_url="http://localhost:8000",
        language="EN",
        speaker="EN-US",
        speed=1.0
    )

    # Create voice assistant
    assistant = agents.VoiceAssistant(
        vad=agents.silero.VAD(),
        stt=stt,
        llm=llm,
        tts=tts,
        chat_ctx=agents.ChatContext().append(
            role="system",
            text="You are a helpful assistant."
        )
    )

    # Start the assistant
    await ctx.connect()
    assistant.start(ctx.room)

    # The assistant will:
    # 1. Listen for speech (VAD)
    # 2. Transcribe (STT)
    # 3. Generate response (LLM)
    # 4. Speak response (TTS - our plugin!)

    # Clean up
    await tts.aclose()

if __name__ == "__main__":
    cli.run_app(WorkerOptions(entrypoint_fnc=entrypoint))
```

### Multi-Language Agent

```python
async def entrypoint(ctx: JobContext):
    # Support multiple languages
    tts_en = TTS(language="EN", speaker="EN-US")
    tts_es = TTS(language="ES", speaker="ES")
    tts_fr = TTS(language="FR", speaker="FR")

    # Detect user language and use appropriate TTS
    user_language = detect_language(user_message)

    if user_language == "EN":
        stream = tts_en.synthesize(response)
    elif user_language == "ES":
        stream = tts_es.synthesize(response)
    elif user_language == "FR":
        stream = tts_fr.synthesize(response)

    # Clean up all instances
    await tts_en.aclose()
    await tts_es.aclose()
    await tts_fr.aclose()
```

## Error Handling

The plugin raises LiveKit-standard exceptions:

### APIConnectionError

Raised when cannot connect to the API server.

```python
from livekit.agents import APIConnectionError

try:
    stream = tts.synthesize("Hello")
    await stream._run(emitter)
except APIConnectionError as e:
    print(f"Connection failed: {e}")
    # Handle error (retry, fallback, etc.)
```

### APITimeoutError

Raised when request times out.

```python
from livekit.agents import APITimeoutError

try:
    stream = tts.synthesize("Hello")
    await stream._run(emitter)
except APITimeoutError:
    print("Request timed out")
    # Handle timeout
```

### APIStatusError

Raised when API returns error status.

```python
from livekit.agents import APIStatusError

try:
    stream = tts.synthesize("Hello")
    await stream._run(emitter)
except APIStatusError as e:
    print(f"API error {e.status_code}: {e.message}")
    # Handle API error
```

### Complete Error Handling

```python
from livekit.agents import APIConnectionError, APITimeoutError, APIStatusError

async def safe_synthesize(tts, text):
    try:
        stream = tts.synthesize(text)
        return stream

    except APITimeoutError:
        print("Request timed out, retrying...")
        # Retry logic
        return tts.synthesize(text)

    except APIConnectionError as e:
        print(f"Connection failed: {e}")
        # Fall back to alternative TTS
        fallback_tts = get_fallback_tts()
        return fallback_tts.synthesize(text)

    except APIStatusError as e:
        print(f"API error: {e.message}")
        # Handle specific errors
        if e.status_code == 400:
            # Invalid input
            return None
        else:
            raise

    except Exception as e:
        print(f"Unexpected error: {e}")
        raise
```

## Best Practices

### 1. Resource Management

Always close the TTS instance when done:

```python
tts = TTS()
try:
    # Use TTS
    stream = tts.synthesize("Hello")
finally:
    await tts.aclose()
```

Or use context manager pattern (if implemented):

```python
async with TTS() as tts:
    stream = tts.synthesize("Hello")
```

### 2. Connection Pooling

Reuse the same TTS instance across multiple syntheses:

```python
# Good: Single instance
tts = TTS()
stream1 = tts.synthesize("First message")
stream2 = tts.synthesize("Second message")
await tts.aclose()

# Avoid: Creating new instances
# (Creates new HTTP sessions each time)
TTS().synthesize("First")
TTS().synthesize("Second")
```

### 3. Error Recovery

Implement retry logic for transient errors:

```python
async def synthesize_with_retry(tts, text, max_retries=3):
    for attempt in range(max_retries):
        try:
            return tts.synthesize(text)
        except APIConnectionError:
            if attempt < max_retries - 1:
                await asyncio.sleep(2 ** attempt)  # Exponential backoff
            else:
                raise
```

### 4. Text Preprocessing

Optimize text for better synthesis:

```python
def preprocess_text(text):
    # Remove URLs
    text = re.sub(r'http\S+', '', text)

    # Expand abbreviations
    text = text.replace('Mr.', 'Mister')
    text = text.replace('Dr.', 'Doctor')

    # Remove special characters
    text = re.sub(r'[^\w\s.,!?-]', '', text)

    return text

# Use preprocessed text
clean_text = preprocess_text(user_input)
stream = tts.synthesize(clean_text)
```

### 5. Chunking Long Text

Break long texts into sentences:

```python
import nltk

def chunk_text(text, max_length=500):
    sentences = nltk.sent_tokenize(text)
    chunks = []
    current_chunk = ""

    for sentence in sentences:
        if len(current_chunk) + len(sentence) < max_length:
            current_chunk += " " + sentence
        else:
            if current_chunk:
                chunks.append(current_chunk.strip())
            current_chunk = sentence

    if current_chunk:
        chunks.append(current_chunk.strip())

    return chunks

# Synthesize in chunks
for chunk in chunk_text(long_text):
    stream = tts.synthesize(chunk)
    # Process stream...
```

## Performance Tips

1. **Keep API Server Close**: Deploy API server near your LiveKit agents to minimize latency

2. **Use Appropriate Timeout**: Set longer timeout for longer texts

3. **Monitor Memory**: The plugin uses aiohttp sessions which are memory-efficient

4. **Cache Common Phrases**: Cache frequently used phrases at application level

5. **Load Balance**: Run multiple API server instances behind a load balancer

## Troubleshooting

### Plugin can't connect to API

**Check:**
- API server is running: `curl http://localhost:8000/`
- URL is correct in `api_base_url`
- Network connectivity
- Firewall rules

### Audio quality issues

**Try:**
- Different voices/speakers
- Adjust speed parameter
- Verify sample rate matches
- Check API server audio output

### Timeouts

**Solutions:**
- Increase `timeout` parameter
- Break long texts into chunks
- Check API server performance
- Verify network latency

### Memory leaks

**Ensure:**
- Call `await tts.aclose()` when done
- Don't create excessive TTS instances
- Monitor with memory profiler

## Testing

Run the plugin tests:

```bash
# Start API server first
cd api && python server.py

# Run tests
cd tests
pytest test_plugin.py -v
```

## Migration from Other Providers

### From OpenAI TTS

```python
# Before
from livekit.plugins import openai
tts = openai.TTS(voice="alloy")

# After
from melotts_plugin import TTS
tts = TTS(language="EN", speaker="EN-US")
```

### From ElevenLabs

```python
# Before
from livekit.plugins import elevenlabs
tts = elevenlabs.TTS(voice_id="...")

# After
from melotts_plugin import TTS
tts = TTS(language="EN", speaker="EN-US")
```

### From Google TTS

```python
# Before
from livekit.plugins import google
tts = google.TTS(language="en-US")

# After
from melotts_plugin import TTS
tts = TTS(language="EN", speaker="EN-US")
```

## Advanced Usage

### Custom Audio Processing

```python
class CustomChunkedStream(ChunkedStream):
    async def _run(self, output_emitter):
        # Custom preprocessing
        processed_text = custom_preprocess(self._input_text)

        # Call parent implementation
        await super()._run(output_emitter)

        # Custom postprocessing if needed
```

### Monitoring

```python
import time

class MonitoredTTS(TTS):
    async def synthesize(self, text, **kwargs):
        start = time.time()
        stream = await super().synthesize(text, **kwargs)
        duration = time.time() - start

        print(f"Synthesis started in {duration:.2f}s for {len(text)} chars")
        return stream
```

## Support

For issues:
1. Check API server is running and accessible
2. Review error messages and logs
3. Run test suite to verify setup
4. Check [examples/](../examples/) for working code

## API Compatibility

This plugin is compatible with:
- LiveKit Agents >= 0.8.0
- Python >= 3.9
- MeloTTS API Server v1.0.0+

## Version History

### 1.0.0
- Initial release
- Full LiveKit integration
- Streaming support
- Multi-language support
- Comprehensive error handling
