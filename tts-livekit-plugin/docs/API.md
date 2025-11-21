# MeloTTS API Documentation

Complete reference for the MeloTTS FastAPI server.

## Base URL

```
http://localhost:8000
```

## Authentication

Currently no authentication is required. For production deployments, consider adding:
- API key authentication
- Rate limiting
- IP whitelisting

## Endpoints

### GET /

Health check endpoint.

**Response:**
```json
{
  "status": "ok",
  "service": "MeloTTS API",
  "version": "1.0.0"
}
```

**Example:**
```bash
curl http://localhost:8000/
```

---

### GET /voices

List available voices for a language.

**Query Parameters:**
- `language` (string, required): Language code (EN, ES, FR, ZH, JP, KR)

**Response:**
```json
{
  "language": "EN",
  "voices": ["EN-US", "EN-BR", "EN-AU", "EN-IN"]
}
```

**Example:**
```bash
curl "http://localhost:8000/voices?language=EN"
```

---

### POST /synthesize

Generate complete TTS audio (non-streaming).

**Request Body:**
```json
{
  "text": "Text to synthesize",
  "language": "EN",
  "speaker": "EN-US",
  "speed": 1.0
}
```

**Parameters:**
- `text` (string, required): Text to synthesize (1-5000 characters)
- `language` (string, optional): Language code, default: "EN"
- `speaker` (string, optional): Speaker ID, default: first available for language
- `speed` (float, optional): Speech speed (0.5-2.0), default: 1.0

**Response:**
- Content-Type: `audio/wav`
- Body: Complete WAV audio file

**Example:**
```bash
curl -X POST http://localhost:8000/synthesize \
  -H "Content-Type: application/json" \
  -d '{
    "text": "Hello, this is a test.",
    "language": "EN",
    "speaker": "EN-US",
    "speed": 1.0
  }' \
  --output output.wav
```

**Python Example:**
```python
import aiohttp
import asyncio

async def synthesize():
    async with aiohttp.ClientSession() as session:
        payload = {
            "text": "Hello world",
            "language": "EN",
            "speaker": "EN-US",
            "speed": 1.0
        }

        async with session.post(
            "http://localhost:8000/synthesize",
            json=payload
        ) as resp:
            audio_data = await resp.read()
            with open("output.wav", "wb") as f:
                f.write(audio_data)

asyncio.run(synthesize())
```

---

### POST /synthesize/stream

Generate TTS audio with streaming (optimized for LiveKit).

**Request Body:**
Same as `/synthesize`

**Response:**
- Content-Type: `audio/wav`
- Body: Chunked audio stream
- Headers:
  - `Cache-Control: no-cache`
  - `Content-Disposition: attachment; filename=speech.wav`

**Example:**
```bash
curl -X POST http://localhost:8000/synthesize/stream \
  -H "Content-Type: application/json" \
  -d '{
    "text": "Streaming audio test.",
    "language": "EN",
    "speaker": "EN-US"
  }' \
  --output streaming_output.wav
```

**Python Example with Streaming:**
```python
import aiohttp
import asyncio

async def synthesize_stream():
    async with aiohttp.ClientSession() as session:
        payload = {
            "text": "This is a streaming test.",
            "language": "EN",
            "speaker": "EN-US"
        }

        async with session.post(
            "http://localhost:8000/synthesize/stream",
            json=payload
        ) as resp:
            with open("streaming_output.wav", "wb") as f:
                async for chunk, _ in resp.content.iter_chunks():
                    if chunk:
                        f.write(chunk)
                        print(f"Received chunk: {len(chunk)} bytes")

asyncio.run(synthesize_stream())
```

---

## Error Responses

### 400 Bad Request

Invalid parameters or unknown speaker.

```json
{
  "detail": "Speaker 'INVALID' not found. Available speakers: ['EN-US', 'EN-BR', ...]"
}
```

### 422 Unprocessable Entity

Validation error (e.g., text too long, invalid speed).

```json
{
  "detail": [
    {
      "loc": ["body", "speed"],
      "msg": "ensure this value is greater than or equal to 0.5",
      "type": "value_error"
    }
  ]
}
```

### 500 Internal Server Error

Server-side error during synthesis.

```json
{
  "detail": "Audio generation failed: [error message]"
}
```

---

## Language and Speaker Reference

### English (EN)
Available speakers:
- `EN-US`: American English
- `EN-BR`: British English
- `EN-IN`: Indian English
- `EN-AU`: Australian English

**Example:**
```json
{
  "text": "Hello from America",
  "language": "EN",
  "speaker": "EN-US"
}
```

### Spanish (ES)
Available speakers:
- `ES`: Spanish

**Example:**
```json
{
  "text": "Hola mundo",
  "language": "ES",
  "speaker": "ES"
}
```

### French (FR)
Available speakers:
- `FR`: French

**Example:**
```json
{
  "text": "Bonjour le monde",
  "language": "FR",
  "speaker": "FR"
}
```

### Chinese (ZH)
Available speakers:
- `ZH`: Chinese

**Example:**
```json
{
  "text": "你好世界",
  "language": "ZH",
  "speaker": "ZH"
}
```

### Japanese (JP)
Available speakers:
- `JP`: Japanese

**Example:**
```json
{
  "text": "こんにちは世界",
  "language": "JP",
  "speaker": "JP"
}
```

### Korean (KR)
Available speakers:
- `KR`: Korean

**Example:**
```json
{
  "text": "안녕하세요 세계",
  "language": "KR",
  "speaker": "KR"
}
```

---

## Audio Format

**Output Format:** WAV (Waveform Audio File Format)
- **Sample Rate:** 44,100 Hz
- **Bit Depth:** 16-bit
- **Channels:** Mono (1 channel)
- **Encoding:** PCM

---

## Rate Limiting

Currently no rate limiting is implemented. For production use, consider:

- Adding rate limiting middleware
- Implementing request queuing
- Setting up load balancing

---

## Performance Tips

1. **Use Streaming**: The `/synthesize/stream` endpoint provides lower latency for real-time applications

2. **GPU Acceleration**: The server automatically uses GPU if available. Set `CUDA_VISIBLE_DEVICES` to control GPU usage

3. **Concurrency**: The server handles multiple requests concurrently using asyncio

4. **Caching**: Consider caching common phrases at the application level

5. **Text Length**: Shorter texts synthesize faster. Consider breaking long texts into sentences

---

## Server Configuration

Edit `server.py` to configure:

```python
# Server settings
uvicorn.run(
    "server:app",
    host="0.0.0.0",      # Listen address
    port=8000,            # Port
    reload=True,          # Auto-reload on code changes
    log_level="info"      # Logging level
)

# TTS settings
class TTSModels:
    def __init__(self):
        self.device = "auto"  # Change to "cpu" or "cuda"
```

---

## Monitoring

The server logs all requests. Monitor for:

- Request latency
- Error rates
- Memory usage
- GPU utilization (if applicable)

Example logs:
```
INFO:     127.0.0.1:52364 - "POST /synthesize HTTP/1.1" 200 OK
INFO:     Initializing TTS models...
INFO:     TTS models initialized successfully
```

---

## Security Considerations

For production deployments:

1. **Add Authentication**: Implement API key or OAuth
2. **Enable HTTPS**: Use TLS/SSL certificates
3. **Rate Limiting**: Prevent abuse
4. **Input Validation**: Already implemented, but monitor for edge cases
5. **CORS**: Configure allowed origins
6. **Firewall**: Restrict access to known IPs

---

## Troubleshooting

### Model Loading Fails

**Problem:** `Failed to load TTS model for language EN`

**Solutions:**
- Run `python -m unidic download`
- Check MeloTTS installation: `pip install git+https://github.com/myshell-ai/MeloTTS.git`
- Verify Python version >= 3.9

### Out of Memory

**Problem:** Server crashes during synthesis

**Solutions:**
- Reduce concurrent requests
- Use CPU mode: Set `device = "cpu"`
- Increase system RAM
- Implement request queuing

### Slow Synthesis

**Problem:** Synthesis takes too long

**Solutions:**
- Enable GPU: Ensure CUDA is installed
- Reduce text length
- Use faster hardware
- Pre-load models at startup

---

## API Client Libraries

### Python (aiohttp)
```python
import aiohttp

async with aiohttp.ClientSession() as session:
    async with session.post(url, json=payload) as resp:
        audio = await resp.read()
```

### Python (requests)
```python
import requests

response = requests.post(url, json=payload)
audio = response.content
```

### JavaScript (fetch)
```javascript
const response = await fetch(url, {
  method: 'POST',
  headers: {'Content-Type': 'application/json'},
  body: JSON.stringify(payload)
});
const audio = await response.blob();
```

### cURL
```bash
curl -X POST $URL -H "Content-Type: application/json" -d "$JSON" -o output.wav
```

---

## Interactive API Documentation

FastAPI provides interactive documentation:

- **Swagger UI**: http://localhost:8000/docs
- **ReDoc**: http://localhost:8000/redoc

These interfaces allow you to:
- Explore all endpoints
- Test requests directly
- View request/response schemas
- Download API specifications
