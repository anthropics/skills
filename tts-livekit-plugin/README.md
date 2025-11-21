# MeloTTS LiveKit Plugin

A complete TTS (Text-to-Speech) solution for LiveKit voice agents using self-hosted MeloTTS models from Hugging Face.

## Overview

This project provides:

1. **TTS API Server**: Self-hosted FastAPI server using MeloTTS
2. **LiveKit Plugin**: Integration plugin for LiveKit agents
3. **Full Documentation**: Comprehensive guides and examples
4. **Test Suite**: Complete test coverage for API and plugin

## Features

- ✅ **Self-Hosted**: Run your own TTS service with no external API dependencies
- ✅ **High Quality**: MeloTTS provides natural-sounding speech
- ✅ **Multi-Language**: Supports English, Spanish, French, Chinese, Japanese, Korean
- ✅ **Multiple Voices**: Different accents and speakers per language
- ✅ **Streaming**: Low-latency chunked audio streaming
- ✅ **CPU-Friendly**: Optimized for real-time inference even on CPUs
- ✅ **LiveKit Ready**: Drop-in replacement for LiveKit TTS providers
- ✅ **Fully Tested**: Comprehensive test suite with no mocks

## Architecture

```
┌─────────────────┐      HTTP/JSON      ┌──────────────────┐
│  LiveKit Agent  │ ◄──────────────────► │   TTS API        │
│                 │                      │   Server         │
│  ┌───────────┐  │                      │                  │
│  │ MeloTTS   │  │   Audio Streaming   │  ┌────────────┐  │
│  │ Plugin    │  │ ◄──────────────────► │  │  MeloTTS   │  │
│  └───────────┘  │                      │  │  Model     │  │
└─────────────────┘                      │  └────────────┘  │
                                         └──────────────────┘
```

## Quick Start

### 1. Install Dependencies

**For the API Server:**
```bash
cd api
pip install -r requirements.txt
python -m unidic download  # Required for MeloTTS
```

**For the LiveKit Plugin:**
```bash
cd plugin
pip install -r requirements.txt
```

### 2. Start the TTS API Server

```bash
cd api
python server.py
```

The server will start on `http://localhost:8000`

### 3. Test the API

```bash
cd examples
python test_api_client.py
```

This will run comprehensive tests and generate sample audio files.

### 4. Use in LiveKit Agent

```python
from melotts_plugin import TTS

# Initialize the plugin
tts = TTS(
    api_base_url="http://localhost:8000",
    language="EN",
    speaker="EN-US",
    speed=1.0
)

# Synthesize speech
stream = tts.synthesize("Hello from MeloTTS!")
```

See the [examples/](examples/) directory for complete agent implementations.

## Project Structure

```
tts-livekit-plugin/
├── api/                      # TTS API Server
│   ├── server.py            # FastAPI server implementation
│   └── requirements.txt     # Server dependencies
├── plugin/                   # LiveKit Plugin
│   ├── melotts_plugin.py    # Plugin implementation
│   ├── __init__.py          # Package initialization
│   ├── requirements.txt     # Plugin dependencies
│   └── pyproject.toml       # Package configuration
├── tests/                    # Test Suite
│   ├── test_api.py          # API server tests
│   ├── test_plugin.py       # Plugin integration tests
│   └── requirements.txt     # Test dependencies
├── examples/                 # Usage Examples
│   ├── test_api_client.py   # API testing script
│   ├── simple_agent.py      # Basic agent example
│   └── voice_assistant.py   # Complete voice assistant
├── docs/                     # Documentation
│   ├── API.md               # API documentation
│   ├── PLUGIN.md            # Plugin documentation
│   └── DEPLOYMENT.md        # Deployment guide
├── SKILL.md                 # Skill definition
└── README.md                # This file
```

## Documentation

- [API Documentation](docs/API.md) - Complete API reference
- [Plugin Documentation](docs/PLUGIN.md) - Plugin usage guide
- [Deployment Guide](docs/DEPLOYMENT.md) - Production deployment
- [Examples](examples/) - Working code examples

## Supported Languages and Voices

### English (EN)
- `EN-US`: American English
- `EN-BR`: British English
- `EN-IN`: Indian English
- `EN-AU`: Australian English

### Spanish (ES)
- `ES`: Spanish

### French (FR)
- `FR`: French

### Chinese (ZH)
- `ZH`: Chinese

### Japanese (JP)
- `JP`: Japanese

### Korean (KR)
- `KR`: Korean

## API Endpoints

### Health Check
```bash
GET /
```

### List Voices
```bash
GET /voices?language=EN
```

### Synthesize (Full)
```bash
POST /synthesize
Content-Type: application/json

{
  "text": "Hello world",
  "language": "EN",
  "speaker": "EN-US",
  "speed": 1.0
}
```

### Synthesize (Streaming)
```bash
POST /synthesize/stream
Content-Type: application/json

{
  "text": "Hello world",
  "language": "EN",
  "speaker": "EN-US",
  "speed": 1.0
}
```

## Testing

### Run API Tests
```bash
# Start the API server first
cd api && python server.py

# In another terminal, run tests
cd tests
pytest test_api.py -v
```

### Run Plugin Tests
```bash
# Make sure API server is running
cd tests
pytest test_plugin.py -v
```

### Run All Tests
```bash
cd tests
pytest -v
```

## Performance

- **Latency**: ~150-200ms TTFB on suitable hardware
- **CPU Usage**: Optimized for real-time inference on CPUs
- **GPU Support**: Automatically uses GPU if available
- **Streaming**: Audio chunks delivered as they're generated
- **Concurrency**: Handles multiple simultaneous requests

## Requirements

### API Server
- Python 3.9+
- FastAPI
- MeloTTS
- uvicorn
- 2GB+ RAM
- (Optional) CUDA-capable GPU for faster inference

### LiveKit Plugin
- Python 3.9+
- livekit-agents >= 0.8.0
- aiohttp >= 3.9.0

## Troubleshooting

### Server won't start
- Make sure you've run `python -m unidic download`
- Check that port 8000 is available
- Verify all dependencies are installed

### Plugin connection errors
- Ensure the API server is running
- Check the `api_base_url` configuration
- Verify network connectivity

### Audio quality issues
- Try adjusting the `speed` parameter (0.5-2.0)
- Experiment with different voices/speakers
- Check your audio sample rate configuration

## Contributing

Contributions are welcome! Please see the examples and tests for coding standards.

## License

Apache 2.0 License - See LICENSE file for details

## Acknowledgments

- [MeloTTS](https://github.com/myshell-ai/MeloTTS) by MyShell.ai
- [LiveKit](https://livekit.io) for the agents framework
- [FastAPI](https://fastapi.tiangolo.com) for the web framework

## Support

For issues and questions:
1. Check the [documentation](docs/)
2. Review the [examples](examples/)
3. Run the test suite to verify your setup

## Changelog

### Version 1.0.0 (Initial Release)
- FastAPI-based TTS server with MeloTTS
- LiveKit plugin with streaming support
- Multi-language and multi-voice support
- Comprehensive test suite
- Complete documentation and examples
