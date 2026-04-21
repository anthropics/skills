---
name: skillboss-ai-gateway
description: Access 100+ AI services through a unified OpenAI-compatible API. Use Claude, GPT, Gemini, DeepSeek for LLMs; DALL-E, Midjourney, Flux for images; Runway, Kling for videos; and ElevenLabs for voice - all with one API key.
---

# SkillBoss AI Gateway

A unified gateway to access 100+ AI services through a single OpenAI-compatible API.

## Supported Services

### LLMs
- Claude (Opus, Sonnet, Haiku)
- GPT-4, GPT-4o, o1, o3
- Gemini Pro, Gemini Flash
- DeepSeek R1, DeepSeek V3
- Llama 3, Mistral, Qwen

### Image Generation
- DALL-E 3
- Midjourney
- Flux Pro/Dev
- Stable Diffusion 3

### Video Generation
- Runway Gen-3
- Kling 1.6
- Pika Labs

### Voice & Audio
- ElevenLabs TTS
- Whisper transcription

## Installation

### As MCP Server
```bash
npx @skillboss/mcp-server
```

### Direct API Access
```python
from openai import OpenAI

client = OpenAI(
    base_url="https://api.heybossai.com/v1",
    api_key="your-skillboss-key"
)

# Use any model
response = client.chat.completions.create(
    model="claude-sonnet-4",  # or gpt-4o, gemini-2-flash, etc.
    messages=[{"role": "user", "content": "Hello!"}]
)
```

## Key Features

- **One API key** for all services
- **OpenAI-compatible** format
- **Pay-as-you-go** pricing
- **No vendor lock-in**
- Works in Claude Code, Cursor, Windsurf, Codex

## Links

- Website: https://skillboss.co
- GitHub: https://github.com/heeyo-life/skillboss-mcp
- npm: `@skillboss/mcp-server`
