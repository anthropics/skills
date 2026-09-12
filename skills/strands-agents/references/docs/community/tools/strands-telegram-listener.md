---
project:
  pypi: https://pypi.org/project/strands-telegram-listener/
  github: https://github.com/eraykeskinmac/strands-telegram-listener
  maintainer: eraykeskinmac
service:
  name: telegram
  link: https://core.telegram.org/bots
---

# strands-telegram-listener

{{ community_contribution_banner }}

[strands-telegram-listener](https://github.com/eraykeskinmac/strands-telegram-listener) is a real-time Telegram message processing tool with AI-powered auto-replies and comprehensive event handling.

## Installation

```bash
pip install strands-telegram-listener
```

## Usage

```python
from strands import Agent
from strands_telegram_listener import telegram_listener

agent = Agent(tools=[telegram_listener])

# Start listening for messages
agent("start Telegram listener")

# Get recent messages
agent("get last 10 Telegram messages")

# Check listener status
agent("check Telegram listener status")
```

## Key Features

- **Real-time Processing**: Long polling for instant message handling
- **AI Auto-replies**: Intelligent responses using Strands agents
- **Event Storage**: Comprehensive message history in JSONL format
- **Smart Filtering**: Message deduplication and selective processing
- **Background Threading**: Non-blocking operation
- **Status Monitoring**: Real-time listener status and metrics
- **Flexible Configuration**: Environment-based settings

## Configuration

```bash
TELEGRAM_BOT_TOKEN=your_bot_token         # Required
STRANDS_TELEGRAM_AUTO_REPLY=true          # Optional
STRANDS_TELEGRAM_LISTEN_ONLY_TAG=#support # Optional
```

Get your bot token at: [BotFather](https://core.telegram.org/bots#botfather)

## Resources

- [PyPI Package](https://pypi.org/project/strands-telegram-listener/)
- [GitHub Repository](https://github.com/eraykeskinmac/strands-telegram-listener)
- [Examples & Demos](https://github.com/eraykeskinmac/strands-tools-examples)
- [Bot Creation Guide](https://core.telegram.org/bots)
- [Telegram Bot API](https://core.telegram.org/bots/api)
