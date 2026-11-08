---
project:
  pypi: https://pypi.org/project/strands-telegram/
  github: https://github.com/eraykeskinmac/strands-telegram
  maintainer: eraykeskinmac
service:
  name: telegram
  link: https://core.telegram.org/bots
---

# strands-telegram

{{ community_contribution_banner }}

[strands-telegram](https://github.com/eraykeskinmac/strands-telegram) is a comprehensive Telegram Bot API integration tool with 60+ methods for complete bot development capabilities.

## Installation

```bash
pip install strands-telegram
```

## Usage

```python
from strands import Agent
from strands_telegram import telegram

agent = Agent(tools=[telegram])

# Send simple message
agent("send a Telegram message 'Hello World' to chat 123456")

# Send media with caption
agent("send photo.jpg to Telegram with caption 'Check this out!'")

# Create interactive keyboard
agent("send a message with buttons: Yes/No for approval")
```

## Key Features

- **60+ Telegram API Methods**: Complete Bot API coverage
- **Media Support**: Photos, videos, audio, documents, and stickers
- **Interactive Elements**: Inline keyboards, polls, dice games
- **Group Management**: Admin functions, member management, permissions
- **File Operations**: Upload, download, and media handling
- **Webhook Support**: Real-time message processing
- **Custom API Calls**: Extensible for any Telegram method

## Configuration

```bash
TELEGRAM_BOT_TOKEN=your_bot_token         # Required
```

Get your bot token at: [BotFather](https://core.telegram.org/bots#botfather)

## Resources

- [PyPI Package](https://pypi.org/project/strands-telegram/)
- [GitHub Repository](https://github.com/eraykeskinmac/strands-telegram)
- [Examples & Demos](https://github.com/eraykeskinmac/strands-tools-examples)
- [Bot Creation Guide](https://core.telegram.org/bots)
- [Telegram Bot API](https://core.telegram.org/bots/api)
