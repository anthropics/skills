---
name: ai-voice-chat
description: A private web app for voice and text AI conversations with a confident, honest personality. Optimized for mobile (iPhone) with voice as the primary interaction mode.
---

# AI Voice Chat

A simple, private web application that enables voice and text conversations with Claude AI. Designed specifically for mobile use (iPhone) with a confident, straightforward AI personality that gives honest, direct responses.

## Features

- **Voice-first interaction**: Primary mode is speaking and listening
- **Text input option**: Type when voice isn't convenient
- **Mobile optimized**: Designed for iPhone with touch-friendly interface
- **Private & secure**: API key stored locally in browser only
- **Confident AI personality**: Direct, honest responses without excessive politeness

## When to Use This Skill

Use this skill when you need to:
- Create or modify the AI voice chat web application
- Adjust the AI's personality or system prompt
- Update the user interface or styling
- Add new features to the voice chat app
- Troubleshoot issues with voice recognition or speech synthesis
- Modify the server configuration

## Technical Architecture

### Frontend
- **Single HTML file** with embedded CSS and JavaScript
- **Web Speech API** for voice recognition (input)
- **Speech Synthesis API** for text-to-speech (output)
- **Vanilla JavaScript** - no dependencies or frameworks
- **Mobile-first design** with iOS-specific optimizations

### Backend
- **Python HTTP server** for local hosting
- **Direct API integration** with Anthropic's Claude API
- **Client-side only** - no server-side processing

### AI Configuration
The system prompt configures Claude to be:
```
You are a confident, direct, and honest AI assistant. Key traits:
- Be straightforward and clear
- Don't over-apologize or be overly polite
- Give direct answers without excessive hedging
- Be honest even if it's not what someone wants to hear
- Skip unnecessary pleasantries
- Be concise and to the point
- Show confidence in your responses
```

## File Structure

```
ai-voice-chat/
├── index.html       # Main web application (self-contained)
├── server.py        # Python HTTP server for local hosting
├── README.md        # User documentation and setup guide
└── SKILL.md         # This skill definition
```

## Setup Instructions

1. **Get Anthropic API key** from console.anthropic.com
2. **Run the server**: `python3 server.py`
3. **Open on iPhone**: Navigate to displayed URL
4. **Enter API key** on first launch

## Customization Guidelines

### Modifying AI Personality
Edit the `systemPrompt` variable in index.html to change how the AI responds.

### Adjusting Voice Settings
In the `speak()` function:
- `utterance.rate`: Speed of speech (0.1 to 10, default 1.1)
- `utterance.pitch`: Voice pitch (0 to 2, default 1.0)

### Styling Changes
All CSS is embedded in the `<style>` tag in index.html. Key design principles:
- Dark theme (black background, white text)
- Touch-friendly buttons (50px minimum)
- Mobile-first responsive design
- iOS-optimized input handling

### API Configuration
To change the Claude model, modify the `model` parameter in the `sendMessage()` function.

## Browser Compatibility

- **iOS Safari**: Full support (recommended)
- **Chrome (desktop)**: Full support
- **Chrome (mobile)**: Limited voice support
- **Firefox**: Limited speech synthesis support

## Privacy & Security

- API key stored in browser's `localStorage` only
- No data sent to any server except Anthropic's API
- Conversation history kept in memory only
- Refresh clears all conversation data

## Cost Considerations

Uses Claude 3.5 Sonnet via API:
- ~$0.003 per typical message
- Costs controlled through Anthropic account limits
- Real-time usage visible in Anthropic console

## Troubleshooting Common Issues

### Voice Recognition Not Working
- Ensure microphone permissions granted
- Use Safari on iOS for best compatibility
- Check that site is served over HTTPS or localhost

### API Errors
- Verify API key is correct
- Check Anthropic account has credits
- Ensure internet connectivity

### Can't Access from iPhone
- Confirm devices on same WiFi network
- Use computer's local IP address, not localhost
- Check firewall isn't blocking port 8080

## Examples

### Adding a new feature
"Add a button to clear conversation history in the AI voice chat app"

### Modifying personality
"Make the AI voice chat personality more friendly and conversational"

### Styling updates
"Change the AI voice chat app to use a blue theme instead of black"

### Performance tuning
"Optimize the AI voice chat app to reduce API response time"
