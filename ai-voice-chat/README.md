# AI Voice Chat

A simple, private web app for voice and text conversations with AI. Designed for mobile (iPhone) with a confident, honest AI personality.

## Features

- 🎤 **Voice conversations** - Primary mode of interaction
- ⌨️ **Text input** - Type when voice isn't convenient
- 📱 **Mobile-optimized** - Works perfectly on iPhone
- 🔒 **Private** - Your API key stays in your browser
- 💪 **Confident AI** - Direct, honest responses without excessive politeness

## Setup

### 1. Get an Anthropic API Key

1. Go to [console.anthropic.com](https://console.anthropic.com/)
2. Sign up or log in
3. Navigate to API Keys
4. Create a new API key

### 2. Run the App

**Option A: Simple Python Server (Recommended)**
```bash
cd ai-voice-chat
python3 server.py
```

Then open your iPhone's browser and go to: `http://YOUR_COMPUTER_IP:8080`

**Option B: Any HTTP Server**
```bash
cd ai-voice-chat
python3 -m http.server 8080
```

### 3. First Time Setup

1. Open the app in your browser
2. Enter your Anthropic API key
3. Tap "Start"
4. Your key is saved locally - you won't need to enter it again

## How to Use

### Voice Mode (Primary)
1. **Tap and hold** the microphone button
2. **Speak** your message
3. **Release** when done
4. AI will respond with voice

### Text Mode
1. Type in the text box
2. Press Enter
3. AI will respond (with voice)

### Controls
- 🎤 **Blue mic button** - Ready to listen
- 🎤 **Red pulsing** - Listening to you
- 🎤 **Green** - AI is speaking
- Tap mic while speaking to **stop** the AI

## Privacy

- Your API key is stored **only** in your browser's local storage
- No data is sent anywhere except directly to Anthropic's API
- Your conversation history stays in your browser's memory
- Refresh the page to clear conversation history

## AI Personality

The AI is configured to be:
- **Confident** - Gives clear, direct answers
- **Honest** - Tells you the truth, not just what you want to hear
- **Straightforward** - No excessive politeness or hedging
- **Concise** - Gets to the point

## Troubleshooting

**Voice not working?**
- Make sure you're using Safari on iPhone (best compatibility)
- Allow microphone permissions when prompted
- Check that you're on HTTPS or localhost

**API errors?**
- Verify your API key is correct
- Check you have credits in your Anthropic account
- Check your internet connection

**Can't access from phone?**
- Make sure phone and computer are on same WiFi
- Use your computer's local IP address (not localhost)
- On Mac: System Preferences → Network → check IP
- On Windows: `ipconfig` in command prompt

## Cost

This uses Claude 3.5 Sonnet via Anthropic's API:
- ~$0.003 per request for typical conversations
- You control costs through your Anthropic account
- Set spending limits in the Anthropic console

## Technical Details

- **Framework**: Vanilla JavaScript (no dependencies)
- **Voice Input**: Web Speech API
- **Voice Output**: Speech Synthesis API
- **AI Model**: Claude 3.5 Sonnet
- **Browser Support**: Safari (iOS), Chrome (desktop)

---

**Note**: This is a private, self-hosted web app. Your API key and conversations never leave your control.
