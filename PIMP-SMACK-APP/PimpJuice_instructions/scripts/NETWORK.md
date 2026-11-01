# Network and Service Map

- **Purpose**: Single reference for how the local stack fits together so you can run, test, and debug fast.
- **Scope**: HubStation (9199), Ollama (11434), Evidence UI (index.html), and API integrations.

## Overview
- **HubStation (PowerShell HttpListener)**
  - Listens on: http://127.0.0.1:9199
  - Proxies to Ollama at: http://127.0.0.1:11434
  - Serves static site: /web → D:\court doc corrupion\scripts
  - API endpoints: /status, /models, /chat, /tts, /stt, /voices, /ollama/pull, /ollama/stop, /ollama/ps, /queue/*, /heartbeat/*, /notify/*, /logs, /run, /reflect/*
  - **API Models Working**: Kimi K2 Thinking (confirmed active)
- **Ollama**
  - Listens on: http://127.0.0.1:11434
  - Endpoints used by HubStation: /api/version, /api/tags, /api/chat
- **Chrome DevTools MCP (optional)**
  - Connects to Chrome at: http://127.0.0.1:9222
  - Configured in: d:\THE_ESCAPE\MCP\mcp.json (server: chrome-devtools-mcp@latest)

## Ports and URLs
- **9199** → HubStation base (local): http://127.0.0.1:9199
- **11434** → Ollama API: http://127.0.0.1:11434
- **9222** → Chrome remote debugging (MCP, optional): http://127.0.0.1:9222

## Evidence Management UI
- **Location**: D:\court doc corrupion\scripts\index.html
- **Access**: http://127.0.0.1:9199/web/index.html (via HubStation)
- **Direct**: file:///D:/court%20doc%20corrupion/scripts/index.html (limited features)
- **Features**:
  - Timeline navigation (claims 100-1400)
  - Circular menu (14 legal claims)
  - Evidence card creation/editing
  - VIP Evidence panel (left)
  - Video Evidence panel (right, YouTube embeds)
  - PDF viewer for complaint documents
  - Gemini AI integration for auto-analysis
  - Google Drive upload (requires OAuth)
  - Side controller (draggable, with hotkeys)
  - Real-time notifications from HubStation
  - Heartbeat system for auto-updates

## HubStation API (quick reference)
### Core
- GET /ping → { ok, msg: 'pong', time }
- GET /status → health + defaults + voices + heartbeat state
- GET /models → list of available models (maps to Ollama /api/tags)
- POST /chat → { model, messages:[{role,content}], temperature, options:{num_ctx,num_predict} }

### Voice (TTS/STT)
- POST /tts → { text, voice?, rate?, volume?, saveToFile? }
- POST /stt → { audioPath|audioBase64, extension?, language?, whisperExe?, modelPath? }
- GET /voices → { default, voices:[...] }
- POST /voices/set → { voice }

### Ollama Management
- GET /ollama/list → list models
- GET /ollama/ps → running models/process info
- POST /ollama/pull → { model }
- POST /ollama/stop → { model }

### Message Queue
- POST /queue/push → { text, target?, priority?, release? }
- GET /queue/list → queue items + counts
- POST /queue/pop → { release?: 'immediate'|'heartbeat'|'end', max? }

### Heartbeat
- POST /heartbeat/tick → record heartbeat
- POST /heartbeat/enable → { enabled: bool }
- GET /heartbeat/state → { enabled, last, count }

### Notifications
- POST /notify/push → { text, severity?: 'info'|'warn'|'error' }
- GET /notify/list → all notifications
- POST /notify/pop → { max? } → pop notifications

### Logs & Utilities
- GET /logs?n=200 → last N log lines
- GET /logs/csv/tail?rows=30 → reflection CSV tail
- POST /run → { action: 'recent-processes'|'save-note', ... }

### Reflection System
- GET /reflect/window?rows=30 → get reflection window
- POST /reflect/submit → submit reflection record

### Static Files
- GET /web → serves D:\court doc corrupion\scripts
- GET /web/index.html → Evidence Management UI

### Example calls (PowerShell)
- Status
  - irm http://127.0.0.1:9199/status | ConvertTo-Json -Depth 6
- Pull a model
  - irm -Method Post http://127.0.0.1:9199/ollama/pull -ContentType application/json -Body '{"model":"qwen3:latest"}'
- Chat
  - $b=@{model='qwen3:latest';temperature=0.7;messages=@(@{role='user';content='Say hello'})}|ConvertTo-Json -Depth 6; irm -Method Post http://127.0.0.1:9199/chat -ContentType application/json -Body $b
- TTS
  - irm -Method Post http://127.0.0.1:9199/tts -ContentType application/json -Body '{"text":"Hello Tyler","voice":"Microsoft Brian","rate":0,"volume":100}'

## Ollama API (used indirectly)
- GET /api/version → check Ollama is running
- GET /api/tags → list models
- POST /api/chat → chat completions (HubStation calls this for you)

## Static UI
- Base: http://127.0.0.1:9199/web
- Ollama GUI: http://127.0.0.1:9199/web/ollama-gui.html
  - Model list, Pull/Stop model, Chat, Speak (Windows TTS)
  - Self-prompt schema helpers: Insert Template, Send w/ Schema

## Configuration
- **File**: D:\court doc corrupion\HubStation\hub_config.json
  - **Current Settings**:
    - Port: **9199**
    - OllamaBaseUrl: "http://127.0.0.1:11434"
    - DefaultModel: "qwen3:latest"
    - DefaultVoice: "Microsoft Mark"
    - StaticRoot: "..\\scripts"
    - MaxCtxTokens: 10000
    - MaxPredictTokens: 512
    - WhisperCppExe: "D:\\tools\\whisper.cpp\\main.exe"
    - WhisperModelPath: "D:\\models\\ggml-base.en.bin"
    - Reflection: { WindowCount: 10, TailDefaultCount: 30 }

## Launch & Health
- **HubStation** (PowerShell):
  ```powershell
  cd "D:\court doc corrupion\HubStation"
  .\HubStation.ps1
  ```
  Should see: `Hub Station listening on http://127.0.0.1:9199/`

- **Ollama** (if not running):
  ```powershell
  ollama serve
  ```

- **Evidence UI**:
  - Via HubStation: http://127.0.0.1:9199/web/index.html
  - Direct file: Double-click `D:\court doc corrupion\scripts\index.html`

- **Health checks**:
  - HubStation: http://127.0.0.1:9199/ping
  - Ollama: http://127.0.0.1:11434/api/version
  - UI loaded: Check browser console (F12) for "System Initialized - Welcome Tyler!"

## Troubleshooting
- **"Hub not reachable"** in UI → Start HubStation.ps1
- **/models returns error** → Start Ollama, then pull a model (qwen3 or qwen2.5)
- **TTS voice missing** → Use default (no voice), or choose Mark/Brian/Zira
- **Port in use** → Check if another process is on 9199: `Get-NetTCPConnection -LocalPort 9199`
- **Static site not loading** → Confirm path D:\court doc corrupion\scripts exists
- **Google Drive not working** → Must use http:// (not file://), need OAuth Client ID
- **Kimi K2 showing** → ✅ Confirmed working (API calls functioning)
- **Missing functions errors** → ✅ Fixed: attachLogsButtons, attachStopButtons, attachNotifications added

## API Models Confirmed Working
- ✅ **Kimi K2 Thinking** (active, signed in)
- ⚙️ **Ollama** (qwen3:latest via port 11434)
- 🔄 **Gemini** (integration in index.html, needs API key)

## Recent Fixes (2025-01-14)
- ✅ Added missing `attachLogsButtons()` function
- ✅ Added missing `attachStopButtons()` function  
- ✅ Added missing `attachNotifications()` function with ephemeral notification system
- ✅ Verified port 9199 matches hub_config.json
- ✅ Connected all HubStation API endpoints to UI
- ✅ Fixed notification polling (3-second interval)

---
Last updated: 2025-01-14 (Tyler setup verification)
