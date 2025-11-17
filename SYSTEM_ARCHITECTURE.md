# System Architecture Overview

## High-Level Component Architecture

```mermaid
graph TB
    subgraph Browser["Browser (Client)"]
        UI[index.html<br/>Evidence Cards UI<br/>PDF Viewer<br/>Timeline/Menu]
        IDB[(IndexedDB<br/>evidence_cards)]
        OAuth[Google Identity<br/>OAuth Client]
    end

    subgraph HubServer["Hub Station (PowerShell)<br/>127.0.0.1:9099"]
        Hub[HubStation.ps1<br/>HTTP Listener]
        Config[hub_config.json]
        Routes{Routes}
        Queue[(Queue<br/>In-Memory)]
        HBState[(Heartbeat State)]
    end

    subgraph LocalServices["Local Services"]
        Ollama[Ollama LLM<br/>127.0.0.1:11434]
        Whisper[Whisper.cpp<br/>STT Engine]
    end

    subgraph GoogleServices["Google Cloud"]
        Drive[Google Drive API]
        GeminiAPI[Gemini API<br/>Not Implemented]
    end

    subgraph PromptAssets["Prompt Assets"]
        PromptSummary[2_PROMPT_SUMMARY.txt<br/>Evidence Card Spec]
        Schema[self_prompt_schema.json<br/>9-Path Structure]
        Template[self_prompt_template.json<br/>9-Path Template]
        Responses[gemini_responses.txt<br/>Sample Cards]
    end

    UI -->|Static Files| Hub
    UI -->|POST /chat| Routes
    UI -->|POST /stt| Routes
    UI -->|POST /queue/push| Routes
    UI -->|GET /logs| Routes
    UI -->|Heartbeat| Routes
    UI -->|OAuth Token| OAuth
    OAuth -->|Upload Files| Drive
    UI -.->|POST /api/gemini/analyze<br/>NOT WIRED| GeminiAPI

    Routes -->|Forward| Ollama
    Routes -->|Execute| Whisper
    Routes -->|Store/Retrieve| Queue
    Routes -->|Track| HBState
    Routes -->|Read Config| Config

    Hub -->|Serve Static| UI

    PromptAssets -.->|Reference| GeminiAPI
    PromptAssets -.->|Schema| Queue

    style GeminiAPI fill:#f99,stroke:#333,stroke-width:4px
    style UI fill:#9cf,stroke:#333,stroke-width:2px
    style Hub fill:#9f9,stroke:#333,stroke-width:2px
```

## Component Responsibilities

### Browser UI (index.html)
- **Evidence Card Management**: Create, edit, save cards to IndexedDB
- **PDF Viewer**: Display and annotate documents
- **Timeline & Navigation**: Organize evidence chronologically
- **Audio Input**: Record and transcribe via STT
- **Google Integration**: OAuth and Drive uploads
- **Chat Interface**: Mini-chat with LLM

### Hub Station (PowerShell Server)
- **Static File Server**: Serves web assets from `StaticRoot`
- **API Gateway**: Routes requests to local services
- **Queue Manager**: Manages message queue for 9-path prompts
- **Heartbeat Monitor**: Tracks system health/cadence
- **Log Aggregator**: Collects and serves system logs
- **Bridge**: Connects UI to Ollama, Whisper, and local tools

### Local Services
- **Ollama**: LLM inference engine (qwen3:latest default)
- **Whisper.cpp**: Speech-to-text transcription

### Google Services
- **Drive API**: File storage and retrieval
- **Gemini API**: ⚠️ NOT IMPLEMENTED - Evidence card auto-fill

## Data Stores

| Store | Type | Location | Purpose |
|-------|------|----------|---------|
| IndexedDB | Browser | Client | Evidence cards persistence |
| Queue | In-Memory | Hub Server | 9-path prompt messages |
| Heartbeat State | In-Memory | Hub Server | Health monitoring |
| Log Buffer | In-Memory | Hub Server | System logs |

## Network Topology

```mermaid
graph LR
    Browser[Browser<br/>localhost]
    Hub[Hub Server<br/>127.0.0.1:9099]
    Ollama[Ollama<br/>127.0.0.1:11434]
    Drive[Google Drive<br/>External]
    Gemini[Gemini API<br/>External]

    Browser <-->|HTTP| Hub
    Browser -->|HTTPS| Drive
    Browser -.->|HTTPS<br/>NOT WIRED| Gemini
    Hub -->|HTTP| Ollama
    Hub -->|Local Exec| Whisper[Whisper.cpp<br/>Local Binary]

    style Gemini fill:#f99,stroke:#333,stroke-width:4px
```

## Port Map

| Service | Address | Protocol | Status |
|---------|---------|----------|--------|
| Hub Station | 127.0.0.1:9099 | HTTP | ✅ Ready |
| Ollama | 127.0.0.1:11434 | HTTP | ⚠️ Needs Running |
| Whisper.cpp | Local Exec | File | ⚠️ Needs Binary |
| Google Drive | External | HTTPS | ✅ Ready |
| Gemini API | External | HTTPS | ❌ Not Wired |

## Security Model

- **Local-First**: Hub only binds to 127.0.0.1 (localhost)
- **No Authentication**: Hub assumes trusted local environment
- **Google OAuth**: Browser-based OAuth flow for Drive access
- **No API Keys in Frontend**: Gemini requires server-side proxy
- **CORS**: Hub allows all origins for local dev

## Configuration Files

```mermaid
graph TD
    HubConfig[hub_config.json] -->|StaticRoot| Static[Web Files Path]
    HubConfig -->|OllamaBaseUrl| Ollama[Ollama URL]
    HubConfig -->|WhisperCppExe| WhisperBin[Whisper Binary]
    HubConfig -->|WhisperModelPath| WhisperModel[Whisper Model]
    HubConfig -->|MaxNumCtx| LLMSettings[LLM Limits]

    ConfigYaml[Config.yaml] -.->|Hint| NodeServer[Node Server<br/>Alternative]

    Schema[self_prompt_schema.json] -->|Defines| QueueFormat[9-Path Message Format]
    Template[self_prompt_template.json] -->|Provides| Blank[Empty Template]
    PromptSummary[2_PROMPT_SUMMARY.txt] -->|Specifies| EvidenceFormat[Evidence Card Format]

    style NodeServer fill:#ff9,stroke:#333,stroke-width:2px
```

## Critical Gaps

⚠️ **Missing Gemini Integration**
- UI expects `POST /api/gemini/analyze`
- Returns 404 currently
- Blocks "Auto-Fill with Gemini" feature

**Two Options to Fix:**
1. **Add to Hub**: Implement `/api/gemini/analyze` in HubStation.ps1
2. **Separate Service**: Run Node Express server on port 3000

See detailed wiring instructions in GEMINI_INTEGRATION.md
