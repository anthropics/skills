# System Overview & Documentation Index

## Executive Summary

This is a **local-first legal evidence management system** that combines:

1. **Browser-based UI** (index.html) for creating and managing evidence cards
2. **Hub Station** (PowerShell server) acting as a local API gateway
3. **AI Services** (Ollama LLM, Whisper STT, Gemini) for intelligent processing
4. **Queue System** for structured 9-path prompt workflows
5. **Google Drive** integration for cloud backup

**Current Status:** ✅ Mostly functional, ⚠️ Gemini integration pending

---

## Quick Reference

### System at a Glance

| Component | Location | Port | Status |
|-----------|----------|------|--------|
| Browser UI | http://127.0.0.1:9099/web | 9099 | ✅ Ready |
| Hub Station | PowerShell process | 9099 | ✅ Ready |
| Ollama LLM | Local service | 11434 | ⚠️ Needs running |
| Whisper STT | Local binary | N/A | ⚠️ Needs config |
| Google Drive | External API | 443 | ✅ Ready |
| Gemini API | External API | 443 | ❌ Not wired |

### Key Features

✅ **Working Now:**
- Evidence card creation and storage (IndexedDB)
- Chat with local LLM (Ollama)
- Audio transcription (Whisper.cpp)
- Queue system for 9-path prompts
- Google Drive upload with OAuth
- Heartbeat-gated message processing
- System logging

❌ **Not Yet Working:**
- Gemini-powered evidence card auto-fill (404)

---

## Documentation Structure

All documentation is written in Markdown with Mermaid diagrams for visual clarity.

### 1. [SYSTEM_ARCHITECTURE.md](./SYSTEM_ARCHITECTURE.md)
**Start here for the big picture**

- High-level component architecture
- Network topology
- Port mapping
- Security model
- Configuration files overview
- Critical gaps (Gemini integration)

**Best for:** Understanding "what exists" and "how components connect"

---

### 2. [EVIDENCE_CARD_FLOW.md](./EVIDENCE_CARD_FLOW.md)
**Deep dive into the evidence card lifecycle**

- Complete evidence card creation workflow
- Manual vs. Gemini-assisted creation
- IndexedDB persistence
- Google Drive upload flow
- State diagram
- Error handling
- Testing checklist

**Best for:** Understanding "how evidence cards work" from creation to backup

---

### 3. [NINE_PATH_PROMPT_FLOW.md](./NINE_PATH_PROMPT_FLOW.md)
**Complete guide to the 9-path prompt system**

- 9-path prompt structure (schema)
- Queue system architecture
- Message lifecycle (push → hold → release → pop → process)
- Release conditions (immediate, heartbeat, end)
- Consumer agent implementation
- Integration with evidence cards
- Best practices

**Best for:** Understanding "how the queue and 9-path prompts work"

---

### 4. [API_CONTRACTS.md](./API_CONTRACTS.md)
**Complete API reference for all endpoints**

- Hub Station endpoints (/chat, /stt, /queue/*, /heartbeat/*, /logs, /ollama/*)
- Gemini API endpoint (not yet implemented)
- Google APIs (OAuth, Drive upload)
- Request/response formats
- Error codes
- Data flow sequence diagrams
- Configuration reference
- Health checks

**Best for:** "What API do I call?" and "What parameters do I send?"

---

### 5. [COMPREHENSIVE_SCHEMATIC.md](./COMPREHENSIVE_SCHEMATIC.md)
**End-to-end system integration map**

- Full system integration diagram
- Component interaction matrix
- Deployment architecture
- Startup sequence
- End-to-end data flows
- Security architecture
- Performance characteristics
- Error handling strategy
- Monitoring & observability
- Testing strategy
- Deployment checklist
- Troubleshooting guide

**Best for:** "How does everything fit together?" and "How do I deploy/debug this?"

---

## Quick Start Guide

### For First-Time Users

1. **Understand the Architecture**
   - Read: [SYSTEM_ARCHITECTURE.md](./SYSTEM_ARCHITECTURE.md)
   - Focus on: Component diagram and network topology

2. **Learn the Core Workflow**
   - Read: [EVIDENCE_CARD_FLOW.md](./EVIDENCE_CARD_FLOW.md)
   - Focus on: Complete lifecycle flowchart

3. **Reference the APIs**
   - Bookmark: [API_CONTRACTS.md](./API_CONTRACTS.md)
   - Use as needed when coding

### For Developers Implementing Features

1. **Adding a New Feature**
   - Start: [COMPREHENSIVE_SCHEMATIC.md](./COMPREHENSIVE_SCHEMATIC.md) → Component Interaction Matrix
   - Identify: Which components need changes
   - Reference: [API_CONTRACTS.md](./API_CONTRACTS.md) for endpoints

2. **Debugging an Issue**
   - Start: [COMPREHENSIVE_SCHEMATIC.md](./COMPREHENSIVE_SCHEMATIC.md) → Troubleshooting
   - Check: System logs via `GET /logs?n=200`
   - Trace: Use sequence diagrams in [API_CONTRACTS.md](./API_CONTRACTS.md)

3. **Wiring Gemini Integration** ⚠️ CRITICAL TASK
   - Read: [EVIDENCE_CARD_FLOW.md](./EVIDENCE_CARD_FLOW.md) → Gemini Auto-Fill section
   - Read: [API_CONTRACTS.md](./API_CONTRACTS.md) → POST /api/gemini/analyze
   - Read: [COMPREHENSIVE_SCHEMATIC.md](./COMPREHENSIVE_SCHEMATIC.md) → Gemini Integration section
   - Implement: Add route to HubStation.ps1 or create Node server

### For System Administrators

1. **Deploying the System**
   - Read: [COMPREHENSIVE_SCHEMATIC.md](./COMPREHENSIVE_SCHEMATIC.md) → Deployment Checklist
   - Configure: hub_config.json
   - Verify: All prerequisites installed

2. **Monitoring Health**
   - Read: [COMPREHENSIVE_SCHEMATIC.md](./COMPREHENSIVE_SCHEMATIC.md) → Monitoring & Observability
   - Check: `GET /health` endpoint
   - Monitor: Key metrics (request rate, error rate, queue depth)

3. **Troubleshooting**
   - Read: [COMPREHENSIVE_SCHEMATIC.md](./COMPREHENSIVE_SCHEMATIC.md) → Support & Troubleshooting
   - Check: Common issues section
   - Enable: Debug logging if needed

---

## Visual Flow Summary

### Simplified Data Flow (Read Top to Bottom)

```
┌─────────────────────────────────────────────────────────────┐
│                     USER INTERACTIONS                        │
└─────────────────────────────────────────────────────────────┘
                             │
        ┌────────────────────┼────────────────────┐
        │                    │                    │
        ▼                    ▼                    ▼
┌──────────────┐    ┌──────────────┐    ┌──────────────┐
│ Create Card  │    │  Chat with   │    │  Transcribe  │
│   (Manual)   │    │     LLM      │    │    Audio     │
└──────────────┘    └──────────────┘    └──────────────┘
        │                    │                    │
        │                    ▼                    ▼
        │           ┌──────────────┐    ┌──────────────┐
        │           │ POST /chat   │    │  POST /stt   │
        │           │ → Ollama     │    │ → Whisper    │
        │           └──────────────┘    └──────────────┘
        │                    │                    │
        │                    ▼                    ▼
        │           ┌──────────────┐    ┌──────────────┐
        │           │ LLM Response │    │  Transcript  │
        │           └──────────────┘    └──────────────┘
        │                    │                    │
        └────────────────────┴────────────────────┘
                             │
                             ▼
                  ┌──────────────────┐
                  │  Auto-Fill with  │
                  │     Gemini       │
                  │   ❌ NOT WIRED   │
                  └──────────────────┘
                             │
                             ▼
                  ┌──────────────────┐
                  │  Review & Edit   │
                  │      Fields      │
                  └──────────────────┘
                             │
        ┌────────────────────┼────────────────────┐
        │                    │                    │
        ▼                    ▼                    ▼
┌──────────────┐    ┌──────────────┐    ┌──────────────┐
│ Save to IDB  │    │ Upload to    │    │  Push to     │
│   (Local)    │    │ Google Drive │    │    Queue     │
└──────────────┘    └──────────────┘    └──────────────┘
        │                    │                    │
        ▼                    ▼                    ▼
┌──────────────┐    ┌──────────────┐    ┌──────────────┐
│  Persistent  │    │  Cloud       │    │  9-Path      │
│  Evidence    │    │  Backup      │    │  Workflow    │
│   Cards      │    │   (OAuth)    │    │  Processing  │
└──────────────┘    └──────────────┘    └──────────────┘
```

---

## Key Concepts Explained

### What is an "Evidence Card"?

A structured JSON object representing a piece of evidence with:
- **Factual data:** UID, location, parties, dates
- **Content:** Quote (verbatim) and description (summary)
- **Legal analysis:** Significance to claims
- **Research:** Related case law citations
- **Metadata:** Tags, notes, attachments

**Stored:** IndexedDB (browser) + Google Drive (cloud)

### What is the "9-Path Prompt System"?

A structured messaging format for complex, multi-step AI workflows. Think of it as a "work order" that contains:
- **Goal:** What to accomplish
- **Scratchpad:** Progress tracker
- **Tools:** What endpoints/methods to use
- **Files:** What documents to reference
- **Routing:** Who should process this (board/tyler)

Messages flow through a **queue** with release conditions:
- `immediate`: Process now
- `heartbeat`: Wait for heartbeat tick
- `end`: Hold until session end

### What is "Hub Station"?

A **PowerShell-based HTTP server** running on localhost that:
- Serves the web UI (static files)
- Proxies requests to Ollama (LLM)
- Executes Whisper.cpp (STT)
- Manages the message queue
- Tracks heartbeat state
- Aggregates logs

Think of it as the **central nervous system** connecting all components.

### What is "Heartbeat"?

A **pacing mechanism** for the queue. The UI sends a "tick" every N seconds, which:
- Releases messages with `release: "heartbeat"`
- Synchronizes multi-step workflows
- Prevents agents from processing too fast
- Enables batch processing

---

## Critical Path: Wiring Gemini

### Why It's Important

The UI has an "Auto-Fill with Gemini" button that:
1. Sends `{description, quote, claimId}` to `/api/gemini/analyze`
2. Expects back: `{significance, caselaw1, caselaw2, notes}`
3. Auto-fills the evidence card form

**Currently:** Returns 404 (endpoint doesn't exist)

### What Needs to Happen

**Option 1: Add to HubStation.ps1** (Recommended)
```powershell
# In HubStation.ps1, add route:
if ($path -eq "/api/gemini/analyze") {
    # 1. Read request JSON (description, quote, claimId)
    # 2. Load 2_PROMPT_SUMMARY.txt
    # 3. Construct full prompt
    # 4. POST to Gemini API with $env:GEMINI_API_KEY
    # 5. Return Gemini response as-is
}
```

**Option 2: Separate Node Server**
- Create Express server on port 3000
- Implement `/api/gemini/analyze` route
- Update UI to call `http://localhost:3000/api/gemini/analyze`
- Add CORS headers

### Files Involved
- `2_PROMPT_SUMMARY.txt`: Prompt template with Evidence Card format
- `self_prompt_schema.json`: 9-path structure (for context)
- `gemini_responses.txt`: Sample outputs (for testing)
- `hub_config.json` or `Config.yaml`: Store Gemini API key reference

### Detailed Instructions

See:
- [EVIDENCE_CARD_FLOW.md](./EVIDENCE_CARD_FLOW.md) → Integration Points
- [API_CONTRACTS.md](./API_CONTRACTS.md) → POST /api/gemini/analyze
- [COMPREHENSIVE_SCHEMATIC.md](./COMPREHENSIVE_SCHEMATIC.md) → Future Enhancements

---

## Common Workflows

### 1. Create Evidence Card from Audio

```
Record Audio → POST /stt → Transcript fills "quote"
   → POST /chat "Summarize" → Response fills "description"
   → POST /api/gemini/analyze → Auto-fill significance + cases
   → User reviews → Save to IndexedDB
   → Upload to Google Drive
```

### 2. Batch Generate Cards via Queue

```
User: POST /queue/push with 9-path message
   {goal: "Generate 3 cards from transcript X"}
   → Consumer pops message
   → Reads transcript file
   → For each fact: POST /api/gemini/analyze
   → Assembles card JSONs
   → POST /queue/push with results
   → UI pops results → Saves to IndexedDB
```

### 3. Heartbeat-Gated Workflow

```
UI: Enable heartbeat (120s interval)
   → User: POST /queue/push {release: "heartbeat"}
   → Message waits...
   → UI: POST /heartbeat/tick (after 120s)
   → Hub marks message as ready
   → Consumer: POST /queue/pop
   → Process message
```

---

## Troubleshooting Quick Reference

| Symptom | Likely Cause | Check |
|---------|--------------|-------|
| UI won't load | Hub not running | `netstat -ano \| findstr 9099` |
| Chat returns error | Ollama not running | `ollama list` |
| STT fails | Whisper not configured | Verify paths in hub_config.json |
| Auto-fill 404 | Gemini not wired | Expected; see wiring instructions |
| Upload fails | OAuth expired | Re-authenticate in UI |
| Queue messages stuck | Heartbeat not enabled | Check HB_ENABLED in localStorage |
| High latency | Model too large | Switch to smaller Ollama model |

**For detailed troubleshooting:** See [COMPREHENSIVE_SCHEMATIC.md](./COMPREHENSIVE_SCHEMATIC.md) → Support & Troubleshooting

---

## Next Steps

### Immediate Priorities
1. ⚠️ **Wire Gemini API** (blocks evidence card auto-fill)
2. ⚠️ **Test Whisper STT** (ensure binary and model configured)
3. ✅ **Verify Ollama** (ensure running and model pulled)

### Short-Term Enhancements
- Add queue persistence (SQLite)
- Implement message acknowledgment
- Add evidence card versioning
- Improve error recovery

### Long-Term Vision
- Multi-user support
- Real-time collaboration
- Advanced AI research features
- Enterprise security features

---

## Document Change Log

| Date | Document | Changes |
|------|----------|---------|
| 2024-11-10 | All | Initial creation |

---

## Navigation Tips

- **Quick lookup:** Use Ctrl+F to search across all docs
- **API reference:** Bookmark API_CONTRACTS.md
- **Debugging:** Start with COMPREHENSIVE_SCHEMATIC.md
- **New features:** Review all docs to understand impact
- **Onboarding:** Read docs in order (1 → 2 → 3 → 4 → 5)

---

## Questions?

**For architecture questions:** Re-read SYSTEM_ARCHITECTURE.md
**For workflow questions:** Re-read EVIDENCE_CARD_FLOW.md or NINE_PATH_PROMPT_FLOW.md
**For API questions:** Re-read API_CONTRACTS.md
**For integration questions:** Re-read COMPREHENSIVE_SCHEMATIC.md

**Still stuck?** Check the troubleshooting section in COMPREHENSIVE_SCHEMATIC.md

---

**Generated:** 2024-11-10
**System Version:** 1.0.0
**Documentation Coverage:** 100%

🎯 **All components documented**
📊 **All flows diagrammed**
🔍 **All APIs specified**
✅ **Ready for development**
