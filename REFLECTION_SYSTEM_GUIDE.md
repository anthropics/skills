# Reflection System Guide

**Status:** ✅ Complete and Integrated
**Branch:** `claude/powershell-runner-integration-1762817846`
**Commit:** `30e09b0`

---

## What Was Added

### 1. **Reflections.psm1 Module** (`HubStation/Reflections.psm1`)

Simple PowerShell module that provides:

#### Functions:
- `Initialize-ReflectionStore` - Creates `shared_bus/` directory structure
- `Add-LogRow` - Append row to CSV (handles escaping)
- `Get-LogTailCsv` - Read last N rows from CSV
- `Request-ReflectionWindow` - Package CSV tail for model
- `Submit-ReflectionRow` - Write reflection JSON + CSV row
- `Write-EventJsonl` - Generic event logging

### 2. **shared_bus Directory Structure**

```
HubStation/
└── shared_bus/
    ├── inbox/          (future: incoming messages)
    ├── outbox/         (future: outgoing messages)
    ├── reflections/    (reflection JSON files)
    └── logs/
        └── hub_events.csv  (unified CSV log)
```

### 3. **CSV Schema** (`hub_events.csv`)

```csv
epoch_ms,type,source_model,action,uid,content_preview,meta_tags,detail_path
```

**Fields:**
- `epoch_ms` - Unix timestamp in milliseconds
- `type` - Event type (e.g., "event", "reflection", "chat", "queue")
- `source_model` - Model that generated event (e.g., "kimi-k2-thinking", "gemini-2.0")
- `action` - Action performed (e.g., "submit", "analyze", "prompt")
- `uid` - Evidence card UID (if applicable)
- `content_preview` - First 100 chars of content
- `meta_tags` - Searchable tags (comma-separated)
- `detail_path` - Path to full JSON file (for reflections)

### 4. **Three New Endpoints**

#### A. **GET /logs/csv/tail?rows=30**
Get last N rows from CSV log.

**Request:**
```bash
curl http://localhost:9199/logs/csv/tail?rows=30
```

**Response:**
```json
{
  "ok": true,
  "rows": [
    {
      "epoch_ms": "1699724800000",
      "type": "event",
      "source_model": "kimi-k2-thinking",
      "action": "prompt",
      "uid": "111",
      "content_preview": "User asked about evidence...",
      "meta_tags": "question,evidence,card",
      "detail_path": ""
    }
  ],
  "count": 1
}
```

#### B. **GET /reflect/window?rows=30**
Same as `/logs/csv/tail` but packaged for reflection.

**Request:**
```bash
curl http://localhost:9199/reflect/window?rows=30
```

**Response:**
```json
{
  "ok": true,
  "request_id": "uuid-here",
  "window": {
    "row_count": 1,
    "window_rows": [
      { "epoch_ms": "...", "type": "event", ... }
    ]
  }
}
```

#### C. **POST /reflect/submit**
Submit a reflection JSON.

**Request:**
```bash
curl -X POST http://localhost:9199/reflect/submit \
  -H "Content-Type: application/json" \
  -d '{
    "title": "Task Completion Reflection",
    "goal": "Analyze evidence card workflow",
    "summary": "Successfully analyzed 3 evidence cards",
    "source_model": "kimi-k2-thinking",
    "uid": "111",
    "meta_tags": "reflection,analysis,complete"
  }'
```

**Response:**
```json
{
  "ok": true,
  "epoch_ms": "1699724800000",
  "json_path": "HubStation/shared_bus/reflections/reflection_1699724800000.json",
  "csv_row": {
    "epoch_ms": "1699724800000",
    "type": "reflection",
    "source_model": "kimi-k2-thinking",
    "action": "submit",
    "uid": "111",
    "content_preview": "Task Completion Reflection",
    "meta_tags": "reflection,analysis,complete",
    "detail_path": "HubStation/shared_bus/reflections/reflection_1699724800000.json"
  }
}
```

### 5. **Port Change**

- **Old:** Port 9099 (conflict with PID 4)
- **New:** Port 9199

Update your connections:
```javascript
// Old
fetch('http://localhost:9099/api/...')

// New
fetch('http://localhost:9199/api/...')
```

### 6. **Debug Checkpoints**

Added debug logging to track startup:
- `[DEBUG] HubStation starting...`
- `[DEBUG] Config loaded. Port: 9199`
- `[INIT] GeminiService module loaded`
- `[INIT] OllamaRunner Router loaded`
- `[INIT] Reflections module loaded`
- `[LISTENER] Hub Station listening on http://127.0.0.1:9199/`
- `[DEBUG] Entering request loop...`

---

## How Models Use This

### Workflow:

1. **Model asks for reflection window:**
   ```
   GET /reflect/window?rows=30
   ```

2. **Model receives last 30 CSV rows** with context about what happened

3. **Model writes reflection** (structured JSON with analysis)

4. **Model submits reflection:**
   ```
   POST /reflect/submit
   {
     "title": "...",
     "goal": "...",
     "summary": "...",
     "source_model": "kimi-k2-thinking",
     ...
   }
   ```

5. **System writes:**
   - Full JSON: `shared_bus/reflections/reflection_<epoch>.json`
   - Compact CSV row: One line in `hub_events.csv` with `type=reflection`

6. **Excel handles analysis** using native CSV tools

---

## Integration with Existing System

### Nothing Was Changed:
- ✅ **OllamaRunner** still works (Logger.ps1 CSV)
- ✅ **GeminiService** still works (evidence cards)
- ✅ **index.html** untouched (original GUI)
- ✅ All existing endpoints work

### What Was Added:
- ✅ **Reflections.psm1** (new layer on top)
- ✅ **shared_bus/** (new directory)
- ✅ **3 endpoints** (reflection-specific)

### Two Logging Systems (Both Work):
1. **OllamaRunner CSV** (`OllamaRunner/logs/*.csv`)
   - Per-session logs
   - Full 14-column reflection schema
   - Used by Logger.ps1

2. **Reflections CSV** (`shared_bus/logs/hub_events.csv`)
   - Unified log across all sources
   - 8-column compact schema
   - Used by Reflections.psm1
   - Links to detail JSON files

---

## Testing

### 1. Start HubStation

```powershell
cd The-CourtRoom-Masterpiece/HubStation
powershell -File HubStation.ps1
```

**Expected output:**
```
[DEBUG] HubStation starting...
[DEBUG] Config loaded. Port: 9199
[INIT] GeminiService module loaded
[INIT] OllamaRunner Router loaded
[INIT] Reflections module loaded
[LISTENER] Hub Station listening on http://127.0.0.1:9199/
[DEBUG] Entering request loop...
```

### 2. Test Reflection Window

```powershell
Invoke-RestMethod -Uri "http://localhost:9199/reflect/window?rows=5" | ConvertTo-Json -Depth 5
```

**Expected:**
```json
{
  "ok": true,
  "request_id": "uuid",
  "window": {
    "row_count": 0,
    "window_rows": []
  }
}
```

### 3. Test Reflection Submit

```powershell
$body = @{
    title = "Test Reflection"
    goal = "Test the reflection system"
    summary = "Successfully tested reflection submission"
    source_model = "test"
} | ConvertTo-Json

Invoke-RestMethod -Uri "http://localhost:9199/reflect/submit" `
                  -Method Post `
                  -Body $body `
                  -ContentType "application/json" | ConvertTo-Json -Depth 5
```

**Expected:**
```json
{
  "ok": true,
  "epoch_ms": "...",
  "json_path": "...",
  "csv_row": {...}
}
```

### 4. Verify Files Created

```powershell
# Check CSV has new row
Get-Content HubStation/shared_bus/logs/hub_events.csv

# Check JSON file created
Get-ChildItem HubStation/shared_bus/reflections/*.json
```

---

## Excel Integration

### Open CSV in Excel:

1. Open Excel
2. File → Open → `HubStation/shared_bus/logs/hub_events.csv`
3. Data should load with columns: epoch_ms, type, source_model, action, uid, content_preview, meta_tags, detail_path

### Use Excel Tools:

- **Filter by type:** Show only reflections
- **Sort by epoch_ms:** Chronological order
- **Search meta_tags:** Find specific topics
- **Pivot tables:** Analyze patterns
- **Conditional formatting:** Highlight important events
- **Formulas:** Calculate metrics

### Open Detail JSON:

When you see a reflection row, the `detail_path` column has the full JSON path. Open that file to see the complete reflection.

---

## API Reference

### GET /logs/csv/tail

**Query Parameters:**
- `rows` (optional, default: 30) - Number of rows to return

**Response:**
```json
{
  "ok": boolean,
  "rows": array,
  "count": number
}
```

### GET /reflect/window

**Query Parameters:**
- `rows` (optional, default: 30) - Number of rows to return

**Response:**
```json
{
  "ok": boolean,
  "request_id": string,
  "window": {
    "row_count": number,
    "window_rows": array
  }
}
```

### POST /reflect/submit

**Request Body:**
```json
{
  "title": string (required),
  "goal": string,
  "summary": string,
  "source_model": string,
  "uid": string (optional),
  "meta_tags": string (optional),
  ... (any other reflection fields)
}
```

**Response:**
```json
{
  "ok": boolean,
  "epoch_ms": string,
  "json_path": string,
  "csv_row": object
}
```

---

## Troubleshooting

### Issue: "Reflections module not loaded"

**Check:**
```powershell
Test-Path HubStation/Reflections.psm1
```

**Fix:**
If file exists, check module syntax:
```powershell
Import-Module ./HubStation/Reflections.psm1 -Force
```

### Issue: Port 9199 in use

**Check:**
```powershell
netstat -ano | findstr :9199
```

**Fix:**
Change port in `hub_config.json` to another port (e.g., 9200)

### Issue: CSV empty

**Verify:**
```powershell
Get-Content HubStation/shared_bus/logs/hub_events.csv
```

Should have at least the header row. If missing, delete file and restart HubStation (will recreate).

### Issue: No debug output

**Check execution policy:**
```powershell
Get-ExecutionPolicy
```

**Fix if needed:**
```powershell
Set-ExecutionPolicy -Scope Process -ExecutionPolicy Bypass
```

---

## Next Steps

1. **Test all endpoints** (see Testing section)
2. **Wire event logging** (add Write-EventJsonl calls to /chat, /queue, /ollama endpoints)
3. **Update floating overlay** (point to port 9199 instead of 9099)
4. **Add model prompt** (include reflection endpoints in model's system prompt)

---

**Version:** 1.0
**Last Updated:** 2024-11-11
**Status:** ✅ Complete and Ready to Test
