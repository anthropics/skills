# Easy Start Guide - For Screen Readers

**This guide is optimized for screen readers and blind users.**

---

## One-Click Startup

### Option 1: Double-Click the Batch File (Easiest)

1. Navigate to: `The-CourtRoom-Masterpiece\HubStation\`
2. Find: `START.bat`
3. Double-click (or press Enter on it)
4. **Listen for audio feedback** - The system will speak to you

### Option 2: PowerShell (If batch file doesn't work)

1. Open PowerShell
2. Type or paste:
   ```
   cd The-CourtRoom-Masterpiece\HubStation
   powershell -File Start-HubStation.ps1
   ```
3. Press Enter
4. **Listen for audio feedback**

---

## What You'll Hear

The startup script will **speak** each step:

1. "Starting HubStation setup"
2. "Directory check passed"
3. "Checking for Ollama"
   - If Ollama is running: "Ollama is running"
   - If not: "WARNING: Ollama is not running"
4. "Checking for Gemini API key"
   - If found: "Gemini API key found"
   - If not: You'll be asked to enter it
5. "Checking if port 9199 is available"
   - If available: "Port 9199 is available"
6. "All checks passed. Starting HubStation now."
7. Then you'll hear module loading messages

---

## Success Messages

When HubStation starts successfully, you'll hear:

- "GeminiService module loaded"
- "OllamaRunner Router loaded"
- "Reflections module loaded"
- "Hub Station listening on http://127.0.0.1:9199/"

**If you hear all these, you're good to go!**

---

## If Something Goes Wrong

### Problem: "Ollama is not running"

**Solution:**
1. Open a **new** PowerShell window (don't close the current one)
2. Type: `ollama serve`
3. Press Enter
4. Go back to the HubStation window and type: `y` (then Enter)

### Problem: "Port 9199 is already in use"

**Solution:**
1. Something else is using port 9199
2. Close HubStation if it's already running
3. Or change the port:
   - Open: `HubStation\hub_config.json`
   - Change `"Port": 9199` to `"Port": 9299`
   - Save and try again

### Problem: No audio feedback

**Solution:**
1. Check your speaker volume
2. Or run with: `powershell -File Start-HubStation.ps1 -NoSound`
   (This disables audio but still shows text)

---

## Keyboard Shortcuts

While HubStation is running:

- **Ctrl+C** - Stop HubStation (you'll hear Windows beep)
- **Ctrl+Break** - Force stop (if Ctrl+C doesn't work)

---

## What Runs on Startup

1. **Checks** - Verifies Ollama, Gemini API, port availability
2. **Loads modules:**
   - GeminiService (evidence card generation)
   - OllamaRunner (6 routes for AI model)
   - Reflections (CSV logging system)
3. **Starts web server** on http://localhost:9199

---

## After Startup - Quick Tests

### Test 1: Check if server is running

In a **new** PowerShell window:
```powershell
Invoke-RestMethod -Uri "http://localhost:9199/status"
```

You should hear your screen reader say: "ok: True, port: 9199"

### Test 2: Check reflection system

```powershell
Invoke-RestMethod -Uri "http://localhost:9199/reflect/window?rows=5"
```

Should hear: "ok: True, window: ..."

---

## Stopping HubStation

1. Go back to the HubStation window
2. Press **Ctrl+C**
3. You'll hear Windows beep (confirmation)
4. HubStation will say "Stopping..." (if audio is working)

---

## Files You Need to Know About

All in `HubStation\` directory:

- **START.bat** - Double-click this to start (easiest!)
- **Start-HubStation.ps1** - PowerShell startup script (has audio)
- **HubStation.ps1** - Main server (don't run this directly)
- **hub_config.json** - Settings (port, API keys, etc.)

---

## Troubleshooting Audio

If audio doesn't work:

1. Your system might not have Microsoft voices installed
2. Check: Control Panel → Speech → Text to Speech
3. You should see voices like "Microsoft Mark" or "Microsoft Zira"
4. If no voices, the script still works but won't speak

**Windows 10/11 should have voices by default**

---

## Setting Gemini API Key (If Needed)

### During Startup:
- Script will ask: "Enter your Gemini API key"
- Paste your key (Ctrl+V)
- Press Enter

### Before Startup (Permanent):
1. Open PowerShell
2. Type:
   ```powershell
   [System.Environment]::SetEnvironmentVariable('GEMINI_API_KEY', 'your-key-here', 'User')
   ```
3. Close PowerShell
4. Open new PowerShell
5. Run startup script

---

## Quick Reference - Common Commands

**Start HubStation:**
```
cd The-CourtRoom-Masterpiece\HubStation
.\START.bat
```

**Check status:**
```powershell
Invoke-RestMethod -Uri "http://localhost:9199/status"
```

**Stop HubStation:**
- Press **Ctrl+C** in HubStation window

**Check logs:**
```powershell
Get-Content shared_bus\logs\hub_events.csv
```

---

## Help! I'm Stuck

If you can't get it working:

1. **Check your speaker is on** (for audio feedback)
2. **Make sure Ollama is running** (`ollama serve`)
3. **Try the batch file** (`START.bat`) - easiest method
4. **Check you're in the right directory** (should see `HubStation.ps1`)

---

## Screen Reader Tips

- **NVDA users:** Make sure "Speak command output" is enabled
- **JAWS users:** Use virtual cursor mode for reading output
- **Narrator users:** Should work automatically with verbose mode

---

**That's it! Just double-click START.bat and listen for the audio feedback.**

If you hear "Hub Station listening on...", you're all set! 🎉
