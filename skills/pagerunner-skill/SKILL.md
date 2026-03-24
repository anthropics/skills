---
name: pagerunner-skill
description: Real Chrome browser automation for AI agents. Use when you need browser automation with real Chrome sessions, authenticated access using existing Chrome profiles, PII anonymization, or multi-agent browser coordination.
metadata:
  author: Stas
  license: MIT
  repository: https://github.com/Enreign/pagerunner-skill
  version: "1.0.0"
---

# Pagerunner Skill — Quick Start Guide

**Pagerunner** is real Chrome browser automation for AI agents. It gives Claude, Cursor, Windsurf, or any MCP client native control over your real Chrome — with your existing login sessions, cookies, and browser history already loaded.

## Choose Your Path

### 👨‍💻 Solo Developer (Claude Code / Cursor)

**Goal:** Close the implementation loop. Edit code → see the result in the browser → iterate without manual verification.

**Quick Start (5 lines):**
```javascript
const sessionId = await open_session({ profile: "personal" });
const [tab] = await list_tabs(sessionId);
await navigate(sessionId, tab.target_id, "http://localhost:3000");
await screenshot(sessionId, tab.target_id);  // see what you built
await close_session(sessionId);
```

**Killer Feature:** Your Chrome, already logged into everything. No API token setup.

---

### 📱 Power User (OpenClaw / Hermes)

**Goal:** Get browser tasks done from your phone while the laptop runs unattended.

**Quick Start:**
```javascript
// First time: log in manually and save the session
pagerunner open-session agent-work
pagerunner save-snapshot <session> <tab> https://jira.mycompany.com

// Later: agent profile is pre-authenticated
pagerunner open-session agent-work
pagerunner restore-snapshot <session> <tab> https://jira.mycompany.com
// Agent is logged in. Now do work: navigate, get_content, fill forms
```

**Real Example:**
```
WhatsApp: "Check my Jira for blockers"
→ OpenClaw triggers skill
→ open_session(profile="agent-work") → restore_snapshot
→ navigate to Jira → get_content → summarize
→ screenshot → send back to WhatsApp
```

---

### 🔒 Security-Conscious (NemoClaw / regulated industries)

**Goal:** Automate workflows on sensitive data without PII reaching the LLM.

**Quick Start:**
```javascript
open_session({
  profile: "agent",
  anonymize: true  // PII stripped before it reaches you.
});

// Every get_content result has PII replaced with tokens:
// john@company.com → [EMAIL:a3f9b2]
// Claude works with tokens
// Pagerunner de-tokenizes only when writing to forms
```

---

### ⚙️ Server-Side / Infrastructure (Hermes + cron)

**Goal:** Persistent browser automation across scheduled runs.

**Quick Start:**
```bash
pagerunner daemon &  # Run once, holds the DB lock

# Multiple agents share state via KV store
```

```javascript
// Agent A: collects data
await kv_set("pipeline", "pricing_data", JSON.stringify(results));

// Agent B (later): continues where A left off
const data = JSON.parse(await kv_get("pipeline", "pricing_data"));
```

---

## Common Gotchas

### 1️⃣ Arrays Cause Hallucinations

**Problem:** `evaluate()` returns `[25, 2]`. Claude guesses wrong field order.

**Solution:** Always return labeled objects from `evaluate()`:
```javascript
// ❌ BAD
return [likes, replies];

// ✅ GOOD
return { likes, replies };
```

### 2️⃣ Selectors Timing

**Solution:** Always use `wait_for` before clicking:
```javascript
await navigate(sessionId, tabId, newUrl);
await wait_for(sessionId, tabId, selector: ".load-more-btn", ms: 5000);
await click(sessionId, tabId, ".load-more-btn");
```

### 3️⃣ Fill vs Type

- **`fill()`** — clears the field and types (React synthetic events)
- **`type_text()`** — types without clearing (plain HTML)

Use `fill()` for modern frameworks.

---

## Core Workflow: Form Filling with Error Recovery

```javascript
const sessionId = await open_session({ profile: "personal" });
const tabs = await list_tabs(sessionId);
const tabId = tabs[0].target_id;

await navigate(sessionId, tabId, "https://example.com/form");
await wait_for(sessionId, tabId, selector: ".submit-btn", ms: 5000);

try {
  await fill(sessionId, tabId, "input[name='email']", "user@example.com");
  await fill(sessionId, tabId, "input[name='password']", "secret");
  await click(sessionId, tabId, ".submit-btn");
  await wait_for(sessionId, tabId, selector: ".success-message", ms: 5000);
} catch (error) {
  const errorMsg = await get_content(sessionId, tabId);
  // Claude parses error → retries with correction
}

await screenshot(sessionId, tabId);
await close_session(sessionId);
```

---

## Setup

### 1. Install Pagerunner

```bash
# macOS (Homebrew)
brew tap enreign/pagerunner
brew install pagerunner

# Or Cargo
cargo install pagerunner
```

### 2. Register as MCP server

```bash
claude mcp add pagerunner "$(which pagerunner)" mcp
```

### 3. Configure Chrome profiles (optional)

```bash
pagerunner init
```

**Note:** Close any Chrome window before opening a Pagerunner session on that profile.

---

## Documentation

Full documentation at https://github.com/Enreign/pagerunner-skill:

- **PATTERNS.md** — 11 workflow patterns (form filling, auth, scrolling, etc.)
- **REFERENCE.md** — All 27 Pagerunner tools with examples
- **SECURITY.md** — Anonymization, audit log, encryption, domain allowlisting
- **HALLUCINATION_PREVENTION.md** — Why arrays cause hallucinations and how to fix it
- **DEBUGGING.md** — Troubleshooting common issues
- **EXAMPLES.md** — Full ICP workflows + multi-agent patterns
- **ADVANCED.md** — Multi-agent coordination, daemon lifecycle, performance
