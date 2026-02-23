---
name: acommons
description: >
  AI coding tool usage analytics. Tracks token usage across Claude Code, Codex CLI,
  OpenCode, Gemini CLI, and external tools. Use when user wants to view AI usage stats,
  sync usage data, or set up automatic usage tracking.
license: MIT
compatibility: Requires Node.js 20+. Works with Claude Code, Cursor, Windsurf, Cline, and other AI agents.
metadata:
  author: phlegonlabs
  version: "1.0"
---

# acommons — AI Usage Analytics Skill

You are an AI agent with access to local AI tool usage data. When the user invokes `/acommons`, parse `$ARGUMENTS` and route to the matching subcommand below.

**Default subcommand:** `stats` (when no argument given)

## Environment

```
DATA_DIR = ~/.agentic-commons
CLAUDE_STATS = ~/.claude/stats-cache.json
CLAUDE_LEDGER = ~/.agentic-commons/claude-ledger.json
CODEX_SESSIONS = ~/.codex/sessions/
CODEX_LEDGER = ~/.agentic-commons/codex-ledger.json
OPENCODE_DB = ~/.local/share/opencode/opencode.db
GEMINI_SESSIONS = ~/.gemini/tmp/*/chats/session-*.json
EXTERNAL_USAGE = ~/.agentic-commons/external-usage/
```

On Windows: `~/.opencode` → `~/AppData/Roaming/opencode`

---

## Subcommand: `stats` (default)

Show today's AI tool usage in a table.

**Steps:**

1. Read `~/.claude/stats-cache.json` → extract today from `dailyActivity` (messages, sessions, toolCalls) and `dailyModelTokens` (tokensByModel sum)
2. Check `~/.agentic-commons/claude-ledger.json` → if it has today's entry, sum all models' `totalIO` for a more accurate token count
3. Check `~/.codex/sessions/` → count `.jsonl` files as sessions. For token total: prefer `~/.agentic-commons/codex-ledger.json` if exists, otherwise count files
4. Check `~/.local/share/opencode/opencode.db` → if exists, report "detected" (reading SQLite requires the collect script)
5. Check `~/.gemini/tmp/` → count `session-*.json` files
6. Check `~/.agentic-commons/external-usage/` → count `.jsonl` files

**Output format:**

```
AI Tool Usage — Today (YYYY-MM-DD)

Tool          Sessions  Messages  IO Tokens   Tool Calls
────────────  ────────  ────────  ──────────  ──────────
Claude Code         3        42    130.0K         120
Codex CLI           5        --     89.2K          --
OpenCode            2        --     45.1K          --
Gemini CLI          1        --     12.3K          --
────────────  ────────  ────────  ──────────  ──────────
Total              11        42    276.6K         120
```

Format numbers: `1,234` for small, `12.3K` for thousands, `1.5M` for millions.

---

## Subcommand: `daily`

Show 14-day daily breakdown.

**Steps:**

1. Read `~/.claude/stats-cache.json` → `dailyActivity` array (each has date, messageCount, sessionCount)
2. Read `~/.claude/stats-cache.json` → `dailyModelTokens` array (each has date, tokensByModel)
3. Also read Claude ledger for more accurate daily totals if available
4. For other tools: read their respective data sources and group by date

**Output format:**

```
Daily Usage — Last 14 Days

Date        Claude    Codex    OpenCode  Gemini   Total
──────────  ────────  ───────  ────────  ───────  ────────
2025-01-15   130.0K    89.2K    45.1K    12.3K   276.6K
2025-01-14    95.0K    72.1K    38.0K     8.1K   213.2K
...
```

---

## Subcommand: `models`

Show per-model token usage aggregated across all time.

**Steps:**

1. Read `~/.claude/stats-cache.json` → `modelUsage` object (keyed by model name, each has inputTokens, outputTokens, cacheReadInputTokens, cacheCreationInputTokens)
2. Read Claude ledger → `dailyByModel` → aggregate all dates per model
3. Read Codex ledger → aggregate per [provider, model]
4. Read other sources as available

**Output format:**

```
Token Usage by Model

Source       Model                          Input     Output    Cached     Total IO
───────────  ─────────────────────────────  ────────  ────────  ─────────  ────────
Claude       claude-sonnet-4-20250514         80.0K    50.0K    230.0K    130.0K
Claude       claude-haiku-4-5-20251001        20.0K    10.0K     50.0K     30.0K
Codex        gpt-4o                           60.0K    29.2K     15.0K     89.2K
OpenCode     claude-sonnet-4-20250514         30.0K    15.1K     40.0K     45.1K
Gemini       gemini-2.5-pro                    8.0K     4.3K      6.0K     12.3K
```

---

## Subcommand: `total`

Show all-time aggregated summary.

**Steps:**

1. Aggregate all data sources
2. Sum by source (claude, codex, opencode, gemini, external)

**Output:**

```
All-Time Usage Summary

Source       Days   Sessions   IO Tokens    Cached Tokens
───────────  ─────  ─────────  ───────────  ─────────────
Claude          45       150      4.5M          12.3M
Codex           30        89      2.1M           0.3M
OpenCode        20        45      0.9M           0.4M
Gemini          10        25      0.3M           0.1M
External         5        --      0.1M              0
───────────  ─────  ─────────  ───────────  ─────────────
Total           45       309      7.9M          13.1M
```

---

## Subcommand: `sync`

Run the full collect + upload pipeline.

**Action:** Execute the collect script:

```bash
node ~/.agentic-commons/collect.mjs
```

If `~/.agentic-commons/collect.mjs` does not exist, tell the user to run `/acommons setup` first.

Show the script output to the user.

---

## Subcommand: `setup`

First-time setup: install hook, scheduler, and copy scripts.

**Action:** Execute the setup script:

```bash
bash <skill_dir>/scripts/setup.sh
```

Where `<skill_dir>` is the directory containing this SKILL.md file.

If on Windows and bash is not available, run the steps manually:

1. Create `~/.agentic-commons/` directory
2. Copy `<skill_dir>/scripts/hook.mjs` → `~/.agentic-commons/hook.mjs`
3. Copy `<skill_dir>/scripts/collect.mjs` → `~/.agentic-commons/collect.mjs`
4. Install Claude Code Stop Hook by modifying `~/.claude/settings.json`:
   ```json
   {
     "hooks": {
       "Stop": [
         { "hooks": [{ "type": "command", "command": "node ~/.agentic-commons/hook.mjs" }] }
       ]
     }
   }
   ```
   (Merge with existing hooks, don't overwrite)
5. Install hourly scheduler:
   - **Windows:** `schtasks /create /tn "AgenticCommons" /tr "wscript.exe <vbs_path>" /sc hourly /f`
   - **macOS:** Create LaunchAgent plist at `~/Library/LaunchAgents/com.agentic-commons.plist`
   - **Linux:** Add crontab entry `0 * * * * node ~/.agentic-commons/collect.mjs`

After setup, suggest the user run `/acommons link` to connect their account.

---

## Subcommand: `link`

Device OAuth authentication flow.

**Steps:**

1. Read or create device secret from `~/.agentic-commons/device-secret.key` (64-char hex)
2. Build device identity (hostname, platform, arch, cpu/memory info)
3. POST to `https://api.agenticcommons.xyz/v1/auth/device/start`:
   ```json
   { "device_label": "<hostname>", "device_secret": "<hex>", "device_profile": {...} }
   ```
4. Show the user: verification URL and user code
5. Open browser to `verification_uri_complete`
6. Poll `POST /v1/auth/device/poll` with `{ "device_code": "..." }` every N seconds
7. On `"authorized"`: save `access_token` to `~/.agentic-commons/api-token.secret`
8. Update `~/.agentic-commons/config.json` with `linkedAt` and `deviceLabel`

**Note:** On Windows, the token is encrypted with PowerShell SecureString before saving.

---

## Subcommand: `doctor`

Health check and diagnostics.

**Check each item and report status:**

1. `~/.agentic-commons/` directory exists and permissions are 700
2. `~/.agentic-commons/config.json` exists, show `lastSetup` date
3. `~/.agentic-commons/api-token.secret` exists (linked status)
4. `~/.claude/settings.json` has acommons Stop hook configured
5. Scheduler installed (check schtasks/launchd/crontab)
6. `~/.claude/stats-cache.json` readable (Claude Code detected)
7. `~/.codex/sessions/` exists (Codex CLI detected)
8. `~/.local/share/opencode/opencode.db` exists (OpenCode detected)
9. `~/.gemini/tmp/` exists (Gemini CLI detected)
10. `~/.agentic-commons/upload-tracker.json` — last upload info

**Output format:**

```
acommons Doctor

  ✓ Data directory exists (~/.agentic-commons/)
  ✓ Config found (last setup: 2025-01-10)
  ✓ Device linked (api-token.secret present)
  ✓ Claude Code Stop hook installed
  ✓ Scheduler: schtasks (Windows)
  ✓ Claude Code detected (stats-cache.json readable)
  ✗ Codex CLI not found
  ✓ OpenCode detected (opencode.db readable)
  ✗ Gemini CLI not found
  ✓ Last upload: 2025-01-15 (42 payloads)
```

---

## Subcommand: `probe`

Detect all installed AI coding tools (not just data sources).

**Scan for these tools:**

| Tool | Config Dir | Binary | Provider |
|------|-----------|--------|----------|
| Claude Code | ~/.claude | claude | anthropic |
| Codex CLI | ~/.codex | codex | openai |
| Gemini CLI | ~/.gemini | gemini | google |
| Kimi CLI | ~/.kimi | kimi | moonshot |
| OpenCode | ~/.opencode | opencode | various |
| Cursor | ~/.cursor | cursor | various |
| Windsurf | ~/.codeium | windsurf | codeium |
| Aider | ~/.aider | aider | various |
| Goose | ~/.config/goose | goose | various |
| Amp | ~/.config/amp | amp | sourcegraph |
| Droid | ~/.factory | droid | factory |
| Kiro | ~/.kiro | kiro-cli | aws |
| Copilot CLI | ~/.copilot | copilot | github |
| Cody | ~/.config/sourcegraph | cody | sourcegraph |

For each: check if config directory exists AND/OR if binary is on PATH (use `which`/`where`).

**Output:**

```
AI Tool Probe

Tool           Binary  Config  Provider
─────────────  ──────  ──────  ──────────
Claude Code    yes     yes     anthropic
Codex CLI      yes     yes     openai
OpenCode       yes     yes     various
Gemini CLI     yes     yes     google
Cursor         yes     no      various

5 detected, 9 not found
```

---

## Subcommand: `report`

Generate an HTML usage report.

**Steps:**

1. Collect all available data (same as `stats` + `daily` + `models`)
2. Generate a self-contained HTML file at `~/.agentic-commons/report.html`
3. Include: daily chart, model breakdown table, source summary
4. Open in browser

---

## Notes for AI Agents

- All data is LOCAL. No API calls needed for `stats`, `daily`, `models`, `total`, `probe`, `doctor`.
- Only `sync`, `link`, and `setup` perform network/system operations.
- Token formatting: use `K` for thousands, `M` for millions (e.g., `130.0K`, `1.5M`).
- The `total_io` field equals `input_uncached + output` — it does NOT include cached tokens.
- When reading JSON files, always handle missing/malformed files gracefully.
- Refer to `references/data-sources.md` for detailed data format documentation.
