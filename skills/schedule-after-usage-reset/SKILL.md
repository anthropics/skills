---
name: schedule-after-usage-reset
description: Schedule a task to run after the Claude usage limit resets. Use this skill whenever the user says things like "schedule this after my usage resets", "run this when my tokens refresh", "queue this task for after the limit lifts", "do this when usage resets", or any variation of wanting to defer a task until after a Claude usage/token limit reset. This skill finds the reset time and calls /schedule with that exact time.
license: Complete terms in LICENSE.txt
compatibility: Requires Claude Code on macOS with the built-in schedule skill. Reads OAuth credentials from Keychain (Claude Code-credentials).
---

# Schedule After Usage Reset

Automatically find the usage reset time and call `/schedule` with it. No questions asked.

## Steps

### 1. Get the reset time

Fetch from the Anthropic usage API:

```bash
token_json=$(/usr/bin/security find-generic-password -s 'Claude Code-credentials' -w 2>/dev/null)
access_token=$(echo "$token_json" | python3 -c "import sys,json; d=json.load(sys.stdin); print(d.get('claudeAiOauth',{}).get('accessToken',''))")
curl -s -H "Authorization: Bearer $access_token" \
     -H "anthropic-beta: oauth-2025-04-20" \
     -H "User-Agent: claude-code/2.1" \
     "https://api.anthropic.com/api/oauth/usage"
```

Parse `five_hour.resets_at` (or `seven_day.resets_at`). Convert UTC → user's local timezone. Add 5 minutes as buffer.

If rate limited, wait 15s and retry once. If still failing, ask the user for the reset time.

### 2. Get the task

If not provided as an argument, ask: "What should I run after the reset?"

### 3. Call /schedule

Invoke the `schedule` skill, passing the task and the reset time + 5min buffer:

```
/schedule "<task>" at <HH:MM> <timezone>
```

The `schedule` skill handles everything from there — just like calling it directly.

## Example

**User**: "Schedule this after my usage resets: summarize the new PRs in my inbox"

**Behavior**: Fetch reset time from the usage API, add a 5-minute buffer, then invoke `/schedule` with the task and local time.
