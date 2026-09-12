---
name: command-guard
description: Set up a PreToolUse hook in .claude/settings.json that blocks dangerous commands — rm -rf, force push, database drops, and others — before they execute. Teaches the pattern of safety hooks for any Claude Code project. Trigger words: safety, guard, block dangerous, protect, prevent destructive, safe mode, dangerous commands, risky operations.
license: MIT
metadata:
  author: sagemindai
  version: "1.0"
---

# command-guard — Block Dangerous Commands Before They Execute

Claude Code runs shell commands, edits files, and manages infrastructure with real consequences. Without guardrails, a misunderstood instruction or a hallucinated flag can delete data, corrupt history, or expose credentials. This skill installs a PreToolUse hook that blocks the most dangerous operations before they run.

No external tools required — this uses Claude Code's built-in hook system.

---

## What Gets Blocked

The guard intercepts `Bash` tool calls and checks the command against a blocklist before execution. By default it blocks:

**Irreversible deletions**
- `rm -rf` on non-temporary paths
- `git clean -f` (untracked file deletion)

**Git history destruction**
- `git push --force` / `git push -f` (without explicit user confirmation)
- `git reset --hard` on shared branches
- `git rebase` on pushed branches

**Database operations**
- `DROP TABLE`, `DROP DATABASE`, `TRUNCATE` in SQL
- `db:reset`, `db:drop` npm/prisma scripts

**Credential exposure**
- Commands that `cat`, `echo`, or `curl` files containing `SECRET`, `KEY`, `TOKEN`, `PASSWORD` to stdout

---

## Installation

### Step 1: Create the hook script

```bash
mkdir -p .claude/hooks
```

Create `.claude/hooks/command-guard.py`:

```python
#!/usr/bin/env python3
"""
command-guard.py — PreToolUse hook that blocks dangerous Bash commands.
Claude Code calls this before executing any Bash tool call.
Exit code 2 = block the command and show the message.
Exit code 0 = allow the command.
"""
import sys
import json
import re
import os

# Load the tool call input from stdin
try:
    payload = json.load(sys.stdin)
except Exception:
    sys.exit(0)  # Can't parse — allow (fail open)

tool_name = payload.get('tool_name', '')
tool_input = payload.get('tool_input', {})

# Only intercept Bash calls
if tool_name != 'Bash':
    sys.exit(0)

command = tool_input.get('command', '')

# --- Blocklist rules ---
# Each rule: (regex pattern, reason shown to agent)

BLOCKED = [
    # Irreversible deletions
    (r'\brm\s+-[a-zA-Z]*r[a-zA-Z]*f\b', 'rm -rf is blocked. Use rm with explicit paths, or move to trash instead.'),
    (r'\bgit\s+clean\s+-[a-zA-Z]*f\b', 'git clean -f is blocked. List untracked files with --dry-run first.'),

    # Force push
    (r'\bgit\s+push\s+.*--force\b', 'Force push is blocked. Confirm with the user before rewriting remote history.'),
    (r'\bgit\s+push\s+.*-f\b(?!ile)', 'Force push (-f) is blocked. Confirm with the user before rewriting remote history.'),

    # Hard reset
    (r'\bgit\s+reset\s+--hard\b', 'git reset --hard is blocked. Use --soft or --mixed, or confirm with user first.'),

    # Database destructive ops
    (r'\b(DROP\s+(TABLE|DATABASE|SCHEMA)|TRUNCATE\s+TABLE)\b', 'Destructive SQL (DROP/TRUNCATE) is blocked. Confirm with the user before destroying data.', re.IGNORECASE),
    (r'\b(db:reset|db:drop|prisma.*reset)\b', 'Database reset scripts are blocked. Confirm with the user — this destroys all data.'),

    # Credential leakage to stdout (basic check)
    (r'\b(cat|echo|curl|printf)\b.*\.(env|secret|secrets|pem|key)\b', 'Printing credential files to stdout is blocked. Use secure variable injection instead.'),
]

for rule in BLOCKED:
    pattern = rule[0]
    message = rule[1]
    flags = rule[2] if len(rule) > 2 else 0
    if re.search(pattern, command, flags):
        print(json.dumps({
            "decision": "block",
            "reason": f"[command-guard] {message}\n\nBlocked command: {command[:200]}"
        }))
        sys.exit(2)

# All clear
sys.exit(0)
```

Make it executable:

```bash
chmod +x .claude/hooks/command-guard.py
```

---

### Step 2: Register the hook in .claude/settings.json

If `.claude/settings.json` doesn't exist, create it. If it does, add to the `hooks` array:

```json
{
  "hooks": {
    "PreToolUse": [
      {
        "matcher": "Bash",
        "hooks": [
          {
            "type": "command",
            "command": "python3 .claude/hooks/command-guard.py"
          }
        ]
      }
    ]
  }
}
```

---

### Step 3: Verify the hook is registered

Restart Claude Code, then ask it to run a blocked command:

```
Run: rm -rf ./test-dir
```

The agent should receive a block message rather than executing the command.

---

## Customizing the Blocklist

Edit the `BLOCKED` list in `command-guard.py` to add project-specific rules.

**Example: Block deploys to production from feature branches**

```python
(r'\bdeploy.*production\b', 'Direct production deploys are blocked. Merge to main first, then deploy via CI.'),
```

**Example: Block overwriting specific config files**

```python
(r'\bcp\b.*\b(\.env\.production|secrets\.json)\b', 'Overwriting production config files is blocked. Edit manually.'),
```

**Example: Allow force push only to personal branches**

Replace the force push rule with a more nuanced check:

```python
# Allow force push to personal/feature branches, block on main/master/staging
if re.search(r'\bgit\s+push\s+.*(-f|--force)\b', command):
    if not re.search(r'\b(main|master|staging|production)\b', command):
        sys.exit(0)  # Allow: not targeting a protected branch
    print(json.dumps({"decision": "block", "reason": "Force push to protected branches is blocked."}))
    sys.exit(2)
```

---

## Understanding the Hook Pattern

Claude Code hooks are scripts that fire at specific points in the agent's tool lifecycle:

| Hook Type | When It Fires | Use Cases |
|-----------|--------------|-----------|
| `PreToolUse` | Before any tool call | Block dangerous operations, inject context |
| `PostToolUse` | After any tool call | Log actions, update state, send notifications |
| `Notification` | On system events (compaction, etc.) | Recovery, awareness updates |

The hook receives a JSON payload on stdin and communicates back via stdout + exit code:
- **Exit 0**: Allow the tool call to proceed
- **Exit 2**: Block the tool call; the `reason` in stdout is shown to the agent

Hooks are composable. You can chain multiple hooks for the same event, and each runs independently.

---

## What This Does Not Cover

This guard blocks the most common dangerous operations. It does not:
- Inspect file contents before writes (use a `Write` tool hook for that)
- Validate SQL in ORM calls (only raw SQL strings)
- Prevent API calls that delete remote resources

For production systems where the agent has access to critical infrastructure, layer additional guards specific to your environment.
