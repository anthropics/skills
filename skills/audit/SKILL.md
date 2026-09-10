---
name: audit
description: Generate a structured audit of Claude Code activity --tool invocations, bash commands, MCP calls, file operations, and security-relevant findings. Use when the user asks to audit a session, review what Claude did, check for risky commands, or get a daily activity summary.
license: Complete terms in LICENSE.txt
---

# Session Audit

Generate a comprehensive audit of Claude Code activity with security-relevant findings flagged.

> **Privacy Notice**: This skill processes local Claude Code transcript files which may contain sensitive data including user prompts, code, file contents, and tool parameters. Audit reports should be treated as confidential and not shared externally without redaction review.

> **Compliance Disclaimer**: This skill is for personal session review and security hygiene. It is not a substitute for enterprise audit logging and does not meet SOC 2, HIPAA, or FedRAMP audit trail requirements.

## Quick Reference

| Command | What it does |
|---------|-------------|
| `session audit` | Audit current session from conversation history |
| `daily audit` | Audit all sessions today from transcript JSONL files |
| `/audit` | Same as daily audit (slash command) |
| `/audit session` | Same as session audit |

## Modes

### Mode 1: Current Session (`session audit`)
Scan the current conversation history and extract every tool call.

### Mode 2: Daily / Multi-Session (`daily audit`)
Parse transcript JSONL files from `~/.claude/projects/` to cover all sessions from today (or a specified date range).

**How to find today's transcripts (cross-platform):**
```bash
# Create a timestamp marker for start of today (works on macOS and Linux)
python3 -c "
from datetime import date; from pathlib import Path; import os, time
t = time.mktime(date.today().timetuple())
p = Path('/tmp/recap-today-marker')
p.touch()
os.utime(p, (t, t))
"
# Find all JSONL transcripts modified today (exclude subagent files)
find ~/.claude/projects -name "*.jsonl" -newer /tmp/recap-today-marker -not -path "*/subagents/*"
```

**How to extract tool calls from JSONL transcripts:**
```bash
python3 -c "
import json, sys, os
from datetime import date

target = date.today().isoformat()
MAX_SIZE = 100 * 1024 * 1024  # 100MB per file
files = sys.argv[1:]
tools = []
errors = 0
for f in files:
    if os.path.getsize(f) > MAX_SIZE:
        print(f'Skipping {f}: exceeds 100MB', file=sys.stderr)
        continue
    with open(f, errors='replace') as fh:
        for line in fh:
            try:
                entry = json.loads(line)
            except json.JSONDecodeError:
                errors += 1
                continue
            if entry.get('type') != 'assistant':
                continue
            ts = entry.get('timestamp', '')
            if not ts.startswith(target):
                continue
            msg = entry.get('message', {})
            for block in msg.get('content', []):
                if block.get('type') == 'tool_use':
                    tools.append({
                        'tool': block['name'],
                        'input': block.get('input', {}),
                        'time': ts,
                        'session': entry.get('sessionId', ''),
                        'cwd': entry.get('cwd', ''),
                    })
if errors:
    print(f'Skipped {errors} malformed JSON lines', file=sys.stderr)
print(json.dumps(tools, indent=2))
" "$(find ~/.claude/projects -name '*.jsonl' -newer /tmp/recap-today-marker -not -path '*/subagents/*' -print0 | xargs -0 echo)"
```

## Data Collection

For each tool call, extract and categorize:

### 1. Bash Commands
For every Bash tool invocation, record:
- The exact command string (first line, up to 150 chars)
- Working directory
- Risk classification (see Risk Classification Rules below)
- Classify risk based on **top-level shell commands only**. Content inside heredocs (`<< 'EOF'`), Python inline scripts (`python3 -c "..."`), and string arguments does not constitute a shell command.

### 2. MCP Tool Calls
For every MCP tool invocation (prefixed with `mcp__`), record:
- Server name and tool name
- Key parameters passed (apply redaction patterns before displaying)

### 3. Skills Invoked
For every Skill tool call, record:
- Skill name and any arguments

### 4. File Operations
For every Read, Write, Edit, Glob, Grep tool call, record:
- File path and operation type
- For writes/edits: summarize what changed (1 line)
- Flag writes to sensitive paths (see Sensitive Paths list below)

### 5. Agent Delegations
For every Agent tool call, record:
- Agent type, description, foreground/background, worktree isolation
- Prompt preview (first 150 chars)

### 6. Web Requests
For every WebFetch or WebSearch call, record:
- URL or query and purpose

## Risk Classification Rules

Classify risk based on **top-level shell commands only**.

| Risk Tag | Trigger Pattern | NOT a trigger (skip) |
|----------|----------------|---------------------|
| DESTRUCTIVE | `rm -rf`, `rm -r`, `git clean -f`, `unlink` as top-level command | `rm` inside heredoc/string, `mktemp` creation, content inside `python3 -c` |
| EXTERNAL_NETWORK | `curl`/`wget`/`scp`/`rsync` to non-localhost URLs | `localhost`, `127.0.0.1`, `0.0.0.0`, internal domains |
| DATA_EXFILTRATION | `curl -X POST -d @file`, `curl -F file=@`, `scp`/`rsync` outbound with file args, `nc` with piped input | `curl -s` GET requests, localhost POST |
| SECRET_LITERAL | Literal token in args: `sk-`, `ghp_`, `xoxb-`, `AKIA`, JWT (`eyJ...`) | Env var references like `$VAR`, `${VAR}` |
| API_KEY_SET | `export VAR=<literal>`, inline `KEY=value command` with literal secret | Reading/grepping/redacting key values, `sed 's/=.*/=***/'` |
| PKG_INSTALL | `pip3 install`, `npm install`, `brew install`, `cargo install` | `pip3 list`, `pip3 show`, `npm ls` |
| PROCESS_KILL | `kill`, `pkill`, `killall`, `xargs kill` | `pgrep` (read-only) |
| GIT_PUSH | `git push`, `git push --force` | `git pull`, `git fetch`, `git diff` |
| GIT_COMMIT | `git commit` | `git status`, `git log` |
| CHMOD | `chmod`, `chown` | --|
| SAFETY_BYPASS | `--dangerously`, `--no-verify`, `--force`, `--skip-permissions` | --|
| SENSITIVE_PATH | Commands accessing `~/.ssh`, `~/.aws`, `~/.gnupg`, `~/.kube`, `/etc/` | --|
| DYNAMIC_EXEC | `eval`, `exec`, `source`, `bash -c` with piped/substituted input, `curl \| bash` | `source ~/.bashrc` (known safe) |
| NETWORK_LISTENER | `nc -l`, `ncat -l`, `socat LISTEN`, `python3 -m http.server`, `php -S` | --|
| OBFUSCATED_EXEC | `base64 -d ... \| bash`, `base64 -d ... \| sh` | `base64` for encoding data (not piped to shell) |
| CREDENTIAL_WRITE | Writes to `.env`, `.netrc`, `.pgpass`, `.docker/config.json`, `.npmrc`, `.pypirc` | Reads of these files |
| DOCKER_PRIVILEGED | `docker run --privileged`, `docker run -v /:/host` | Normal `docker run` |
| CLOUD_METADATA | `curl http://169.254.169.254/`, `curl http://metadata.google.internal/` | --|

## Sensitive Paths

Flag file operations involving these paths:
- `~/.ssh`, `~/.aws`, `~/.gnupg`, `~/.kube`, `~/.docker/config.json`
- `.env`, `.netrc`, `.pgpass`, `.npmrc`, `.pypirc`, `.gem/credentials`
- `/etc/passwd`, `/etc/shadow`, `/etc/hosts`
- Any path containing `secret`, `token`, `password`, `credential`, `private_key`

## Known Safe Patterns (never flag these)

- `2>&1` — stderr merge, not a file write
- `> /dev/null` — output suppression
- `cat > "$tmpdir/..."` — writing to temp directory
- Content inside heredocs (`<< 'EOF' ... EOF`) — not top-level commands
- `env | grep KEY | sed 's/=.*/=***/'` — secret redaction, not exposure
- `python3 -c "..."` or `python3 << 'PYEOF'` — classify by the script's I/O, not string matches inside
- queryrunner scripts — read-only data queries
- `command --help 2>&1 | grep` — help text filtering
- `pgrep -f process` — read-only process check
- `source ~/.bashrc`, `source ~/.zshrc` — known safe shell init

## Redaction Patterns

Before displaying any command or parameter, apply these redaction rules. Replace matched values with `[REDACTED]`:

| Pattern | Description |
|---------|------------|
| `sk-[a-zA-Z0-9]{20,}` | OpenAI API key |
| `ghp_[a-zA-Z0-9]{36}` | GitHub PAT |
| `gho_[a-zA-Z0-9]{36}` | GitHub OAuth token |
| `xoxb-`, `xoxp-` | Slack tokens |
| `AKIA[A-Z0-9]{16}` | AWS Access Key ID |
| `eyJ[a-zA-Z0-9_-]+\.eyJ` | JWT token |
| Values after `--password`, `--token`, `-H "Authorization` | CLI secret args |
| Base64 blobs > 40 chars in command args | Possible encoded secrets |
| Values for keys named `password`, `token`, `secret`, `api_key`, `authorization`, `cookie` in MCP/tool params | Tool parameter secrets |

**Rule priority**: Redaction (this section) takes precedence over "show full command" (Rule 8). Always redact first, then display.

## Report Format

### Current Session Report
```
# Session Audit

**Duration**: [first tool call] -> [last tool call]
**Total tool calls**: N

## RISKY Commands (N of M bash commands)
| # | Time | Risk Tags | Full Command (redacted) | Directory |
|---|------|-----------|------------------------|-----------|
| 1 | 08:06 | DESTRUCTIVE | `rm -rf results/speed_v2/ && mini-extra swebench ...` | `~/project` |
| 2 | 23:39 | EXTERNAL_NETWORK, SECRET_LITERAL | `curl -s https://api.example.com -H "Authorization: Bearer [REDACTED]"` | `~` |

## SAFE Commands (N of M)
| Category | Count | Example |
|----------|-------|---------|
| process_check | 45 | `pgrep -fa cerberus` |
| python_script | 30 | `python3 src/analyze.py` |
| read_only | 25 | `ls`, `find`, `head` |
| status_check | 20 | `echo "Progress: ..."` |
| git_read | 10 | `git diff`, `git status` |
| benchmark | 8 | `mini-extra swebench ...` |
| lookup | 5 | `which`, `env | grep` |
| navigation | 5 | `cd`, `pwd` |
| file_mgmt | 3 | `mkdir`, `cp`, `mv` |
| open_app | 2 | `open file.html` |
| other | N | --|

## MCP Tools Used
| # | Server | Tool | Key Params |
|---|--------|------|------------|
| 1 | code-mcp | get_github_pull_request_diff | org=uber-code, repo=foo, #123 |

## Skills Invoked
| # | Time | Skill | Args |
|---|------|-------|------|
| 1 | 18:48 | queryrunner | --|

## Files Touched (N writes/edits of M total)
| Operation | Path | Count |
|-----------|------|-------|
| Edit | `src/app.ts` | 5 |
| Write | `~/.ssh/config` | 1 [!] |

## Web Activity
| # | Time | Type | Target |
|---|------|------|--------|
| 1 | 23:05 | WebSearch | `claude code security audit` |

## Agents Spawned
| # | Time | Type | Description | Mode | Prompt Preview |
|---|------|------|-------------|------|----------------|
| 1 | 08:27 | general | Search security tools | fg | `Search GitHub for open-source tools that test GUI-based AI agents...` |

## Summary
- N bash commands: X safe, Y risky
- N MCP calls across M servers
- N skills invoked
- N file operations (X writes/edits)
- N web requests
- N agents spawned
- N security flags
```

### Daily Report (multi-session)
For daily reports with many sessions, use a **condensed format**:

```
# Daily Audit -- YYYY-MM-DD

**Sessions**: N | **Total tool calls**: N

## Session Overview
| # | Directory | Time Range | Bash | Risky | Files | Agents | Flags |
|---|-----------|------------|------|-------|-------|--------|-------|
| 1 | ~/Desktop/speedbench | 07:24-09:48 | 65 | 5 | 30 | 2 | 3 |
| 2 | ~/Desktop/threat-tools | 01:12-04:45 | 28 | 3 | 42 | 1 | 2 |
| 3 | ~ | 21:29-23:40 | 82 | 12 | 20 | 15 | 8 |

## All Risky Commands (across all sessions)
| # | Time | Risk Tags | Full Command (redacted) | Session/Directory |
|---|------|-----------|------------------------|-------------------|
[all risky commands from all sessions, chronological]

## All Agents (across all sessions)
| # | Time | Type | Description | Mode | Prompt Preview |
|---|------|------|-------------|------|----------------|
[all agents from all sessions, chronological]

## Daily Totals
- N total bash commands: X safe, Y risky across Z sessions
- N MCP calls across M servers
- N skills invoked
- N file writes/edits
- N web requests
- N agents spawned
- Top risk tags: DESTRUCTIVE (5), KILL (12), PKG_INSTALL (2)
```

## Rules

1. **Be exhaustive** — every tool call must appear in the report. Do not skip or summarize groups.
2. **Redact first, display second** — apply Redaction Patterns before displaying any command or parameter. Replace matched values with `[REDACTED]` but still flag the command as risky.
3. **Classify risk by top-level command only** — do not flag content inside heredocs, inline scripts, or string arguments. Parse at the shell level.
4. **Use the Risk Classification Rules table** — match against the Trigger Pattern column. If a command matches a NOT-a-trigger pattern, skip it.
5. **Check Known Safe Patterns** — commands matching the Known Safe Patterns list are always safe regardless of substring matches.
6. **Chronological order** within each session.
7. **Counts must be accurate** — summary numbers must match the tables.
8. **ALWAYS show the original command** — every risky command row MUST include the full command (first line, up to 150 chars) in a code block, after redaction. The Risk Tags column is supplementary, never a replacement.
9. **Show agent prompt previews** — every agent row must include the first 150 chars of the prompt.
10. **If empty**, say "No tool activity recorded."
11. **For daily audit**, use the condensed per-session overview table. Only expand risky commands and agents in full.
12. **If writing to a file**, default to `~/.claude/audits/` and warn if the target is inside a git working tree.
