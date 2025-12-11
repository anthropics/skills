---
name: codex-cli
description: Run Codex from a process, capture output cleanly, and select the right model and sandbox policy. Updated 2025-11-23.
---

# Codex CLI — Run & Capture + Model/Sandbox Guide

## References (skim first)
- Use codex for plans and code reviews
- Plans and reviews should be done with `--sandbox read-only`
- The model is set by the user so do not try to change
- Most tasks should be done using exec
- Codex CLI documentation — Check `codex --help` for latest options
- GitHub repo (if open-source) — github.com/anthropics/codex 


---

## Quick start
```bash
# Interactive (REPL-like)
codex "explain the repo layout"

# Non-interactive (script/CI)
codex exec "generate unit tests for src/utils.py"
```

## Capture patterns
```bash
# Redirect output to file
codex exec "summarize README.md" > out.txt


## Sandbox & Approval Policies

### Sandbox modes (`-s`, `--sandbox`)
Control what file system access is allowed:
- **`read-only`** — Only read files, no writes
- **`workspace-write`** — Allow writes within workspace directory
- **`danger-full-access`** — Full file system access (dangerous)

### Approval policies (`-a`, `--ask-for-approval`)
Control when to ask for approval before executing commands:
- **`untrusted`** — Only run trusted commands (ls, cat, sed) without approval
- **`on-failure`** — Run all commands, ask only if execution fails
- **`on-request`** — Let the model decide when to ask
- **`never`** — Never ask for approval (dangerous)

### Quick combinations
```bash
# Safe automatic execution (workspace writes, model decides approvals)
codex --full-auto "refactor the auth module"

# Equivalent to:
codex -a on-request --sandbox workspace-write "refactor the auth module"

# DANGEROUS: Skip all approvals and sandbox (externally sandboxed environments only)
codex --dangerously-bypass-approvals-and-sandbox "your prompt"
```

### Set defaults
```toml
# ~/.codex/config.toml
sandbox_mode = "workspace-write"
approval_policy = "untrusted"
```

---

## Additional Options

### Configuration override
```bash
# Override config values at runtime using -c flag
# Use dotted paths for nested values; values parsed as TOML
codex -c 'sandbox_permissions=["disk-full-read-access"]' "your prompt"
codex -c shell_environment_policy.inherit=all "your prompt"
```

### Working directory
```bash
# Specify working directory
codex -C /path/to/project "analyze the code"

# Add additional writable directories
codex --add-dir /other/path "your prompt"
```

### Web search
```bash
# Enable web search (off by default)
codex --search "find latest best practices for React 19"
```

### Images
```bash
# Attach images to initial prompt
codex -i screenshot.png "explain this UI"
codex -i image1.png -i image2.png "compare these diagrams"
```

### Profiles
```bash
# Use configuration profile from config.toml
codex -p my-profile "your prompt"
```

---

## CI/Scripting Usage
```bash
# Non-interactive execution
codex exec "generate unit tests for src/utils.py"

# Specify working directory and model
codex -C /path/to/repo -m opus exec "analyze security issues"

# With sandbox and approval settings
codex --sandbox read-only -a never exec "list all TODO comments"
```

## Cloud Features (Experimental)
```bash
# Browse and apply changes from Codex Cloud
codex cloud
```

## MCP Server (Experimental)
```bash
# Run as MCP server
codex mcp-server

# Manage MCP servers
codex mcp [subcommand]
```
