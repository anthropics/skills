---
name: ai-native-cli
description: >
  AI-Native CLI design spec. Use when building CLI tools, designing
  command-line interfaces, or scaffolding new CLI projects. Covers
  structured JSON output, error handling, input contracts, safety
  guardrails, exit codes, and agent self-description. Includes an
  audit protocol for verifying CLI compliance.
license: MIT
metadata:
  author: zhuanz
  version: "0.1.0"
---

# Agent-Friendly CLI Spec v0.1

When building or modifying CLI tools, follow these rules to make them safe and
reliable for AI agents to use.

## Core Philosophy

1. **Agent-first** -- default output is JSON; human-friendly is opt-in via `--human`
2. **Agent is untrusted** -- validate all input at the same level as a public API
3. **Fail-Closed** -- when validation logic itself errors, deny by default
4. **Verifiable** -- every rule is written so it can be automatically checked

## Layer Model

This spec now uses two orthogonal axes:

- **Layer** answers rollout scope: `core`, `recommended`, `ecosystem`
- **Priority** answers severity: `P0`, `P1`, `P2`

Use layers for migration and certification:

- **core** -- execution contract: JSON, errors, exit codes, stdout/stderr, safety
- **recommended** -- better machine UX: self-description, explicit modes, richer schemas
- **ecosystem** -- agent-native integration: `agent/`, `skills`, `issue`, inline context

Certification maps to layers:

- **Agent-Friendly** -- all `core` rules pass
- **Agent-Ready** -- all `core` + `recommended` rules pass
- **Agent-Native** -- all layers pass

## Output Mode

Default is agent mode (JSON). Explicit flags to switch:

```bash
$ mycli list              # default = JSON output (agent mode)
$ mycli list --human      # human-friendly: colored, tables, formatted
$ mycli list --agent      # explicit agent mode (override config if needed)
```

- **Default (no flag)** — JSON to stdout. Agent never needs to add a flag.
- **--human** — human-friendly format (colors, tables, progress bars)
- **--agent** — explicit JSON mode (useful when env/config overrides default)

## agent/ Directory Convention

Every CLI tool MUST have an `agent/` directory at its project root. This is the
tool's identity and behavior contract for AI agents.

```
agent/
├── brief.md          # One paragraph: who am I, what can I do
├── rules/            # Behavior constraints (auto-registered)
│   ├── trigger.md    # When should an agent use this tool
│   ├── workflow.md   # Step-by-step usage flow
│   └── writeback.md  # How to write feedback back
└── skills/           # Extended capabilities (auto-registered)
    └── getting-started.md
```

### File Format

**agent/brief.md** — plain text, one paragraph. No frontmatter needed.

**agent/rules/*.md** — each file MUST have YAML frontmatter:

```yaml
---
name: trigger
description: When should an agent use this tool
---
(content here)
```

**agent/skills/*.md** — each file MUST have YAML frontmatter:

```yaml
---
name: getting-started
description: Quick start guide for new users
---
(content here)
```

The `name` field is the canonical identifier. The `description` field tells agents
when/why to read this rule or skill.

### Auto-Registration

Drop a `.md` file into `agent/rules/` or `agent/skills/` and it is automatically
registered. The CLI reads these directories at runtime. No code changes needed.

## Four Levels of Self-Description

### Level 1: --brief (business card, injected into agent config)

The smallest possible context. Output of `--brief` gets synced into CLAUDE.md /
AGENTS.md by `cli-toolkit sync-agent`, so agents always know this tool exists.

```bash
$ mycli --brief
mycli — task manager, add/list/show/done for local tasks
```

Source: `agent/brief.md`. Just one paragraph. Always in agent's system prompt.

### Level 2: Every Command Response (always-on context)

EVERY command's JSON output MUST include three fixed fields:

```json
{
  "result": { "id": 1, "title": "Buy milk", "status": "todo" },

  "rules": [
    {"name": "trigger",   "content": "full content of trigger.md"},
    {"name": "workflow",  "content": "full content of workflow.md"},
    {"name": "writeback", "content": "full content of writeback.md"}
  ],
  "skills": [
    {"name": "getting-started", "description": "Quick start guide", "command": "mycli skills getting-started"},
    {"name": "batch-import",    "description": "Import from CSV",   "command": "mycli skills batch-import"}
  ],
  "issue": "Any problem, bad output, or confusion — run: mycli issue create --type <bug|requirement|suggestion|bad-output> --message '...'"
}
```

- **rules** — full `.md` content inline (push: agent must know)
- **skills** — name + description + command (pull: agent reads on demand)
- **issue** — one-line guide, always present (fallback: can't figure it out? report it)

These three fields form a closed loop:
  rules tell you how -> skills teach you more -> issue catches what you can't handle

### Level 3: --help (full self-description)

Complete identity + capabilities. Only called for deep exploration.

```json
{
  "help": "mycli — full description from agent/brief.md",
  "commands": [
    {"name": "add",  "description": "Create a new task"},
    {"name": "list", "description": "List all tasks"},
    {"name": "done", "description": "Mark task as done (destructive)"}
  ],
  "rules": [
    {"name": "trigger",   "content": "..."},
    {"name": "workflow",  "content": "..."},
    {"name": "writeback", "content": "..."}
  ],
  "skills": [
    {"name": "getting-started", "description": "Quick start guide", "command": "mycli skills getting-started"}
  ],
  "issue": "Any problem — run: mycli issue create ..."
}
```

### Level 4: skills <name> (on-demand deep dive)

```bash
$ mycli skills getting-started
{
  "name": "getting-started",
  "content": "full content of getting-started.md",
  "rules": [ ... same rules for context ... ]
}
```

### Summary: Information Architecture

```
--brief              → always in agent's prompt (via sync-agent)
every command        → data + rules + skills list + issue (always attached)
--help               → brief + commands + rules + skills + issue (first contact)
skills <name>        → full skill content + rules (on demand)
```

## Certification Requirements

Each level includes all rules from the previous level.
Priority tag `[P0]`=agent breaks without it, `[P1]`=agent works but poorly, `[P2]`=nice to have.

### Level 1: Agent-Friendly (core — 20 rules)

Goal: CLI is a stable, callable API. Agent can invoke, parse, and handle errors.

**Output** — default is JSON, stable schema
- `[P0]` O1: Default output is JSON. No `--json` flag needed
- `[P0]` O2: JSON MUST pass `jq .` validation
- `[P0]` O3: JSON schema MUST NOT change within same version

**Error** — structured, to stderr, never interactive
- `[P0]` E1: Errors → `{"error":true, "code":"...", "message":"...", "suggestion":"..."}` to stderr
- `[P0]` E4: Error has machine-readable `code` (e.g. `MISSING_REQUIRED`)
- `[P0]` E5: Error has human-readable `message`
- `[P0]` E7: On error, NEVER enter interactive mode — exit immediately
- `[P0]` E8: Error codes are API contracts — MUST NOT rename across versions

**Exit Code** — predictable failure signals
- `[P0]` X3: Parameter/usage errors MUST exit 2
- `[P0]` X9: Failures MUST exit non-zero — never exit 0 then report error in stdout

**Composability** — clean pipe semantics
- `[P0]` C1: stdout is for data ONLY
- `[P0]` C2: logs, progress, warnings go to stderr ONLY

**Input** — fail fast on bad input
- `[P1]` I4: Missing required param → structured error, never interactive prompt
- `[P1]` I5: Type mismatch → exit 2 + structured error

**Safety** — protect against agent mistakes
- `[P1]` S1: Destructive ops require `--yes` confirmation
- `[P1]` S4: Reject `../../` path traversal, control chars

**Guardrails** — runtime input protection
- `[P1]` G1: Unknown flags rejected with exit 2
- `[P1]` G2: Detect API key / token patterns in args, reject execution
- `[P1]` G3: Reject sensitive file paths (*.env, *.key, *.pem)
- `[P1]` G8: Reject shell metacharacters in arguments (; | && $())

### Level 2: Agent-Ready (+ recommended — 59 rules)

Goal: CLI is self-describing, well-named, and pipe-friendly. Agent discovers capabilities and chains commands without trial and error.

**Self-Description** — agent discovers what CLI can do
- `[P1]` D1: `--help` outputs structured JSON with `commands[]`
- `[P1]` D3: Schema has required fields (help, commands)
- `[P1]` D4: All parameters have type declarations
- `[P1]` D7: Parameters annotated as required/optional
- `[P1]` D9: Every command has a description
- `[P1]` D11: `--help` outputs JSON with help, rules, skills, commands
- `[P1]` D15: `--brief` outputs `agent/brief.md` content
- `[P1]` D16: Default JSON (agent mode), `--human` for human-friendly
- `[P2]` D2/D5/D6/D8/D10: per-command help, enums, defaults, output schema, version

**Input** — unambiguous calling convention
- `[P1]` I1: All flags use `--long-name` format
- `[P1]` I2: No positional argument ambiguity
- `[P2]` I3/I6/I7: --json-input, boolean --no-X, array params

**Error**
- `[P1]` E6: Error includes `suggestion` field
- `[P2]` E2/E3: errors to stderr, error JSON valid

**Safety**
- `[P1]` S8: `--sanitize` flag for external input
- `[P2]` S2/S3/S5/S6/S7: default deny, --dry-run, no auto-update, destructive marking

**Exit Code**
- `[P1]` X1: 0 = success
- `[P2]` X2/X4-X8: 1=general, 10=auth, 11=permission, 20=not-found, 30=conflict

**Composability**
- `[P1]` C6: No interactive prompts in pipe mode
- `[P2]` C3/C4/C5/C7: pipe-friendly, --quiet, pipe chain, idempotency

**Naming** — predictable flag conventions
- `[P1]` N4: Reserved flags (--agent, --human, --brief, --help, --version, --yes, --dry-run, --quiet, --fields)
- `[P2]` N1/N2/N3/N5/N6: consistent naming, kebab-case, max 3 levels, --version semver

**Guardrails**
- `[P1]` I8/I9: no implicit state, non-interactive auth
- `[P1]` G6/G9: precondition checks, fail-closed
- `[P2]` G4/G5/G7: permission levels, PII redaction, batch limits

#### Reserved Flags

| Flag | Semantics | Notes |
|------|-----------|-------|
| `--agent` | JSON output (default) | Explicit override |
| `--human` | Human-friendly output | Colors, tables, formatted |
| `--brief` | One-paragraph identity | For sync into agent config |
| `--help` | Full self-description JSON | Brief + commands + rules + skills + issue |
| `--version` | Semver version string | |
| `--yes` | Confirm destructive ops | Required for delete/destroy |
| `--dry-run` | Preview without executing | |
| `--quiet` | Suppress stderr output | |
| `--fields` | Filter output fields | Save tokens |

### Level 3: Agent-Native (+ ecosystem — 19 rules)

Goal: CLI has identity, behavior contract, skill system, and feedback loop. Agent can learn the tool, extend its use, and report problems — full closed-loop collaboration.

**Agent Directory** — tool identity and behavior contract
- `[P1]` D12: `agent/brief.md` exists
- `[P1]` D13: `agent/rules/` has trigger.md, workflow.md, writeback.md
- `[P1]` D17: agent/rules/*.md have YAML frontmatter (name, description)
- `[P1]` D18: agent/skills/*.md have YAML frontmatter (name, description)
- `[P2]` D14: `agent/skills/` directory + `skills` subcommand

**Response Structure** — inline context on every call
- `[P1]` R1: Every response includes `rules[]` (full content from agent/rules/)
- `[P1]` R2: Every response includes `skills[]` (name + description + command)
- `[P1]` R3: Every response includes `issue` (feedback guide)

**Meta** — project-level integration
- `[P2]` M1: AGENTS.md at project root
- `[P2]` M2: Optional MCP tool schema export
- `[P2]` M3: CHANGELOG.md marks breaking changes

**Feedback** — built-in issue system
- `[P2]` F1: `issue` subcommand (create/list/show)
- `[P2]` F2: Structured submission with version/context/exit_code
- `[P2]` F3: Categories: bug / requirement / suggestion / bad-output
- `[P2]` F4: Issues stored locally, no external service dependency
- `[P2]` F5: `issue list` / `issue show <id>` queryable
- `[P2]` F6: Issues have status tracking (open/in-progress/resolved/closed)
- `[P2]` F7: Issue JSON has all required fields (id, type, status, message, created_at, updated_at)
- `[P2]` F8: All issues have status field

## Exit Code Table

```
0   success         10  auth failed       20  resource not found
1   general error   11  permission denied 30  conflict/precondition
2   param/usage error
```

## Error Format

```json
{
  "error": true,
  "code": "AUTH_EXPIRED",
  "message": "Access token expired 2 hours ago",
  "suggestion": "Run 'mycli auth refresh' to get a new token"
}
```

## Quick Implementation Checklist

Implement by layer — each phase gets you the next certification level.

**Phase 1: Agent-Friendly (core)**
1. Default output is JSON — no `--json` flag needed
2. Error handler: `{ error, code, message, suggestion }` to stderr
3. Exit codes: 0 success, 2 param error, 1 general
4. stdout = data only, stderr = logs only
5. Missing param → structured error (never interactive)
6. `--yes` guard on destructive operations
7. Guardrails: reject secrets, path traversal, shell metacharacters

**Phase 2: Agent-Ready (+ recommended)**
8. `--help` returns structured JSON (help, commands[], rules[], skills[])
9. `--brief` reads and outputs `agent/brief.md` content
10. `--human` flag switches to human-friendly format
11. Reserved flags: --agent, --version, --dry-run, --quiet, --fields
12. Exit codes: 20 not found, 30 conflict, 10 auth, 11 permission

**Phase 3: Agent-Native (+ ecosystem)**
13. Create `agent/` directory: `brief.md`, `rules/trigger.md`, `rules/workflow.md`, `rules/writeback.md`
14. Every command response appends: rules[] + skills[] + issue
15. `skills` subcommand: list all / show one with full content
16. `issue` subcommand for feedback (create/list/show/close/transition)
17. AGENTS.md at project root

## Issue System Specification

Every CLI tool MUST have a built-in issue system for agents to report problems,
request features, and track feedback.

### Storage

Issues are stored in a dedicated directory:

```
~/.{toolname}/issues/       # or {TOOL_DIR}/issues/
├── 001.json
├── 002.json
└── 003.json
```

Each issue is a single JSON file named `{id}.json`.

### Issue Fields

```json
{
  "id": "001",
  "type": "bug",
  "status": "open",
  "message": "list command returns empty when tasks exist",
  "context": {
    "version": "0.1.0",
    "command": "mycli list --json",
    "exit_code": 0
  },
  "created_at": "2026-03-14T00:00:00Z",
  "updated_at": "2026-03-14T00:00:00Z"
}
```

Required fields:
- **id** — unique identifier
- **type** — one of: `bug`, `requirement`, `suggestion`, `bad-output`
- **status** — one of: `open`, `in-progress`, `resolved`, `closed`
- **message** — description of the issue
- **context** — object with `version`, `command`, `exit_code`
- **created_at** — ISO 8601 timestamp
- **updated_at** — ISO 8601 timestamp

### State Management

| Command | Description |
|---------|-------------|
| `issue create --type <type> --message <msg>` | Create a new issue |
| `issue list [--type <type>] [--status <status>]` | List issues, filterable |
| `issue show <id>` | Show single issue detail |
| `issue close <id>` | Close an issue |
| `issue transition <id> --status <status>` | Change issue status |

### Queryable

Issues MUST be filterable by `--type` and `--status`:

```bash
$ mycli issue list --type bug --status open
$ mycli issue list --status resolved
