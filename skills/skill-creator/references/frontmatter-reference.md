# Frontmatter Reference

Complete reference for SKILL.md frontmatter fields.

## Field Reference

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `name` | string | Directory name | Display name (max 64 chars, lowercase + hyphens only) |
| `description` | string | First paragraph | What the skill does and when to use it (max 1024 chars) |
| `argument-hint` | string | None | Hint shown during autocomplete (e.g., `[issue-number]`) |
| `disable-model-invocation` | boolean | `false` | `true` = only user can invoke via `/name` |
| `user-invocable` | boolean | `true` | `false` = hide from `/` menu (Claude-only) |
| `allowed-tools` | string | All tools | Comma-separated list of allowed tools |
| `model` | string | Inherited | Model override when skill is active |
| `context` | string | Inline | `fork` = run in isolated subagent |
| `agent` | string | `general-purpose` | Subagent type when `context: fork` |
| `hooks` | object | None | Scoped hooks for skill lifecycle |

## Invocation Control Matrix

| Frontmatter | User `/name` | Claude auto-invoke | Description visible |
|-------------|--------------|-------------------|---------------------|
| (default) | Yes | Yes | Yes |
| `disable-model-invocation: true` | Yes | No | No |
| `user-invocable: false` | No | Yes | Yes |
| Both set | No | No | No (skill disabled) |

### Use Cases

**`disable-model-invocation: true`**
- Deploy scripts
- Git commit workflows
- Sending messages/notifications
- Any workflow with side effects

**`user-invocable: false`**
- Background knowledge (legacy system context)
- API patterns Claude should follow
- Style guidelines
- Domain knowledge that isn't a command

## String Substitutions

| Variable | Description | Example |
|----------|-------------|---------|
| `$ARGUMENTS` | Arguments passed after `/skill-name` | `/fix-issue 123` → `$ARGUMENTS` = `123` |
| `${CLAUDE_SESSION_ID}` | Current session ID | `logs/${CLAUDE_SESSION_ID}.log` |

**Auto-append behavior:** If `$ARGUMENTS` is not present in skill content, arguments are appended as:
```
ARGUMENTS: <user input>
```

## Dynamic Context Injection

Shell commands can be executed before the skill content reaches Claude using the exclamation-backtick syntax.

**Syntax:** exclamation mark followed by backtick-wrapped command: `EXCLAIM` + `BACKTICK command BACKTICK`

**Example skill content:**

```
## Current PR
- Diff: EXCLAIM-BACKTICK gh pr diff BACKTICK
- Comments: EXCLAIM-BACKTICK gh pr view --comments BACKTICK

Based on the above, summarize this PR...
```

(Replace EXCLAIM with the exclamation mark character and BACKTICK with the backtick character in real skills)

**Execution order:**
1. All exclamation-backtick placeholders execute
2. Output replaces each placeholder
3. Fully-rendered content sent to Claude

**Note:** This is preprocessing, not Claude execution. Claude only sees results.

## Subagent Execution

When `context: fork` is set, the skill runs in an isolated subagent:

```yaml
---
name: deep-research
context: fork
agent: Explore
---

Research $ARGUMENTS thoroughly...
```

### Agent Types

| Agent | Tools Available | Use Case |
|-------|-----------------|----------|
| `Explore` | Glob, Grep, Read, WebFetch | Read-only codebase exploration |
| `Plan` | Glob, Grep, Read, WebFetch | Architecture planning |
| `general-purpose` | All tools | Full capabilities (default) |
| Custom | Defined in `.claude/agents/` | Custom agent configurations |

### Skill-Subagent Relationship

| Approach | System Prompt | Task | Loaded Content |
|----------|---------------|------|----------------|
| Skill with `context: fork` | From agent type | SKILL.md content | CLAUDE.md |
| Subagent with `skills` field | Subagent's markdown | Delegation message | Preloaded skills + CLAUDE.md |

## Tool Restrictions

The `allowed-tools` field restricts which tools Claude can use:

```yaml
allowed-tools: Read, Grep, Glob
```

### Tool Permission Syntax

| Syntax | Meaning |
|--------|---------|
| `Read` | Exact tool match |
| `Bash(git:*)` | Bash with git prefix |
| `Bash(npm:*)` | Bash with npm prefix |
| `Read, Grep` | Multiple tools |

## Examples

### Deploy Skill (User-Only)

```yaml
---
name: deploy
description: Deploy the application to production
disable-model-invocation: true
argument-hint: [environment]
allowed-tools: Bash(deploy:*), Read
---

Deploy to $ARGUMENTS environment:
1. Run tests
2. Build application
3. Push to target
```

### Research Skill (Subagent)

```yaml
---
name: deep-research
description: Research a topic thoroughly using codebase exploration
context: fork
agent: Explore
---

Research $ARGUMENTS:
1. Find relevant files with Glob and Grep
2. Read and analyze code
3. Summarize with file references
```

### Background Knowledge (Claude-Only)

```yaml
---
name: api-conventions
description: REST API conventions for this codebase
user-invocable: false
---

When writing API endpoints:
- Use RESTful naming
- Return consistent error formats
- Include request validation
```

### PR Summary with Dynamic Context

```yaml
---
name: pr-summary
description: Summarize the current pull request
context: fork
agent: Explore
allowed-tools: Bash(gh:*)
---

## PR Context
- Diff: EXCLAIM-BACKTICK gh pr diff BACKTICK
- Comments: EXCLAIM-BACKTICK gh pr view --comments BACKTICK
- Files: EXCLAIM-BACKTICK gh pr diff --name-only BACKTICK

Summarize this pull request focusing on:
1. What changed
2. Why it changed
3. Potential concerns
```

(Replace EXCLAIM with the exclamation mark character and BACKTICK with the backtick character in real skills)
