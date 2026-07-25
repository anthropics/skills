---
name: "remember"
description: "Explicitly save important knowledge to auto-memory with timestamp and context. Use when a discovery is too important to rely on auto-capture."
---

# /si:remember — Save Knowledge Explicitly

Writes an explicit entry to auto-memory when something is important enough that you don't want to rely on Claude noticing it automatically.

## Usage

```
/si:remember <what to remember>
/si:remember "This project's CI requires Node 20 LTS — v22 breaks the build"
/si:remember "The /api/auth endpoint uses a custom JWT library, not passport"
/si:remember "Reza prefers explicit error handling over try-catch-all patterns"
```

## When to Use

| Situation | Example |
|-----------|---------|
| Hard-won debugging insight | "CORS errors on /api/upload are caused by the CDN, not the backend" |
| Project convention not in CLAUDE.md | "We use barrel exports in src/components/" |
| Tool-specific gotcha | "Jest needs `--forceExit` flag or it hangs on DB tests" |
| Architecture decision | "We chose Drizzle over Prisma for type-safe SQL" |
| Preference you want Claude to learn | "Don't add comments explaining obvious code" |

## Workflow

### Step 1: Parse the knowledge

Extract from the user's input:
- **What**: The concrete fact or pattern
- **Why it matters**: Context (if provided)
- **Scope**: Project-specific or global?

### Step 2: Check for duplicates

```bash
MEMORY_DIR="$HOME/.claude/projects/$(pwd | sed 's|/|%2F|g; s|%2F|/|; s|^/||')/memory"
grep -ni "<keywords>" "$MEMORY_DIR/MEMORY.md" 2>/dev/null
```

If a similar entry exists:
- Show it to the user
- Ask: "Update the existing entry or add a new one?"

### Step 3: Write to MEMORY.md

Append to the end of `MEMORY.md`:

```markdown
- {{concise fact or pattern}}
```

Keep entries concise — one line when possible. Auto-memory entries don't need timestamps, IDs, or metadata. They're notes, not database records.

If MEMORY.md is over 180 lines, warn the user:

```
⚠️ MEMORY.md is at {{n}}/200 lines. Consider running /si:memory-review to free space.
```

### Step 4: Suggest promotion

If the knowledge sounds like a rule (imperative, always/never, convention):

```
💡 This sounds like it could be a CLAUDE.md rule rather than a memory entry.
   Rules are enforced with higher priority. Want to /si:promote it instead?
```

### Step 5: Confirm

```
✅ Saved to auto-memory

  "{{entry}}"

  MEMORY.md: {{n}}/200 lines
  Claude will see this at the start of every session in this project.
```

## What NOT to use /si:remember for

- **Temporary context**: Use session memory or just tell Claude in conversation
- **Enforced rules**: Use `/si:promote` to write directly to CLAUDE.md
- **Cross-project knowledge**: Use `~/.claude/CLAUDE.md` for global rules
- **Sensitive data**: Never store credentials, tokens, or secrets in memory files

## Tips

- Be concise — one line beats a paragraph
- Include the concrete command or value, not just the concept
  - ✅ "Build with `pnpm build`, tests with `pnpm test:e2e`"
  - ❌ "The project uses pnpm for building and testing"
- If you're remembering the same thing twice, promote it to CLAUDE.md
