---
name: "extract"
description: "Turn a proven pattern or debugging solution into a standalone reusable skill with SKILL.md, reference docs, and examples. Use when the user runs /si:extract or asks to package a recurring solution from memory into a skill."
---

# /si:extract — Create Skills from Patterns

Transforms a recurring pattern or debugging solution into a standalone, portable skill that can be installed in any project.

## Usage

```
/si:extract <pattern description>                  # Interactive extraction
/si:extract <pattern> --name docker-m1-fixes       # Specify skill name
/si:extract <pattern> --output ./skills/            # Custom output directory
/si:extract <pattern> --dry-run                     # Preview without creating files
```

## When to Extract

A learning qualifies for skill extraction when ANY of these are true:

| Criterion | Signal |
|---|---|
| **Recurring** | Same issue across 2+ projects |
| **Non-obvious** | Required real debugging to discover |
| **Broadly applicable** | Not tied to one specific codebase |
| **Complex solution** | Multi-step fix that's easy to forget |
| **User-flagged** | "Save this as a skill", "I want to reuse this" |

## Workflow

### Step 1: Identify the pattern

Read the user's description. Search auto-memory for related entries:

```bash
MEMORY_DIR="$HOME/.claude/projects/$(pwd | sed 's|/|%2F|g; s|%2F|/|; s|^/||')/memory"
grep -rni "<keywords>" "$MEMORY_DIR/"
```

If found in auto-memory, use those entries as source material. If not, use the user's description directly.

### Step 2: Determine skill scope

Ask (max 2 questions):
- "What problem does this solve?" (if not clear)
- "Should this include code examples?" (if applicable)

### Step 3: Generate skill name

Rules for naming:
- Lowercase, hyphens between words
- Descriptive but concise (2-4 words)
- Examples: `docker-m1-fixes`, `api-timeout-patterns`, `pnpm-workspace-setup`

**Reserved fragments — must NOT appear in the skill name:**
- `claude`
- `anthropic`

For skills about Claude Code itself, use the `cc-` prefix instead:
- ❌ `claude-code-settings` → ✅ `cc-settings`
- ❌ `claude-code-maintenance` → ✅ `cc-maintenance`
- ❌ `claude-mcp-tools` → ✅ `cc-mcp-tools`
- ❌ `claude-plugin-development` → ✅ `cc-plugin-development`

Before writing the skill directory, check the proposed name against this list.
If a reserved fragment is present, transform it (drop the fragment or replace
the `claude*`/`anthropic*` prefix with `cc-`) and confirm with the user.

### Step 4: Create the skill files

**Spawn the `skill-extractor` agent** for the actual file generation.

The agent creates:

```
<skill-name>/
├── SKILL.md            # Main skill file with frontmatter
├── README.md           # Human-readable overview
└── reference/          # (optional) Supporting documentation
    └── examples.md     # Concrete examples and edge cases
```

### Step 5: SKILL.md structure

The generated SKILL.md must follow this format:

```markdown
---
name: "skill-name"
description: "<one-line description>. Use when: <trigger conditions>."
---

# <Skill Title>

> One-line summary of what this skill solves.

## Quick Reference

| Problem | Solution |
|---------|----------|
| {{problem 1}} | {{solution 1}} |
| {{problem 2}} | {{solution 2}} |

## The Problem

{{2-3 sentences explaining what goes wrong and why it's non-obvious.}}

## Solutions

### Option 1: {{Name}} (Recommended)

{{Step-by-step with code examples.}}

### Option 2: {{Alternative}}

{{For when Option 1 doesn't apply.}}

## Trade-offs

| Approach | Pros | Cons |
|----------|------|------|
| Option 1 | {{pros}} | {{cons}} |
| Option 2 | {{pros}} | {{cons}} |

## Edge Cases

- {{edge case 1 and how to handle it}}
- {{edge case 2 and how to handle it}}
```

### Step 6: Quality gates

Before finalizing, verify:

- [ ] SKILL.md has valid YAML frontmatter with `name` and `description`
- [ ] `name` matches the folder name (lowercase, hyphens)
- [ ] `name` does NOT contain reserved fragments `claude` or `anthropic` (use `cc-` prefix for Claude Code skills)
- [ ] Description includes "Use when:" trigger conditions
- [ ] Solutions are self-contained (no external context needed)
- [ ] Code examples are complete and copy-pasteable
- [ ] No project-specific hardcoded values (paths, URLs, credentials)
- [ ] No unnecessary dependencies

### Step 7: Report

```
✅ Skill extracted: {{skill-name}}

Files created:
  {{path}}/SKILL.md          ({{lines}} lines)
  {{path}}/README.md         ({{lines}} lines)
  {{path}}/reference/examples.md  ({{lines}} lines)

Install: /plugin install (copy to your skills directory)
Publish: clawhub publish {{path}}

Source: MEMORY.md entries at lines {{n, m, ...}} (retained — the skill is portable, the memory is project-specific)
```

## Examples

### Extracting a debugging pattern

```
/si:extract "Fix for Docker builds failing on Apple Silicon with platform mismatch"
```

Creates `docker-m1-fixes/SKILL.md` with:
- The platform mismatch error message
- Three solutions (build flag, Dockerfile, docker-compose)
- Trade-offs table
- Performance note about Rosetta 2 emulation

### Extracting a workflow pattern

```
/si:extract "Always regenerate TypeScript API client after modifying OpenAPI spec"
```

Creates `api-client-regen/SKILL.md` with:
- Why manual regen is needed
- The exact command sequence
- CI integration snippet
- Common failure modes

## Tips

- Extract patterns that would save time in a *different* project
- Keep skills focused — one problem per skill
- Include the error messages people would search for
- Test the skill by reading it without the original context — does it make sense?
