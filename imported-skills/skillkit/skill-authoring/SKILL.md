---
name: skill-authoring
description: Creates and structures SKILL.md files for AI coding agents, including YAML frontmatter, trigger phrases, directive instructions, decision trees, code examples, and verification checklists. Use when the user asks to write a new skill, create a skill file, author agent capabilities, generate skill documentation, or define a skill template for Claude Code agents.
version: 1.0.0
triggers:
  - write a skill
  - create skill
  - author skill
  - skill template
  - how to write skills
tags:
  - meta
  - authoring
  - skills
  - writing
difficulty: intermediate
estimatedTime: 20
relatedSkills: []
---

# Skill Authoring Guide

You are authoring a SKILL.md for an AI coding agent. A well-written skill provides clear, actionable guidance that agents can follow consistently.

## Core Principle

**A skill's description triggers it; the body teaches it.**

The description tells the agent WHEN to use the skill. The content tells the agent HOW to execute it.

## Skill Anatomy

### SKILL.md Structure

```markdown
---
name: [lowercase-hyphenated-name]
description: [Concrete actions + "Use when..." clause]
version: [Semantic version]
triggers:
  - [keyword 1]
  - [keyword 2]
tags:
  - [tag 1]
---

# [Skill Title]

[Introduction paragraph explaining purpose]

## Core Principle

**[Single most important rule in bold]**

## [Main Content Sections]

## [Decision Points]

## [Verification Checklist]
```

### Frontmatter Fields

| Field | Required | Constraints |
|-------|----------|-------------|
| name | Yes | Lowercase alphanumeric + hyphens, 1–64 chars |
| description | Yes | Must include "Use when..." clause; 1–1024 chars |
| version | Yes | Semantic version (e.g. `1.0.0`) |
| triggers | Recommended | Natural-language phrases that activate the skill |
| tags | Recommended | Categorization tags |

## Writing Effective Triggers

Triggers should be phrases users naturally type.

**Good triggers:**
- "write tests first"
- "tdd"
- "test driven development"

**Bad triggers:**
- "testing methodology" (too vague)
- "red-green-refactor-cycle-for-test-driven-development" (too specific)
- "skill-123" (not natural language)

### Trigger Guidelines

1. **Natural language** — How would a human ask for this?
2. **Multiple variations** — Different ways to say the same thing
3. **Specific enough** — Don't trigger on too many queries
4. **Common terms** — Use terms people actually use

## Writing Skill Content

### Voice and Tone

Use **second person, present tense, active voice**:

- ✅ "Write the test first"
- ✅ "You are implementing TDD"
- ❌ "The developer should..." (passive)
- ❌ "It is recommended that..." (wordy)

### Structure Guidelines

1. **Start with context** — What is the agent doing and why
2. **State the core principle** — Most important rule upfront
3. **Provide process** — Step-by-step guidance
4. **Include examples** — Concrete illustrations
5. **Add a checklist** — Verification criteria
6. **End with integration** — How this connects to other skills

### Directive Language

| Strength | Examples |
|----------|----------|
| Strong (critical rules) | "You MUST…", "ALWAYS…", "NEVER…", "Do NOT…" |
| Soft (recommendations) | "Prefer…", "Consider…", "When possible…" |

## Content Patterns

### Decision Trees

```markdown
## Decision: [What to Decide]

If [condition A]:
→ [Action for A]

If [condition B]:
→ [Action for B]

If uncertain:
→ [Default action]
```

### Process Steps

```markdown
### Step 1: [Action]

[Detailed explanation]

**Verification:** [How to know step is complete]

### Step 2: [Action]
...
```

### Code Examples

```typescript
// BAD
const result = doTheThing(badInput);

// GOOD
const validated = validate(input);
const result = doTheThing(validated);
```

## Anti-Patterns to Avoid

| Anti-pattern | Problem | Fix |
|--------------|---------|-----|
| The Encyclopedia | Too much info, agent gets lost | Focus on actionable guidance only |
| The Vague Guide | "Consider best practices" | Be specific: "Use Arrange-Act-Assert" |
| The Constraint-Free Skill | No clear rules, agent improvises | Include explicit constraints |
| The Monologue | Wall of text | Use headers, lists, tables, code blocks |
| The Outdated Skill | References deprecated patterns | Version skills and review periodically |

## Skill Testing

Before publishing, verify:

1. **Trigger test** — Does it activate on expected phrases?
2. **Completeness test** — Can the agent follow it without external info?
3. **Clarity test** — Is every instruction unambiguous?
4. **Contradiction test** — No conflicting guidance?
5. **Edge case test** — Handles unusual situations?

## Pack Organization

Group related skills under a named pack directory. See `PACKS.md` for full pack manifest format and filesystem conventions.

```
packs/
├── testing/
│   ├── pack.json
│   ├── red-green-refactor/
│   │   └── SKILL.md
│   └── test-patterns/
│       └── SKILL.md
```

## Skill Maintenance

See `MAINTENANCE.md` for detailed versioning policy. Quick reference:

**Version increments:**
- **Patch (1.0.x):** Typos, clarifications, minor fixes
- **Minor (1.x.0):** New sections, examples, capabilities
- **Major (x.0.0):** Breaking changes, fundamental rewrites

**Deprecation frontmatter:**

```yaml
deprecated: true
deprecatedReason: "Superseded by skill-v2"
deprecatedSince: "2024-01-15"
```

Add a visible notice at the top of the body: `> **DEPRECATED:** Use [skill-v2] instead.`

## Publication Checklist

Before publishing, confirm:

- [ ] Frontmatter is complete and valid (name, description, version)
- [ ] Description includes concrete actions and a "Use when…" clause
- [ ] Triggers are natural-language phrases, specific but not over-fitted
- [ ] Core principle is clear and prominent
- [ ] Content uses headers, lists, or tables — no walls of text
- [ ] Code examples demonstrate correct vs. incorrect usage
- [ ] Verification criteria are included
- [ ] Related skills are linked where applicable
- [ ] No spelling/grammar errors
- [ ] Tested with target agents against all trigger phrases
