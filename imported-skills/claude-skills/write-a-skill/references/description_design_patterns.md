# Description Design Patterns for Skills

This reference answers exactly one decision: **how do we write a skill description that an agent actually picks correctly when faced with a long skill list?**

Pair with `scripts/skill_description_validator.py` for automated enforcement.

## Matt Pocock's Foundational Rule

> "The description is **the only thing your agent sees** when deciding which skill to load."
>
> — Matt Pocock, write-a-skill

Implication: the description is not marketing copy. It's a routing signal for the agent. Every word competes with every other skill's description for activation attention.

## The Four Format Rules (per Matt)

1. **Max 1024 chars** — beyond this, agents lose the early sentences when condensing context
2. **Third person** — first-person ("I help with...") confuses agent self-identification; second-person ("You can...") confuses pronoun reference
3. **First sentence: what it does** — front-load the verb + object
4. **Second sentence: "Use when [specific triggers]"** — agent's most reliable activation cue

## Good vs Bad Examples (Matt's pattern, expanded)

**Good** (Matt's PDF example):

```
Extract text and tables from PDF files, fill forms, merge documents. Use when working with PDF files or when user mentions PDFs, forms, or document extraction.
```

**Why good:**
- Front-loaded verbs: Extract, fill, merge
- Concrete objects: text, tables, PDF files, forms
- Explicit trigger: "Use when working with PDF files"
- Specific keywords for matching: "PDFs", "forms", "document extraction"

**Bad** (Matt's):

```
Helps with documents.
```

**Why bad:**
- "Helps" is content-free
- "Documents" is generic — every doc skill has this
- No trigger
- No keyword variety

**Bad in different way** (over-specified):

```
This skill performs comprehensive PDF document processing including but not limited to extraction, manipulation, format conversion, content analysis, metadata management, and security operations on PDF files, with support for various PDF versions and embedded media types.
```

**Why bad:** verbose, no triggers, agent can't extract the key keywords from the wall of text.

## The Trigger Sentence Pattern

The "Use when" sentence is the highest-leverage part of the description. Patterns that work:

**Keyword triggers** (when user types specific words):
```
Use when user mentions PDFs, forms, or document extraction.
```

**File-type triggers** (when agent sees specific files):
```
Use when working with `.tsx` files or React component tests.
```

**Context triggers** (when agent is in a specific state):
```
Use when the user requests a code review of a pull request.
```

**Workflow triggers** (when agent is mid-workflow):
```
Use after running tests and before committing changes.
```

## Vocabulary Selection

The description's words must overlap with words users + agents naturally use for the task.

| Bad keyword | Better keyword | Why |
|---|---|---|
| "documents" | "PDF files" / "Word docs" | More specific = less collision |
| "improve" | "refactor" / "fix" / "optimize" | Specific verb = clearer routing |
| "various" | (delete; just list them) | Hedge language = no info |
| "modern" | (cite the actual tool/version) | Trend words age badly |
| "comprehensive" | (delete; just list capabilities) | Adjective inflation |

## Length Optimization

Below 1024 chars, shorter is usually better. Target: 100-300 chars for most skills.

Where complexity demands more chars, prioritize:
1. The verb-object pair (what it does) — never compress
2. The trigger phrase — never compress
3. Keyword variety (different ways users describe it) — expand here if space allows
4. Anti-keyword (what it does NOT do) — only if there's a frequently-confused sibling skill

## Anti-Patterns to Avoid

1. **First-person voice** — "I extract PDFs" — confuses agent self-reference
2. **Marketing language** — "fast, powerful, intuitive" — agent doesn't care, ignores adjectives
3. **Trigger-less descriptions** — every skill needs "Use when X"
4. **Multi-purpose dumping** — if your skill does 10 unrelated things, it's probably 10 skills
5. **Pronouns and hedges** — "you can also use this if you want to" — drop entirely
6. **Recursive descriptions** — "Use this skill when you need this skill" — adds nothing
7. **Implementation details** — "Built on Python + stdlib" — agent doesn't care; matters for README, not description

## Pre-Commit Discipline

Run before every skill PR:

```bash
python scripts/skill_description_validator.py path/to/SKILL.md
```

If validator returns FAIL, fix before merging. If WARN, justify and document the trade-off.

## When This Reference Doesn't Help

- **Naming the skill itself** — different concern; see naming-conventions guidance per-repo
- **Skill discovery in marketplaces** — different audience (humans browsing), different rules
- **System-prompt design for the agent that loads skills** — upstream concern

---

**Source authorities (non-exhaustive):**

- **Matt Pocock — write-a-skill** (https://github.com/mattpocock/skills/, MIT) — the 4 format rules + good/bad example pattern
- **Anthropic — Building agents with skills** (https://docs.claude.com/en/docs/agents/skills) — official format guidance
- **Anthropic Engineering — Effective system prompts** (continuously updated blog) — same principles applied to system-prompt design
- **Claude Code documentation — Skill registry** — how Claude's skill-loader uses descriptions
- **Karpathy, A. — public commentary on LLM prompt design** — emphasis on specificity + lack of ambiguity
- **Garrett, J.J. — "The Elements of User Experience"** (2002) + information architecture principles — labels must match user mental models
- **Nielsen Norman Group — Microcontent guidelines** — applies to skill descriptions: front-load value, hard-cap length, scannable structure
- **Search-engine + SEO patterns adapted for agent routing** — keyword density, intent matching, semantic field coverage
