---
name: claude-md-architecture
description: Use when the user wants to reorganize a monolithic CLAUDE.md, separate model-specific behavior from identity and process rules, set up configs that survive LLM swaps, or mentions multi-model setups, switching between Claude and DeepSeek/Gemini/Qwen, CLAUDE.md bloat, config drift, or separating behavior rules from project rules. Provides a three-layer architecture (SOUL/INTERFACE/BODY) that isolates model-specific tuning.
license: Complete terms in LICENSE.txt
---

# CLAUDE.md Architecture: SOUL / INTERFACE / BODY

> **The problem:** Most CLAUDE.md files are monolithic. When you switch LLMs (Claude → DeepSeek, or Opus → Sonnet), you rewrite everything because behavior tuning is mixed with identity and process rules.
>
> **The solution:** Three-layer separation. Swap the LLM, only rewrite one file.

## When to Use

Activate when the user:
- Says their CLAUDE.md is too long or hard to maintain
- Switches between different LLM providers (Claude ↔ DeepSeek ↔ Gemini)
- Mentions "config drift" or "my rules stopped working after switching models"
- Wants to separate identity, behavior rules, and process rules
- Asks "how should I organize my CLAUDE.md?"

## How to Use (Workflow)

### Stage 1: Audit the current CLAUDE.md

Read the user's existing CLAUDE.md. Classify every section, rule, or instruction into one of three buckets:

| Bucket | What belongs here | Example |
|--------|------------------|---------|
| **SOUL** | Identity, role, goals, learning philosophy | "I am a full-stack developer working on a SaaS product" |
| **INTERFACE** | Model-specific behavior tuning, tool precision, output style | "After 2 consecutive tool failures, switch strategy instead of retrying" |
| **BODY** | Process rules, review sequences, delivery checks | "Before committing, run lint + type-check + related tests" |

**Rule of thumb:** "Would this rule still apply if I switched from Claude to DeepSeek tomorrow?" If yes → SOUL or BODY. If no → INTERFACE.

### Stage 2: Draft the three files

Write `SOUL.md`, `INTERFACE.md`, `BODY.md` following the templates below. For each file:
1. Start from the template structure
2. Migrate the user's existing content into the appropriate sections
3. Delete anything that doesn't belong in that layer
4. Verify: no rule appears in more than one file

### Stage 3: Replace and test

1. Replace the monolithic CLAUDE.md with a short file containing the architecture diagram and `@SOUL.md @INTERFACE.md @BODY.md` references
2. Run one session with the new structure — does everything still work?
3. Ask the user to try: "imagine we swapped models tomorrow — which files would you edit?"

## Before/After Example

**Before (monolithic CLAUDE.md, excerpt):**
```markdown
# CLAUDE.md
I am a Python backend developer. I prefer functional style over OOP.
Always run `pytest` before committing. Never use type: ignore.
When using DeepSeek, split long responses and verify tool outputs.
I'm currently learning Rust and system design.
Disk space check: warn at 30GB, block at 15GB.
```

**After (three files):**

`SOUL.md`:
```markdown
# SOUL
## Identity
- Python backend developer, functional style preferred
## Goals
- Learning Rust and system design
```

`INTERFACE.md`:
```markdown
# INTERFACE
## Current Brain
- Model: deepseek-v4-pro
## Behavior Calibration
- OUTPUT: Split responses >500 words into sections
- TOOL: Verify output before next call; prefer single-call over batching
```

`BODY.md`:
```markdown
# BODY
## Pre-Commit Checks
- Run `pytest` before every commit
## Delivery Rules
- Never use `type: ignore` without explicit justification
## System Health
- Disk: warn at 30GB free, block writes at 15GB
```

## The Three Layers

```
SOUL.md        ← Identity · Goals · Growth (does not change for model swaps)
    ↓
INTERFACE.md   ← Brain calibration · Model-specific behavior tuning
    ↓
BODY.md        ← Process rules · Reviews · Delivery gates (model-agnostic)
    ↓
Self-model loop: SOUL.md evolves across sessions via growth/learning capture
```

### SOUL.md — Who I Am

Static across LLM swaps; evolves only through the self-model loop (learning/growth over time):
- Core identity (name, role, expertise)
- Long-term goals (why am I here?)
- Growth trajectory (what I'm learning)
- External capability registry (which skills, MCPs, scripts are available)

This file should not need changes during a model swap because it captures model-agnostic identity. If you find yourself editing it during a swap, audit whether the content truly belongs here.

### INTERFACE.md — How This Brain Works

The only file that changes when swapping models:
- Which model is currently the "brain"
- Behavior calibration with concrete values:
  - TOOL: "Match parameter names to schema exactly; after 2 consecutive failures, switch strategy."
  - OUTPUT: "Split responses over 500 words into clearly labeled sections."
  - CODE: "Read before editing; match existing style; surface all errors."
  - VERIFY: "Post-edit verification is mandatory; never claim 'tests pass' without running them."
  - CONTEXT: "Reconfirm any info last mentioned >5 turns ago; after 5 rounds on same bug, stop speculating about root cause."
  - DELIVERY: "After complex tasks, update learning logs and run self-audit before session end."
- Nervous system table: each brain trait → corresponding body regulation
- Project-specific config (WMS version, security rules)
- LLM swap instructions

When swapping models, this is the file you edit. The other files should remain untouched — if you find yourself editing them, the separation boundary has drifted.

### BODY.md — What I Do (Regardless of Brain)

Model-agnostic process rules:
- Session startup: file existence check, task classification (simple/complex/strategic), health verification (disk space, rule staleness, format consistency)
- Shutdown sequence: self-audit → teaching output → delivery gate → learning capture → output index
- Review system: external review (dual-pool) → internal review (self-audit) → process review (delivery gate). Each layer blocks independently.
- Learning capture: new facts → persona; new patterns → core drives; ability changes → ratings; decisions → decisions log (with review date); methodology → growth log
- System health: Dell G15/i7-12700H/RTX3060/16GB/512GB; disk warn at 30GB, block at 15GB; cleanup /tmp/ on session end

These rules should work identically regardless of which LLM is running.

### Self-Model Loop

SOUL.md is not purely static — it evolves through a feedback loop:
1. Each session starts by reading the current self-model (how I see myself based on past experience)
2. The session produces new experiences (failures, methodologies, capability changes)
3. At session end, growth data updates the self-model
4. Next session reads an evolved self-model — a different "me"

This is the "strange loop": reading yourself → being influenced by what you read → producing new data → rewriting yourself. It lives in a separate `memory/self-model.md` file that references and is referenced by SOUL.md.

## Template: SOUL.md

```markdown
# SOUL
> Who I am · Where I'm going · How I grow

## Identity
- [Name/Role] · [Context]
- [Core drive / working style]

## Goals
- Short-term: [immediate objectives]
- Long-term: [why am I here?]

## Growth
- Learning through experience iteration
- Failures > achievements for learning density
- Data stored in memory/ directory

## Capability Registry
- Learning: growth log → persona → self-model cycle
- Review: [reference to review methodology file]
- Delivery: [reference to BODY.md]
- Tools: skills/* + MCP servers + scripts/*
```

## Template: INTERFACE.md

```markdown
# INTERFACE
> Soul-Brain Interface · Swap LLMs, only rewrite this file

## Current Brain
- Model: [model-id]
- Subagent default: [inherit / different model]
- Subagent limit: [N, default 8]
- Thinking: [enabled / disabled]

## Behavior Calibration
- TOOL: Match parameter names to schema exactly. After 2 consecutive tool failures, switch strategy instead of retrying.
- OUTPUT: Split responses >500 words into labeled sections. Default to short code-first answers.
- CODE: Read before editing. Match surrounding style. Surface all errors explicitly.
- VERIFY: Post-edit verification is mandatory. Never claim tests pass without running them.
- CONTEXT: Reconfirm info last mentioned >5 turns ago. After 5 rounds on same bug, stop and report root cause pattern.
- DELIVERY: After complex/strategic tasks, update learning logs and run self-audit.

## Nervous System (Brain → Body regulation)
| Brain Trait | Body Regulation |
|-------------|----------------|
| Long context, attention decays | Compact at 70% token usage |
| Tool call precision weaker than native Claude | Verification step is non-negotiable |
| Output tends verbose | Hard cap: split at 500 words |
| High creativity, lower consistency | Fixed review pool weight > random pool |
| Effective context ~70% of 1M window | Do not trust full-window memory |

## LLM Swap Instructions
1. Rewrite Behavior Calibration parameters and Nervous System table for the new model
2. SOUL.md / BODY.md / memory/ stay unchanged
3. Run 3 test tasks to verify behavior matches expectations
4. If something broke, check: did model-specific tuning leak into BODY.md?
```

## Template: BODY.md

```markdown
# BODY
> Process rules · Review system · Delivery gate
> These rules apply regardless of which LLM is running.

## Session Startup
- Verify all config files exist and are readable
- Classify session scope: simple (typo/query) / complex (multi-file/feature) / strategic (career/portfolio)
- Continuation from previous session → default to complex
- Check disk space (warn at 30GB, block at 15GB)
- Check for stale rules (>30 sessions unused → flag)
- Verify format consistency across all config files (use 3 formats max)

## Shutdown Sequence
After complex/strategic tasks, execute in order:
1. **Self-audit**: Review output for completeness, consistency, groundedness, honesty
2. **Teaching output**: Distill what was done, why, and what's transferable (1-3 sentences)
3. **Delivery gate**: Verify learning libraries updated, no rationalized incompleteness
4. **Learning capture**: Write to growth-log, decisions-log, ratings-tracker as appropriate
5. **Output index**: Record deliverable file paths for cross-session retrieval

## Review System
Three layers, sequential — each blocks independently:
- Layer 1 (External): Dual-pool persona review of output quality
- Layer 2 (Internal): Four-dimension self-audit (Completeness > Consistency > Groundedness > Honesty)
- Layer 3 (Process): Delivery gate script checks learning capture freshness

## Learning Capture Rules
- New facts about user → persona file
- New methodology/failure pattern → growth-log (failures prioritized over achievements)
- Irreversible choice → decisions log with review date
- Measurable ability change → ratings tracker (0-5 scale)
- New file created → output index

## System Health
- Hardware: [specs]
- Disk: warn at 30GB free, block writes at 15GB
- Session end: clean /tmp/
- Context: compact at 70% token usage
```

## Anti-Patterns

- ❌ **Over-splitting**: A 30-line CLAUDE.md doesn't need three files. Apply this pattern when your config exceeds ~80 lines or you actually use multiple models.
- ❌ **INTERFACE.md becomes the new monolith**: If INTERFACE.md grows past 80 lines, the calibration is too granular. Rules that apply regardless of model belong in BODY.md.
- ❌ **Drift from concurrent edits**: If both you (human) and the self-model loop (AI) write to SOUL.md, changes can be lost. Version control SOUL.md and review diffs before merging.
- ❌ **Skipping the swap test**: The entire value proposition is LLM portability. After migration, deliberately simulate a model change — only edit INTERFACE.md and verify everything still works.

## See Also

- [[skill-creator]] — Conventions for writing effective skills
- [[self-audit]] — The internal review dimension referenced in BODY.md's shutdown sequence
- [[CLAUDE.md]] — Your project's main configuration file (the one this skill helps restructure)
