---
name: claude-md-architecture
description: Architecture pattern for CLAUDE.md — separate identity (SOUL) from brain calibration (INTERFACE) from process rules (BODY). Essential for multi-model setups where you swap LLMs but keep identity and workflows.
license: Complete terms in LICENSE.txt
---

# CLAUDE.md Architecture: SOUL / INTERFACE / BODY

> **The problem:** Most CLAUDE.md files are monolithic. When you switch LLMs (Claude → DeepSeek, or Opus → Sonnet), you rewrite everything because behavior tuning is mixed with identity and process rules.
>
> **The solution:** Three-layer separation. Swap the LLM, only rewrite one file.

## The Three Layers

```
SOUL.md        ← Identity · Goals · Growth (LLM-agnostic, NEVER changes)
    ↓
INTERFACE.md   ← Brain calibration · Model-specific behavior tuning
    ↓
BODY.md        ← Process rules · Reviews · Delivery gates (LLM-agnostic)
    ↓
Write back SOUL.md ← Closed loop (self-model reads itself each session)
```

### SOUL.md — Who I Am

Static identity that persists across LLM swaps:
- Core identity (name, role, expertise)
- Long-term goals (why am I here?)
- Growth trajectory (what I'm learning)
- External capability registry (which skills, MCPs, scripts are available)

**Rule:** This file NEVER changes when you swap models. It's your digital twin's "soul."

### INTERFACE.md — How I Think

Model-specific behavior calibration:
- Which model is currently the "brain"
- Behavior tuning: tool call precision, output length, verification strictness
- Nervous system table: brain trait → body regulation (e.g. "long context → compact at 70%")
- Project-specific config (WMS version, security rules)
- LLM swap instructions

**Rule:** This is the ONLY file that changes when you swap models. Everything else stays.

### BODY.md — What I Do

Model-agnostic process rules:
- Session startup checklist (health check, task classification)
- Shutdown sequence (review → teach → gate → capture → index)
- Three-layer review system (external review → self-audit → delivery gate)
- Learning capture rules (growth log, decisions log, ratings tracker)
- System health (disk space, cleanup)

**Rule:** These rules should work identically regardless of which LLM is running.

## Why This Matters

### For Multi-Model Users
DeepSeek, Gemini, Qwen — each needs different behavior tuning. INTERFACE.md isolates those differences.

### For Teams
Everyone shares SOUL.md and BODY.md. Individual developers customize only INTERFACE.md for their preferred model.

### For Maintainability
Rules don't drift. Identity doesn't get lost in a 500-line CLAUDE.md. Each layer has clear ownership.

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
- Learning: [growth log → persona → self-model cycle]
- Review: [review methodology reference]
- Delivery: [process rules reference]
- Tools: skills/* + MCP servers + scripts/*
```

## Template: INTERFACE.md

```markdown
# INTERFACE
> Soul-Brain Interface · Swap LLMs, only rewrite this file

## Current Brain
- Model: [model-id]
- Subagent default: [same / different model]
- Subagent limit: [N]
- Thinking: [enabled / disabled]

## Behavior Calibration
- TOOL: [tool precision rules]
- OUTPUT: [conciseness / splitting rules]
- CODE: [modification style / verification rules]
- VERIFY: [post-edit verification rules]
- CONTEXT: [stale info / repeated bug rules]
- DELIVERY: [output + capture rules]

## Nervous System (Brain → Body regulation)
| Brain Trait | Body Regulation |
|-------------|----------------|
| [trait]     | [compensating rule] |

## LLM Swap Instructions
1. Rewrite calibration parameters + behavior rules + nervous system table
2. SOUL.md / BODY.md / memory/ stay unchanged
3. Run 3 test tasks to verify
```

## Template: BODY.md (excerpt)

```markdown
# BODY
> Process rules · Review system · Delivery gate

## Session Startup
- File existence check
- Task classification: simple / complex / strategic
- Health: disk space, rule staleness, format consistency

## Shutdown Sequence
1. Self-audit → 2. Teaching output → 3. Delivery gate → 4. Capture → 5. Output index

## Learning Capture
- New facts → persona updates
- New patterns → core drives
- Ability changes → ratings tracker
- Decisions → decisions log (with review date)
- Methodology → growth log (failures prioritized)
```

## Migration Guide: Monolithic → Three-Layer

1. **Extract identity** from CLAUDE.md → SOUL.md (who am I, goals, growth)
2. **Extract behavior rules** → INTERFACE.md (tool/output/code/verify/context)
3. **Extract process rules** → BODY.md (startup/shutdown/reviews/capture)
4. **Replace CLAUDE.md** with architecture diagram + `@SOUL.md @INTERFACE.md @BODY.md` references
5. **Test**: swap the model in INTERFACE.md, verify everything else still works

## Anti-Patterns

- ❌ Keeping model-specific tuning in SOUL.md or BODY.md (defeats the purpose)
- ❌ Duplicating behavior rules across all three files (INTERFACE.md is authoritative)
- ❌ Making SOUL.md too large (identity is who, not how)
- ❌ Skip the swap test after migration (the whole point is LLM portability)

## Origin

Extracted from a DeepSeek V4 Pro + Claude Code configuration system that runs 4 active skills, 7 MCP servers, 5 learning libraries, and a self-referential self-model loop — all surviving multiple LLM configuration changes because identity and process were never mixed with brain calibration.
