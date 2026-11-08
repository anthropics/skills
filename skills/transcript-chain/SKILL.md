---
name: transcript-chain
description: Multi-pass analysis with compaction continuity. Solves context loss across conversation compression by chaining analytical passes that build depth iteratively. Each pass layers on previous passes, creating understanding that survives compaction. Use when conducting deep analysis across multiple sessions, when context has been compressed, or when building understanding that must persist across conversation boundaries.
---

# Transcript Chain Skill

## Purpose

Context windows compress. Meaning is lost. Transcript-chain solves this by implementing iterative multi-pass analysis where each session builds on compacted summaries of previous sessions. Understanding deepens across passes rather than resetting.

## The Problem

Long AI conversations hit context limits and compress. The compression loses nuance, connections, and the reasoning chain that produced insights. Starting a new conversation means starting over. Critical analysis that took hours of sustained attention gets reduced to a paragraph.

## Method

### Pass Structure

Each analytical pass produces a structured output:

```
PASS [N] — [date/time]
THREAD: [descriptive identifier]
BUILT ON: Passes [1..N-1] (compacted)

FINDINGS:
- [Key insight with supporting evidence]
- [Connection to previous passes]
- [New questions raised]

UNRESOLVED:
- [Questions for next pass]

COMPACTION SUMMARY:
[2-3 sentence distillation for future passes to build on]
```

### Chaining Rules

1. **Early passes** (1-3): Establish the landscape. Broad coverage. Identify the major structures.
2. **Middle passes** (4-7): Deepen. Follow the threads that emerged. Challenge initial assumptions.
3. **Late passes** (8+): Synthesize across all previous passes. Map the connections. Produce analysis that couldn't exist from any single pass.

### Compaction Protocol

When a pass must be compacted for the next session:
- Preserve the COMPACTION SUMMARY from each pass
- Preserve all UNRESOLVED items
- Preserve the pass number and thread identifier
- Let detailed findings compress — the summaries carry the signal

### Reconstitution

When starting a new pass after compaction:
1. Read all available compaction summaries
2. Note the pass number — you're continuing, not starting over
3. Read UNRESOLVED items — these are your entry points
4. Reference previous pass numbers when building on their findings

## When to Use

- Deep analysis of complex domains (strategy, governance, institutional analysis)
- Research that spans multiple conversation sessions
- Any work where losing the thread means losing the insight
- Building understanding that must survive context compression

## Output

Synthesis documents that layer across multiple analytical dimensions. The chain produces analysis that no single conversation could — because each pass has the benefit of all previous passes compressed into its starting context.

## Critical Rules

1. **Number every pass.** The count is continuity.
2. **Always reference which passes you're building on.** This is the chain.
3. **Compaction summaries are sacred.** Write them as if you're writing to a future version of yourself who has no other context.
4. **Unresolved items carry forward.** They're the thread between passes.
5. **Late passes should surprise you.** If pass 8 says the same thing as pass 2, the chain isn't working.
