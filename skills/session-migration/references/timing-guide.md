# Migration Timing Reference

Use this guide to decide when migration is appropriate. These thresholds come from Microsoft Research (arxiv 2505.06120) and Anthropic's context engineering guidance.

## Context Usage vs Quality

| Context usage | Quality status |
|--------------|----------------|
| < 50% | Minimal degradation |
| 50-70% | Subtle degradation begins |
| 70-85% | Noticeable degradation |
| 85%+ | Significant degradation |

**Recommended action window: 70-75% context usage.** Before that is wasteful; after that, the AI's output is already compromised.

## Migration Timing by Scenario

| Scenario | Recommended threshold | Approximate turns | Why |
|----------|----------------------|-------------------|-----|
| Casual Q&A / chat | 50-60% | 20-30 turns | Low precision requirement, can tolerate some drift |
| Writing (requires rigor) | 40-50% | 10-15 turns | Tool calls produce large intermediate artifacts |
| Coding / Agent tasks | 40-50% | 8-12 turns | Search, file reads, command output consume heavy tokens |
| Exploration / brainstorming | 60-70% | 25-40 turns | Low precision requirement, drift is acceptable |

## Special Case: Agent Users

If the user is working with an agent (Claude Code, Hermes, Cursor, etc.), each conversation turn can produce 5-10x more tokens than a plain chatbot turn due to tool invocations. This means:

- 4-5 turns may already fill 40-50% of context
- Compression may have already fired by turn 5-6
- Each compression is lossy — early details start degrading after 2-3 compressions

For agent users, migration should be considered earlier and more proactively.
