# Session Documentation Patterns

## Existing Approaches and Their Gaps

### Architecture Decision Records (ADRs)
ADRs (Nygard, 2011) are the standard for capturing architectural decisions. Format: context → decision → consequences. Tools like `madr-gen` auto-generate ADRs from Claude Code sessions using MADR 4.0 format.

**Gap**: ADRs don't capture *who* made the decision. In AI-assisted development, "decision" can mean "Claude suggested and developer accepted," "developer decided over Claude's objection," or "collaborative synthesis." Without this distinction, ADRs are incomplete evidence.

Source: [MADR format](https://adr.github.io/madr/), [madr-gen](https://github.com/Tazic123/madr-gen)

### Session Loggers (claude-sessions, claude-diary)
Tools like `maleta/claude-sessions` automatically summarize Claude Code sessions and generate `SESSION_SUMMARIES.md`. `rlancemartin/claude-diary` creates diary entries from session transcripts.

**Gap**: These tools answer "what happened?" not "what was the reasoning?" and not "what did each party contribute?" They're logs, not decision records.

Source: [maleta/claude-sessions](https://github.com/maleta/claude-sessions), [claude-diary](https://github.com/rlancemartin/claude-diary)

### Memory Compilers (claude-memory-compiler)
`coleam00/claude-memory-compiler` uses hooks to capture sessions, extracts key decisions with the Claude Agent SDK, and compiles cross-referenced knowledge articles.

**Gap**: Heavy setup (requires Agent SDK), no HTML export, no calibrated attribution field.

Source: [claude-memory-compiler](https://github.com/coleam00/claude-memory-compiler)

## The Signal Filtering Pattern

Not all sessions deserve documentation. Vela's 3-layer pipeline (signal detection → intent classification → output generation) filters noise before generating artifacts:

- **Layer 01 (Signal)**: git diff + conversation analysis → HIGH/MEDIUM/LOW
- **Layer 02 (Intent)**: ADHD 4-frame parallel reasoning → intent class
- **Layer 03 (Output)**: proportional artifact generation

This prevents the "everything is documented" anti-pattern where signal-to-noise ratio collapses.

Reference: Signal-filtering pipeline pattern — see [collab-proof SKILL.md](https://github.com/alirezarezvani/claude-skills/tree/main/engineering/collab-proof/skills/collab-proof/SKILL.md)

## ADHD Tree-of-Thought in Layer 02

The ADHD tree-of-thought approach (UditAkhourii, 2025) fans out parallel divergent thoughts under different cognitive frames, scores, prunes traps, and deepens survivors.

Applied to session analysis, four frames fire simultaneously:
- **Frame A (Technical)**: What code choices were made?
- **Frame B (Uncertainty)**: Where was the developer unsure?
- **Frame C (Fork)**: What could have gone differently?
- **Frame D (AI contribution)**: Where did Claude change the outcome?

Frames scoring below 0.4 are pruned. Only surviving frames contribute to output.

Source: [UditAkhourii/adhd](https://github.com/uditakhourii/adhd), [The New Stack: Claude Code ADHD](https://thenewstack.io/claude-code-adhd/)

## SessionEnd Hook (Claude Code 1.0.84+)

Claude Code introduced the `SessionEnd` hook in version 1.0.84. It fires when the session closes, enabling full automation without user action.

```json
"hooks": {
  "SessionEnd": [{
    "hooks": [{"type": "command", "command": "~/.claude/hooks/collab-proof-on-session-end.sh"}]
  }]
}
```

Known issue: `SessionEnd` hook may report "Hook cancelled" even on exit 0 (GitHub issue #63495, open as of 2026-06). Hook executes correctly despite the warning.

Source: [Claude Code Hooks Reference](https://code.claude.com/docs/en/hooks), [Issue #63495](https://github.com/anthropics/claude-code/issues/63495)
