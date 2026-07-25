---
name: karpathy-coder
description: Use when writing, reviewing, or committing code to enforce Karpathy's 4 coding principles — surface assumptions before coding, keep it simple, make surgical changes, define verifiable goals. Triggers on "review my diff", "check complexity", "am I overcomplicating this", "karpathy check", "before I commit", or any code quality concern where the LLM might be overcoding.
context: fork
version: 2.9.0
author: claude-code-skills
license: MIT
tags: [code-quality, discipline, karpathy, simplicity, surgical-changes, anti-patterns, review]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# Karpathy Coder — Active Coding Discipline

Derived from [Andrej Karpathy's observations](https://x.com/karpathy/status/2015883857489522876) on LLM coding pitfalls. This is **not just guidelines** — it ships Python tools that detect violations, a review agent, a slash command, and a pre-commit hook.

> "The models make wrong assumptions on your behalf and just run along with them without checking. They don't manage their confusion, don't seek clarifications, don't surface inconsistencies, don't present tradeoffs, don't push back when they should."
>
> "They really like to overcomplicate code and APIs, bloat abstractions, don't clean up dead code... implement a bloated construction over 1000 lines when 100 would do."
>
> "LLMs are exceptionally good at looping until they meet specific goals... Don't tell it what to do, give it success criteria and watch it go."
>
> — Andrej Karpathy

## The four principles

### 1. Think Before Coding

**Don't assume. Don't hide confusion. Surface tradeoffs.**

- State assumptions explicitly. If uncertain, ask.
- If multiple interpretations exist, present them — don't pick silently.
- If a simpler approach exists, say so. Push back when warranted.
- If something is unclear, stop. Name what's confusing. Ask.

### 2. Simplicity First

**Minimum code that solves the problem. Nothing speculative.**

- No features beyond what was asked.
- No abstractions for single-use code.
- No "flexibility" or "configurability" that wasn't requested.
- No error handling for impossible scenarios.
- If you write 200 lines and it could be 50, rewrite it.

**The test:** Would a senior engineer say this is overcomplicated? If yes, simplify.

### 3. Surgical Changes

**Touch only what you must. Clean up only your own mess.**

- Don't "improve" adjacent code, comments, or formatting.
- Don't refactor things that aren't broken.
- Match existing style, even if you'd do it differently.
- If you notice unrelated dead code, mention it — don't delete it.
- Remove imports/variables/functions that YOUR changes made unused.
- Don't remove pre-existing dead code unless asked.

**The test:** Every changed line should trace directly to the user's request.

### 4. Goal-Driven Execution

**Define success criteria. Loop until verified.**

| Instead of... | Transform to... |
|---|---|
| "Add validation" | "Write tests for invalid inputs, then make them pass" |
| "Fix the bug" | "Write a test that reproduces it, then make it pass" |
| "Refactor X" | "Ensure tests pass before and after" |

For multi-step tasks, state a brief plan:

```
1. [Step] → verify: [check]
2. [Step] → verify: [check]
3. [Step] → verify: [check]
```

## Slash command

`/karpathy-check` — Run the full 4-principle review on your staged changes.

## Python tools (`scripts/`)

All tools are stdlib-only. Run with `--help`.

| Script | What it detects |
|---|---|
| `complexity_checker.py` | Over-engineering: too many classes, deep nesting, high cyclomatic complexity, unused params, premature abstractions |
| `diff_surgeon.py` | Diff noise: lines that don't trace to the stated goal — comment changes, style drift, drive-by refactors |
| `assumption_linter.py` | Hidden assumptions in a plan: unasked features, missing clarifications, silent interpretation choices |
| `goal_verifier.py` | Weak success criteria: vague plans without verifiable checks, missing test assertions |

## Sub-agent

`karpathy-reviewer` — Runs all 4 principles against a diff. Dispatched by `/karpathy-check` or manually before committing.

## Pre-commit hook

`hooks/karpathy-gate.sh` — runs `complexity_checker.py` and `diff_surgeon.py` on staged files. Warns (non-blocking) when violations are found. Wire it via `.claude/settings.json` or Husky.

## References

- `references/karpathy-principles.md` — the source quotes, deeper context, when to relax each principle
- `references/anti-patterns.md` — 10+ before/after examples across Python, TypeScript, and shell
- `references/enforcement-patterns.md` — how to wire hooks, CI integration, team adoption

## When to relax

These principles bias toward **caution over speed**. For trivial tasks (typo fixes, obvious one-liners), use judgment. The principles matter most on:

- Non-trivial implementations (>20 lines changed)
- Code you don't fully understand
- Multi-step tasks with unclear requirements
- Anything that will be reviewed by humans

## Cross-tool compatibility

Installs via plugin for Claude Code. For other tools, copy the principles into your schema file:

| Tool | Schema file |
|---|---|
| Claude Code | `CLAUDE.md` (auto-loaded by plugin) |
| Codex CLI | `AGENTS.md` |
| Cursor | `AGENTS.md` or `.cursorrules` |
| Antigravity / OpenCode / Gemini CLI | `AGENTS.md` |

## Related skills (chains via `context: fork`)

- **`self-eval`** — honest quality scoring after completing work
- **`code-reviewer`** — broader code review; karpathy-coder focuses on the 4 LLM-specific pitfalls
- **`llm-wiki`** — compound knowledge; karpathy-coder ensures you don't overcomplicate while building it
