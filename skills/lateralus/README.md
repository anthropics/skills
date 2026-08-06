# lateralus skill

Lateralus has two modes: **stuck-debugging** and **brainstorming**.

## lateralus — stuck debugging

Designed for situations where normal debugging loops are not producing progress.
Instead of repeating nearby fixes, it forces an explicit three-tier ideation pass:

1. Tier 1 · Ground: concrete, testable hypotheses outside the obvious failure category
2. Tier 2 · Balanced: assumption-questioning hypotheses that remain loosely verifiable
3. Tier 3 · Wild: speculative reframes designed to jolt new associations

### Use when

- The same bug survives multiple attempted fixes
- The user reports repeated failure (for example: "still broken")
- The agent detects it is about to repeat a rejected fix category

### Do not use when

- It is the first attempt to debug a bug
- The issue has not been reproduced yet
- There is still an obvious untried baseline path

### Output contract

1. Dead ends already ruled out
2. Tier 1 (Ground) list — each with exact diagnostic to run before fixing
3. Tier 2 (Balanced) list — assumption + loose test signal
4. Tier 3 (Wild) list — non-literal reframes
5. Closing question asking which direction to investigate

---

## lateralus-brainstorm — planning and idea generation

Designed for planning new features, architecture decisions, and exploring options.
Activates automatically in plan mode ("let's plan", "brainstorm", "what are our options").

Three modes:

1. Grounded: practical ideas within current constraints, shippable soon
2. Balanced: ideas that challenge one assumption each, loosely feasible
3. Wild: constraint-free, blue-sky, no wrong answers

Always establishes goal and horizon before generating anything.

---

## Source of truth

- `skills/lateralus/SKILL.md` — full debugging skill
- `skills/lateralus-brainstorm/SKILL.md` — brainstorming / plan-mode skill
- Copilot mirrors: `.github/skills/`
