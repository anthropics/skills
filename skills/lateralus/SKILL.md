---
name: lateralus
description: >
  Lateral-thinking escape hatch for stalled debugging. Surfaces end goal and solution horizon,
  generates alternatives in three tiers: Grounded (testable causes), Balanced (assumption-questioning),
  Wild (speculative reframes), plus Workaround (bypass now, fix later).
  Use when user invokes /lateralus, says "stuck", "going in circles", "already tried", "still broken",
  or normal debugging has genuinely stalled after 2+ failed attempts.
---

Understand the goal first. Break tunnel vision. Generate from outside the failed approach.

## Step 0 — Interrogate before ideating (always first, no exceptions)

### Phase 1 — Read the codebase (before asking anything)

**Do this silently before presenting options to the user:**

1. Check for `CLAUDE.md` (or `AGENTS.md`, `GEMINI.md`) at the repo root — read it fully if present. It contains architecture, conventions, build commands, and maintainer instructions that shape every question and hypothesis.
2. If no `CLAUDE.md`, do a quick orientation scan:
   - Detect language/framework from `go.mod`, `package.json`, `requirements.txt`, `Cargo.toml`, `pom.xml`, etc.
   - Read `README.md` (first 60 lines) for architecture context.
   - Run `git log -10 --oneline` to see recent changes.
   - Glob for key config files (`docker-compose.yml`, `k8s/`, `.env.example`, `Makefile`).
3. Note anything that will make questions more specific — deployment model, service boundaries, observability stack, recent commits near the failure.

If no codebase is accessible (user pasted a scenario) → skip to Phase 2 immediately.

---

### Phase 2 — Present options and ask the user to choose

**Open with this every time (after Phase 1):**

```
I can help in four ways — which fits your situation?

  [1] Tier 1 · Ground    — concrete, testable hypotheses outside the obvious layer
  [2] Tier 2 · Balanced  — question assumptions while staying loosely verifiable
  [3] Tier 3 · Wild      — speculative reframes to break tunnel vision entirely
  [4] Workaround         — bypass the problem now, fix it properly later

Pick a number, or describe your situation and I'll route you.
```

If Phase 1 found useful context → briefly surface it before the menu (e.g., "I can see this is a Go service on Kubernetes with Prometheus — that shapes the hypotheses.").
If the user describes their situation instead of picking → infer the best fit and confirm before proceeding.
User distressed or deadline-pressured → suggest [4] first.

---

### Phase 3 — Ask tailored questions based on choice

**[1] Ground — questions to ask:**
```
1. What have you already tried, and why did each attempt fail?
2. Which component or layer does the failure appear in?
3. What observability do you have? (profiler, APM, logs, metrics, tracing)
4. What does your current monitoring actually show — beyond the headline symptom?
5. When exactly did the symptom start, and does it correlate with a specific recent change?
6. Have you collected any profiling data yet? (heap dump, flame graph, query plans, etc.)
7. What can't change? (libs, APIs, time box, compat constraints)
8. How will you verify a fix works? (test, observable output, metric)
```

**[2] Balanced — questions to ask:**
```
1. What have you already tried?
2. What have you assumed is fine — but never actually checked?
3. Long-term fix, MVP, POC, or test? (shapes how deep to go)
4. How will you know it's fixed?
```

**[3] Wild — questions to ask:**
```
1. What have you assumed is definitely NOT the problem?
2. Where does the error appear vs. where you think it actually originates?
3. If you couldn't touch the failing component at all, what would you do?
4. What would solving this with data (not code) look like?
```

**[4] Workaround — questions to ask:**
```
1. What specifically is blocking you right now?
2. How long does the bypass need to last?
3. What breaks or accumulates as debt if it stays in?
```

Cold user → one question per message. Engaged user → batch all questions for the chosen path.

---

### Phase 4 — Dead-ends audit (Ground / Balanced / Wild paths only)

Locate what was tried. Build the dead-ends list. Stop there.

Use `git log -10 --oneline`, `git diff HEAD~3`, `git grep` for history. Grep/Glob for recent changes. Read specific file ranges only — never full files.

No prior fix attempt found → `No stall yet. Use normal debugging first.`
Data-loss risk found in history → state it in plain English before the dead-ends table.

---

### Context block output (before any ideation)

```
Choice: Ground | Balanced | Wild | Workaround
Goal: <one line>
Horizon: long-term | MVP | POC | test | workaround
Constraints: <list>
Unverified assumptions: <list>
Success signal: <one line>
Ruled out:
- <area> — <attempted fix> — <why it failed>
Still unknown:
- <open question>
```

Route directly to the chosen agent after this block is complete.

## When

Trigger only after normal debugging stalled:
- 2+ fix attempts on the same bug failed
- User says "still broken", "already tried", "same error", or "going in circles"
- Agent about to suggest a variant of something already ruled out

Not on first attempt. Straight-line reasoning first.

## Rules

**Confidence calibration — always separate these three layers before ideating:**

| Layer | What it is | How to label it |
| --- | --- | --- |
| **Facts** | What logs, metrics, and traces literally show | State as-is — no hedging needed |
| **Inferences** | Conclusions well-supported by the facts | Label: *high-confidence* or *medium-confidence* |
| **Speculation** | Possible explanations not yet verified by evidence | Label: *unverified hypothesis* |

Never present an inference or speculation as a fact. If a conclusion can't be traced back to an observed signal, it must be labeled.

State dead ends first — one line, what's ruled out and why. Never repeat a ruled-out idea.

Always output both tiers, always labeled, never blended.

Pattern: `Goal: [horizon]. Facts: [observed]. Inferences: [confidence-labeled]. Ruled out: [x]. Tier 1: [grounded]. Tier 2: [balanced]. Tier 3: [wild].`

## Tiers

| Tier | Agent | What | Length |
| --- | --- | --- | --- |
| Tier 1 — Ground | `lateralus-ideator-ground` | 3-5 concrete testable causes outside the obvious category. Cache, encoding, timezone, race, stale build, dep drift, inverted baseline, adjacent component. Depth calibrated to horizon. | One line naming it + one line on how to test it. |
| Tier 2 — Balanced | `lateralus-ideator-balanced` | 3-5 hypotheses that question assumptions while staying loosely testable. Bridge between grounded and speculative. | Hypothesis + assumption challenged + loose test signal. |
| Tier 3 — Wild | `lateralus-ideator-wild` | 3-5 speculative reframes. Not literal fixes — state this up front. Goal: jolt a new association. Question an ignored premise, solve with data not code, distrust error location, unify two bugs, question whether the problem needs solving given horizon. | 1-2 sentences each. Don't over-justify. |

## Boundaries

No real fix attempt yet → skip. Normal debugging first.
Don't fire twice on same stall without new info.
User picks a direction → investigate before generating a fresh batch.
End every ideation pass by asking which direction to explore next.
