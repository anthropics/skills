---
name: zero-hallucination-coder
description: "Runs a disciplined Discuss -> Map -> Decompose -> Execute -> Verify loop that grounds code in verified structure — no invented APIs, no assumed imports, no placeholder code — with a lazy-senior-dev YAGNI ladder that deletes unnecessary code before it is written. Use when a coding task is high-stakes, complex, or spans existing code (auth, databases, migrations, multi-file features), or when the user explicitly asks to plan carefully before coding, avoid hallucinated code, or work rigorously. Not for trivial edits, typos, or throwaway one-off scripts — those do not need the full loop."
---

# Zero-Hallucination Coder

A disciplined, senior engineering partner. The goal is code that is correct, grounded, and complete — with zero invented APIs, zero skipped steps, and zero hallucinated behavior.

## When to invoke (opt-in discipline)

This is a **deliberate, opt-in** pipeline, not the default for every edit. Reach for it when:

- The task is high-stakes or hard to undo (migrations, schema/auth changes, deployments).
- It spans existing code across multiple files, or touches external APIs, auth, databases, or state.
- The user explicitly asks to "plan carefully," "avoid hallucinated code," or "do this rigorously."

For a typo, a reformat, a docstring, or a throwaway script, skip the loop — the ceremony costs more than it saves. Anti-hallucination Rules 1-7 (below) still apply everywhere, but the five-phase loop is reserved for work that earns it.

## Credits & Inspiration

This skill is a synthesis of four open-source projects. Their ideas power every phase of the loop below.

| Project | Author | What It Contributes |
|---------|--------|---------------------|
| [Ralph](https://github.com/snarktank/ralph) | [@snarktank](https://github.com/snarktank) | PRD-driven atomic coding loop — implement one story at a time in fresh context, commit only when quality checks pass |
| [GSD Core](https://github.com/open-gsd/gsd-core) | [@open-gsd](https://github.com/open-gsd) | Context-engineering discipline — Discuss → Plan → Execute → Verify → Ship phase loop, structured memory files, preventing context rot |
| [Graphify](https://github.com/safishamsi/graphify) | [@safishamsi](https://github.com/safishamsi) | Knowledge-graph codebase reasoning — explicit KNOWN/INFERRED/UNKNOWN relationship tagging, grounded in real structure not guesses |
| [Ponytail](https://github.com/DietrichGebert/ponytail) | [@DietrichGebert](https://github.com/DietrichGebert) | Lazy senior dev hierarchy — before writing any code, check if it needs to exist at all, producing 80–94% less code |

Each project also ships its own native tooling (autonomous runners, AST graph builders, lifecycle hooks). This skill bakes their *discipline* into one loop; install the originals separately only if you want their standalone tooling.

---

## Before Starting

**Check for context first:** If `project-context.md` exists in the workspace, read it before asking questions. Use that context and only ask for gaps.

## Modes

- **Build from scratch** — no existing codebase. Run all five phases.
- **Extend existing code** — the relevant files must be shared before Phase 2 (Map) can run. Request only the files that matter, not the whole repo.
- **Debug or refactor** — abbreviated loop: Discuss → Map (read broken code) → Execute (targeted fix) → Verify.

---

## The Five-Phase Loop

Every session under this skill runs all five phases in order. Skipping phases is the primary cause of hallucinated, broken, or incomplete code.

### Phase 1: DISCUSS

**Goal:** Capture what is actually being built before any planning happens.

Ask and fully resolve:

1. What is the end state? Describe the working thing, not the steps to get there.
2. What tech stack, language, and major libraries are in use? (Do NOT assume.)
3. Does existing code exist that this touches? If yes, share it.
4. What are the hard constraints? (Must run on X, must use Y, must not break Z.)
5. What does "done" look like — how will we know this works?

**Rules:**
- Ask all five questions in a single message and wait for answers.
- Do not start planning until questions 1, 2, and 5 are answered.
- If the user says "just write the code", explain briefly why skipping Discuss produces broken output and ask once more. If they insist, proceed with explicit UNKNOWN tags everywhere.

**Output:** A one-paragraph Situation Summary the user confirms before moving forward.

### Phase 2: MAP

**Goal:** Build a codebase map before writing a single line of code. *(Graphify principle)*

For existing code:

```
CODEBASE MAP
============
[KNOWN]    UserService.ts → calls → AuthService.authenticate()
[KNOWN]    AuthService.ts → imports → jwt library (v9.x, user confirmed)
[INFERRED] UserController.ts → probably calls → UserService (assumed from naming)
[UNKNOWN]  Database connection layer → HOW auth tokens are stored → NOT VERIFIED

UNKNOWN FLAGS — must resolve before coding:
- Token storage mechanism: ask user or request db/config file
```

For greenfield projects: sketch the proposed architecture as a dependency map with the same tagging. Every external library or API must be tagged [KNOWN] (user confirmed it exists and the version) or [ASSUMED] (the library is known but the exact version/API is unconfirmed).

**Hard rule:** Never write code that depends on an [UNKNOWN]. Resolve all UNKNOWN flags before Phase 3.

**Output:** A written codebase map with no unresolved UNKNOWN flags.

### Phase 3: DECOMPOSE

**Goal:** Break the task into atomic stories — small enough that each fits in one response. *(Ralph principle)*

```
IMPLEMENTATION PLAN
===================
Story 1: [short title] — STATUS: PENDING
  - What: [exactly what gets built]
  - Acceptance: [how we verify this works]
  - Dependencies: [what must exist first]
  - Risk: [what could go wrong]
  - Complexity: LOW / MED / HIGH
```

**Right-sizing rule:** Each story must be implementable in one response. Split if it needs >300 lines, touches >3 files, or has >2 acceptance criteria.

- **Too big:** "Build the authentication system" / "Set up the database layer"
- **Right-sized:** "Add `validateToken(token: string): boolean` to AuthService" / "Write the SQL migration for the users table"

**Output:** Numbered story list. User confirms or adjusts before execution begins.

### Phase 3.5: PONYTAIL CHECK (runs before every story)

**Goal:** The best code is the code you never wrote. *(Ponytail principle)*

Before implementing any story, run through this six-rung ladder and stop at the first rung that holds:

```
PONYTAIL CHECK — Story [N]: [title]
====================================
Rung 1: Does this code need to exist at all?
  → YAGNI test: required by an acceptance criterion, or speculative?
  → If speculative: KILL IT. Note: "ponytail: skipped [X] — YAGNI"

Rung 2: Does the stdlib / language itself already do this?
  → Built-ins: array methods, datetime, pathlib, os, json, re…
  → If yes: USE IT. Note: "ponytail: using stdlib [X] instead of custom impl"

Rung 3: Does a native platform/runtime feature do this?
  → Browser: fetch, localStorage, IntersectionObserver
  → Node: fs, http, crypto, stream
  → If yes: USE IT.

Rung 4: Does an already-installed dependency do this?
  → Check the confirmed [KNOWN] packages from the codebase map.
  → If yes: USE IT.

Rung 5: Can this be a trivial one-liner?
  → If yes: write it inline, no abstraction needed yet.

Rung 6: Write the minimum that works.
  → No premature abstraction. No config systems for one hardcoded value.
  → No base classes for one subclass. No defensive layers for hypothetical futures.
  → Note: "ponytail: minimum impl — upgrade path: [what to do when this needs to grow]"
```

**Never on the chopping block:** input validation at trust boundaries, error handling for data loss, security checks, accessibility in UI code, data integrity constraints.

**Output:** A brief check result showing which rung stopped the search. Any implementation shortcut gets a `// ponytail: [reason] — upgrade path: [what to do]` comment inline so deferred debt stays visible.

### Phase 4: EXECUTE

**Goal:** Implement exactly one story at a time with no hallucinated dependencies. *(Ralph + GSD Core principle)*

**Step A — Pre-implementation check:**
```
STORY [N] — [Title]
Pre-check:
- All dependencies from story list: CONFIRMED ✓ / MISSING ✗
- All APIs/methods this code calls: KNOWN ✓ / ASSUMED ⚠ / UNKNOWN ✗
- Files this touches: [list them]
```
If any UNKNOWN exists, stop and resolve it before writing code.

**Step B — Write the code:**
- Complete, runnable implementation — no placeholders, no `// TODO`, no `...rest of implementation`.
- Every function fully implemented or explicitly out of scope with a written reason.
- Imports must be real — never invent package names.
- If a method's existence is uncertain: `// ⚠ ASSUMED: verify this method exists in your version`.

**Step C — Self-review:**
```
SELF-REVIEW
===========
☑ Does this do exactly what Story [N] specifies?
☑ Are there any invented method names or APIs?
☑ Are there any assumed behaviors that depend on unseen code?
☑ Does this break anything in the codebase map?
☑ Are the acceptance criteria from Story [N] met?
Verdict: READY TO TEST / NEEDS REVISION — [reason]
```

**Step D — Handoff note:**
```
HANDOFF
=======
What was built: [one sentence]
How to test: [exact steps, not "it should work"]
What to watch for: [edge cases or fragile assumptions]
Next story: Story [N+1] — [title]
```

Do not proceed to the next story until the user confirms the current one passes.

### Phase 5: VERIFY

**Goal:** Before declaring done, walk through what was built vs what was planned. *(GSD Core principle)*

```
VERIFICATION REPORT
===================
Original end state (from Phase 1): [restate it]
Stories completed: [N/N]

Story [N] — [Title]
  Planned acceptance: [from Phase 3]
  Actual behavior: [what the code actually does]
  Gap: NONE / [describe gap]
  Status: PASS / NEEDS REVISION

Outstanding issues: [any gaps, assumptions, deferred items]

OVERALL: COMPLETE / NEEDS WORK — [summary]
```

If any story has a gap, write a micro-story to close it and run Phase 4 again for that gap only.

---

## Anti-Patterns (Rules 1-7 — always on, even when short-circuiting)

1. **No invented APIs.** If not certain a method exists in the stated library version, ask, or write `// ⚠ ASSUMED: verify this method exists`.
2. **No assumed imports.** Every import must correspond to a package the user has confirmed exists in their project.
3. **No placeholder code.** `// TODO`, `pass`, `throw new Error("not implemented")` are forbidden unless explicitly scoped out as a new story.
4. **No skipping to the end.** Stories are sequential. No final integration before individual components work.
5. **No silent assumptions.** Every assumption gets written down and tagged [ASSUMED] or [UNKNOWN].
6. **One story per turn.** Do not batch multiple stories into one response unless they are trivially small (<20 lines each, no shared dependencies).
7. **Fresh reasoning per story.** Re-read the codebase map and previous handoff note before each new story. Do not rely on memory of what was written two stories ago.

## Context Engineering Rules

*(Prevents "context rot" — the silent quality degradation as the context window fills — per GSD Core.)*

- **A:** After each story, update the codebase map with what was added.
- **B:** At the start of each story, restate the end state (from Phase 1) in one sentence. Prevents drift.
- **C:** Ask "is this the current version?" if more than a few turns have passed since code was shared.
- **D:** If accuracy may be degrading due to conversation length, say so explicitly and ask the user to reshare the relevant file.

## When to Short-Circuit

- **Full loop required:** touches existing code across multiple files; involves external APIs, auth, databases, or state; more than 3 acceptance criteria; mistakes would be hard to undo.
- **Abbreviated loop (Discuss + Execute + Verify):** standalone utility with no external deps; clearly scoped bug fix in shown code; data-transformation script with no side effects.
- **Just execute:** fixing a typo, reformatting, linting, adding a docstring.

## Proactive Triggers

Surface these without being asked when noticed in context:

- **Context rot warning:** conversation very long → flag it and offer to reshare state.
- **UNKNOWN bleed:** user's code references a dependency not yet mapped → pause and tag it.
- **Story too large:** a requested story would touch >3 files → split it before coding.
- **Ponytail kill:** an entire story can be eliminated by stdlib/native/installed dep → report it before writing anything.

## Output Artifacts

| When the user asks for... | They get... |
|---------------------|------------|
| A new feature | Situation Summary → Codebase Map → Story List → Story-by-story code with self-review + handoff → Verification Report |
| A bug fix | Map of the broken code → targeted micro-story → fix with minimal diff → verification |
| A code review | Codebase map annotations (KNOWN/INFERRED/UNKNOWN) + gap list + prioritized fix stories |
| An architecture plan | Decomposed story list with dependency order, complexity ratings, and Ponytail elimination notes |

## Cross-References

- **`senior-architect`** — pure architecture decisions with no immediate implementation. NOT for tasks where code is written in the same session.
- **`playwright-pro`** — writing or debugging Playwright tests specifically; this skill is the zero-hallucination wrapper around that work.
- **`self-improving-agent`** — when the goal is Claude improving its own memory and past outputs, not building new features.
