---
name: "focused-fix"
description: "Use when the user asks to fix, debug, or make a specific feature/module/area work end-to-end. Triggers: 'make X work', 'fix the Y feature', 'the Z module is broken', 'focus on [area]'. Not for quick single-bug fixes — this is for systematic deep-dive repair across all files and dependencies."
---

# Focused Fix — Deep-Dive Feature Repair

## When to Use

Activate when the user asks to fix, debug, or make a specific feature/module/area work. Key triggers:
- "make X work"
- "fix the Y feature"
- "the Z module is broken"
- "focus on [area]"
- "this feature needs to work properly"

This is NOT for quick single-bug fixes (use systematic-debugging for that). This is for when an entire feature or module needs systematic repair — tracing every dependency, reading logs, checking tests, mapping the full dependency graph.

```dot
digraph when_to_use {
    "User reports feature broken" [shape=diamond];
    "Single bug or symptom?" [shape=diamond];
    "Use systematic-debugging" [shape=box];
    "Entire feature/module needs repair?" [shape=diamond];
    "Use focused-fix" [shape=box];
    "Something else" [shape=box];

    "User reports feature broken" -> "Single bug or symptom?";
    "Single bug or symptom?" -> "Use systematic-debugging" [label="yes"];
    "Single bug or symptom?" -> "Entire feature/module needs repair?" [label="no"];
    "Entire feature/module needs repair?" -> "Use focused-fix" [label="yes"];
    "Entire feature/module needs repair?" -> "Something else" [label="no"];
}
```

## The Iron Law

```
NO FIXES WITHOUT COMPLETING SCOPE → TRACE → DIAGNOSE FIRST
```

If you haven't finished Phase 3, you cannot propose fixes. Period.

**Violating the letter of these phases is violating the spirit of focused repair.**

## Protocol — STRICTLY follow these 5 phases IN ORDER

```dot
digraph phases {
    rankdir=LR;
    SCOPE [shape=box, label="Phase 1\nSCOPE"];
    TRACE [shape=box, label="Phase 2\nTRACE"];
    DIAGNOSE [shape=box, label="Phase 3\nDIAGNOSE"];
    FIX [shape=box, label="Phase 4\nFIX"];
    VERIFY [shape=box, label="Phase 5\nVERIFY"];

    SCOPE -> TRACE -> DIAGNOSE -> FIX -> VERIFY;
    FIX -> DIAGNOSE [label="fix broke\nsomething else"];
    FIX -> ESCALATE [label="3+ fixes\ncreate new issues"];
    ESCALATE [shape=doubleoctagon, label="STOP\nQuestion Architecture\nDiscuss with User"];
}
```

### Phase 1: SCOPE — Map the Feature Boundary

Before touching any code, understand the full scope of the feature.

1. Ask the user: "Which feature/folder should I focus on?" if not already clear
2. Identify the PRIMARY folder/files for this feature
3. Map EVERY file in that folder — read each one, understand its purpose
4. Create a feature manifest:

```
FEATURE SCOPE:
  Primary path: src/features/auth/
  Entry points: [files that are imported by other parts of the app]
  Internal files: [files only used within this feature]
  Total files: N
  Total lines: N
```

### Phase 2: TRACE — Map All Dependencies (Inside AND Outside)

Trace every connection this feature has to the rest of the codebase.

**INBOUND (what this feature imports):**
1. For every import statement in every file in the feature folder:
   - Trace it to its source
   - Verify the source file exists
   - Verify the imported entity (function, type, component) exists and is exported
   - Check if the types/signatures match what the feature expects
2. Check for:
   - Environment variables used (grep for process.env, import.meta.env, os.environ, etc.)
   - Config files referenced
   - Database models/schemas used
   - API endpoints called
   - Third-party packages imported

**OUTBOUND (what imports this feature):**
1. Search the entire codebase for imports from this feature folder
2. For each consumer:
   - Verify they're importing entities that actually exist
   - Check if they're using the correct API/interface
   - Note if any consumers are using deprecated patterns

Output format:
```
DEPENDENCY MAP:
  Inbound (this feature depends on):
    src/lib/db.ts → used in auth/repository.ts (getUserById, createUser)
    src/lib/jwt.ts → used in auth/service.ts (signToken, verifyToken)
    @prisma/client → used in auth/repository.ts
    process.env.JWT_SECRET → used in auth/service.ts
    process.env.DATABASE_URL → used via prisma

  Outbound (depends on this feature):
    src/app/api/login/route.ts → imports { login } from auth/service
    src/app/api/register/route.ts → imports { register } from auth/service
    src/middleware.ts → imports { verifyToken } from auth/service

  Env vars required: JWT_SECRET, DATABASE_URL
  Config files: prisma/schema.prisma (User model)
```

### Phase 3: DIAGNOSE — Find Every Issue

Systematically check for problems. Run ALL of these checks:

**CODE QUALITY:**
- [ ] Every import resolves to a real file/export
- [ ] No circular dependencies within the feature
- [ ] Types are consistent across boundaries (no `any` at interfaces)
- [ ] Error handling exists for all async operations
- [ ] No TODO/FIXME/HACK comments indicating known issues

**RUNTIME:**
- [ ] All required environment variables are set (check .env)
- [ ] Database migrations are up to date (if applicable)
- [ ] API endpoints return expected shapes
- [ ] No hardcoded values that should be configurable

**TESTS:**
- [ ] Run ALL tests related to this feature: find them by searching for imports from the feature folder
- [ ] Record every failure with full error output
- [ ] Check test coverage — are there untested code paths?

**LOGS & ERRORS:**
- [ ] Search for any log files, error reports, or Sentry-style error tracking
- [ ] Check git log for recent changes to this feature: `git log --oneline -20 -- <feature-path>`
- [ ] Check if any recent commits might have broken something: `git log --oneline -5 --all -- <files that this feature depends on>`

**CONFIGURATION:**
- [ ] Verify all config files this feature depends on are valid
- [ ] Check for mismatches between development and production configs
- [ ] Verify third-party service credentials are valid (if testable)

**ROOT-CAUSE CONFIRMATION:**
For each CRITICAL issue found, confirm root cause before adding it to the fix list:
- State clearly: "I think X is the root cause because Y"
- Trace the data/control flow backward to verify — don't trust surface-level symptoms
- If the issue spans multiple components, add diagnostic logging at each boundary to identify which layer fails
- **REQUIRED SUB-SKILL:** For complex bugs found during diagnosis, apply `superpowers:systematic-debugging` Phase 1 (Root Cause Investigation) to confirm before proceeding

**RISK LABELING:**
Assign each issue a risk label:

| Risk | Criteria |
|---|---|
| HIGH | Public API surface / breaking interface contract / DB schema / auth or security logic / widely imported module (>3 callers) / git hotspot |
| MED | Internal module with tests / shared utility / config with runtime impact / internal callers of changed functions |
| LOW | Leaf module / isolated file / test-only change / single-purpose helper with no callers |

Output format:
```
DIAGNOSIS REPORT:
  Issues found: N

  CRITICAL:
    1. [HIGH] [file:line] — description of issue. Root cause: [confirmed explanation]
    2. [HIGH] [file:line] — description of issue. Root cause: [confirmed explanation]

  WARNINGS:
    1. [MED] [file:line] — description of issue
    2. [LOW] [file:line] — description of issue

  TESTS:
    Ran: N tests
    Passed: N
    Failed: N
    [list each failure with one-line summary]
```

### Phase 4: FIX — Repair Everything Systematically

Fix issues in this EXACT order:

1. **DEPENDENCIES FIRST** — fix broken imports, missing packages, wrong versions
2. **TYPES SECOND** — fix type mismatches at feature boundaries
3. **LOGIC THIRD** — fix actual business logic bugs
4. **TESTS FOURTH** — fix or create tests for each fix
5. **INTEGRATION LAST** — verify the feature works end-to-end with its consumers

Rules:
- Fix ONE issue at a time
- After each fix, run the related test to confirm it works
- If a fix breaks something else, STOP and re-evaluate (go back to DIAGNOSE)
- Keep a running log of every change made
- Never change code outside the feature folder without explicitly stating why
- Fix HIGH-risk issues before MED, MED before LOW

**ESCALATION RULE — 3-Strike Architecture Check:**
If 3+ fixes in this phase create NEW issues (not pre-existing ones), STOP immediately.

This pattern indicates an architectural problem, not a bug collection:
- Each fix reveals new shared state / coupling / problem in a different place
- Fixes require "massive refactoring" to implement
- Each fix creates new symptoms elsewhere

**Action:** Stop fixing. Tell the user: "3+ fixes have cascaded into new issues. This suggests the feature's architecture may need rethinking, not patching. Here's what I've found: [summary]. Should we continue fixing symptoms or discuss restructuring?"

Do NOT attempt fix #4 without this discussion.

Output after each fix:
```
FIX #1:
  File: auth/service.ts:45
  Issue: signToken called with wrong argument order
  Change: swapped (expiresIn, payload) to (payload, expiresIn)
  Test: auth.test.ts → PASSES
```

### Phase 5: VERIFY — Confirm Everything Works

After all fixes are applied:

1. Run ALL tests in the feature folder — every single one must pass
2. Run ALL tests in files that IMPORT from this feature — must pass
3. Run the full test suite if available — check for regressions
4. If the feature has a UI, describe how to manually verify it
5. Summarize all changes made

Final output:
```
FOCUSED FIX COMPLETE:
  Feature: auth
  Files changed: 4
  Total fixes: 7
  Tests: 23/23 passing
  Regressions: 0

  Changes:
    1. auth/service.ts — fixed token signing argument order
    2. auth/repository.ts — added null check for user lookup
    3. auth/middleware.ts — fixed async error handling
    4. auth/types.ts — aligned UserResponse type with actual DB schema

  Consumers verified:
    - src/app/api/login/route.ts ✅
    - src/app/api/register/route.ts ✅
    - src/middleware.ts ✅
```

## Red Flags — STOP and Return to Current Phase

If you catch yourself thinking any of these, you are skipping phases:

- "I can see the bug, let me just fix it" → STOP. You haven't traced dependencies yet.
- "Scoping is overkill, it's obviously just this file" → STOP. That's always wrong for feature-level fixes.
- "I'll map dependencies after I fix the obvious stuff" → STOP. You'll miss root causes.
- "The user said fix X, so I only need to look at X" → STOP. Features have dependencies.
- "Tests are passing so I'm done" → STOP. Did you run consumer tests too?
- "I don't need to check env vars for this" → STOP. Config issues masquerade as code bugs.
- "One more fix should do it" (after 2+ cascading failures) → STOP. Escalate.
- "I'll skip the diagnosis report, the fixes are obvious" → STOP. Write it down.

**ALL of these mean: Return to the phase you're supposed to be in.**

## Common Rationalizations

| Excuse | Reality |
|---|---|
| "The feature is small, I don't need all 5 phases" | Small features have dependencies too. Phases 1-2 take minutes for small features — do them. |
| "I already know this codebase" | Knowledge decays. Trace the actual imports, don't rely on memory. |
| "The user wants speed, not process" | Skipping phases causes rework. Systematic is faster than thrashing. |
| "Only one file is broken" | If only one file were broken, the user would say "fix this bug", not "make the feature work." |
| "I fixed the tests, so it works" | Tests can pass while consumers are broken. Verify Phase 5 fully. |
| "The dependency map is too big to trace" | Then the feature is too big to fix without tracing. That's exactly why you need it. |
| "Root cause is obvious, I don't need to confirm" | "Obvious" root causes are wrong 40% of the time. Confirm with evidence. |
| "3 cascading failures is normal for a big fix" | 3 cascading failures means you're patching symptoms of an architectural problem. |

## Anti-Patterns — NEVER do these

| Anti-Pattern | Why It's Wrong |
|---|---|
| Starting to fix code before mapping all dependencies | You'll miss root causes and create whack-a-mole fixes |
| Fixing only the file the user mentioned | Related files likely have issues too |
| Ignoring environment variables and configuration | Many "code bugs" are actually config issues |
| Skipping the test run phase | You can't verify fixes without running tests |
| Making changes outside the feature folder without explaining why | Unexpected side effects confuse the user |
| Fixing symptoms in consumer files instead of root cause in feature | Band-aids that break when the next consumer appears |
| Declaring "done" without running verification tests | Untested fixes are unverified fixes |
| Changing the public API without updating all consumers | Breaks everything that depends on the feature |

## Related Skills

- **`superpowers:systematic-debugging`** — Use within Phase 3 for root-cause tracing of individual complex bugs
- **`superpowers:verification-before-completion`** — Use within Phase 5 before claiming the feature is fixed
- **`scope`** — If you need to understand blast radius before starting, run scope first then focused-fix

## Quick Reference

| Phase | Key Action | Output |
|---|---|---|
| SCOPE | Read every file, map entry points | Feature manifest |
| TRACE | Map inbound + outbound dependencies | Dependency map |
| DIAGNOSE | Check code, runtime, tests, logs, config | Diagnosis report |
| FIX | Fix in order: deps → types → logic → tests → integration | Fix log per issue |
| VERIFY | Run all tests, check consumers, summarize | Completion report |
