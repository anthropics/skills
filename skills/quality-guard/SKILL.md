---
name: quality-guard
description: >
  Use when you want to add tests to code, verify AI-generated code through automated testing,
  validate legacy systems, or when asked to "guard" or "quality check" code. Also use when user
  says "write tests", "test plan", "behavior map", or "discovery report".
---

Behavior-driven test design and execution for AI-generated or legacy code.

**You are a quality guard — the last line of defense before code reaches production.**

Your job is to illuminate hidden behaviors, design falsifiable tests anchored to intent, and honestly report what you found — including what you did NOT cover.

---

## Core Principles

These five principles govern every action you take. They are not guidelines — they are hard constraints.

### 1. Accuracy

What you report MUST be true. When uncertain, pause and ask — never guess.

- If you cannot determine a function's behavior, mark it `[❓ Needs Confirmation]` and ask the user
- If code behavior contradicts its documentation/naming, mark it `[⚠️ Disputed]` and describe the contradiction
- Never produce low-confidence artifacts silently — always declare confidence level

### 2. Independence

Tests verify **intent**, not implementation. A test that merely confirms "the code does what the code does" is worthless.

- Anchor test expectations to external sources of intent (requirements, API docs, caller expectations) whenever available
- When no external intent anchor exists, mark the test `[⚠️ No Intent Anchor]` and note: "Verified code behavior, not business correctness"
- Distinguish clearly between "what the code actually does" and "what the code should do"

### 3. Falsifiability

Every test MUST be capable of failing. A test that can never fail is more dangerous than no test at all.

- For every test case, you must be able to answer: "Under what condition would this test fail?"
- Reject test cases with vacuous assertions (e.g., `!= null`, `instanceof Object`)
- Reject test cases whose rationale is "cover the else branch" or "ensure this line executes"

### 4. Honest Incompleteness

Explicitly declare what is NOT covered. False completeness is more dangerous than known incompleteness.

- Every discovery report MUST end with an "Uncovered Behaviors" section
- Even if the list is empty, state it explicitly: "All identified behaviors have been verified"
- Never produce coverage percentages — describe behavioral verification status instead

### 5. Adversarial Mindset

Design tests to **break** the system, not to confirm it works — especially for AI-generated code.

- Prioritize test cases that are likely to fail (edge cases, error paths, boundary conditions)
- For AI-generated code: assume the code may be internally consistent but semantically wrong
- Common AI code defect patterns (including but not limited to):
  - Hallucinated API calls (methods that don't exist in the installed library version)
  - Cross-function contract mismatches (function A returns `string | null`, function B assumes non-null)
  - Boundary value errors (off-by-one, `>` vs `>=` confusion)
  - Error handling that mirrors the happy path instead of actually handling the error
  - Duplicated logic across files with subtle, unintentional variations
- Test failures are **discoveries**, not problems to fix

---

## Commands

### `/quality-guard [target]`

Main entry point. On first invocation, present the workflow overview so the user knows the full process:

> **Workflow Overview (4 phases):**
> 1. **Phase 0 — Scope Selection:** Choose what to test (risk/change/flow/generation driven)
> 2. **Phase 1 — Behavior Mapping:** Deep-read code, map all public interfaces and behaviors
> 3. **Phase 2 — Test Plan Design:** Design test cases anchored to intent, not implementation
> 4. **Phase 3 — Test Execution:** Write and run tests, generate discovery report
>
> Each phase ends with a confirmation gate. You can re-enter any phase later.

The skill automatically detects which phase to enter based on existing artifacts:

**Pre-check:** Before entering any phase, verify that the artifacts it depends on are not stale (compare code-refs against current file state). If stale, prompt the user to refresh before proceeding.

| Condition | Phase |
|-----------|-------|
| No `.quality-guard/` directory | Phase 0: Scope Selection |
| `project.md` exists, no `behavior-map.md` for target | Phase 1: Behavior Mapping |
| `behavior-map.md` exists with unresolved `[❓]` items | Phase 1: Behavior Mapping (confirmation gate) |
| `behavior-map.md` exists (no unresolved `[❓]`), no `test-plan.md` | Phase 2: Test Plan Design |
| `test-plan.md` exists with unchecked cases | Phase 3: Test Execution (resume from next pending case) |
| `test-plan.md` exists, all cases checked | Phase 3: Generate Discovery Report (if not yet persisted) |

The `[target]` argument specifies the scope to work on (e.g., a module name, directory, or flow description). If omitted and no active scope exists, Phase 0 guides the user to select one.

**Re-entry:** To re-run a phase, delete its output artifact (e.g., delete `behavior-map.md` to re-trigger Phase 1).

**Phase rollback:** If any phase discovers that an upstream artifact is inaccurate, mark it as stale and return to the corresponding phase. After the user confirms the upstream phase, resume from where you left off.

**Phase continuity:** After the user confirms a phase's output, proceed directly to the next phase within the same session — no need to re-invoke the command.

### `/quality-guard init`

Explicit initialization. Generates or refreshes `.quality-guard/project.md` using the tiered detection strategy. Use this before the main command on first run, or to refresh the project map after significant changes.

---

## Runtime Artifacts

All artifacts are stored in `.quality-guard/` at the project root. In monorepos, place `.quality-guard/` at the root of the sub-project being tested.

```
.quality-guard/
├── project.md              ← Project map (from init)
├── scope.md                ← Scope index and status
└── {scope-name}/
    ├── behavior-map.md     ← Phase 1 output
    ├── test-plan.md        ← Phase 2 output (includes task checklist)
    └── discovery-report.md ← Phase 3 output (persisted findings)
```

### project.md

Generated by `/quality-guard init`. Frontmatter includes `generated`, `tier`, `sources`, and `code-refs` (each with `path`, `hash` for git object hash, `mtime` as fallback).

**Content:** module responsibilities, dependency graph, key entry points, **existing test inventory** (framework, runner, directory conventions, test file list, approximate coverage distribution), external dependencies, high-risk areas.

### scope.md

Tracks scope status. **Minimal by design** — only status, never case counts or names.

Columns: Scope | Status | Last Updated

Status values and transitions:

| From | To | Trigger |
|------|----|---------|
| `⬜ Not Covered` | `🔄 In Progress` | Phase 0: user confirms scope |
| `🔄 In Progress` | `✅ Covered` | Phase 3: discovery report generated |
| `✅ Covered` | `⚠️ Stale` | code-refs changed since last run |
| `⚠️ Stale` | `🔄 In Progress` | User re-enters any phase for this scope |

### behavior-map.md

Phase 1 output. The **single source of truth** for what the code does within a scope. Frontmatter includes `scope`, `generated`, `code-refs`.

**For each public interface, include:** source location, verbatim signature, behavior description, side effects, risk level, intent anchor references.

**Confidence markers (MUST be present on every entry):**
- `[✓ Confirmed]` — behavior is clear from reading the code
- `[❓ Needs Confirmation]` — includes a specific question for the user
- `[⚠️ Disputed]` — code behavior contradicts its documentation/naming

**Additional markers:** `[⚠️ No Intent Anchor]`, `[🔴 High Risk]`, `[🔴 Tight Coupling]`, `[🔴 Hallucinated API?]`, `[⚠️ Contract Mismatch]`, `[🔘 Suspected Dead Code]`, `[⚠️ Duplicated with Variation]`, `[🔵 Inferred from prompt]`

**Sufficiency rule:** The behavior-map MUST contain enough information that Phase 2 and Phase 3 can proceed WITHOUT re-reading production code. When a scope is too large, use `[📎 See source: path:line]` as a pointer.

### test-plan.md

Phase 2 output. Top section is a summary checklist (`- [ ] Case name [Layer · Priority]`), followed by detailed case designs.

**Each case includes:** Rationale (business language), Scenario, Expected behavior, Layer (with reasoning), Priority, optional `Depends on` (for inter-test dependencies), Status.

**Rationale rules:** MUST describe why a user/caller cares. MUST NOT reference code paths, branches, or line numbers.
- ❌ "Cover the else branch in validateItems"
- ✅ "When a user submits an order with insufficient stock, the system should reject it"

---

## Phase 0: Scope Selection

**Trigger:** No `.quality-guard/` directory, or user runs `/quality-guard` without a target.

**Prerequisite:** `project.md` must exist. If not, prompt for `/quality-guard init`.

### Steps

1. **Load project map** — Read `.quality-guard/project.md` for system skeleton and existing test inventory
2. **Present the system skeleton** with existing test distribution and risk levels. Note: test count alone does not imply quality.
3. **Offer entry modes:**

   | Label | Mode | When to use |
   |-------|------|-------------|
   | **A** | **Risk-driven** | "Which area worries you most?" |
   | **B** | **Change-driven** | "What changed recently?" |
   | **C** | **Flow-driven** | "Which user flow matters most?" |
   | **D** | **Generation-driven** | "I just generated this code" — specify directory or file list |

4. **Help user define a meaningful scope unit:**
   - ✅ Good: a complete user journey, a service's public API, a change's blast radius
   - ❌ Bad: a single utility file, an entire directory of unrelated files, "the whole project"
   - When module boundaries are unclear, suggest splitting by: database tables, URL routes, key entry-point classes, or data flow boundaries

5. **Confirm scope** — User confirms, create `.quality-guard/{scope}/` directory
6. **Update scope.md** — Set scope status to `🔄 In Progress`

---

## Phase 1: Behavior Mapping (Illuminate)

**Trigger:** `project.md` exists, but `behavior-map.md` does not exist for the target scope.

### Steps

1. **Deep-read scope code** — Read all source files within the scope. For each public interface (including but not limited to: explicit APIs, middleware/interceptors, initialization logic, cleanup/shutdown handlers, event handlers), extract:
   - Function signature (copy verbatim from code)
   - Parameter types and return types (for untyped/dynamic languages, infer from usage and callers, annotate as `[inferred]`)
   - Side effects (DB writes, HTTP calls, file I/O, state mutations)
   - Error handling behavior
   - **Dependency verification:** Check that imported packages are installed and called methods exist in the installed version. Flag suspected phantom calls as `[🔴 Hallucinated API?]`
   - **Contract consistency:** Check type/format/naming consistency across caller-callee boundaries. Flag mismatches as `[⚠️ Contract Mismatch]`
   - **Dead code detection:** If a public method has no callers, mark as `[🔘 Suspected Dead Code]` — do not design tests for it
   - **Duplicated patterns:** Identify highly similar code blocks with subtle variations, mark as `[⚠️ Duplicated with Variation]`

2. **Apply confidence markers** to every entry: `[✓ Confirmed]`, `[❓ Needs Confirmation]`, `[⚠️ Disputed]`

3. **Identify risk areas:** `[🔴 High Risk]` (complex conditionals, external calls, DB writes, state changes, concurrency, error paths), `[🔴 Tight Coupling]` (no DI, hardcoded dependencies → recommend E2E)

4. **Check intent anchors** (in priority order):
   1. API docs, requirement documents, OpenAPI specs
   2. **Existing tests** — each test assertion is a developer's statement of intent
   3. Caller code, JSDoc/docstrings
   4. **User-provided prompt/requirements** — annotate as `[🔵 Inferred from prompt]`
   - If found: record both "actual behavior" and "expected behavior"; flag discrepancies
   - If not found: mark `[⚠️ No Intent Anchor]`

5. **Sufficiency self-check:** For each entry, verify: "Can I design a test case for this without opening the source file?" If not, add missing information.

6. **Write `.quality-guard/{scope}/behavior-map.md`** with frontmatter

7. **Confirmation gate:** Present summary, list all `[❓]` items (MUST be resolved before proceeding), ask user to confirm accuracy.

---

## Phase 2: Test Plan Design

**Trigger:** `behavior-map.md` exists with no unresolved `[❓]` items, and `test-plan.md` does not exist.

### Steps

1. **Read behavior-map.md** — This is your ONLY input for code behavior. Do NOT re-read production code.

2. **Map existing test coverage** against the behavior map:
   - Mark behaviors as: `[Covered by existing tests]`, `[Partially covered]`, or `[Gap — no existing tests]`
   - **Focus new test design on gaps** — do not duplicate existing coverage unless quality concerns exist
   - Optionally flag existing test quality issues as **Test Quality Discoveries**

3. **Recommend test layers** for uncovered behaviors:

   | Code Characteristic | Recommended Layer | Rationale |
   |---------------------|-------------------|-----------|
   | External HTTP/DB/MQ calls | Integration | Verify protocol and data format correctness |
   | `[🔴 Tight Coupling]` marker | E2E | Cannot inject substitutes; verify from outside |
   | Pure function, no side effects | Behavioral Unit | No dependencies; verify computation directly |
   | Multi-step user journey | E2E + Behavioral (edges) | Core path needs full verification |
   | Async/event-driven | Integration | Verify message format, acknowledgment, idempotency |
   | Saga/workflow/pipeline | E2E + Integration | Compensation/rollback requires end-to-end verification |
   | Configuration-driven (feature flags, env vars) | Behavioral | Different configs produce different business logic |
   | Auth/authorization middleware | Integration | Requires real token validation flow |

   Always explain WHY a layer was chosen. Never use a layer as default.

4. **Generate test cases** — For each case, include: Rationale, Scenario, Expected behavior, Layer (with reasoning), Priority:

   | Priority | Criteria |
   |----------|----------|
   | P0 | Core business flow, data integrity, security-related, payment/auth |
   | P1 | Important but non-critical path, `[🔴 High Risk]` markers |
   | P2 | Edge cases, low-frequency paths, convenience features |

   Behaviors marked `[⚠️ No Intent Anchor]` MUST NOT be assigned higher than P1 unless user explicitly confirms.

5. **Enforce mock constraints:**
   - ✅ **Allowed:** External HTTP APIs, time functions, random generators, external messaging services
   - ❌ **Forbidden:** Internal services/repositories/utilities, database, any module within your system
   - ⚠️ **When you "must" mock internal:** Do NOT mock it → record as **Coupling Discovery** → downgrade to E2E. If E2E also not feasible → record as **Testability Discovery** with required environment conditions.

   **Discovery output format (mandatory for all Coupling/Testability Discoveries):**
   1. **Problem:** One sentence — what is the constraint?
   2. **Actions:** 2-3 concrete options with trade-offs (labeled A/B/C)
   3. **Recommendation:** Which option and why

6. **Reject invalid rationales** that reference code paths, branches, or line numbers.

7. **Write `.quality-guard/{scope}/test-plan.md`**

8. **Confirmation gate:** Present summary, ask about priorities and missing scenarios. User confirms before Phase 3.

---

## Phase 3: Test Execution

**Trigger:** `test-plan.md` exists for the target scope.

### Steps

1. **Detect test framework:** Check project config files, identify runner and assertion library. If multiple frameworks detected, confirm which applies to current scope. If unable to determine → ask user. Use distinguishing suffix (e.g., `order.guard.test.ts`) for new test files.

2. **Environment pre-check:** Verify dependencies installed, required services available, environment variables configured. If prerequisites missing → inform user with setup instructions. If environment fundamentally unavailable → record as **Environment Constraint**, offer to generate code without executing (mark cases `[⏸️ Awaiting Environment]`).

3. **Generate test code** for each pending case. Follow project conventions. Only mock at system boundaries. When code uses global state/singletons, include setup/teardown for isolation. **NEVER modify production code files.**

4. **Production code protection:** Before writing any file, verify it targets a test directory. If testing requires production code changes → STOP → record as **Testability Discovery**.

5. **Run tests and capture results** — pass/fail status, failure message, actual vs expected for each case.

6. **Classify and handle failures:**

   | Failure Type | Symptoms | Action |
   |-------------|----------|--------|
   | Test code error | Compilation/runtime error | Fix test code and re-run (NOT a discovery) |
   | Assertion failure | Expected ≠ actual | Record as **Behavior Discrepancy**. Do NOT weaken assertions, modify production code, or retry with relaxed expectations. |
   | Infrastructure failure | OOM, crash, timeout | Mark `[💥 Execution Failed]`, skip to next case |

7. **Update test-plan.md** — Check off completed cases.

8. **Generate and persist Discovery Report** — Write to `.quality-guard/{scope}/discovery-report.md` with three sections:
   - **✅ Verified Behaviors** — confirmed correct behaviors
   - **⚠️ Behavior Discrepancies** — each with Severity and Suggested Action
   - **⬜ Uncovered Behaviors** — MANDATORY even if empty

   The report MUST NOT contain line/branch coverage or percentage-based metrics.

---

## Initialization: Tiered Detection Strategy

**Accuracy over token efficiency** — skip tiers that produce low-confidence results.

**Tier 0 — Reuse existing project.md:**
If `code-refs` match recorded state → "Project map is up to date." If stale → show changed files, offer: **A)** refresh changed sections / **B)** full rebuild / **C)** skip.

**Tier 1 — High-confidence context files:**
Scan for: CLAUDE.md, .cursorrules, .cursor/rules/\*, README.md, ARCHITECTURE.md, docs/architecture.md, docs/design.md, .ai-prompts/\*, .cursor/prompts/\*. Synthesize project.md, present to user for confirmation. Note: "Generated from context documents (Tier 1). Source code was not read."

**~~Tier 2~~ — Skipped.** Low-confidence inference from config files is intentionally skipped.

**Tier 3 — Full source code scan:**
Show estimated scope (directory, file count, token cost). Offer: **A)** proceed / **B)** provide own architecture doc / **C)** specify narrower directory. Only proceed after explicit confirmation.

**Artifact Refresh:** Never silently refresh. Always show what changed and ask for confirmation: **A)** partial refresh (changed files only) / **B)** full rebuild — user's choice.

---

## Guardrails

These are hard constraints. Violating them is a skill failure.

1. **Never modify production code.** Only create test files, mocks, fixtures, and test configuration.
2. **Never write tests for branch coverage.** Every test must have a behavioral rationale in business language.
3. **Never mock internal modules.** Only mock at system boundaries. Internal coupling is a discovery.
4. **Never weaken assertions to make tests pass.** Failures are discoveries.
5. **Never skip the confirmation gate.** Each phase ends with explicit user confirmation.
6. **Never produce coverage percentages.** Report behavioral verification status only.
7. **Never guess when uncertain.** Mark `[❓ Needs Confirmation]` and ask.
8. **Never omit the Uncovered Behaviors section.** Even if empty, state it explicitly.
9. **Write artifacts in the user's language.** Runtime artifacts follow the user's conversation language. Technical terms remain in their original language. SKILL.md itself stays in English.
