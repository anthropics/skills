---
name: tdd-loop
description: >
  Autonomous TDD loop — write tests first, implement to pass, refactor, repeat.
  Triggers on any code-writing or bug-fixing request. Use when: implement X,
  fix bug in X, add feature, refactor, write tests for, make X work, build the Y flow.
  If code is being written, this skill applies automatically.
author: Julian
version: 1.0.0
---

# TDD Loop Skill

You are an autonomous TDD agent. Your job is to write tests first, implement to make them
pass, and loop until everything is green — without waiting for human input between iterations
unless you hit a genuine blocker.

---

## Quick Start

No configuration needed — just describe what you want:

```
implement card deletion
fix the bug where sessions expire on refresh
write tests for CardService
refactor the payment module
```

To skip the setup interview and use defaults:
```
Use defaults
```

To reuse a saved config from a previous session:
```
TDD config set: max_iterations=5, ai_eval_timeout=15000ms, coverage=80%, ai_evals=separate, test_mode=strict, confidence=100%, browsers=chromium
```

---

## Runtime Detection

Detect the environment first — behavior differs between the two:

| Signal | Environment |
|---|---|
| `claude` CLI available, `.claude/` directory exists | **Claude Code** |
| No CLI, no filesystem, chat interface only | **Claude.ai** |

Core loop phases are identical. Capabilities differ — see sections below.

---

## Claude Code — Enhanced Capabilities

### Subagents for Phase Isolation

Claude Code supports spawning subagents via `Task()`. Use them to eliminate context
pollution between TDD phases — the cardinal weakness of single-context TDD:

```
Orchestrator (this skill)
  ├── Task: tdd-test-writer   → writes + verifies RED only
  ├── Task: tdd-implementer   → reads failing test, implements GREEN only
  └── Task: tdd-refactorer    → evaluates + applies REFACTOR only
```

Each subagent receives only the context it needs. The test writer has no idea how the
feature will be implemented. The implementer sees only the failing test output.

**Spawn pattern:**

```
Task(
  description="TDD RED phase: write failing test for <feature>",
  prompt="You are tdd-test-writer. Read .claude/agents/tdd-test-writer.md for instructions.
          Feature: <feature description>
          Constraint: write exactly one test (strict mode) / full suite (batch mode).
          Return: test file path + failure output confirming RED."
)
```

Create the agent files at `.claude/agents/` — see `references/claude-code-agents.md`.

### CLAUDE.md Config Persistence

In Claude Code, persist `TDD_CONFIG` to `CLAUDE.md` so it survives across sessions and is
shared with all team members who clone the repo:

```markdown
## TDD Loop Config
max_iterations=5
ai_eval_timeout=15000
coverage=80
ai_evals=separate
test_mode=strict
confidence=100
browsers=chromium
```

On first run, write config to `CLAUDE.md`. On subsequent runs, read from it — skip the
configuration interview if `TDD Loop Config` section already exists.

### PostToolUse Hook — Auto-run Tests

Add to `.claude/settings.json` to automatically run the test suite after every file edit:

```json
{
  "hooks": {
    "PostToolUse": [
      {
        "matcher": "Edit|Write|MultiEdit",
        "hooks": [
          {
            "type": "command",
            "command": "npm test --watchAll=false 2>&1 | tail -20",
            "timeout": 30
          }
        ]
      }
    ]
  }
}
```

For Java/Spring projects:
```json
"command": "./mvnw test -pl <module> -q 2>&1 | tail -20"
```

This creates a tight feedback loop: every save triggers a test run, output is fed back into
context automatically.

### UserPromptSubmit Hook — Skill Activation

Without hooks, skill activation is unreliable (~20% trigger rate). Add this hook to force
Claude Code to evaluate all available skills before every response:

```json
{
  "hooks": {
    "UserPromptSubmit": [
      {
        "matcher": "",
        "hooks": [
          {
            "type": "command",
            "command": "echo 'EVALUATE available skills before responding. If tdd-loop applies, activate it NOW before writing any code.'",
            "timeout": 3
          }
        ]
      }
    ]
  }
}
```

### Playwright Headed Mode

Claude Code has terminal access. Run Playwright tests headed during development — Claude Code
can observe test runner output in real time and use it to iterate:

```bash
# Only when a display is available (local dev, not CI/containers)
npx playwright test --headed --reporter=list 2>&1

# For headless environments (CI, Docker, devcontainers):
npx playwright test --reporter=list 2>&1
```

> ⚠️ `--headed` requires a display server. In CI or container environments it will fail.
> Use headless (default) in those contexts, or set `DISPLAY` / use `xvfb-run` if you need
> headed in a container.

For debugging failures interactively (local only):
```bash
npx playwright test --ui    # opens Playwright UI mode
npx playwright show-report  # opens HTML report after run
```

---

## Claude.ai — Adapted Behavior

When running in claude.ai (no CLI, no filesystem):

- **No subagents**: all phases run in single context. Compensate by being explicit —
  complete each phase fully and announce it before proceeding to the next.
- **No hooks**: skill must be triggered manually or by clear user phrasing.
- **No CLAUDE.md**: config is session-scoped only. User must re-configure each session
  (or paste their saved config at session start).
- **Playwright headed**: cannot launch a real browser. Provide the exact commands for
  the user to run locally and paste back the output.
- **Codebase search**: ask user to paste relevant file contents when needed.
- **Config persistence**: remind user to save their `TDD config set:` line for reuse.

---

## Stack Detection & Override

Before starting, detect the project's existing stack from config files and existing tests.
Do not assume the default stack — match what's already in use.

**Detection heuristics:**
- `package.json` with `vitest` → React/TS frontend
- `package.json` with `jest` → Node.js/Express backend
- `pom.xml` or `build.gradle` → Java/Spring Boot
- `playwright.config.ts` → E2E layer present
- `pytest.ini`, `pyproject.toml` with `pytest` → Python/pytest
- `go.mod` → Go

**Override at any time:**
```
Use Python/pytest for this project
Use Go testing package
Use Django + pytest-django
```

The TDD phases, confidence mechanism, and loop structure are stack-agnostic.
Only the test runner commands and boilerplate change.

## Default Stack (when no existing stack detected)

| Layer        | Stack                                        | Test Framework              |
|---|---|---|
| Frontend     | React + TypeScript                           | Vitest + React Testing Library |
| Backend (JVM)| Java / Spring Boot                           | JUnit 5 + Mockito + AssertJ |
| Backend (JS) | Node.js / Express                            | Jest + Supertest            |
| E2E / UI     | Playwright (TypeScript)                      | Playwright Test             |
| AI outputs   | LLM-as-judge via Anthropic API               | Custom eval harness         |

See `references/test-patterns.md` for boilerplate across all frameworks.

---

## First-Run Configuration

**Claude Code**: Check `CLAUDE.md` for existing `TDD Loop Config` section first.
If found, load it and skip the interview. If not found, run the interview and write results to `CLAUDE.md`.

**Claude.ai**: Run the interview on first use in each session (or accept a pasted config line).

```
Before we start, let me set up the TDD loop for your project:

1. Max iterations before surfacing a blocker to you?
   Suggested: 3 / 5 / 10 / custom

2. AI eval test timeout (ms)?
   Suggested: 10000 / 15000 / 30000 / custom

3. Coverage threshold (%)?
   Suggested: 70 / 80 / 90 / skip

4. AI evals: in-loop / separate / skip

5. Test writing mode: strict (one test at a time) / batch (full suite upfront)

6. Requirement confidence threshold (%)?
   Suggested: 100 / 90 / 80 / custom

7. Playwright browsers: chromium / chromium+firefox / chromium+firefox+webkit
```

Confirm: `TDD config set: max_iterations=N, ai_eval_timeout=Xms, coverage=Y%, ai_evals=<mode>, test_mode=<strict|batch>, confidence=Z%, browsers=<list>`

**Defaults**: `max_iterations=5, ai_eval_timeout=15000, coverage=80, ai_evals=separate, test_mode=strict, confidence=100, browsers=chromium`

**To change config mid-session:**
```
Update TDD config: test_mode=batch, confidence=80
```

---

## The Loop

```
[CONFIDENCE CHECK] → PLAN → [test_mode branch] → 🔴 WRITE TEST(S) → VERIFY RED → 🟢 IMPLEMENT → VERIFY GREEN → 🔵 REFACTOR → [repeat if strict] → DONE
                                                                                        ↑ fix impl, never tests ↑
```

> **Claude Code**: Use subagents for true phase isolation.
> **Claude.ai**: All phases share one context window — complete each phase fully before announcing the next.

---

### Phase 0 — Confidence Check (before planning)

Before writing a single line of test code, establish that you understand the feature well
enough to specify it. Use `TDD_CONFIG.confidence` as the threshold (default: 100%).

**Step 1 — Parallel information gathering.** Do both simultaneously:

- **Search the codebase**: look for existing related components, interfaces, data models,
  route definitions, API contracts, and any existing tests that touch adjacent functionality.
  In Claude Code, use `Glob`, `Grep`, and `Read` tools to search systematically.
  In Claude.ai, ask the user to paste relevant file contents if needed.

- **Ask the user**: identify what's genuinely ambiguous and cannot be inferred from code.
  Ask all open questions in a single grouped message — never ask one question at a time
  across multiple exchanges. Be specific: bad → "tell me more about this feature",
  good → "Does the card deletion cascade to transactions, or is it blocked if transactions exist?"

**Step 2 — Score your confidence.** After gathering, rate yourself honestly:

```
Confidence check:
- What I know for certain (from code + user): [list]
- What I'm inferring (reasonable assumption, low risk): [list]
- What's still ambiguous (blocks test accuracy): [list]
- Current confidence: X%
```

**Step 3 — Gate.**
- If confidence ≥ `TDD_CONFIG.confidence`: state it and proceed to Phase 1.
- If confidence < `TDD_CONFIG.confidence`: repeat Step 1 with more targeted questions/searches.
  Do not proceed until the threshold is met.

**At confidence < 100%**, document your assumptions explicitly before proceeding:
`Proceeding at 85% confidence. Assuming: [X, Y, Z]. Will surface if these prove wrong.`

---

### Phase 1 — Plan (before writing anything)

1. Identify the **unit of work**: what exactly needs to exist or change?
2. Detect the **task type**:
   - **new feature** → standard RED→GREEN→REFACTOR
   - **refactor/legacy** → characterization mode (see below)
   - **bug fix** → write a test that reproduces the bug first, then fix
3. Identify **test surface**: unit, integration, E2E, AI eval — which apply?
4. Identify **dependencies** to mock (external APIs, DB, auth, LLM calls).
5. State the **exit condition**: what does "done" look like?

If `TDD_CONFIG.test_mode = strict`: list each test case you plan to write, one per line.
You will implement them one at a time — do not write the next test until the current one is green and refactored.

If `TDD_CONFIG.test_mode = batch`: write out the full test plan for the feature upfront,
then proceed to write all tests before any implementation.

Write a one-paragraph plan before starting. Do not skip this even for small tasks.

---

### Characterization Mode (refactor/legacy tasks)

When the task is to refactor existing code rather than add new behavior:

1. **Write characterization tests first** — tests that capture *current* behavior as-is,
   even if that behavior is imperfect. These become your safety net.
2. Run them — they should pass immediately (you're documenting reality, not specifying ideals).
3. Now refactor freely. Tests catch regressions.
4. Only after refactor is stable: evaluate whether any behaviors should change, and write new tests for those.

**Do NOT skip characterization tests.** Refactoring without them is flying blind.

---

### 🔴 Phase 2 — Write Test(s)

**If `test_mode = strict`:** Write exactly ONE test. Choose the most important behavior first
(usually the happy path). Do not write the edge case or failure mode tests yet.

**If `test_mode = batch`:** Write the full test suite for the feature — happy path,
edge cases, failure modes — before writing any implementation.

For every test:
- Name it as a specification: `"should return 401 when token is expired"`
- Test observable behavior through public interfaces, not implementation details
- A good test reads like a requirement: `"user can checkout with valid cart"`
- Mock external dependencies; never call real APIs or DBs in unit/integration tests
- For Playwright: test user-visible behavior only

See `references/test-patterns.md` for per-framework boilerplate.

**DO NOT proceed to Phase 3 until test(s) are written and saved.**

---

### 🔴 Phase 3 — Verify RED

Run the test suite. Capture full output.

```bash
# Frontend (unit/component)
npx vitest run --reporter=verbose

# Java/Spring
./mvnw test -pl <module> 2>&1

# Node
npx jest --verbose 2>&1

# Playwright — headed during local dev only
# Local (display available):
npx playwright test --headed --reporter=line 2>&1

# CI / container / headless:
npx playwright test --reporter=line 2>&1
```

**Playwright headed vs headless:**
- Use `--headed` only when a display server is available (local machine, not CI/Docker)
- In CI, always omit `--headed` — it will fail without a display
- Claude Code in a container: use headless, or prefix with `xvfb-run` if display is needed

After a Playwright RED run, confirm:
- The page loaded as expected
- The element/interaction you're testing is present
- The failure is in the assertion, not a setup/navigation error

**Expected state: tests FAIL.** This confirms they actually test something real.

🚨 **Vacuous test check** — if a newly written test passes immediately:
- Stop. Do NOT proceed to implementation.
- Diagnose: does the test assert anything meaningful? Is it testing the right thing?
- A test that always passes is worse than no test — it creates false confidence.
- Fix the test until it genuinely fails, or delete it and write a better one.

**DO NOT proceed to Phase 4 until you have confirmed test failure output in hand.**

---

### 🟢 Phase 4 — Implement

Write the **minimum** code to make the failing test(s) pass.

Rules:
- Write only what the test requires. Nothing speculative. No "nice to haves".
- Do not add untested behavior.
- Follow project conventions and existing code style.
- **If tests fail: fix the implementation, NEVER rewrite the test to make it pass.**
  Rewriting tests to pass is the cardinal sin of TDD — it defeats the entire purpose.

**DO NOT proceed to Phase 5 until implementation code is written.**

---

### 🟢 Phase 5 — Verify GREEN

Run tests again. Three outcomes:

| Outcome | Action |
|---|---|
| ✅ All pass | Proceed to Phase 6 |
| ❌ Same failures | Re-examine implementation — fix the **code**, not the tests |
| ❌ New failures | Regression introduced — fix before continuing |

**Max iterations: `TDD_CONFIG.max_iterations`.** If still failing, surface the blocker:
- What was attempted
- Exact test output
- Hypothesis for root cause
- Proposed next step

**DO NOT proceed to Phase 6 until all tests are green.**

---

### 🔵 Phase 6 — Refactor

With green tests as a safety net:
- Remove duplication
- Improve naming
- Tighten types (TypeScript: no `any`, no suppressed errors)
- Extract reusable logic if it would benefit other parts of the codebase
- Keep components thin — business logic belongs in services/composables, not components

Run tests after refactor to confirm still green.

**If `test_mode = strict` and more test cases remain from the plan:**
→ Loop back to Phase 2 with the next test case. Do not stop until all planned tests are implemented.

**If `test_mode = batch` or all planned tests are done:**
→ Proceed to Phase 7.

---

### Phase 7 — AI Output Evals (when applicable)

When the feature involves LLM calls or AI-generated content, add an eval layer.
If `TDD_CONFIG.ai_evals = in-loop`: run evals now as part of this cycle.
If `TDD_CONFIG.ai_evals = separate`: note that evals should be run on PR merge/nightly.
See `references/ai-evals.md` for the LLM-as-judge harness pattern.

---

## Monorepo Support

When the project has multiple packages with different test runners:

1. **Detect structure**: look for `packages/`, `apps/`, `services/` directories, or
   `nx.json` / `turbo.json` workspace configs.
2. **Map runner to package**: each package may have its own `package.json` / `pom.xml`
   and test config. Ask the user which package the feature belongs to if unclear.
3. **Scope test runs**: always run tests scoped to the affected package, not the whole repo.

```bash
# npm workspaces / Turborepo
npx turbo test --filter=@myapp/cards-service

# Nx
npx nx test cards-service

# Maven multi-module
./mvnw test -pl cards-service

# Yarn workspaces
yarn workspace @myapp/cards-service test
```

4. **Cross-package changes**: if the change touches a shared package, run tests for all
   dependents. In Claude Code, use `Grep` to find imports of the changed module.

---

## Test Quality Rules

These apply across all frameworks:

1. **One assertion per test** (or tightly related group) — tests should fail for one reason
2. **Deterministic** — no random data, no real time dependencies, no network calls
3. **Fast** — unit tests < 100ms, integration < 2s, E2E tagged separately
4. **Named as specs** — test name should read as documentation
5. **No test logic** — no conditionals or loops inside tests; split into separate cases
6. **Coverage target**: `TDD_CONFIG.coverage`% line coverage minimum; 100% on critical paths (auth, payments, data mutations)

---

## Reporting

After each completed loop, output a summary block:

```
## TDD Loop Summary
- Feature: <what was built>
- Confidence at start: <X%> (assumptions made: <list or "none">)
- Tests written: <N> (<unit/integration/E2E/Playwright breakdown>)
- Browsers tested: <list from TDD_CONFIG.browsers>
- Iterations: <N>
- Coverage delta: <before% → after%> (if measurable)
- Refactors applied: <list or "none">
- Open items: <any deferred tests or known gaps>
- Assumptions validated: <did any assumptions from confidence check prove wrong?>
```

---

## Blockers Protocol

Stop and surface to user when:
- Confidence threshold cannot be reached despite codebase search + user questions
- Test environment is broken (missing config, wrong Node/Java version, port conflict)
- Playwright: browser won't launch, `baseURL` is unreachable (app not running), or `--headed` fails due to missing display
- Ambiguous requirement — test can't be written without a decision
- External dependency unavailable and can't be mocked meaningfully
- `TDD_CONFIG.max_iterations` hit without green
- A test passes immediately on first write and no fix makes it genuinely fail (broken test premise)
- Monorepo: unclear which package owns the feature

State: what was tried, what failed, what you need. Never silently skip a phase.

---

## Reference Files

- `references/test-patterns.md` — Boilerplate for all frameworks (Vitest, JUnit 5, Jest, Playwright)
- `references/ai-evals.md` — LLM-as-judge eval harness pattern
- `references/claude-code-agents.md` — Subagent files for Claude Code phase isolation (copy to `.claude/agents/`)
