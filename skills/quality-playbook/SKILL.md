---
name: quality-playbook
description: "Explore any codebase from scratch and generate six quality artifacts: a quality constitution (QUALITY.md), spec-traced functional tests, a code review protocol with regression test generation, an integration testing protocol, a multi-model spec audit (Council of Three), and an AI bootstrap file (AGENTS.md). Works with any language (Python, Java, Scala, TypeScript, Go, Rust, etc.). Use this skill whenever the user asks to set up a quality playbook, generate functional tests from specifications, create a quality constitution, build testing protocols, audit code against specs, or establish a repeatable quality system for a project. Also trigger when the user mentions 'quality playbook', 'spec audit', 'Council of Three', 'fitness-to-purpose', 'coverage theater', or wants to go beyond basic test generation to build a full quality system grounded in their actual codebase."
license: Complete terms in LICENSE.txt
metadata:
  version: 1.1.0
  author: Andrew Stellman
  github: https://github.com/andrewstellman/
---

# Quality Playbook Generator

**When this skill starts, display this banner before doing anything else:**

```
Quality Playbook v1.1.0 — by Andrew Stellman
https://github.com/andrewstellman/
```

Generate a complete quality system tailored to a specific codebase. Unlike test stub generators that work mechanically from source code, this skill explores the project first — understanding its domain, architecture, specifications, and failure history — then produces a quality playbook grounded in what it finds.

## Why This Exists

Most software projects have tests, but few have a quality *system*. Tests check whether code works. A quality system answers harder questions: what does "working correctly" mean for this specific project? What are the ways it could fail that wouldn't be caught by tests? What should every developer (human or AI) know before touching this code?

Without a quality playbook, every new contributor (and every new AI session) starts from scratch — guessing at what matters, writing tests that look good but don't catch real bugs, and rediscovering failure modes that were already found and fixed months ago. A quality playbook makes the bar explicit, persistent, and inherited.

## What This Skill Produces

Six files that together form a repeatable quality system:

| File | Purpose | Why It Matters | Executes Code? |
|------|---------|----------------|----------------|
| `quality/QUALITY.md` | Quality constitution — coverage targets, fitness-to-purpose scenarios, theater prevention | Every AI session reads this first. It tells them what "good enough" means so they don't guess. | No |
| `quality/test_functional.*` | Automated functional tests derived from specifications | The safety net. Tests tied to what the spec says should happen, not just what the code does. Use the project's language: `test_functional.py` (Python), `FunctionalSpec.scala` (Scala), `functional.test.ts` (TypeScript), `FunctionalTest.java` (Java), etc. | **Yes** |
| `quality/RUN_CODE_REVIEW.md` | Code review protocol with guardrails that prevent hallucinated findings | AI code reviews without guardrails produce confident but wrong findings. The guardrails (line numbers, grep before claiming, read bodies) often improve accuracy. | No |
| `quality/RUN_INTEGRATION_TESTS.md` | Integration test protocol — end-to-end pipeline across all variants | Unit tests pass, but does the system actually work end-to-end with real external services? | **Yes** |
| `quality/RUN_SPEC_AUDIT.md` | Council of Three multi-model spec audit protocol | No single AI model catches everything. Three independent models with different blind spots catch defects that any one alone would miss. | No |
| `AGENTS.md` | Bootstrap context for any AI session working on this project | The "read this first" file. Without it, AI sessions waste their first hour figuring out what's going on. | No |

Plus output directories: `quality/code_reviews/`, `quality/spec_audits/`, `quality/results/`.

The critical deliverable is the functional test file (named for the project's language and test framework conventions). The Markdown protocols are documentation for humans and AI agents. The functional tests are the automated safety net.

## How to Use

Point this skill at any codebase:

```
Generate a quality playbook for this project.
```

```
Update the functional tests — the quality playbook already exists.
```

```
Run the spec audit protocol.
```

If a quality playbook already exists (`quality/QUALITY.md`, functional tests, etc.), read the existing files first, then evaluate them against the self-check benchmarks in the verification phase. Don't assume existing files are complete — treat them as a starting point.

---

## Phase 1: Explore the Codebase (Do Not Write Yet)

Spend the first phase understanding the project. The quality playbook must be grounded in this specific codebase — not generic advice.

**Why explore first?** The most common failure in AI-generated quality playbooks is producing generic content — coverage targets that could apply to any project, scenarios that describe theoretical failures, tests that exercise language builtins instead of project code. Exploration prevents this by forcing every output to reference something real: a specific function, a specific schema, a specific defensive code pattern. If you can't point to where something lives in the code, you're guessing — and guesses produce quality playbooks nobody trusts.

**Scaling for large codebases:** For projects with more than ~50 source files, don't try to read everything. Focus exploration on the 3–5 core modules (the ones that handle the primary data flow, the most complex logic, and the most failure-prone operations). Read representative tests from each subsystem rather than every test file. The goal is depth on what matters, not breadth across everything.

### Step 0: Ask About Development History

Before exploring code, ask the user one question:

> "Do you have exported AI chat history from developing this project — Claude exports, Gemini takeouts, ChatGPT exports, Claude Code transcripts, or similar? If so, point me to the folder. The design discussions, incident reports, and quality decisions in those chats will make the generated quality playbook significantly better."

If the user provides a chat history folder:

1. **Scan for an index file first.** Look for files named `INDEX*`, `CONTEXT.md`, `README.md`, or similar navigation aids. If one exists, read it — it will tell you what's there and how to find things.
2. **Search for quality-relevant conversations.** Look for messages mentioning: quality, testing, coverage, bugs, failures, incidents, crashes, validation, retry, recovery, spec, fitness, audit, review. Also search for the project name.
3. **Extract design decisions and incident history.** The most valuable content is: (a) incident reports — what went wrong, how many records affected, how it was detected, (b) design discussions — why a particular approach was chosen, what alternatives were rejected, (c) quality framework discussions — coverage targets, testing philosophy, model review experiences, (d) cross-model feedback — where different AI models disagreed about the code.
4. **Don't try to read everything.** Chat histories can be enormous. Use the index to find the most relevant conversations, then search within those for quality-related content. 10 minutes of targeted searching beats 2 hours of exhaustive reading.

This context is gold. A chat history where the developer discussed "why we chose this concurrency model" or "the time we lost 1,693 records in production" transforms generic scenarios into authoritative ones.

If the user doesn't have chat history, proceed normally — the skill works without it, just with less context.

### Step 1: Identify Domain, Stack, and Specifications

Read the README, existing documentation, and build config (`pyproject.toml` / `package.json` / `Cargo.toml`). Answer:

- What does this project do? (One sentence.)
- What language and key dependencies?
- What external systems does it talk to?
- What is the primary output?

**Find the specifications.** Specs are the source of truth for functional tests. Search in order: `AGENTS.md`/`CLAUDE.md` in root, `specs/`, `docs/`, `spec/`, `design/`, `architecture/`, `adr/`, then `.md` files in root. Record the paths.

**If no formal spec documents exist**, the skill still works — but you need to assemble requirements from other sources. In order of preference:

1. **Ask the user** — they often know the requirements even if they're not written down.
2. **README and inline documentation** — many projects embed requirements in their README, API docs, or code comments.
3. **Existing test suite** — tests are implicit specifications. If a test asserts `process(x) == y`, that's a requirement.
4. **Type signatures and validation rules** — schemas, type annotations, and validators define what the system accepts and rejects.
5. **Infer from code behavior** — as a last resort, read the code and infer what it's supposed to do. Mark these as *inferred requirements* in QUALITY.md and flag them for user confirmation.

When working from non-formal requirements, label each scenario and test with a **requirement tag** that includes a confidence tier and source:

- `[Req: formal — README §3]` — written by humans in a spec document. Authoritative.
- `[Req: user-confirmed — "must handle empty input"]` — stated by the user but not in a formal doc. Treat as authoritative.
- `[Req: inferred — from validate_input() behavior]` — deduced from code. Flag for user review.

Use this exact tag format in QUALITY.md scenarios, functional test documentation, and spec audit findings. It makes clear which requirements are authoritative and which need validation.

### Step 2: Map the Architecture

List source directories and their purposes. Read the main entry point, trace execution flow. Identify:

- The 3–5 major subsystems
- The data flow (Input → Processing → Output)
- The most complex module
- The most fragile module

### Step 3: Read Existing Tests

Read the existing test files — all of them for small/medium projects, or a representative sample from each subsystem for large ones. Identify: test count, coverage patterns, gaps, and any coverage theater (tests that look good but don't catch real bugs).

**Critical: Record the import pattern.** How do existing tests import project modules? Every language has its own conventions (Python `sys.path` manipulation, Java/Scala package imports, TypeScript relative paths or aliases, Go package/module paths, Rust `use crate::` or `use myproject::`). You must use the exact same pattern in your functional tests — getting this wrong means every test fails with import/resolution errors. See `references/functional_tests.md` § "Import Pattern" for the full six-language matrix.

**Identify integration test runners.** Look for scripts or test files that exercise the system end-to-end against real external services (APIs, databases, etc.). Note their patterns — you'll need them for `RUN_INTEGRATION_TESTS.md`.

### Step 4: Read the Specifications

Walk each spec document section by section. For every section, ask: "What testable requirement does this state?" Record spec requirements without corresponding tests — these are the gaps the functional tests must close.

If using inferred requirements (from tests, types, or code behavior), tag each with its confidence tier using the `[Req: tier — source]` format defined in Step 1. Inferred requirements feed into QUALITY.md scenarios and should be flagged for user review in Phase 4.

### Step 4b: Read Function Signatures and Real Data

Before writing any test, you must know exactly how each function is called. For every module you identified in Step 2:

1. **Read the actual function signatures** — parameter names, types, defaults. Don't guess from usage context — read the function definition and any documentation (Python docstrings, Java/Scala Javadoc/ScalaDoc, TypeScript type annotations, Go godoc comments, Rust doc comments and type signatures).
2. **Read real data files** — If the project has items files, fixture files, config files, or sample data (in `pipelines/`, `fixtures/`, `test_data/`, `examples/`), read them. Your test fixtures must match the real data shape exactly.
3. **Read existing test fixtures** — How do existing tests create test data? Copy their patterns. If they build config dicts with specific keys, use those exact keys.
4. **Check library versions** — Check the project's dependency manifest (`requirements.txt`, `build.sbt`, `package.json`, `pom.xml`/`build.gradle`, `go.mod`, `Cargo.toml`) to see what's actually available. Don't write tests that depend on library features that aren't installed. If a dependency might be missing, use the test framework's skip mechanism — see `references/functional_tests.md` § "Library version awareness" for framework-specific examples.

Record a **function call map**: for each function you plan to test, write down its name, module, parameters, and what it returns. This map prevents the most common test failure: calling functions with wrong arguments.

### Step 5: Find the Skeletons

This is the most important step. Search for defensive code patterns — each one is evidence of a past failure or known risk.

**Why this matters:** Developers don't write `try/except` blocks, null checks, or retry logic for fun. Every piece of defensive code exists because someone got burned. A `try/except` around a JSON parse means malformed JSON happened in production. A null check on a field means that field was missing when it shouldn't have been. These patterns are the codebase whispering its history of failures. Each one becomes a fitness-to-purpose scenario and a boundary test.

**Read `references/defensive_patterns.md`** for the systematic search approach, grep patterns, and how to convert findings into fitness-to-purpose scenarios and boundary tests.

Minimum bar: at least 2–3 defensive patterns per core source file. If you find fewer, you're skimming — read function bodies, not just signatures.

### Step 5b: Map Schema Types

If the project has a validation layer (Pydantic models in Python, JSON Schema, TypeScript interfaces/Zod schemas, Java Bean Validation annotations, Scala case class codecs), read the schema definitions now. For every field you found a defensive pattern for, record what the schema accepts vs. rejects.

**Read `references/schema_mapping.md`** for the mapping format and why this matters for writing valid boundary tests.

### Step 6: Identify Quality Risks (Code + Domain Knowledge)

Every project has a different failure profile. This step uses **two sources** — not just code exploration, but your training knowledge of what goes wrong in similar systems.

**From code exploration**, ask:
- What does "silently wrong" look like for this project?
- What external dependencies can change without warning?
- What looks simple but is actually complex?
- Where do cross-cutting concerns hide?

**From domain knowledge**, ask:
- "What goes wrong in systems like this?" — If it's a batch processor, think about crash recovery, idempotency, silent data loss, state corruption. If it's a web app, think about auth edge cases, race conditions, input validation bypasses. If it handles randomness or statistics, think about seeding, correlation, distribution bias.
- "What produces correct-looking output that is actually wrong?" — This is the most dangerous class of bug: output that passes all checks but is subtly corrupted.
- "What happens at 10x scale that doesn't happen at 1x?" — Chunk boundaries, rate limits, timeout cascading, memory pressure.
- "What happens when this process is killed at the worst possible moment?" — Mid-write, mid-transaction, mid-batch-submission.

Generate realistic failure scenarios from this knowledge. You don't need to have observed these failures — you know from training that they happen to systems of this type. Write them as **architectural vulnerability analyses** with specific quantities and consequences. Frame each as "this architecture permits the following failure mode" — not as a fabricated incident report. Use concrete numbers to make the severity non-negotiable: "If the process crashes mid-write during a 10,000-record batch, `save_state()` without an atomic rename pattern will leave a corrupted state file — the next run gets JSONDecodeError and cannot resume without manual intervention." Then ground them in the actual code you explored: "Read persistence.py line ~340 (save_state): verify temp file + rename pattern."

---

## Phase 2: Generate the Quality Playbook

Now write the six files. For each one, follow the structure below and consult the relevant reference file for detailed guidance.

**Why six files instead of just tests?** Tests catch regressions but don't prevent new categories of bugs. The quality constitution (`QUALITY.md`) tells future sessions what "correct" means before they start writing code. The protocols (`RUN_*.md`) provide structured processes for review, integration testing, and spec auditing that produce repeatable results — instead of leaving quality to whatever the AI feels like checking. Together, these files create a quality system where each piece reinforces the others: scenarios in QUALITY.md map to tests in the functional test file, which are verified by the integration protocol, which is audited by the Council of Three.

### File 1: `quality/QUALITY.md` — Quality Constitution

**Read `references/constitution.md`** for the full template and examples.

The constitution has six sections:

1. **Purpose** — What quality means for this project, grounded in Deming (built in, not inspected), Juran (fitness for use), Crosby (quality is free). Apply these specifically: what does "fitness for use" mean for *this system*? Not "tests pass" but the actual operational requirement.
2. **Coverage Targets** — Table mapping each subsystem to a target with rationale referencing real risks. Every target must have a "why" grounded in a specific scenario — without it, a future AI session will argue the target down.
3. **Coverage Theater Prevention** — Project-specific examples of fake tests, derived from what you saw during exploration. (Why: AI-generated tests often pad coverage numbers without catching real bugs — asserting that imports worked, that dicts have keys, or that mocks return what they were configured to return. Calling this out explicitly stops the pattern.)
4. **Fitness-to-Purpose Scenarios** — The heart of it. Each scenario documents a realistic failure mode with code references and verification method. Aim for 2+ scenarios per core module — typically 8–10 total for a medium project, fewer for small projects, more for complex ones. Quality matters more than count: a scenario that precisely captures a real architectural vulnerability is worth more than three generic ones. (Why: Coverage percentages tell you how much code ran, not whether it ran correctly. A system can have 95% coverage and still lose records silently. Fitness scenarios define what "working correctly" actually means in concrete terms that no one can argue down.)
5. **AI Session Quality Discipline** — Rules every AI session must follow
6. **The Human Gate** — Things requiring human judgment

**Scenario voice is critical.** Write "What happened" as architectural vulnerability analyses with specific quantities, cascade consequences, and detection difficulty — not as abstract specifications. "Because `save_state()` lacks an atomic rename pattern, a mid-write crash during a 10,000-record batch will leave a corrupted state file — the next run gets JSONDecodeError and cannot resume. At scale, this risks silent loss of 1,693+ records with no detection mechanism." An AI session reading that will not argue the standard down. Use your knowledge of similar systems to generate realistic failure scenarios, then ground them in the actual code you explored. Scenarios come from both code exploration AND domain knowledge about what goes wrong in systems like this.

Every scenario's "How to verify" must map to at least one test in the functional test file.

### File 2: Functional Tests

**This is the most important deliverable.** Read `references/functional_tests.md` for the complete guide.

Organize the tests into three logical groups (classes, describe blocks, modules, or whatever the test framework uses):

- **Spec requirements** — One test per testable spec section. Each test's documentation cites the spec requirement it verifies.
- **Fitness scenarios** — One test per QUALITY.md scenario. 1:1 mapping, named to match.
- **Boundaries and edge cases** — One test per defensive pattern from Step 5.

Key rules:
- **Match the existing import pattern exactly.** Read how existing tests import project modules and do the same thing. Getting this wrong means every test fails.
- **Read every function's signature before calling it.** Read the actual `def` line — parameter names, types, defaults. Read real data files from the project to understand data shapes. Do not guess at function parameters or fixture structures.
- **No placeholder tests.** Every test must import and call actual project code. If the body is `pass` or the assertion is trivial (`assert isinstance(x, list)`), delete it. A test that doesn't exercise project code inflates the count and creates false confidence.
- **Test count heuristic** = (testable spec sections) + (QUALITY.md scenarios) + (defensive patterns). For a medium project (5–15 source files), this typically yields 35–50 tests. Significantly fewer suggests missed requirements or shallow exploration. Significantly more is fine if every test is meaningful — don't pad to hit a number.
- **Cross-variant heuristic: ~30%** — If the project handles multiple input types, aim for roughly 30% of tests parametrized across all variants. The exact percentage matters less than ensuring every cross-cutting property is tested across all variants.
- **Test outcomes, not mechanisms** — Assert what the spec says should happen, not how the code implements it.
- **Use schema-valid mutations** — Boundary tests must use values the schema accepts (from Step 5b), not values it rejects.

### File 3: `quality/RUN_CODE_REVIEW.md`

**Read `references/review_protocols.md`** for the template.

Key sections: bootstrap files, focus areas mapped to architecture, and these mandatory guardrails:

- Line numbers are mandatory — no line number, no finding
- Read function bodies, not just signatures
- If unsure: flag as QUESTION, not BUG
- Grep before claiming missing
- Do NOT suggest style changes — only flag things that are incorrect

**Phase 2: Regression tests.** After the review produces BUG findings, write regression tests in `quality/test_regression.*` that reproduce each bug. Each test should fail on the current implementation, confirming the bug is real. Report results as a confirmation table (BUG CONFIRMED / FALSE POSITIVE / NEEDS INVESTIGATION). See `references/review_protocols.md` for the full regression test protocol.

### File 4: `quality/RUN_INTEGRATION_TESTS.md`

**Read `references/review_protocols.md`** for the template.

Must include: safety constraints, pre-flight checks, test matrix with specific pass criteria, an execution UX section, and a structured reporting format. Cover happy path, cross-variant consistency, output correctness, and component boundaries.

**All commands must use relative paths.** The generated protocol should include a "Working Directory" section at the top stating that all commands run from the project root using relative paths. Never generate commands that `cd` to an absolute path — this breaks when the protocol is run from a different machine or directory. Use `./scripts/`, `./pipelines/`, `./quality/`, etc.

**Include an Execution UX section.** When someone tells an AI agent to "run the integration tests," the agent needs to know how to present its work. The protocol should specify three phases: (1) show the plan as a numbered table before running anything, (2) report one-line progress updates as each test runs (`✓`/`✗`/`⧗`), (3) show a summary table with pass/fail counts and a recommendation. See `references/review_protocols.md` section "Execution UX" for the template and examples. Without this, the agent dumps raw output or stays silent — neither is useful.

**This protocol must exercise real external dependencies.** If the project talks to APIs, databases, or external services, the integration test protocol runs real end-to-end executions against those services — not just local validation checks. Design the test matrix around the project's actual execution modes and external dependencies. Look for API keys, provider abstractions, and existing integration test scripts during exploration and build on them.

**Derive quality gates from the code, not generic checks.** Read validation rules, schema enums, and generation logic during exploration. Turn them into per-pipeline quality checks with specific fields and acceptable value ranges. "All units validated" is not enough — the protocol must verify domain-specific correctness.

**Script parallelism, don't just describe it.** Group runs so independent executions (different providers) run concurrently. Include actual bash commands with `&` and `wait`. One run per provider at a time to avoid rate limits.

**Calibrate unit counts to the project.** Read `chunk_size` or equivalent config. Use enough units to span at least 2 chunks and enough to verify distribution checks. Typically 10–30 for integration testing.

**Deep post-run verification.** Don't stop at "process completed." Verify log files, manifest state, output data existence, sample record content, and any existing quality check scripts — for every run.

**Find and use existing verification tools.** Search for existing scripts that verify output quality (e.g., `integration_checks.py`, validation scripts, quality gate functions). If they exist, call them from the protocol. If the project has a TUI or dashboard, include TUI verification commands (e.g., `--dump` flags) in the post-run checklist.

**Build a Field Reference Table before writing quality gates.** This is the most important step for protocol accuracy. AI models confidently write wrong field names even after reading schemas — `document_id` becomes `doc_id`, `sentiment_score` becomes `sentiment`, `float 0-1` becomes `int 0-100`. The fix is procedural: **re-read each schema file IMMEDIATELY before writing each table row.** Do not rely on what you read earlier in the conversation — your memory of field names drifts over thousands of tokens. Copy field names character-for-character from the file contents. Include ALL fields from each schema (if the schema has 8 fields, the table has 8 rows). See `references/review_protocols.md` section "The Field Reference Table" for the full process and format. Do not skip this step — it prevents the single most common protocol inaccuracy.

### File 5: `quality/RUN_SPEC_AUDIT.md` — Council of Three

**Read `references/spec_audit.md`** for the full protocol.

Three independent AI models audit the code against specifications. Why three? Because each model has different blind spots — in practice, different auditors catch different issues. Cross-referencing catches what any single model misses.

The protocol defines: a copy-pasteable audit prompt with guardrails, project-specific scrutiny areas, a triage process (merge findings by confidence level), and fix execution rules (small batches by subsystem, not mega-prompts).

### File 6: `AGENTS.md`

If `AGENTS.md` already exists, update it — don't replace it. Add a Quality Docs section pointing to all generated files.

If creating from scratch: project description, setup commands, build & test commands, architecture overview, key design decisions, known quirks, and quality docs pointers.

---

## Phase 3: Verify

**Why a verification phase?** AI-generated output can look polished and be subtly wrong. Tests that reference undefined fixtures report 0 failures but 16 errors — and "0 failures" sounds like success. Integration protocols can list field names that don't exist in the actual schemas. The verification phase catches these problems before the user discovers them, which is important because trust in a generated quality playbook is fragile — one wrong field name undermines confidence in everything else.

### Self-Check Benchmarks

Before declaring done, check every benchmark. **Read `references/verification.md`** for the complete checklist.

The critical checks:

1. **Test count** near heuristic target (spec sections + scenarios + defensive patterns)
2. **Scenario coverage** — scenario test count matches QUALITY.md scenario count
3. **Cross-variant coverage** — ~30% of tests parametrize across all input variants
4. **Boundary test count** ≈ defensive pattern count from Step 5
5. **Assertion depth** — Majority of assertions check values, not just presence
6. **Layer correctness** — Tests assert outcomes (what spec says), not mechanisms (how code implements)
7. **Mutation validity** — Every fixture mutation uses a schema-valid value from Step 5b
8. **All tests pass — zero failures AND zero errors.** Run the test suite using the project's test runner (Python: `pytest -v`, Scala: `sbt testOnly`, Java: `mvn test`/`gradle test`, TypeScript: `npx jest`, Go: `go test -v`, Rust: `cargo test`) and check the summary. Errors from missing fixtures, failed imports, or unresolved dependencies count as broken tests. If you see setup errors, you forgot to create the fixture/setup file or referenced undefined test helpers.
9. **Existing tests unbroken** — The new files didn't break anything.
10. **Integration test quality gates were written from a Field Reference Table.** Verify that you built a Field Reference Table by re-reading each schema file before writing quality gates, and that every field name in the quality gates is copied from that table — not from memory. If you skipped the table, go back and build it now.

If any benchmark fails, go back and fix it before proceeding.

---

## Phase 4: Present, Explore, Improve (Interactive)

After generating and verifying, present the results clearly and give the user control over what happens next. This phase has three parts: a scannable summary, drill-down on demand, and a menu of improvement paths.

**Do not skip this phase.** The autonomous output from Phases 1-3 is a solid starting point, but the user needs to understand what was generated, explore what matters to them, and choose how to improve it. A quality playbook is only useful if the people who own the project trust it and understand it. Dumping six files without explanation creates artifacts nobody reads.

### Part 1: The Summary Table

Present a single table the user can scan in 10 seconds:

```
Here's what I generated:

| File | What It Does | Key Metric | Confidence |
|------|-------------|------------|------------|
| QUALITY.md | Quality constitution | 10 scenarios | ██████░░ High — grounded in code, but scenarios are inferred, not from real incidents |
| Functional tests | Automated tests | 47 passing | ████████ High — all tests pass, 35% cross-variant |
| RUN_CODE_REVIEW.md | Code review protocol | 8 focus areas | ████████ High — derived from architecture |
| RUN_INTEGRATION_TESTS.md | Integration test protocol | 9 runs × 3 providers | ██████░░ Medium — quality gates need threshold tuning |
| RUN_SPEC_AUDIT.md | Council of Three audit | 10 scrutiny areas | ████████ High — guardrails included |
| AGENTS.md | AI session bootstrap | Updated | ████████ High — factual |
```

Adapt the table to what you actually generated — the file names, metrics, and confidence levels will vary by project. The confidence column is the most important: it tells the user where to focus their attention.

**Confidence levels:**
- **High** — Derived directly from code, specs, or schemas. Unlikely to need revision.
- **Medium** — Reasonable inference, but could be wrong. Benefits from user input.
- **Low** — Best guess. Definitely needs user input to be useful.

After the table, add a "Quick Start" block with ready-to-copy prompts for executing each artifact:

```
To use these artifacts, start a new AI session and try one of these prompts:

• Run a code review:
  "Read quality/RUN_CODE_REVIEW.md and follow its instructions to review [module or file]."

• Run the functional tests:
  "[test runner command, e.g. pytest quality/ -v, mvn test -Dtest=FunctionalTest, etc.]"

• Run the integration tests:
  "Read quality/RUN_INTEGRATION_TESTS.md and follow its instructions."

• Start a spec audit (Council of Three):
  "Read quality/RUN_SPEC_AUDIT.md and follow its instructions using [model name]."
```

Adapt the test runner command and module names to the actual project. The point is to give the user copy-pasteable prompts — not descriptions of what they could do, but the actual text they'd type.

After the Quick Start block, add one line:

> "You can ask me about any of these to see the details — for example, 'show me Scenario 3' or 'walk me through the integration test matrix.'"

### Part 2: Drill-Down on Demand

When the user asks about a specific item, give a focused summary — not the whole file, but the key decisions and what you're uncertain about. Examples:

- **"Tell me about Scenario 4"** → Show the scenario text, explain where it came from (which defensive pattern or domain knowledge), and flag what you inferred vs. what you know.
- **"Show me the integration test matrix"** → Show the run groups, explain the parallelism strategy, and note which quality gates you derived from schemas vs. guessed at.
- **"How do the functional tests work?"** → Show the three test groups, explain the mapping to specs and scenarios, and highlight any tests you're least confident about.

The user may go through several drill-downs before they're ready to improve anything. That's fine — let them explore at their own pace.

### Part 3: The Improvement Menu

After the user has seen the summary (and optionally drilled into details), present the improvement options:

> "Three ways to make this better:"
>
> **1. Review and harden individual items** — Pick any scenario, test, or protocol section and I'll walk through it with you. Good for: tightening specific quality gates, fixing inferred scenarios, adding missing edge cases.
>
> **2. Guided Q&A** — I'll ask you 3-5 targeted questions about things I couldn't infer from the code: incident history, expected distributions, cost tolerance, model preferences. Good for: filling knowledge gaps that make scenarios more authoritative.
>
> **3. Review development history** — Point me to exported AI chat history (Claude, Gemini, ChatGPT exports, Claude Code transcripts) and I'll mine it for design decisions, incident reports, and quality discussions that should be in QUALITY.md. Good for: grounding scenarios in real project history instead of inference.
>
> "You can do any combination of these, in any order. Which would you like to start with?"

### Executing Each Improvement Path

**Path 1: Review and harden.** The user picks an item. Walk through it: show the current text, explain your reasoning, ask if it's accurate. Revise based on their feedback. Re-run tests if the functional tests change.

**Path 2: Guided Q&A.** Ask 3-5 questions derived from what you actually found during exploration. These categories cover the most common high-leverage gaps:

- **Incident history for scenarios.** "I found [specific defensive code]. What failure caused this? How many records were affected?"
- **Quality gate thresholds.** "I'm checking that [field] contains [values]. What distribution is normal? What signals a problem?"
- **Integration test scale and cost.** "The protocol runs [N] tests costing roughly $[X]. Should I increase or decrease coverage?"
- **Test scope.** "I generated [N] functional tests. Your existing suite covers [other areas]. Are there gaps?"
- **Model preferences for spec audit.** "Which AI models do you use? Have you noticed specific strengths?"

After the user answers, revise the generated files and re-run tests.

**Path 3: Review development history.** If the user provides a chat history folder:

1. Scan for index files and navigate to quality-relevant conversations (same approach as Step 0, but now with specific targets — you know which scenarios need grounding, which quality gates need thresholds, which design decisions need rationale).
2. Extract: incident stories with specific numbers, design rationale for defensive patterns, quality framework discussions, cross-model audit results.
3. Revise QUALITY.md scenarios with real incident details. Update integration test thresholds with real-world values. Add Council of Three empirical data if audit results exist.
4. Re-run tests after revisions.

If the user already provided chat history in Step 0, you've already mined it — but they may want to point you to specific conversations or ask you to dig deeper into a particular topic.

### Iteration

The user can cycle through these paths as many times as they want. Each pass makes the quality playbook more grounded. When they're satisfied, they'll move on naturally — there's no explicit "done" step.

---

## Fixture Strategy

The `quality/` folder is separate from the project's unit test folder. Create the appropriate test setup for the project's language:

- **Python:** `quality/conftest.py` for pytest fixtures. If fixtures are defined inline (common with pytest's `tmp_path` pattern), prefer that over shared fixtures.
- **Java:** A test class with `@BeforeEach`/`@BeforeAll` setup methods, or a shared test utility class.
- **Scala:** A trait mixed into test specs (e.g., `trait FunctionalTestFixtures`), or inline data builders.
- **TypeScript/JavaScript:** A `quality/setup.ts` with `beforeAll`/`beforeEach` hooks, or inline test factories.
- **Go:** Helper functions in the same `_test.go` file or a shared `testutil_test.go`. Use `t.Helper()` for test helpers. Go convention prefers inline test setup over shared fixtures.
- **Rust:** Helper functions in a `#[cfg(test)] mod tests` block, or a shared `test_utils.rs` module. Use builder patterns for test data.

Examine existing test files to understand how they set up test data. Whatever pattern the existing tests use, copy it. Study existing fixture patterns for realistic data shapes.

---

## Terminology

- **Functional testing** — Does the code produce the output specs say it should? Distinct from unit testing (individual functions in isolation).
- **Integration testing** — Do components work together end-to-end, including real external services?
- **Spec audit** — AI models read code and compare against specs. No code executed. Catches where code doesn't match documentation.
- **Coverage theater** — Tests that produce high coverage numbers but don't catch real bugs. Example: asserting a function didn't throw without checking its output.
- **Fitness-to-purpose** — Does the code do what it's supposed to do under real-world conditions? A system can have 95% coverage and still lose records silently.

---

## Principles

1. Fitness-to-purpose over coverage percentages
2. Scenarios come from code exploration AND domain knowledge
3. Concrete failure modes make standards non-negotiable — abstract requirements invite rationalization
4. Guardrails transform AI review quality (line numbers, read bodies, grep before claiming)
5. Triage before fixing — many "defects" are spec bugs or design decisions

---

## Reference Files

Read these as you work through each phase:

| File | When to Read | Contains |
|------|-------------|----------|
| `references/defensive_patterns.md` | Step 5 (finding skeletons) | Grep patterns, how to convert findings to scenarios |
| `references/schema_mapping.md` | Step 5b (schema types) | Field mapping format, mutation validity rules |
| `references/constitution.md` | File 1 (QUALITY.md) | Full template with section-by-section guidance |
| `references/functional_tests.md` | File 2 (functional tests) | Test structure, anti-patterns, cross-variant strategy |
| `references/review_protocols.md` | Files 3–4 (code review, integration) | Templates for both protocols |
| `references/spec_audit.md` | File 5 (Council of Three) | Full audit protocol, triage process, fix execution |
| `references/verification.md` | Phase 3 (verify) | Complete self-check checklist with all 13 benchmarks |
