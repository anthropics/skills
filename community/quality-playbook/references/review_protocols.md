# Review Protocols (Files 3 and 4)

## File 3: Code Review Protocol (`RUN_CODE_REVIEW.md`)

### Template

```markdown
# Code Review Protocol: [Project Name]

## Bootstrap (Read First)

Before reviewing, read these files for context:
1. `quality/QUALITY.md` — Quality constitution and fitness-to-purpose scenarios
2. `quality/REQUIREMENTS.md` — Testable requirements derived during playbook generation
3. [Main architectural doc]
4. [Key design decisions doc]
5. [Any other essential context]

## Pass 1: Structural Review

Read the code and report anything that looks wrong. No requirements, no focus areas — use your own knowledge of code correctness. Look for: race conditions, null pointer hazards, resource leaks, off-by-one errors, type mismatches, error handling gaps, and any code that looks suspicious.

### Guardrails

- **Line numbers are mandatory.** If you cannot cite a specific line, do not include the finding.
- **Read function bodies, not just signatures.** Don't assume a function works correctly based on its name.
- **If unsure whether something is a bug or intentional**, flag it as a QUESTION rather than a BUG.
- **Grep before claiming missing.** If you think a feature is absent, search the codebase. If found in a different file, that's a location defect, not a missing feature.
- **Do NOT suggest style changes, refactors, or improvements.** Only flag things that are incorrect or could cause failures.

### Output

For each file reviewed:

#### filename.ext
- **Line NNN:** [BUG / QUESTION / INCOMPLETE] Description. Expected vs. actual. Why it matters.

## Pass 2: Requirement Verification

Read `quality/REQUIREMENTS.md`. For each requirement, check whether the code satisfies it. This is a pure verification pass — your only job is "does the code satisfy this requirement?"

Do NOT also do a general code review. Do NOT look for other bugs. Do NOT evaluate code quality. Just check each requirement.

For each requirement, report one of:
- **SATISFIED**: The code implements this requirement. Quote the specific code.
- **VIOLATED**: The code does NOT satisfy this requirement. Explain what the code does vs. what the requirement says. Quote the code.
- **PARTIALLY SATISFIED**: Some aspects implemented, others missing. Explain both.
- **NOT ASSESSABLE**: Can't be checked from the files under review.

### Output

For each requirement:

#### REQ-N: [requirement text]
**Status**: SATISFIED / VIOLATED / PARTIALLY SATISFIED / NOT ASSESSABLE
**Evidence**: [file:line] — [code quote]
**Analysis**: [explanation]
[If VIOLATED] **Severity**: [impact description]

## Pass 3: Cross-Requirement Consistency

Compare pairs of requirements from `quality/REQUIREMENTS.md` that reference the same field, constant, range, or security policy. For each pair, check whether their constraints are mutually consistent.

What to look for:
- **Numeric range vs bit width**: If one requirement says the valid range is [0, N) and another says the field is M bits wide, does N = 2^M?
- **Security policy propagation**: If one requirement says a CA file is configured, do all requirements about connections that should use it actually reference using it?
- **Validation bounds vs encoding limits**: Does a validation check in one file agree with the storage capacity in another?
- **Lifecycle consistency**: If a resource is created by one requirement's code, is it cleaned up by another's?

For each pair that shares a concept, verify consistency against the actual code.

### Output

For each shared concept:

#### Shared Concept: [name]
**Requirements**: REQ-X, REQ-Y
**What REQ-X claims**: [summary]
**What REQ-Y claims**: [summary]
**Consistency**: CONSISTENT / INCONSISTENT
**Code evidence**: [quotes from both locations]
**Analysis**: [explanation]
[If INCONSISTENT] **Impact**: [what happens when the contradiction is triggered]

## Combined Summary

| Source | Finding | Severity | Status |
|--------|---------|----------|--------|
| Pass 1 | [structural finding] | [severity] | BUG / QUESTION |
| Pass 2, REQ-N | [requirement violation] | [severity] | VIOLATED |
| Pass 3, REQ-X vs REQ-Y | [consistency issue] | [severity] | INCONSISTENT |

- Total findings by pass and severity
- Overall assessment: SHIP / FIX BEFORE MERGE / BLOCK
```

### Execution requirements

**All three passes are mandatory.** Do not consolidate passes into a single review. Each pass produces distinct findings because it uses a different lens:

- **Pass 1** finds structural bugs (race conditions, null hazards, resource leaks)
- **Pass 2** finds requirement violations (missing behavior, spec deviations)
- **Pass 3** finds cross-requirement contradictions (inconsistent ranges, conflicting guarantees)

**Write each pass as a clearly labeled section** in the output file. Use the headers `## Pass 1: Structural Review`, `## Pass 2: Requirement Verification`, `## Pass 3: Cross-Requirement Consistency`, and `## Combined Summary`.

**If a pass has no findings, explain why.** Do not just write "No findings." Write what you checked and why nothing was wrong. For example: "Reviewed 12 functions in lib/response.js for null hazards, resource leaks, and error handling gaps. No confirmed bugs — all error paths either throw or return a well-defined default." A pass with no findings and no explanation is a pass that wasn't done.

**Scoping for large codebases:** If the project has more than 50 requirements, Pass 2 does not need to verify every requirement against every file. Instead, focus Pass 2 on the requirements most relevant to the files being reviewed — check the requirements that reference those files or that govern the behavioral domain those files implement. The goal is depth on the files under review, not breadth across all requirements.

**Self-check before finishing:** After writing all three passes and the combined summary, verify: (1) all three pass sections exist in the output, (2) Pass 2 references specific REQ-NNN numbers with SATISFIED/VIOLATED verdicts, (3) Pass 3 identifies at least one shared concept between requirements (even if consistent), (4) every BUG finding has a corresponding regression test in `quality/test_regression.*` (see Phase 2 below), (5) every regression test exercises the actual code path cited in the finding (see test-finding alignment check below). If any check fails, go back and complete the missing work.

### Adversarial stance when documentation is available

If the playbook was generated with supplemental documentation (reference_docs/, community docs, user guides, API references), the code review must use that documentation *against* the code, not in its defense. Documentation tells you what the code is supposed to do. Your job is to find where it doesn't.

**Do not let documentation explanations excuse code defects.** If the docs say "the library handles X gracefully" but the code doesn't check for X, that's a bug — the documentation makes it *more* of a bug, not less. A richer understanding of intent should make you *harder* on the code, not softer.

The failure mode this addresses: when models have access to documentation, they build a richer mental model of the software and become more *forgiving* of code that approximately matches that model. The documentation gives the model reasons to believe the code works, which suppresses detections. Fight this by treating documentation as the prosecution's evidence — it defines what the code promised, and your job is to find broken promises.

### Test-finding alignment check

For each regression test that claims to reproduce a specific finding, verify that the test actually exercises the cited code path. A test that targets a different function, a different branch, or a different failure mode than the finding it claims to reproduce is worse than no test — it creates false confidence.

**Verification procedure:** For each regression test:
1. Read the finding: note the specific file, line number, function, and failure condition
2. Read the test: identify which function it calls and what condition it asserts
3. Confirm alignment: the test must call the function cited in the finding, trigger the specific condition the finding describes, and assert on the behavior the finding says is wrong

If the test doesn't exercise the cited code path, either fix the test or mark the finding as UNCONFIRMED. Do not ship a regression test that passes or fails for reasons unrelated to the finding.

### Closure mandate

Every confirmed BUG finding must produce a regression test in `quality/test_regression.*`. The test must be an executable source file in the project's language — not a Markdown file, not prose documentation, not a comment block describing what a test would do. If the project uses Java, write a `.java` file. If Python, a `.py` file. The test must compile (or parse) and be runnable by the project's test framework.

**No language exemptions.** If introducing failing tests before fixes is a concern, use the language's expected-failure mechanism. The guard must be the **earliest syntactic guard for the framework** — a decorator or annotation where idiomatic, otherwise the first executable line in the test body:

- **Python (pytest):** `@pytest.mark.xfail(strict=True, reason="BUG-NNN: [description]")` — decorator above `def test_...():`. When the bug is present: XFAIL (expected). When the bug is fixed but marker not removed: XPASS → strict mode fails, signaling the guard should be removed.
- **Python (unittest):** `@unittest.expectedFailure` — decorator above the test method.
- **Go:** `t.Skip("BUG-NNN: [description] — unskip after applying quality/patches/BUG-NNN-fix.patch")` — first line inside the test function. Note: Go's `t.Skip` hides the test (reports SKIP, not FAIL), which is weaker than Python's xfail.
- **Rust:** `#[ignore]` attribute on the test function — the standard "don't run in default suite" mechanism. Use `#[should_panic]` only for panic-shaped bugs.
- **Java (JUnit 5):** `@Disabled("BUG-NNN: [description]")` — annotation above the test method.
- **TypeScript/JavaScript (Jest):** `test.failing("BUG-NNN: [description]", () => { ... })`
- **TypeScript/JavaScript (Vitest):** `test.fails("BUG-NNN: [description]", () => { ... })`
- **JavaScript (Mocha):** `it.skip("BUG-NNN: [description]", () => { ... })` or `this.skip()` inside the test body for conditional skipping.

Every guard must reference the bug ID (BUG-NNN format) and the fix patch path so that someone encountering a skipped test knows how to resolve it.

These patterns ensure every bug has an executable test that can be enabled when the fix lands, without polluting CI with expected failures.

**TDD red/green interaction with skip guards.** During TDD verification, the red and green phases must temporarily bypass the skip guard:
- **Red phase (NEVER SKIPPED):** Remove or disable the guard, run against unpatched code. Must fail. Re-enable guard after recording result. **The red phase is mandatory for every confirmed bug, even when no fix patch exists.** Record `verdict: "confirmed open"` with `red_phase: "fail"` and `green_phase: "skipped"`. Do not use `verdict: "skipped"` — that value is deprecated.
- **Green phase:** Remove or disable the guard, apply fix patch, run. Must pass. Re-enable guard if fix will be reverted. If no fix patch exists, record `green_phase: "skipped"`.
- **After successful red→green:** Generate a per-bug writeup at `quality/writeups/BUG-NNN.md` (see SKILL.md File 7, "Bug writeup generation"). Record the path in `tdd-results.json` as `writeup_path`. After writing `tdd-results.json`, reopen it and verify all required fields, enum values, and no extra undocumented root keys (see SKILL.md post-write validation step). Both sidecar JSON files must use `schema_version: "1.1"`.
- **After TDD cycle:** Guard remains in committed regression test file, removed only when fix is permanently merged.

**The only acceptable exemption** is when a regression test genuinely cannot be written — for example, the bug requires multi-threaded timing that can't be reliably reproduced, or requires an external service not available in the test environment. In that case, write an explicit exemption note in the combined summary explaining why, and include a minimal code sketch showing what you would test if you could.

Findings without either an executable regression test or an explicit exemption note are incomplete. The combined summary must not include unresolved findings — every BUG must have closure.

### Regression test semantic convention

All regression tests must assert **desired correct behavior** and be marked as expected-to-fail on the current code. Do not write tests that assert the current broken behavior and pass. The distinction matters:

- **Correct:** Test says "this input should produce X" → test fails because buggy code produces Y → marked `xfail`/`@Disabled`/`t.Skip` → when bug is fixed, test passes and the skip marker is removed.
- **Wrong:** Test says "this input produces Y (the buggy output)" → test passes on buggy code → when bug is fixed, test fails silently → stale test that now asserts wrong behavior.

The `xfail(strict=True)` pattern (Python/pytest) is the gold standard: it fails if the bug is present (expected), and also fails if the bug is fixed but the `xfail` marker wasn't removed (strict). Other languages should approximate this with skip + reason.

### Post-review closure verification

After writing all regression tests and the combined summary, run this checklist:

1. **Count BUGs in the combined summary.** This is the expected count.
2. **Count test functions in `quality/test_regression.*`.** This should equal or exceed the BUG count (some BUGs may need multiple tests).
3. **For each BUG row in the summary**, verify it has either:
   - A `REGRESSION TEST:` line citing the test function name, OR
   - An `EXEMPTION:` line explaining why no test was written
4. **If any BUG lacks both**, go back and write the test or the exemption before declaring the review complete.

This checklist is the enforcement mechanism for the closure mandate. Without it, the mandate is aspirational — agents document bugs fully in the pass summaries but skip the regression test and move on.

### Post-spec-audit regression tests

The closure mandate applies to spec-audit confirmed code bugs, not just code review bugs. After the spec audit triage categorizes findings, every finding classified as "Real code bug" must get a regression test — using the same conventions as code review regression tests (executable source file, expected-failure marker, test-finding alignment).

**Why this is a separate step:** Code review regression tests are written immediately after the code review, before the spec audit runs. This means spec-audit bugs are systematically orphaned — they appear in the triage report but never enter the regression test file. Across v1.3.4 runs on 8 repos, spec-audit bugs accounted for ~30% of all findings, and only 1 of 8 repos (httpx) wrote regression tests for them.

**Procedure:**
1. After spec audit triage, read the triage summary for findings classified as "Real code bug."
2. For each, write a regression test in `quality/test_regression.*` using the same format as code review regression tests. Use the spec audit report as the source citation: `[BUG from spec_audits/YYYY-MM-DD-triage.md]`.
3. Run the test to confirm it fails (expected) or passes (needs investigation).
4. Update the cumulative BUG tracker in PROGRESS.md with the test reference.

If the spec audit produced no confirmed code bugs, skip this step — but document that in PROGRESS.md so the audit trail is complete.

### Cleaning up after spec audit reversals

When the spec audit overturns a code review finding (classifies a BUG as a design choice or false positive), the corresponding regression test must be either deleted or moved to a separate file (`quality/design_behavior_tests.*`) that documents intentional behavior. A failing test that points at documented-correct behavior is worse than no test — it creates noise and erodes trust in the regression suite.

After spec audit triage, check: does any test in `quality/test_regression.*` correspond to a finding that was reclassified as non-defect? If so, remove it from the regression file.

### Why Three Passes Instead of Focus Areas

Previous experiments (the QPB NSQ benchmark) showed that focus areas don't reliably improve AI code review. A generic "review for bugs" prompt scored 65.5%, while a playbook with 7 named focus areas scored 48.3% — the focus areas narrowed the model's attention and suppressed detections.

The three-pass pipeline works because each pass does one thing well with no cross-contamination:
- **Pass 1** lets the model do what it's already good at (structural review, ~65% of defects)
- **Pass 2** catches individual requirement violations that structural review misses (absence bugs, spec deviations)
- **Pass 3** catches contradictions between individually-correct pieces of code (cross-file arithmetic bugs, security policy gaps)

Experiments on the NSQ codebase showed this pipeline finding 2 of 3 defects that were invisible to all structural review conditions — with zero knowledge of the specific bugs. The defects found were a cross-file numeric mismatch (validation bound vs bit field width) and a security design gap (configured CA not propagated to outbound auth client).

### Phase 2: Regression Tests for Confirmed Bugs

After the code review produces findings, write regression tests that reproduce each BUG finding. This transforms the review from "here are potential bugs" into "here are proven bugs with failing tests."

**Why this matters:** A code review finding without a reproducer is an opinion. A finding with a failing test is a fact. Across multiple codebases (Go, Rust, Python), regression tests written from code review findings have confirmed bugs at a high rate — including data races, cross-tenant data leaks, state machine violations, and silent context loss. The regression tests also serve as the acceptance criteria for fixing the bugs: when the test passes, the bug is fixed.

**How to generate regression tests:**

1. **For each BUG finding**, write a test that:
   - Targets the exact code path and line numbers from the finding
   - Fails on the current implementation, confirming the bug exists
   - Uses mocking/monkeypatching to isolate from external services
   - Includes the finding description in the test docstring for traceability

2. **Name the test file** `quality/test_regression.*` using the project's language:
   - Python: `quality/test_regression.py`
   - Go: `quality/regression_test.go` (or in the relevant package's test directory)
   - Rust: `quality/regression_tests.rs` or a `tests/regression_*.rs` file in the relevant crate
   - Java: `quality/RegressionTest.java`
   - TypeScript: `quality/regression.test.ts`

3. **Each test should document its origin:**
   ```
   # Python example
   def test_webhook_signature_raises_on_malformed_input():
       """[BUG from 2026-03-26-reviewer.md, line 47]
       Webhook signature verification raises instead of returning False
       on malformed signatures, risking 500 instead of clean 401."""

   // Go example
   func TestRestart_DataRace_DirectFieldAccess(t *testing.T) {
       // BUG from 2026-03-26-claude.md, line 3707
       // Restart() writes mutex-protected fields without acquiring the lock
   }
   ```

4. **Run the tests and report results** as a confirmation table:
   ```
   | Finding | Test | Result | Confirmed? |
   |---------|------|--------|------------|
   | Webhook signature raises on malformed input | test_webhook_signature_... | FAILED (expected) | YES — bug confirmed |
   | Queued messages deleted before processing | test_message_queue_... | FAILED (expected) | YES — bug confirmed |
   | Thread active check fails open | test_is_thread_active_... | PASSED (unexpected) | NO — needs investigation |
   ```

5. **If a test passes unexpectedly**, investigate — either the finding was a false positive, or the test doesn't exercise the right code path. Report as NEEDS INVESTIGATION, not as a confirmed bug.

**Language-specific tips:**

- **Go:** Use `go test -race` to confirm data race findings. The race detector is definitive — if it fires, the race is real.
- **Rust:** Use `#[should_panic]` or assert on specific error conditions. For atomicity bugs, assert on cleanup state after injected failures.
- **Python:** Use `monkeypatch` or `unittest.mock.patch` to isolate external dependencies. Use `pytest.raises` for exception-path bugs.
- **Java:** Use Mockito or similar to isolate dependencies. Use `assertThrows` for exception-path bugs.

**Save the regression test output** alongside the code review: if the review is at `quality/code_reviews/2026-03-26-reviewer.md`, the regression tests go in `quality/test_regression.*` and the confirmation results go in the review file as an addendum or in `quality/results/`.

### Why These Guardrails Matter

These four guardrails often improve AI code review quality by reducing vague and hallucinated findings:

1. **Line numbers** force the model to actually locate the issue, not just describe a general concern
2. **Reading bodies** prevents the common failure of assuming a function works based on its name
3. **QUESTION vs BUG** reduces false positives that waste human time
4. **Grep before claiming missing** prevents the most common AI review hallucination: claiming something doesn't exist when it's in a different file

The "no style changes" rule keeps reviews focused on correctness. Style suggestions dilute the signal and waste review time.

---

## File 4: Integration Test Protocol (`RUN_INTEGRATION_TESTS.md`)

### Template

```markdown
# Integration Test Protocol: [Project Name]

## Working Directory

All commands in this protocol use **relative paths from the project root.** Run everything from the directory containing this file's parent (the project root). Do not `cd` to an absolute path or a parent directory — if a command starts with `cd /some/absolute/path`, it's wrong. Use `./scripts/`, `./pipelines/`, `./quality/`, etc.

## Safety Constraints

[If this protocol runs with elevated permissions:]
- DO NOT modify source code
- DO NOT delete files
- ONLY create files in the test results directory
- If something fails, record it and move on — DO NOT fix it

## Pre-Flight Check

Before running integration tests, verify:
- [ ] [Dependencies installed — specific command]
- [ ] [API keys / external services available — specific checks]
- [ ] [Test fixtures exist — specific paths]
- [ ] [Clean state — specific cleanup if needed]

## Test Matrix

| Check | Method | Pass Criteria |
|-------|--------|---------------|
| [Happy path flow] | [Specific command or test] | [Specific expected result] |
| [Variant A end-to-end] | [Command] | [Expected result] |
| [Variant B end-to-end] | [Command] | [Expected result] |
| [Output correctness] | [Specific assertion] | [Expected property] |
| [Component boundary A→B] | [Command] | [Expected result] |

### Design Principles for Integration Checks

- **Happy path** — Does the primary flow work from input to output?
- **Cross-variant consistency** — Does each variant produce correct output?
- **Output correctness** — Don't just check "output exists" — verify specific properties
- **Component boundaries** — Does Module A's output correctly feed Module B?

## Automated Integration Tests

Where possible, encode checks as automated tests:

```bash
[test runner] [integration test file] --verbose
```

## Manual Verification Steps

[Any checks requiring external systems, human judgment, or manual inspection]

## Execution UX (How to Present When Running This Protocol)

When an AI agent runs this protocol, it should communicate in three phases so the user can follow along without reading raw output:

### Phase 1: The Plan

Before running anything, show the user what's about to happen:

```
## Integration Test Plan

**Pre-flight:** Checking dependencies, API keys, and environment
**Tests to run:**

| # | Test | What It Checks | Est. Time |
|---|------|---------------|-----------|
| 1 | [Test name] | [One-line description] | ~30s |
| 2 | [Test name] | [One-line description] | ~2m |
| ... | | | |

**Total:** N tests, estimated M minutes
```

This gives the user a chance to say "skip test 4" or "actually, don't run the live API tests" before anything starts.

### Phase 2: Progress

As each test runs, report a one-line status update. Keep it compact — the user wants a heartbeat, not a log dump:

```
✓ Test 1: Expression evaluation — PASS (0.3s)
✓ Test 2: Schema validation — PASS (0.1s)
⧗ Test 3: Live pipeline (Gemini, realtime)... running
```

Use `✓` for pass, `✗` for fail, `⧗` for in-progress. If a test fails, show one line of context (the error message or assertion that failed), not the full stack trace. The user can ask for details if they want them.

### Phase 3: Results

After all tests complete, show a summary table and a recommendation:

```
## Results

| # | Test | Result | Time | Notes |
|---|------|--------|------|-------|
| 1 | Expression evaluation | ✓ PASS | 0.3s | |
| 2 | Schema validation | ✓ PASS | 0.1s | |
| 3 | Live pipeline (Gemini) | ✗ FAIL | 45s | Rate limited after 8 units |
| ... | | | | |

**Passed:** 7/8 | **Failed:** 1/8

**Recommendation:** FIX BEFORE MERGE — Rate limit handling needs investigation.
```

Then save the detailed results to `quality/results/YYYY-MM-DD-integration.md`.

## Reporting (Saved to File)

Save results to `quality/results/YYYY-MM-DD-integration.md`

### Summary Table
| Check | Result | Notes |
|-------|--------|-------|
| ... | PASS/FAIL | ... |

### Detailed Findings
[Specific failures, unexpected behavior, performance observations]

### Recommendation
[SHIP / FIX BEFORE MERGE / BLOCK]
```

### Tips for Writing Good Integration Checks

- Each check should exercise a real end-to-end flow, not just call a single function
- Pass criteria must be specific and verifiable — not "looks right" but "output contains exactly N records with property X"
- Include timing expectations where relevant (especially for batch/pipeline projects)
- If the project has multiple execution modes (batch vs. realtime, different providers), test each combination

### Live Execution Against External Services

Integration tests must exercise the project's actual external dependencies — APIs, databases, services, file systems. A protocol that only tests local validation and config parsing is not an integration test protocol; it's a unit test suite in disguise.

During exploration, identify:
- **External APIs the project calls** — Look for API keys in .env files, environment variable references, provider/client abstractions, HTTP client configurations
- **Execution modes** — batch vs. realtime, sync vs. async, different provider backends
- **Existing integration test runners** — Scripts or test files that already exercise end-to-end flows

Then design the test matrix as a **provider × pipeline × mode** grid. For example, if the project supports 3 API providers and 3 pipelines with batch and realtime modes, the protocol should run real executions across that matrix — not just validate configs locally.

**Structure runs for parallelism.** Group runs so that at most one run per provider executes simultaneously (to avoid rate limits). Use background processes and `wait` for concurrent execution within groups.

**Define per-pipeline quality checks.** Each pipeline produces different output with different correctness criteria. The protocol must specify what fields to check and what values are acceptable for each pipeline — not just "output exists."

**Include a post-run verification checklist.** For each run, verify: log file exists with completion message, manifest shows terminal state, validated output files exist and contain parseable data, sample records have expected fields populated, and any existing automated quality check scripts pass.

**Pre-flight must check API keys.** If keys are missing, stop and ask — don't skip the live tests silently.

The goal is that running this protocol exercises the full system under real-world conditions, catching issues that local-only testing would miss: provider-specific response format differences, timeout behavior, rate limiting, and output correctness with real LLM responses.

### Parallelism and Rate Limit Awareness

Sequential integration runs waste time. Group runs so that independent runs execute concurrently, with these constraints:

- **At most one run per external provider simultaneously** to avoid rate limits
- **Use background processes and `wait`** for concurrent execution within groups
- **Generate a shared timestamp** at the start of the session for consistent run directory naming

Example grouping for a project with 3 pipelines and 3 providers (9+ runs):

```
Group 1 (parallel): Pipeline_A × Provider_1 | Pipeline_B × Provider_2 | Pipeline_C × Provider_3
Group 2 (parallel): Pipeline_A × Provider_2 | Pipeline_B × Provider_3 | Pipeline_C × Provider_1
Group 3 (parallel): Pipeline_A × Provider_3 | Pipeline_B × Provider_1 | Pipeline_C × Provider_2
```

This pattern maximizes throughput while never hitting the same provider with concurrent requests. Adapt the grouping to the project's actual pipeline and provider count.

In the generated protocol, include the actual bash commands with `&` for background execution and `wait` between groups. Don't just describe parallelism — script it.

### Deriving Quality Gates from Code

Generic pass/fail criteria ("all units validated") miss domain-specific correctness issues. Derive pipeline-specific quality checks from the code itself:

1. **Read validation rules.** If the project validates output (schema validators, assertion functions, business rule checks), those rules define what "correct" looks like. Turn them into quality gates: "field X must satisfy condition Y for all output records."

2. **Read schema enums.** If schemas define enum fields (e.g., `outcome: ["fell_in_water", "reached_ship"]`), the quality gate is: "all outputs must use values from this set, and the distribution should be non-degenerate (not 100% one value)."

3. **Read generation logic.** If the project generates test data (items files, seed data, permutation strategies), understand what variants should appear. If there are 3 personality types, the quality gate is: "all 3 types must appear in output with sufficient sample size."

4. **Read existing quality checks.** Search for scripts or functions that already verify output quality (e.g., `integration_checks.py`, validation functions called after runs). Reference or call them directly from the protocol.

For each pipeline in the project, the integration protocol should have a dedicated "Quality Checks" section listing 2–4 specific checks with expected values derived from the exploration above. Do not use generic checks like "output exists" — every check must reference a specific field and acceptable value range.

### The Field Reference Table (Required Before Writing Quality Gates)

**Why this exists:** AI models confidently write wrong field names even when they've read the schemas. This happens because the model reads the schema during exploration, then writes the protocol hours (or thousands of tokens) later from memory. Memory drifts: `document_id` becomes `doc_id`, `sentiment_score` becomes `sentiment`, `float 0-1` becomes `int 0-100`. The protocol looks authoritative but the field names are hallucinated. When someone runs the quality gates against real data, they fail — and the user loses trust in the entire generated playbook.

**The fix is procedural, not instructional.** Don't just tell yourself to "cross-check later" — build the reference table FIRST, then write quality gates by copying from it.

Before writing any quality gate that references output field names, build a **Field Reference Table** by re-reading each schema file:

```
## Field Reference Table (built from schemas, not memory)

### Pipeline: WeatherForecast
Schema: pipelines/WeatherForecast/schemas/analyze.json
| Field | Type | Constraints |
|-------|------|-------------|
| region_name | string | — |
| temperature | number | min: -50, max: 60 |
| condition | string | enum: ["sunny", "cloudy", "rain", "snow"] |

### Pipeline: SentimentAnalysis
Schema: pipelines/SentimentAnalysis/schemas/evaluate.json
| Field | Type | Constraints |
|-------|------|-------------|
| document_id | string | — |
| sentiment_score | number | min: -1.0, max: 1.0 |
| classification | string | enum: ["positive", "negative", "neutral"] |
...
```

**The process:**
1. **Re-read each schema file IMMEDIATELY before writing each table row.** Do not write any row from memory. The file read and the table row must be adjacent — read the file, write the row, read the next file, write the next row. If you read all schemas earlier in the conversation, that doesn't count — you must read them AGAIN here because your memory of field names drifts over thousands of tokens.
2. **Copy field names character-for-character from the file contents.** Do not retype them. `document_id` is not `doc_id`. `sentiment_score` is not `sentiment`. `classification` is not `category`. Even small differences break quality gates.
3. **Include ALL fields from the schema, not just the ones you think are important.** If the schema has 8 required fields, the table has 8 rows. If you wrote fewer rows than the schema has fields, you skipped fields.
4. Write quality gates by copying field names from the completed table.
5. After writing, count fields: if the quality gates mention a field that isn't in the table, you hallucinated it. Remove it.

This table is an intermediate artifact — include it in the protocol itself (as a reference section) so future protocol users can verify field accuracy. The point is to create it as a concrete step that produces evidence of schema reading, not skip it because you "already know" the fields.

### Calibrating Scale

The number of units/records/iterations per integration test run matters:

- **Too few (1–3):** Fast and cheap, but misses concurrency bugs, distribution checks fail (can't verify "25–75% ratio" with 2 records), and fan-out/expansion logic untested at realistic scale.
- **Too many (100+):** Expensive and slow for a test protocol. Appropriate for production but not for quality verification.
- **Right range:** Enough to exercise the system meaningfully. Guidelines:
  - If the project has chunking/batching logic, use a count that spans at least 2 chunks (e.g., if chunk_size=10, use 15–30 units)
  - If the project has distribution checks, use at least 5–10× the number of categories (e.g., 3 outcome types → at least 15 units)
  - If the project has fan-out/expansion, use a count that produces a non-trivial number of children

Look for `chunk_size`, `batch_size`, or similar configuration in the project to calibrate. When in doubt, 10–30 records is usually the right range for integration testing — enough to catch real issues without burning API budget.

### Integration Testing for Skills and LLM-Automated Tools

When the project under test is an AI skill, CLI tool that wraps LLM calls, or any software whose primary execution path involves invoking an AI model, the integration test protocol must include **LLM-automated integration tests** — tests that run the tool end-to-end via a command-line AI agent and structurally verify the output.

This is distinct from standard integration tests because the system under test doesn't have a deterministic API to call. The "integration" is: install the skill into a test repo, invoke it through a CLI agent (GitHub Copilot CLI, Claude Code, or similar), and verify the output artifacts meet structural and content expectations.

**Why this matters:** Skills and LLM tools cannot be tested by calling functions directly — their execution path goes through an AI agent that interprets instructions, reads files, and produces artifacts. The only way to test whether the skill works is to run it. Manual execution is fine for development, but a quality playbook should encode the test as a repeatable protocol.

**Protocol structure for skill/LLM integration tests:**

```markdown
## Skill Integration Test Protocol

### Prerequisites
- CLI agent installed and configured (e.g., `gh copilot`, `claude`, `npx @anthropic-ai/claude-code`)
- Test repo prepared with skill installed at `.github/skills/SKILL.md` (or equivalent)
- Clean `quality/` directory (no artifacts from prior runs)
- Optional: `reference_docs/` folder for with-docs comparison runs

### Test Matrix

| Test | Method | Pass Criteria |
|------|--------|---------------|
| Full execution | Run skill via CLI with "execute" prompt | All expected artifacts exist in `quality/` |
| PROGRESS.md completeness | Read `quality/PROGRESS.md` | All phases checked complete, BUG tracker populated |
| Artifact structural check | Verify each expected file | Files are non-empty, contain expected sections |
| BUG tracker closure | Count BUG entries vs regression tests | Every BUG has a test reference or exemption |
| Baseline vs with-docs (optional) | Run twice: without and with reference_docs/ | With-docs run produces >= baseline requirement count |

### Execution

```bash
# Install skill into test repo
cp -r path/to/skill/.github test-repo/.github

# Run via CLI agent (adapt command to your agent)
cd test-repo
gh copilot -p "Read .github/skills/SKILL.md and its reference files. Execute the quality playbook for this project." \
    --model gpt-5.4 --yolo > quality_run.output.txt 2>&1
```

### Structural Verification (automated)

After the run, verify output structurally:

```bash
# Required artifacts exist and are non-empty
for f in quality/QUALITY.md quality/REQUIREMENTS.md quality/CONTRACTS.md \
         quality/COVERAGE_MATRIX.md quality/COMPLETENESS_REPORT.md \
         quality/PROGRESS.md quality/RUN_CODE_REVIEW.md \
         quality/RUN_INTEGRATION_TESTS.md quality/RUN_SPEC_AUDIT.md; do
    [ -s "$f" ] || echo "FAIL: $f missing or empty"
done

# Functional test file exists (language-appropriate name)
ls quality/test_functional.* quality/FunctionalSpec.* quality/functional.test.* 2>/dev/null \
    || echo "FAIL: no functional test file"

# PROGRESS.md has all phases checked
grep -c '\[x\]' quality/PROGRESS.md  # should equal total phase count

# BUG tracker has entries (if bugs were found)
grep -c '^| [0-9]' quality/PROGRESS.md

# Code reviews and spec audits produced substantive files
find quality/code_reviews -name "*.md" -size +500c | wc -l  # should be >= 1
find quality/spec_audits -name "*triage*" -size +500c | wc -l  # should be >= 1
```
```

**Baseline vs with-docs comparison pattern:** Run the skill twice on the same repo — once without supplemental docs, once with a `reference_docs/` folder containing project history. Compare: requirement count, scenario count, bug count, and pipeline completion. The with-docs run should produce equal or more requirements and equal or more bugs. If the baseline outperforms the with-docs run on bug detection, that's a finding about the docs quality, not a skill failure.

**When to generate this protocol:** Generate a skill integration test section in `RUN_INTEGRATION_TESTS.md` whenever the project being analyzed is a skill, a CLI tool that wraps AI calls, or a framework for building AI-powered tools. Look for: `SKILL.md` files, prompt templates, LLM client configurations, agent orchestration code, or references to AI models in the codebase.

### Post-Run Verification Depth

A run that completes without errors may still be wrong. For each integration test run, verify at multiple levels:

1. **Process-level:** Did the process exit cleanly? Check log files for completion messages, not just exit codes.
2. **State-level:** Is the run in a terminal state? Check the run manifest/status file for "complete" (not stuck in "running" or "submitted").
3. **Data-level:** Does output data exist and parse correctly? Read actual output files, verify they contain valid JSON/CSV/etc.
4. **Content-level:** Do output records have the expected fields populated with reasonable values? Read 2–3 sample records and check key fields.
5. **Quality-level:** Do the pipeline-specific quality gates pass? Run any existing quality check scripts.
6. **UI-level (if applicable):** If the project has a dashboard/TUI/UI, verify the run appears correctly there.

Include all applicable levels in the generated protocol's post-run checklist. The common failure is stopping at level 2 (process completed) without checking levels 3–5.
