# Review Protocols (Files 3 and 4)

## File 3: Code Review Protocol (`RUN_CODE_REVIEW.md`)

### Template

```markdown
# Code Review Protocol: [Project Name]

## Bootstrap (Read First)

Before reviewing, read these files for context:
1. `quality/QUALITY.md` — Quality constitution and fitness-to-purpose scenarios
2. [Main architectural doc]
3. [Key design decisions doc]
4. [Any other essential context]

## What to Check

### Focus Area 1: [Subsystem/Risk Area Name]

**Where:** [Specific files and functions]
**What:** [Specific things to look for]
**Why:** [What goes wrong if this is incorrect]

### Focus Area 2: [Subsystem/Risk Area Name]

[Repeat for 4–6 focus areas, mapped to architecture and risk areas from exploration]

## Guardrails

- **Line numbers are mandatory.** If you cannot cite a specific line, do not include the finding.
- **Read function bodies, not just signatures.** Don't assume a function works correctly based on its name.
- **If unsure whether something is a bug or intentional**, flag it as a QUESTION rather than a BUG.
- **Grep before claiming missing.** If you think a feature is absent, search the codebase. If found in a different file, that's a location defect, not a missing feature.
- **Do NOT suggest style changes, refactors, or improvements.** Only flag things that are incorrect or could cause failures.

## Output Format

Save findings to `quality/code_reviews/YYYY-MM-DD-reviewer.md`

For each file reviewed:

### filename.ext
- **Line NNN:** [BUG / QUESTION / INCOMPLETE] Description. Expected vs. actual. Why it matters.

### Summary
- Total findings by severity
- Files with no findings
- Overall assessment: SHIP IT / FIX FIRST / NEEDS DISCUSSION
```

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

**Recommendation:** FIX FIRST — Rate limit handling needs investigation.
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
[SHIP IT / FIX FIRST / NEEDS INVESTIGATION]
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

### Post-Run Verification Depth

A run that completes without errors may still be wrong. For each integration test run, verify at multiple levels:

1. **Process-level:** Did the process exit cleanly? Check log files for completion messages, not just exit codes.
2. **State-level:** Is the run in a terminal state? Check the run manifest/status file for "complete" (not stuck in "running" or "submitted").
3. **Data-level:** Does output data exist and parse correctly? Read actual output files, verify they contain valid JSON/CSV/etc.
4. **Content-level:** Do output records have the expected fields populated with reasonable values? Read 2–3 sample records and check key fields.
5. **Quality-level:** Do the pipeline-specific quality gates pass? Run any existing quality check scripts.
6. **UI-level (if applicable):** If the project has a dashboard/TUI/UI, verify the run appears correctly there.

Include all applicable levels in the generated protocol's post-run checklist. The common failure is stopping at level 2 (process completed) without checking levels 3–5.
