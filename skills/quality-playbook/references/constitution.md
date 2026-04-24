# Writing the Quality Constitution (File 1: QUALITY.md)

The quality constitution defines what "quality" means for this specific project and makes the bar explicit, persistent, and inherited by every AI session.

## Template

```markdown
# Quality Constitution: [Project Name]

## Purpose

[2–3 paragraphs grounding quality in three principles:]

- **Deming** ("quality is built in, not inspected in") — Quality is built into context files
  and the quality playbook so every AI session inherits the same bar.
- **Juran** ("fitness for use") — Define fitness specifically for this project. Not "tests pass"
  but the actual real-world requirement. Example: "generates correct output that survives
  input schema changes without silently producing wrong results."
- **Crosby** ("quality is free") — Building a quality playbook upfront costs less than
  debugging problems found after deployment.

## Coverage Targets

| Subsystem | Target | Why |
|-----------|--------|-----|
| [Most fragile module] | 90–95% | [Real edge case or past bug] |
| [Core logic module] | 85–90% | [Concrete risk] |
| [I/O or integration layer] | 80% | [Explain] |
| [Configuration/utilities] | 75–80% | [Explain] |

The rationale column is essential. It must reference specific risks or past failures.
If you can't explain why a subsystem needs high coverage with a concrete example,
the target is arbitrary.

## Coverage Theater Prevention

[Define what constitutes a fake test for this project.]

Generic examples that apply to most projects:
- Asserting a function returned *something* without checking what
- Testing with synthetic data that lacks the quirks of real data
- Asserting an import succeeded
- Asserting mock returns what the mock was configured to return
- Calling a function and only asserting no exception was thrown

[Add project-specific examples based on what you learned during exploration.
For a data pipeline: "counting output records without checking their values."
For a web app: "checking HTTP 200 without checking the response body."
For a compiler: "checking output compiles without checking behavior."]

## Fitness-to-Purpose Scenarios

[5–10 scenarios. Every scenario must include a `[Req: tier — source]` tag linking it to its requirement source. Use the template below:]

### Scenario N: [Memorable Name]

**Requirement tag:** [Req: formal — Spec §X] *(or `user-confirmed` / `inferred` — see SKILL.md Phase 1, Step 1 for tier definitions)*

**What happened:** [The architectural vulnerability, edge case, or design decision.
Reference actual code — function names, file names, line numbers. Frame as "this architecture permits the following failure mode."]

**The requirement:** [What the code must do to prevent this failure.
Be specific enough that an AI can verify it.]

**How to verify:** [Concrete test or query that would fail if this regressed.
Include exact commands, test names, or assertions.]

---

[Repeat for each scenario]

## AI Session Quality Discipline

1. Read QUALITY.md before starting work.
2. Run the full test suite before marking any task complete.
3. Add tests for new functionality (not just happy path — include edge cases).
4. Update this file if new failure modes are discovered.
5. Output a Quality Compliance Checklist before ending a session.
6. Never remove a fitness-to-purpose scenario. Only add new ones.

## The Human Gate

[List things that require human judgment:]
- Output that "looks right" (requires domain knowledge)
- UX and responsiveness
- Documentation accuracy
- Security review of auth changes
- Backward compatibility decisions
```

## Where Scenarios Come From

Scenarios come from two sources — **code exploration** and **domain knowledge** — and the best scenarios combine both.

### Source 1: Defensive Code Patterns (Code Exploration)

Every defensive pattern is evidence of a past failure or known risk:

1. **Defensive code** — Every `if value is None: return` guard is a scenario. Why was it needed?
2. **Normalization functions** — Every function that cleans input exists because raw input caused problems
3. **Configuration that could be hardcoded** — If a value is read from config instead of hardcoded, someone learned the value varies
4. **Git blame / commit messages** — "Fix crash when X is missing" → Scenario: X can be missing
5. **Comments explaining "why"** — "We use hash(id) not sequential index because..." → Scenario about correctness under that constraint

### Source 2: What Could Go Wrong (Domain Knowledge)

Don't limit yourself to what the code already defends against. Use your knowledge of similar systems to generate realistic failure scenarios that the code **should** handle. For every major subsystem, ask:

- "What happens if this process is killed mid-operation?" (state machines, file I/O, batch processing)
- "What happens if external input is subtly wrong?" (validation pipelines, API integrations)
- "What happens if this runs at 10x scale?" (batch processing, databases, queues)
- "What happens if two operations overlap?" (concurrency, file locks, shared state)
- "What produces correct-looking output that is actually wrong?" (randomness, statistical operations, type coercion)

These are not hypothetical — they are things that happen to every system of this type. Write them as **architectural vulnerability analyses**: "Because `save_state()` lacks an atomic rename pattern, a mid-write crash during a 10,000-record batch will leave a corrupted state file — the next run gets JSONDecodeError and cannot resume without manual intervention. At scale (9,240 records across 64 batches), this pattern risks silent loss of 1,693+ records with nothing to flag them as missing." Concrete numbers and specific consequences make scenarios authoritative and non-negotiable. An AI session reading "records can be lost" will argue the standard down. An AI session reading a specific failure mode with quantified impact will not.

### The Narrative Voice

Each scenario's "What happened" must read like an architectural vulnerability analysis, not an abstract specification. Include:

- **Specific quantities** — "308 records across 64 batches" not "some records"
- **Cascade consequences** — "cascading through all subsequent pipeline steps, requiring reprocessing of 4,300 records instead of 308"
- **Detection difficulty** — "nothing would flag them as missing" or "only statistical verification would catch it"
- **Root cause in code** — "`random.seed(index)` creates correlated sequences because sequential integers produce related random streams"

The narrative voice serves a critical purpose: it makes standards non-negotiable. Abstract requirements ("records should not be lost") invite rationalization. Specific failure modes with quantified impact ("a mid-batch crash silently loses 1,693 records with no detection mechanism") do not. Frame these as "this architecture permits the following failure" — grounded in the actual code, not fabricated as past incidents.

### Combining Both Sources

The strongest scenarios combine a defensive pattern found in code with domain knowledge about why it matters:

1. Find the defensive code: `save_state()` writes to a temp file then renames
2. Ask what failure this prevents: mid-write crash leaves corrupted state file
3. Write the scenario as a vulnerability analysis: "Without the atomic rename pattern, a crash mid-write leaves state.json 50% complete. The next run gets JSONDecodeError and cannot resume without manual intervention."
4. Ground it in code: "Read persistence.py line ~340: verify temp file + rename pattern"

### The "Why" Requirement

Every coverage target, every quality gate, every standard must have a "why" that references a specific scenario or risk. Without rationale, a future AI session will optimize for speed and argue the standard down.

Bad: "Core logic: 100% coverage"
Good: "Core logic: 100% — because `random.seed(index)` created correlated sequences that produced 77.5% bias instead of 50/50. Subtle bugs here produce plausible-but-wrong output. Only statistical verification catches them."

The "why" is not documentation — it is protection against erosion.

## Calibrating Scenario Count

Aim for 2+ scenarios per core module (the modules identified as most complex or fragile). For a medium-sized project, this typically yields 8–10 scenarios. Fewer is fine for small projects; more for complex ones. If you're finding very few scenarios, it usually means the exploration was shallow rather than the project being simple — go back and read function bodies more carefully. Quality matters more than count: one scenario that precisely captures an architectural vulnerability is worth more than three generic "what if the input is bad" scenarios.

## Self-Critique Before Finishing

After drafting all scenarios, review each one and ask:

1. **"Would an AI session argue this standard down?"** If yes, the "why" isn't concrete enough. Add numbers, consequences, and detection difficulty.
2. **"Does the 'What happened' read like a vulnerability analysis or an abstract spec?"** If it reads like a spec, rewrite it with specific quantities, cascading consequences, and grounding in actual code.
3. **"Is there a scenario I'm not seeing?"** Think about what a different AI model would flag. Architecture models catch data flow problems. Edge-case models catch boundary conditions. What are you blind to?

## Critical Rule

Each scenario's "How to verify" section must map to at least one automated test in the functional test file. If a scenario can't be automated, note why (it may require the Human Gate) — but most scenarios should be testable.
