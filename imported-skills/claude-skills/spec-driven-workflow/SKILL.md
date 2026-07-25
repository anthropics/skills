---
name: "spec-driven-workflow"
description: "Use when the user asks to write specs before code, define acceptance criteria, plan features before implementation, generate tests from specifications, or follow spec-first development practices."
---

# Spec-Driven Workflow — POWERFUL

## Overview

Spec-driven workflow enforces a single, non-negotiable rule: **write the specification BEFORE you write any code.** Not alongside. Not after. Before.

This is not documentation. This is a contract. A spec defines what the system MUST do, what it SHOULD do, and what it explicitly WILL NOT do. Every line of code you write traces back to a requirement in the spec. Every test traces back to an acceptance criterion. If it is not in the spec, it does not get built.

### Why Spec-First Matters

1. **Eliminates rework.** 60-80% of defects originate from requirements, not implementation. Catching ambiguity in a spec costs minutes; catching it in production costs days.
2. **Forces clarity.** If you cannot write what the system should do in plain language, you do not understand the problem well enough to write code.
3. **Enables parallelism.** Once a spec is approved, frontend, backend, QA, and documentation can all start simultaneously.
4. **Creates accountability.** The spec is the definition of done. No arguments about whether a feature is "complete" — either it satisfies the acceptance criteria or it does not.
5. **Feeds TDD directly.** Acceptance criteria in Given/When/Then format translate 1:1 into test cases. The spec IS the test plan.

### The Iron Law

```
NO CODE WITHOUT AN APPROVED SPEC.
NO EXCEPTIONS. NO "QUICK PROTOTYPES." NO "I'LL DOCUMENT IT LATER."
```

If the spec is not written, reviewed, and approved, implementation does not begin. Period.

---

## The Spec Format

Every spec follows this structure. No sections are optional — if a section does not apply, write "N/A — [reason]" so reviewers know it was considered, not forgotten.

### Mandatory Sections

| # | Section | Key Rules |
|---|---------|-----------|
| 1 | **Title and Metadata** | Author, date, status (Draft/In Review/Approved/Superseded), reviewers |
| 2 | **Context** | Why this feature exists. 2-4 paragraphs with evidence (metrics, tickets). |
| 3 | **Functional Requirements** | RFC 2119 keywords (MUST/SHOULD/MAY). Numbered FR-N. Each is atomic and testable. |
| 4 | **Non-Functional Requirements** | Performance, security, accessibility, scalability, reliability — all with measurable thresholds. |
| 5 | **Acceptance Criteria** | Given/When/Then format. Every AC references at least one FR-* or NFR-*. |
| 6 | **Edge Cases** | Numbered EC-N. Cover failure modes for every external dependency. |
| 7 | **API Contracts** | TypeScript-style interfaces. Cover success and error responses. |
| 8 | **Data Models** | Table format with field, type, constraints. Every entity from requirements must have a model. |
| 9 | **Out of Scope** | Explicit exclusions with reasons. Prevents scope creep during implementation. |

### RFC 2119 Keywords

| Keyword | Meaning |
|---------|---------|
| **MUST** | Absolute requirement. Non-conformant without it. |
| **MUST NOT** | Absolute prohibition. |
| **SHOULD** | Recommended. Omit only with documented justification. |
| **MAY** | Optional. Implementer's discretion. |

See [spec_format_guide.md](references/spec_format_guide.md) for the complete template with section-by-section examples, good/bad requirement patterns, and feature-type templates (CRUD, Integration, Migration).

See [acceptance_criteria_patterns.md](references/acceptance_criteria_patterns.md) for a full pattern library of Given/When/Then criteria across authentication, CRUD, search, file upload, payment, notification, and accessibility scenarios.

---

## Bounded Autonomy Rules

These rules define when an agent (human or AI) MUST stop and ask for guidance vs. when they can proceed independently.

### STOP and Ask When:

1. **Scope creep detected.** The implementation requires something not in the spec. Even if it seems obviously needed, STOP. The spec might have excluded it deliberately.

2. **Ambiguity exceeds 30%.** If you cannot determine the correct behavior from the spec for more than 30% of a given requirement, the spec is incomplete. Do not guess.

3. **Breaking changes required.** The implementation would change an existing API contract, database schema, or public interface. Always escalate.

4. **Security implications.** Any change that touches authentication, authorization, encryption, or PII handling requires explicit approval.

5. **Performance characteristics unknown.** If a requirement says "MUST complete in < 500ms" but you have no way to measure or guarantee that, escalate before implementing a guess.

6. **Cross-team dependencies.** If the spec requires coordination with another team or service, confirm the dependency before building against it.

### Continue Autonomously When:

1. **Spec is clear and unambiguous** for the current task.
2. **All acceptance criteria have passing tests** and you are refactoring internals.
3. **Changes are non-breaking** — no public API, schema, or behavior changes.
4. **Implementation is a direct translation** of a well-defined acceptance criterion.
5. **Error handling follows established patterns** already documented in the codebase.

### Escalation Protocol

When you must stop, provide:

```markdown
## Escalation: [Brief Title]

**Blocked on:** [requirement ID, e.g., FR-3]
**Question:** [Specific, answerable question — not "what should I do?"]
**Options considered:**
  A. [Option] — Pros: [...] Cons: [...]
  B. [Option] — Pros: [...] Cons: [...]
**My recommendation:** [A or B, with reasoning]
**Impact of waiting:** [What is blocked until this is resolved?]
```

Never escalate without a recommendation. Never present an open-ended question. Always give options.

See `references/bounded_autonomy_rules.md` for the complete decision matrix.

---

## Workflow — 6 Phases

### Phase 1: Gather Requirements

**Goal:** Understand what needs to be built and why.

1. **Interview the user.** Ask:
   - What problem does this solve?
   - Who are the users?
   - What does success look like?
   - What explicitly should NOT be built?
2. **Read existing code.** Understand the current system before proposing changes.
3. **Identify constraints.** Performance budgets, security requirements, backward compatibility.
4. **List unknowns.** Every unknown is a risk. Surface them now, not during implementation.

**Exit criteria:** You can explain the feature to someone unfamiliar with the project in 2 minutes.

### Phase 2: Write Spec

**Goal:** Produce a complete spec document following The Spec Format above.

1. Fill every section of the template. No section left blank.
2. Number all requirements (FR-*, NFR-*, AC-*, EC-*, OS-*).
3. Use RFC 2119 keywords precisely.
4. Write acceptance criteria in Given/When/Then format.
5. Define API contracts with TypeScript-style types.
6. List explicit exclusions in Out of Scope.

**Exit criteria:** The spec can be handed to a developer who was not in the requirements meeting, and they can implement the feature without asking clarifying questions.

### Phase 3: Validate Spec

**Goal:** Verify the spec is complete, consistent, and implementable.

Run `spec_validator.py` against the spec file:

```bash
python spec_validator.py --file spec.md --strict
```

Manual validation checklist:
- [ ] Every functional requirement has at least one acceptance criterion
- [ ] Every acceptance criterion is testable (no subjective language)
- [ ] API contracts cover all endpoints mentioned in requirements
- [ ] Data models cover all entities mentioned in requirements
- [ ] Edge cases cover failure modes for every external dependency
- [ ] Out of scope is explicit about what was considered and rejected
- [ ] Non-functional requirements have measurable thresholds

**Exit criteria:** Spec scores 80+ on validator, and all manual checklist items pass.

### Phase 4: Generate Tests

**Goal:** Extract test cases from acceptance criteria before writing implementation code.

Run `test_extractor.py` against the approved spec:

```bash
python test_extractor.py --file spec.md --framework pytest --output tests/
```

1. Each acceptance criterion becomes one or more test cases.
2. Each edge case becomes a test case.
3. Tests are stubs — they define the assertion but not the implementation.
4. All tests MUST fail initially (red phase of TDD).

**Exit criteria:** You have a test file where every test fails with "not implemented" or equivalent.

### Phase 5: Implement

**Goal:** Write code that makes failing tests pass, one acceptance criterion at a time.

1. Pick one acceptance criterion (start with the simplest).
2. Make its test(s) pass with minimal code.
3. Run the full test suite — no regressions.
4. Commit.
5. Pick the next acceptance criterion. Repeat.

**Rules:**
- Do NOT implement anything not in the spec.
- Do NOT optimize before all acceptance criteria pass.
- Do NOT refactor before all acceptance criteria pass.
- If you discover a missing requirement, STOP and update the spec first.

**Exit criteria:** All tests pass. All acceptance criteria satisfied.

### Phase 6: Self-Review

**Goal:** Verify implementation matches spec before marking done.

Run through the Self-Review Checklist below. If any item fails, fix it before declaring the task complete.

---

## Self-Review Checklist

Before marking any implementation as done, verify ALL of the following:

- [ ] **Every acceptance criterion has a passing test.** No exceptions. If AC-3 exists, a test for AC-3 exists and passes.
- [ ] **Every edge case has a test.** EC-1 through EC-N all have corresponding test cases.
- [ ] **No scope creep.** The implementation does not include features not in the spec. If you added something, either update the spec or remove it.
- [ ] **API contracts match implementation.** Request/response shapes in code match the spec exactly. Field names, types, status codes — all of it.
- [ ] **Error scenarios tested.** Every error response defined in the spec has a test that triggers it.
- [ ] **Non-functional requirements verified.** If the spec says < 500ms, you have evidence (benchmark, load test, profiling) that it meets the threshold.
- [ ] **Data model matches.** Database schema matches the spec. No extra columns, no missing constraints.
- [ ] **Out-of-scope items not built.** Double-check that nothing from the Out of Scope section leaked into the implementation.

---

## Integration with TDD Guide

Spec-driven workflow and TDD are complementary, not competing:

```
Spec-Driven Workflow          TDD (Red-Green-Refactor)
─────────────────────         ──────────────────────────
Phase 1: Gather Requirements
Phase 2: Write Spec
Phase 3: Validate Spec
Phase 4: Generate Tests  ──→  RED: Tests exist and fail
Phase 5: Implement       ──→  GREEN: Minimal code to pass
Phase 6: Self-Review     ──→  REFACTOR: Clean up internals
```

**The handoff:** Spec-driven workflow produces the test stubs (Phase 4). TDD takes over from there. The spec tells you WHAT to test. TDD tells you HOW to implement.

Use `engineering-team/tdd-guide` for:
- Red-green-refactor cycle discipline
- Coverage analysis and gap detection
- Framework-specific test patterns (Jest, Pytest, JUnit)

Use `engineering/spec-driven-workflow` for:
- Defining what to build before building it
- Acceptance criteria authoring
- Completeness validation
- Scope control

---

## Examples

A complete worked example (Password Reset spec with extracted test cases) is available in [spec_format_guide.md](references/spec_format_guide.md#full-example-password-reset). It demonstrates all 9 sections, requirement numbering, acceptance criteria, edge cases, and the corresponding pytest stubs generated by `test_extractor.py`.

---

## Anti-Patterns

### 1. Coding Before Spec Approval

**Symptom:** "I'll start coding while the spec is being reviewed."
**Problem:** The review will surface changes. Now you have code that implements a rejected design.
**Rule:** Implementation does not begin until spec status is "Approved."

### 2. Vague Acceptance Criteria

**Symptom:** "The system should work well" or "The UI should be responsive."
**Problem:** Untestable. What does "well" mean? What does "responsive" mean?
**Rule:** Every acceptance criterion must be verifiable by a machine. If you cannot write a test for it, rewrite the criterion.

### 3. Missing Edge Cases

**Symptom:** Happy path is specified, error paths are not.
**Problem:** Developers invent error handling on the fly, leading to inconsistent behavior.
**Rule:** For every external dependency (API, database, file system, user input), specify at least one failure scenario.

### 4. Spec as Post-Hoc Documentation

**Symptom:** "Let me write the spec now that the feature is done."
**Problem:** This is documentation, not specification. It describes what was built, not what should have been built. It cannot catch design errors because the design is already frozen.
**Rule:** If the spec was written after the code, it is not a spec. Relabel it as documentation.

### 5. Gold-Plating Beyond Spec

**Symptom:** "While I was in there, I also added..."
**Problem:** Untested code. Unreviewed design. Potential for subtle bugs in the "bonus" feature.
**Rule:** If it is not in the spec, it does not get built. File a new spec for additional features.

### 6. Acceptance Criteria Without Requirement Traceability

**Symptom:** AC-7 exists but does not reference any FR-* or NFR-*.
**Problem:** Orphaned criteria mean either a requirement is missing or the criterion is unnecessary.
**Rule:** Every AC-* MUST reference at least one FR-* or NFR-*.

### 7. Skipping Validation

**Symptom:** "The spec looks fine, let's just start."
**Problem:** Missing sections discovered during implementation cause blocking delays.
**Rule:** Always run `spec_validator.py --strict` before starting implementation. Fix all warnings.

---

## Cross-References

- **`engineering-team/tdd-guide`** — Red-green-refactor cycle, test generation, coverage analysis. Use after Phase 4 of this workflow.
- **`engineering/focused-fix`** — Deep-dive feature repair. When a spec-driven implementation has systemic issues, use focused-fix for diagnosis.
- **`engineering/rag-architect`** — If the feature involves retrieval or knowledge systems, use rag-architect for the technical design within the spec.
- **`references/spec_format_guide.md`** — Complete template with section-by-section explanations.
- **`references/bounded_autonomy_rules.md`** — Full decision matrix for when to stop vs. continue.
- **`references/acceptance_criteria_patterns.md`** — Pattern library for writing Given/When/Then criteria.

---

## Tools

| Script | Purpose | Key Flags |
|--------|---------|-----------|
| `spec_generator.py` | Generate spec template from feature name/description | `--name`, `--description`, `--format`, `--json` |
| `spec_validator.py` | Validate spec completeness (0-100 score) | `--file`, `--strict`, `--json` |
| `test_extractor.py` | Extract test stubs from acceptance criteria | `--file`, `--framework`, `--output`, `--json` |

```bash
# Generate a spec template
python spec_generator.py --name "User Authentication" --description "OAuth 2.0 login flow"

# Validate a spec
python spec_validator.py --file specs/auth.md --strict

# Extract test cases
python test_extractor.py --file specs/auth.md --framework pytest --output tests/test_auth.py
```
