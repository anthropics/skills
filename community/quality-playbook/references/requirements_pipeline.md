# Requirements Pipeline

## Overview

This document defines the five-phase requirements generation pipeline for Step 7 of the Quality Playbook. The pipeline separates contract discovery from requirement derivation, uses file-based external memory so the model doesn't need to hold everything in context simultaneously, and includes mechanical verification with a completeness gate.

**Why a pipeline?** Single-pass requirement generation runs out of attention after ~70 requirements because the model is simultaneously discovering contracts and writing formal requirements. Separating these into distinct phases with file-based handoffs produces significantly more complete coverage. In testing on Gson (81 source files, ~21K lines), single-pass produced 48 requirements; the pipeline produced 110.

## Files produced

| File | Purpose |
|------|---------|
| `quality/CONTRACTS.md` | Raw behavioral contracts extracted from source |
| `quality/REQUIREMENTS.md` | Testable requirements with narrative (the primary deliverable) |
| `quality/COVERAGE_MATRIX.md` | Contract-to-requirement traceability |
| `quality/COMPLETENESS_REPORT.md` | Final completeness assessment with verdict |
| `quality/VERSION_HISTORY.md` | Review log with version table and provenance |
| `quality/REFINEMENT_HINTS.md` | Review progress and feedback (created during review) |

Versioned backups go in `quality/history/vX.Y/`.

---

## Phase A: Extract behavioral contracts

**Input:** All source files in the project (or a scoped subsystem — see scaling check below).
**Output:** `quality/CONTRACTS.md`

### Scaling check

Before starting extraction, count the source files in the project (exclude tests, generated code, vendored dependencies, and build artifacts).

- **Standard project (≤300 source files):** Proceed normally — extract contracts from all files. Projects in this range have been tested end-to-end (e.g., Gson at ~81 source files produced 110 requirements with full coverage).
- **Large project (301–500 source files):** Focus on the 3–5 core subsystems identified in Phase 1, Step 2. Extract contracts from those modules and their internal dependencies. Note the scope in the CONTRACTS.md header so reviewers know what was covered.
- **Very large project (>500 source files):** Recommend that the user scope the pipeline to one subsystem at a time. Each subsystem gets its own pipeline run producing its own REQUIREMENTS.md, CONTRACTS.md, etc. Tell the user: "This project has N source files. For best results, run the requirements pipeline separately for each major subsystem (e.g., 'Generate requirements for the authentication module'). A single pipeline run across the full codebase will miss contracts due to context limits."

If the user explicitly asks for full-project scope on a large codebase, honor the request but warn that coverage will be thinner than subsystem-level runs.

### Scope breadth on the initial pass

On the first pipeline run, favor breadth over depth. Cover all major subsystems and modules rather than going deep on a few. The goal is a broad baseline that the self-refinement loop and later review/refinement passes can deepen. If you focus on 3 modules and skip 8 others, the completeness check can't find gaps in modules it never saw.

For projects with both a core library and supporting modules (middleware, plugins, adapters, extensions), include at least the core and the highest-risk supporting modules in Phase A. Note the scope in the CONTRACTS.md header so it's clear what was covered and what wasn't. Refinement passes can expand scope later, but the initial pass should cast the widest net the context window allows.

### Contract extraction

Read every source file (within scope) and list every behavioral contract it implements or should implement. A behavioral contract is any promise the code makes to its callers:

- **METHOD**: What a public method guarantees about return value, side effects, exceptions, thread safety
- **NULL**: What happens when null is passed, returned, or stored
- **CONFIG**: What effect a configuration option has at its boundaries
- **ERROR**: What exceptions are thrown, when, and with what diagnostic information
- **INVARIANT**: Properties that must always hold
- **COMPAT**: Behaviors preserved for backward compatibility
- **ORDER**: Whether output/iteration order is stable, documented, or undefined
- **LIFECYCLE**: Resource creation/cleanup, initialization sequencing
- **THREAD**: Thread-safety guarantees or requirements

### Contract extraction rules

- **Be thorough.** For a 200-line file, expect 5–15 contracts. For a 1000-line file, expect 20–40. If you're finding fewer than 3 contracts in a file with real logic, you're skipping things.
- **Include internal files.** Internal contracts matter because the public API depends on them.
- **Include "should exist" contracts** — things the code doesn't do but should based on its domain. These catch absence bugs.
- **Read the code, not just the Javadoc/docstrings.** When documentation and code disagree, list both.
- **This is discovery, not judgment.** List everything, even if it seems obvious.

### Output format

```
# Behavioral Contract Extraction
Generated: [date]
Source files analyzed: N
Total contracts extracted: N

## Summary by category
- METHOD: N
- NULL: N
- CONFIG: N
[etc.]

### path/to/file.ext (N contracts)

1. [METHOD] ClassName.methodName(): description of what it guarantees
2. [NULL] ClassName.methodName(): what happens when null is passed/returned
[etc.]
```

---

### Requirement heading format

All requirements in REQUIREMENTS.md must use the format `### REQ-NNN: Title` where NNN is a zero-padded three-digit number and Title is a short descriptive name. Do not use alternative formats like `### REQ-NNN — Title`, `### REQ-NNN. Title`, `**REQ-NNN**: Title`, or freeform headings without a number. Consistent formatting enables automated tooling to parse and cross-reference requirements.

---

## Phase B: Derive requirements from contracts

**Input:** `quality/CONTRACTS.md`, project documentation, SKILL.md Step 7 template.
**Output:** `quality/REQUIREMENTS.md`

### How to work

**B.1 — Group related contracts.** Many contracts across different files serve the same behavioral requirement. Group them by behavioral concern, not by file. Don't merge unrelated contracts just because they're in the same file.

**B.2 — Enrich with intent.** For each group, find the user story from documentation: GitHub issues state what users expect, the user guide states intended behavior, troubleshooting docs reveal known edge cases, design docs explain design goals. The "so that" clause must come from understanding who cares and why.

**B.3 — Write requirements.** Use the 7-field template from SKILL.md Step 7. Conditions of satisfaction come from the individual contracts in the group — each contract becomes a condition of satisfaction.

**B.4 — Check for orphan contracts.** After writing all requirements, verify every contract in CONTRACTS.md is covered. Uncovered contracts become new requirements or get added to existing requirements' conditions of satisfaction.

### Rules

- **Do not cap the requirement count.** Write as many as the contracts warrant.
- **Every contract must map to at least one requirement.**
- **One requirement per distinct behavioral concern.** Don't merge "thread safety" with "null handling" just because they're in the same class.
- **Do not modify CONTRACTS.md.** Only read it.

---

## Phase C: Verify coverage (loop, max 3 iterations)

**Input:** `quality/CONTRACTS.md`, `quality/REQUIREMENTS.md`
**Output:** `quality/COVERAGE_MATRIX.md`, updated `quality/REQUIREMENTS.md`

For every contract in CONTRACTS.md, determine whether it is covered by a requirement. A contract is "covered" if a requirement's conditions of satisfaction explicitly test the behavior. A contract is NOT covered if it's only tangentially mentioned, implied but not stated, or if a different aspect of the same file is covered but this specific contract isn't.

### Output format

```
# Contract Coverage Matrix
Generated: [date]
Total contracts: N
Covered: N (percentage)
Uncovered: N (percentage)
Partially covered: N (percentage)

## Fully covered contracts
[file]: [contract summary] → REQ-NNN (conditions of satisfaction #M)

## Partially covered contracts
[file]: [contract summary] → REQ-NNN covers the general area but misses [specific aspect]

## Uncovered contracts
[file]: [contract summary] → No requirement addresses this behavior
```

After writing the matrix, fix gaps in REQUIREMENTS.md: add missing conditions to existing requirements or create new requirements. Report changes.

**Loop termination:** If uncovered count reaches 0, proceed to Phase D. Otherwise, regenerate the matrix and check again. Maximum 3 iterations.

---

## Phase D: Completeness check

**Input:** `quality/REQUIREMENTS.md`, `quality/CONTRACTS.md`, `quality/COVERAGE_MATRIX.md`, source tree.
**Output:** `quality/COMPLETENESS_REPORT.md`, updated `quality/REQUIREMENTS.md`

This is the final gate before the narrative pass. Run three checks:

### Check 1: Domain completeness

The following behavioral domains MUST have requirements. Check each one. This checklist is a minimum — if you notice a domain not listed that should have requirements for this project's domain, add it.

- [ ] **Null handling:** explicit null, absent fields, null keys, null values in collections
- [ ] **Type coercion:** string↔number, string↔boolean, number precision, overflow
- [ ] **Primitive vs wrapper:** primitive vs object null semantics during deserialization (for languages with this distinction)
- [ ] **Generic types:** erasure boundaries, wildcard handling, recursive generics (for languages with generics)
- [ ] **Thread safety:** concurrent access, publication safety, cache visibility
- [ ] **Error diagnostics:** exception types, path context, location information
- [ ] **Resource management:** stream closing, reader/writer lifecycle
- [ ] **Backward compatibility:** wire format stability, API behavioral stability
- [ ] **Security:** DoS protection (nesting depth, string length), injection prevention
- [ ] **Encoding:** Unicode, BOM, surrogate pairs, escape sequences
- [ ] **Date/time:** format precedence, timezone handling, precision
- [ ] **Collections:** arrays, lists, sets, maps, queues — empty, null elements, ordering
- [ ] **Enums:** name resolution, aliases, unknown values
- [ ] **Polymorphism:** runtime type vs declared type, adapter/handler delegation
- [ ] **Tree model / intermediate representation:** mutation semantics, deep copy structural independence, null normalization
- [ ] **Configuration:** builder immutability, instance isolation, option composition
- [ ] **Entry points:** every distinct public entry point must have its own contract — string-based, stream-based, tree-based, standalone parsing, multi-value parsing. If the library has N ways to start a read or write, there must be N sets of contracts.
- [ ] **Output escaping:** which characters are escaped by default, what disabling escaping changes, how builder-level and writer-level controls interact
- [ ] **Built-in type handler contracts:** for each built-in handler that processes a standard library type, state what it promises about format, precision, normalization, and round-trip fidelity. The requirement should specify the handler's promise, not just that a handler exists.
- [ ] **Field/property serialization ordering:** whether output order follows declaration order, inheritance order, alphabetical order, or is undefined. State whether ordering is a promised contract or merely observed behavior.
- [ ] **Identity contracts for public types:** `toString()`, `hashCode()`/`equals()` (or language equivalent) on public model types. These are behavioral contracts users depend on for comparison, logging, and collection key usage.
- [ ] **Input validation:** for every configuration field with domain constraints, state the valid range and whether validation exists.

For each domain, either cite the REQ-NNN numbers that cover it or flag it as a gap.

### Check 2: Testability audit

For each requirement, check whether its conditions of satisfaction are actually testable. Can a reviewer write a concrete test case from this condition? Is pass/fail unambiguous? Does the condition cover failure modes, not just the happy path?

### Check 3: Cross-requirement consistency

Check pairs of requirements that reference the same concept. Do ranges agree? Do null-handling rules agree? Do thread-safety guarantees conflict with lifecycle contracts? Do configuration defaults match across requirements?

### Check 4: Cross-artifact consistency (if code review or spec audit results exist)

If `quality/code_reviews/` or `quality/spec_audits/` contain results from a previous or current run, read them. For every finding with status VIOLATED, BUG, or INCONSISTENT, check whether the requirements address the behavioral concern that finding targets. If a code review found a bug in compression header parsing that the requirements don't cover, that's a completeness gap — add a requirement or conditions of satisfaction to close it.

**The completeness report cannot say COMPLETE if unaddressed findings exist.** If any VIOLATED/BUG/INCONSISTENT finding from code review or spec audit targets behavior not covered by requirements, the verdict must be INCOMPLETE with the specific gaps listed.

This check exists because earlier versions of the pipeline produced completeness reports that said "COMPLETE" while the code review in the same run found requirement violations. The completeness report must be consistent with all other quality artifacts.

### Post-review completeness refresh (mandatory)

**After the code review and spec audit are complete**, re-read `quality/COMPLETENESS_REPORT.md` and update it. The initial completeness report was written before the code review and spec audit ran, so it cannot reflect their findings. This refresh step reconciles the completeness verdict with the actual review results.

**Procedure:**
1. Read the combined summary from `quality/code_reviews/` — count VIOLATED and BUG findings.
2. Read the triage summary from `quality/spec_audits/` — count confirmed code bugs.
3. For each finding, check whether REQUIREMENTS.md has a requirement covering that behavior.
4. Append a `## Post-Review Reconciliation` section to COMPLETENESS_REPORT.md:

```
## Post-Review Reconciliation
Updated: [date]

### Code review findings: N VIOLATED, M BUG
- [finding summary] → covered by REQ-NNN / NOT COVERED (gap)
- ...

### Spec audit findings: N confirmed code bugs
- [finding summary] → covered by REQ-NNN / NOT COVERED (gap)
- ...

### Updated verdict
[COMPLETE if all findings are covered by requirements, INCOMPLETE if gaps remain]
```

5. If the original verdict was COMPLETE but unaddressed findings exist, change the verdict to INCOMPLETE.

### Resolving code review vs spec audit conflicts

When the code review and spec audit disagree about the same behavioral claim — one says BUG, the other says design choice or false positive — the reconciliation must resolve the conflict, not paper over it.

**Resolution procedure:**
1. Identify the factual claim at the center of the disagreement. What does the code actually do?
2. Deploy a verification probe: give a model the disputed claim and the relevant source code, and ask it to report ground truth. (See `spec_audit.md` § "The Verification Probe.")
3. Record the resolution in the Post-Review Reconciliation section:
   ```
   ### Conflicts resolved
   - [finding description]: Code review said [X], spec audit said [Y].
     Verification probe: [what the code actually does].
     Resolution: [BUG CONFIRMED / FALSE POSITIVE / DESIGN CHOICE]. [Explanation.]
   ```
4. If the resolution confirms a BUG, ensure it has a regression test. If the resolution overturns a BUG, clean up the regression test per `review_protocols.md` § "Cleaning up after spec audit reversals."

**Do not resolve conflicts by defaulting to one source.** Neither the code review nor the spec audit is automatically more authoritative — they use different methods (structural reading vs. spec comparison) and have different blind spots. The verification probe is the tiebreaker.

**This refresh is not optional.** A completeness report that predates the code review is a timestamp, not a quality gate. The refresh turns it into an actual reconciliation.

### Output format

```
# Completeness Report
Generated: [date]

## Domain coverage
[For each domain: COVERED (REQ-NNN, REQ-NNN) or GAP (description)]

## Testability issues
[For each vague requirement: REQ-NNN — condition N is not testable because...]

## Consistency issues
[For each conflict: REQ-NNN and REQ-NNN disagree about...]

## Cross-artifact gaps (if code review/spec audit results exist)
[For each unaddressed finding: finding summary → missing requirement or condition]

## Verdict
COMPLETE or INCOMPLETE with recommended actions
```

Then fix what you can: add requirements for domain gaps, sharpen vague conditions, resolve consistency issues, and close cross-artifact gaps.

**Important:** This is the final check. Be adversarial. Assume previous passes were imperfect. For each domain marked COVERED, verify that the cited requirements actually address the checklist item — don't just check the box.

### Self-refinement loop (max 3 iterations)

After the initial completeness check, run up to 3 refinement iterations to close the gaps Phase D identified:

1. **Read the completeness report.** Identify all GAP entries, testability issues, and consistency issues.
2. **Fix gaps in REQUIREMENTS.md.** For each GAP: add a new requirement using the 7-field template, or add conditions of satisfaction to an existing requirement. For testability issues: sharpen the condition. For consistency issues: resolve the conflict.
3. **Re-run all three checks** (domain completeness, testability audit, cross-requirement consistency). Write the updated results to COMPLETENESS_REPORT.md.
4. **Count the delta.** How many new requirements were added or existing requirements modified in this iteration?
5. **Short-circuit check:** If the delta is fewer than 3 changes, stop — you've hit diminishing returns. Proceed to Phase E.

**Why this works:** The initial completeness check identifies gaps but the model may not fix all of them in one pass, especially conceptual gaps where the model needs to re-read source files to understand what's missing. Each iteration shrinks the gap. Three iterations is enough to close the mechanical gaps; the remaining conceptual gaps are where cross-model audit and human review earn their keep.

**Why it has limits:** This is self-refinement — the same model checking its own work. It catches gaps the model can see once they're pointed out (uncovered domains, vague conditions, numeric inconsistencies) but won't catch blind spots the model doesn't recognize as gaps. That's by design. The review and refinement protocols exist for closing those deeper gaps with different models or human input.

After the loop completes (or short-circuits), proceed to Phase E.

---

## Phase E: Narrative pass

**Input:** `quality/REQUIREMENTS.md`, `quality/CONTRACTS.md`, project documentation, source tree.
**Output:** Restructured `quality/REQUIREMENTS.md`

**Before starting:** Save a backup: `cp quality/REQUIREMENTS.md quality/REQUIREMENTS_pre_narrative.md`

This phase transforms the specification into a guide. Add explanatory tissue so a new team member, code reviewer, or AI agent can read the document top-to-bottom and understand the software.

### E.1 — Project overview (new, top of document)

Write 400–600 words of connected prose explaining: what the software is, who uses it and why (primary personas and goals), how data flows through the major components, and the design philosophy (key architectural decisions and why they were made).

### E.2 — Use cases (new, after overview)

Write 6–8 use cases in the style of Applied Software Project Management (Stellman & Greene). Each has:

- **Name**: Short descriptive name
- **Actor**: Who initiates it
- **Preconditions**: What must be true before this begins
- **Steps**: Numbered actor/system action sequence
- **Postconditions**: What is true on success
- **Alternative paths**: Variations and error cases
- **Requirements**: Which REQ-NNN numbers this use case exercises

Cover the major usage patterns. The use cases are the bridge between "what the software does" and "what the requirements specify."

### E.3 — Cross-cutting concerns (new, after use cases)

Document architectural invariants that span multiple categories: threading model, null contract, error philosophy, backward compatibility strategy, configuration composition. Each references specific REQ-NNN numbers. Write as prose paragraphs.

### E.4 — Category narratives (augment existing)

For each requirement category, add 2–4 sentences before the first requirement explaining what the category covers, how it relates to other categories, and what a reviewer should keep in mind.

### E.5 — Reorder for top-down flow

Reorder categories from user-facing (entry points, configuration) to infrastructure (error handling, backward compatibility). Fold any catch-all sections into proper categories.

### E.6 — Renumber sequentially

After reordering, renumber all requirements REQ-001 through REQ-NNN following document order. Update all internal cross-references.

### Rules

- **Do not delete, merge, or weaken any existing requirement.**
- **Do not add new requirements in this pass.**
- **Write the overview and use cases from the user's perspective.**
- **Use cases must cite specific REQ numbers.**

---

## Versioning protocol

### Version scheme: major.minor

- **Major** bump: structural changes (new pipeline architecture, narrative pass added, major scope expansion). Bumped by the user.
- **Minor** bump: refinement passes, gap fills, sharpened conditions. Increments automatically on each pipeline run or refinement pass.

### VERSION_HISTORY.md

Maintain a version history file at `quality/VERSION_HISTORY.md`:

```markdown
# Requirements Version History

## Current version: vX.Y

| Version | Date | Model | Author | Reqs | Summary |
|---------|------|-------|--------|------|---------|
| v1.0 | YYYY-MM-DD | [model] | Quality Playbook | N | Initial pipeline generation |
| v1.1 | YYYY-MM-DD | [model] | [author] | N | [what changed] |

## Pending review
[status from REFINEMENT_HINTS.md if review is in progress]
```

The **Author** column records provenance: "Quality Playbook" for automated pipeline runs, a person's name for manual edits, a model name for refinement passes.

### Backup protocol

Before each version change, copy all quality files to `quality/history/vX.Y/`:

```
quality/history/
├── v1.0/
│   ├── REQUIREMENTS.md
│   ├── CONTRACTS.md
│   ├── COVERAGE_MATRIX.md
│   └── COMPLETENESS_REPORT.md
├── v1.1/
│   └── ...
└── v2.0/
    └── ...
```

Each version folder is a complete snapshot. Users can diff any two versions.

### Version stamping

The REQUIREMENTS.md header includes the current version:

```markdown
# Behavioral Requirements — [Project Name]
Version: vX.Y
Generated: [date]
Pipeline: contract-extraction v2 with narrative pass
```

---

## After the pipeline: review and refinement

The pipeline produces a solid baseline, but AI isn't 100% reliable. The skill provides two standalone tools for iterative improvement:

### Requirements review (`quality/REVIEW_REQUIREMENTS.md`)

An interactive or guided review of requirements organized by use case. Three modes:
- **Self-guided**: Pick use cases to drill into
- **Fully guided**: Walk through use cases sequentially
- **Cross-model audit**: A different model fact-checks the completeness report

Progress and feedback are tracked in `quality/REFINEMENT_HINTS.md`. See the generated `quality/REVIEW_REQUIREMENTS.md` for the full protocol.

### Requirements refinement (`quality/REFINE_REQUIREMENTS.md`)

Reads `quality/REFINEMENT_HINTS.md` and updates `quality/REQUIREMENTS.md` to close identified gaps. Can be run with any model. Backs up the current version, bumps minor version, reports all changes. See the generated `quality/REFINE_REQUIREMENTS.md` for the full protocol.

### Multi-model refinement

Users can run refinement passes with different models to catch different blind spots. Each pass: backup → refine → version bump → log in VERSION_HISTORY.md. Run as many models as desired until diminishing returns.
