---
name: synthesis-code-audit
description: >
  Systematic 10-dimension quality scan of code diffs, producing scored
  PASS/WARNING/FAIL verdicts per dimension with a machine-readable overall
  result. Includes PR review mode for cross-referencing findings against
  existing reviewer comments. Use when asked to: code audit, audit my changes,
  quality check, review the diff, check this code, audit my code, scan for
  issues, code quality scan, diff review.
license: "CC0-1.0"
depends_on: []
metadata:
  author: "Emil Peñaló"
  version: "1.0.0"
  source_repo: "github.com/synthesisengineering/synthesis-skills"
  source_type: "public"
---

# Synthesis Code Audit

A code audit is a systematic quality measurement of a diff. It is not a judgment call about whether a change should merge — that is the reviewer's job (see synthesis-pr-review). An audit produces a scored report across 10 orthogonal dimensions, each graded independently. The report tells you *where the quality problems are*; the reviewer decides *what to do about them*.

---

## Where This Fits

Three engineering skills evaluate code at different scopes:

| Skill | Scope | When to use |
|-------|-------|-------------|
| **code-audit** (this one) | Quality scan of a diff | After implementation, standalone or as input to preflight/pr-review |
| **pr-review** | Judgment-based delta review | Every PR, before peer approval or lead integration |
| **codebase-review** | Full system audit (16 categories, tiered) | Periodic health check or major milestone |

Code-audit produces findings. PR-review produces a verdict that may consume those findings. Codebase-review catches systemic patterns that no single diff reveals.

---

## Principles

1. **Fresh base branch.** Compare against an up-to-date base ref. Stale base branches cause false positives (flagging code already addressed upstream) and false negatives (missing new context on the base that changes interpretation).

2. **Read files in full, not just diff hunks.** A diff hunk shows what changed. The surrounding file shows whether the change makes sense in context. Always read changed files in their entirety.

3. **Context isolation.** The best audit comes from fresh eyes. If possible, evaluate the diff without prior knowledge of the planning decisions, trade-offs, or rationale that produced it. Confirmation bias is the default mode — you see what you expect to see. An isolated audit overrides that.

4. **Grade only what changed.** If a serious pre-existing issue is discovered in unchanged code (security vulnerability, data loss risk, race condition), note it as informational but do not let it affect the dimension's grade for this diff.

---

## Diff Scope Detection

Determine what to audit:

- **Uncommitted changes exist** — audit staged and unstaged changes against HEAD.
- **Branch has commits ahead of base** — audit the range from base to HEAD.
- **Nothing to diff** — report that and stop.

**Large diffs (40+ files):** Prioritize files with logic changes (source code, tests) over config, generated, and lock files. If the diff exceeds practical single-pass review scope, note this in the report and focus depth on the highest-risk changes.

---

## The 10-Dimension Framework

For each dimension, evaluate the changed code and assign one of:

- **PASS** — no issues, or only trivial stylistic preferences
- **WARNING** — potential problem that deserves attention but does not block shipping (missing edge-case test, minor inconsistency, could-be-better pattern)
- **FAIL** — concrete defect, security hole, convention violation, or missing coverage that should be fixed before merge

### 1. Project Convention Compliance

Read the project's convention documentation (style guides, architectural decision records, contribution guidelines). Check every changed file against the conventions that apply to it. Flag violations with a reference to the specific convention.

If the project has no documented conventions, skip this dimension and note it as N/A.

### 2. Code Reuse — Existing Before New

When the diff introduces a new component, utility, hook, or abstraction, search the codebase for existing implementations that serve the same purpose. If one exists, flag the new code and recommend using the existing implementation.

When the diff introduces a behavioral pattern (overlay management, keyboard navigation, positioning logic, state machine, API wrapper, error handling), search the broader codebase for functionally similar implementations — different code serving the same purpose is still duplication.

When multiple implementations of the same pattern are found, recommend extracting a shared primitive and migrating callers.

For any shared primitive — existing, introduced in this diff, or recommended for extraction — check whether the project's conventions document it. Undocumented shared primitives will be re-implemented by contributors who do not know they exist.

### 3. Consistency with Existing Patterns

Read 2-3 neighboring files in the same directory or module as each changed file. Note their naming conventions, file structure, export style, error handling approach, and architectural patterns.

Compare the diff against those observed patterns. Flag divergences that are not justified by the change's purpose.

### 4. Security

- Auth checks on all new endpoints
- No injection vectors (SQL injection, XSS, command injection)
- Input validation at system boundaries
- No secrets, credentials, or sensitive data in code, logs, or error messages
- ORM queries preferred over raw SQL (unless justified)

### 5. Scalability & Enterprise Readiness

- Efficient database queries (proper indexes, no N+1, pagination)
- Async patterns used correctly
- Proper logging for observability
- Resource cleanup (connections, file handles, subscriptions)

### 6. Future-Proofing (Without Over-Engineering)

- Extensible where extension is likely
- Migration-safe database changes
- Clean interfaces that do not leak implementation details
- No abstractions for hypothetical requirements

### 7. Code Quality

- DRY — no literal code duplication (copy-pasted blocks, repeated logic). Semantic duplication (different code serving the same purpose) belongs to Dimension 2.
- Single responsibility
- Readable and self-documenting
- Proper error handling at boundaries
- Type safety

### 8. Test Coverage

- New behavior has corresponding test additions or updates (or a clear reason why not)
- Existing test files were not removed or gutted without replacement
- Edge cases and error paths have test coverage

### 9. Documentation & Comments

- No project-management artifacts in code comments (plan phases, ticket numbers, sprint references)
- No stale comments from refactoring
- Complex logic has a "why" comment

### 10. Cleanup

- No dead code, unused imports, or leftover debug statements
- No TODO comments without context
- No commented-out code blocks
- Consistent formatting

---

## Reporting

Present findings as a table:

| # | Dimension | Result | Notes |
|---|-----------|--------|-------|
| 1 | Project Convention Compliance | PASS/WARNING/FAIL | details |
| 2 | Code Reuse | PASS/WARNING/FAIL | details |
| ... | ... | ... | ... |

Below the table, add a one-line verdict:

- **"Clean"** — all dimensions PASS
- **"Has warnings"** — one or more WARNING, no FAIL
- **"Has blockers"** — one or more FAIL

Then list actionable findings with file and line references. For each issue, state what is wrong and how to fix it.

---

## PR Review Mode (Cross-Referencing)

When invoked as part of a PR review workflow, existing reviewer comments may be available as context — a list of entries with reviewer, file path, line number, and comment body.

After completing all 10 dimensions, cross-reference each finding:

1. **File + Line match** — Is there an existing reviewer comment on the same file within +/-10 lines?
2. **Semantic match** — Does an existing comment raise the same category of concern (both flagging missing auth, both noting duplication)?
3. **Annotate each finding:**
   - `[Already noted by @reviewer]` — same or very similar concern at the same location
   - `[Related to @reviewer's comment on file:line]` — similar concern, different location
   - `[New finding]` — not covered by any existing reviewer

End with a **Cross-Reference Summary**: count of new findings vs. already-covered findings.

This mode does not change which dimensions are checked or how issues are evaluated — it only adds overlap annotations so the reviewer knows where their review adds new value vs. confirms existing feedback.

---

## Rules

- Always compare against a fresh base ref — never compare against a stale local ref
- Read changed files in full, not just diff hunks — context matters
- Check project convention documentation and apply project-specific rules explicitly
- Do not flag style nits in code that was not changed by this diff
- Pre-existing issues in unchanged code are informational only — they do not affect dimension grades
- If the audit is invoked by another workflow (preflight, PR review), return findings to that workflow for decision-making
