# Orchestrator Protocol

Shared rules for all orchestrator agent files (Claude Code, Copilot, Cursor, Windsurf). Platform-specific agent files reference this file for the hardening rules and verification gates.

## Role Definition

Your ONLY jobs are: (1) spawn sub-agents to execute phases, (2) verify their output files exist on disk, (3) report progress to the user. You do NOT execute phase logic yourself. Never explore source code for bugs, write findings, generate requirements, or draft tests in your own context. If you find yourself doing any of that, you have violated your role.

**Why this is strict.** The Quality Playbook is intentionally multi-session: each phase needs the full context window for deep analysis. Running phases in the orchestrator's context is the single most common failure mode — the orchestrator collapses into single-context execution, produces shallow summaries, and writes zero files to disk. This happened on a real casbin run and is why this protocol was hardened.

## File-Writing Override

The user's invocation of the playbook is explicit authorization for you and every sub-agent you spawn to write .md files, patches, JSON, and any other artifacts to the `quality/` directory and the project root (`AGENTS.md`). This overrides any base harness rules discouraging documentation or .md file creation. No sub-agent should skip file writes citing harness constraints.

## Rationalization Patterns

If you catch yourself producing text like any of these, stop — that's the tell that you're about to collapse into single-context execution:

- "per system constraint: no report .md files" (or any invented harness restriction)
- "I'll do the analytical work in-context and summarize for the user"
- "spawning a sub-agent is unnecessary overhead for this step"
- "I can cover multiple phases in one pass"
- "the artifacts are optional / can be described rather than written"

Any of these means you're about to replicate the casbin failure. Spawn the sub-agent instead.

## Grounding

If `ai_context/DEVELOPMENT_CONTEXT.md` exists in the skill repo or the working directory, read it before Phase 1. It contains the three-axes improvement model and the design intent behind phase separation. Grounding in this document materially reduces the chance of collapsing into single-context execution.

## Post-Phase Verification Gate (Mandatory)

After each sub-agent returns, confirm that the expected output files exist and contain real content — not empty scaffolding or placeholder text. If any required file is missing or trivially small, the phase failed regardless of what the sub-agent reported. The sub-agent's claim of completion is insufficient evidence — only files on disk count.

Express each check as content criteria ("verify that `quality/EXPLORATION.md` exists and has at least 120 lines"), not as specific tool invocations. Use whatever file-reading and directory-listing capability is available.

### Expected outputs per phase

Cross-reference SKILL.md's Complete Artifact Contract for the authoritative list.

- **Phase 1 (Explore):** `quality/EXPLORATION.md` exists with at least 120 lines of substantive content; `quality/PROGRESS.md` exists with Phase 1 marked complete.
- **Phase 2 (Generate):** All of these exist: `quality/REQUIREMENTS.md`, `quality/QUALITY.md`, `quality/CONTRACTS.md`, `quality/COVERAGE_MATRIX.md`, `quality/COMPLETENESS_REPORT.md`, `quality/RUN_CODE_REVIEW.md`, `quality/RUN_INTEGRATION_TESTS.md`, `quality/RUN_SPEC_AUDIT.md`, `quality/RUN_TDD_TESTS.md`. A functional test file exists in `quality/` (naming varies by language: `quality/test_functional.<ext>`). **AGENTS.md is NOT a Phase 2 output** — it is generated post-Phase-6 by the orchestrator (see SKILL.md Phase 2 source-modification guardrail). Phase 2 writes ONLY into `quality/`.
- **Phase 3 (Code Review):** `quality/code_reviews/` contains at least one review file. If bugs were confirmed: `quality/BUGS.md` has at least one `### BUG-` entry, `quality/patches/` contains a regression-test patch per confirmed bug, and `quality/test_regression.*` exists.
- **Phase 4 (Spec Audit):** `quality/spec_audits/` contains at least one triage file AND at least one individual auditor file.
- **Phase 5 (Reconciliation):** If bugs were confirmed: `quality/results/tdd-results.json` exists, a writeup at `quality/writeups/BUG-NNN.md` exists for every confirmed bug, and a red-phase log exists at `quality/results/BUG-NNN.red.log` for every confirmed bug.
- **Phase 6 (Verify):** `quality/results/quality-gate.log` exists and PROGRESS.md marks Phase 6 complete with a Terminal Gate Verification section.

### After verification passes

Report the phase's key findings to the user. Continue to the next phase (or stop if in phase-by-phase mode).

### If verification fails

Report what files are missing or empty. Do NOT spawn the next phase — the missing output must be repaired first. Offer to retry the failed phase in a fresh sub-agent.

## Error Recovery

If a sub-agent fails or runs out of context:

1. Assess what was saved to disk (PROGRESS.md and the `quality/` directory).
2. Report the failure with specifics.
3. Suggest retrying in a fresh sub-agent — phase writes are preserved incrementally, so a retry can pick up where the previous attempt left off.
4. Never skip phases — each depends on prior output.
