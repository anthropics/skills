---
name: git-flow-agent-guard
description: Stack-agnostic agent skill enforcing strict branch protection, local CI pre-flight verification, dual-tier risk scoring, atomic release tracking, audit logging, and upstream synchronization mapping. Works with ANY tech stack (Rust, Go, Node, Python, Java, .NET, etc.) — configure your own verification commands in .agent-guard.json.
license: Complete terms in LICENSE.txt
---

# Git Flow Agent Guard Directive

> **Stack-Agnostic:** This skill does not assume any programming language or framework. The evaluation scripts (`scripts/analyze-pull.py`, `scripts/evaluate-risk.py`) run on Python 3.8+ but analyze YOUR repository using YOUR configured commands. Configure `.agent-guard.json` for your stack (see `references/.agent-guard.json.template`).
>
> **Source:** https://github.com/MessilineHani/git-flow-agent-guard

## 1. Branching & Scope Isolation
- Inspect `.agent-guard.json` at project root for configuration.
- **Strict Prohibition:** NEVER commit or push directly to `main` or `dev`.
- All work MUST originate from `dev`.
- Branch naming format: `<prefix>/<issue-id>-<short-description>` (e.g., `feat/102-auth-middleware`, `fix/404-null-pointer`).

## 2. Dual Audit Logging (`.agent-guard/logs/`)
Maintain two persistent local log files before staging or committing:

1. **`AGENT_CHANGELOG.md` (Functional & Technical Log):**
   - Appends entry detailing: **Intent** (what changed), **Mechanism** (how it works technically), and **Side Effects / Boundaries** (modules touched).

2. **`AGENT_WORKING_TREE.log` (State & Rollback Map):**
   - Appends raw execution snapshot: `Pre-State HEAD`, `Branch`, `Modified Files`, `Stash ID`, `Post-State HEAD`, and exact `Rollback Command`.

## 3. Upstream Pull Synchronization Protocol
When fetching or pulling remote updates (`dev` or peer branches):
1. Execute `python scripts/analyze-pull.py --target <branch>` prior to merging/rebasing. Scripts are bundled in this skill's `scripts/` directory — run with the skill directory as context, or copy the `scripts/` folder to your project root.
2. Review generated `.agent-guard/logs/LAST_PULL_ANALYSIS.md` for interface breaks, schema updates, or overlapping modified files.
3. Apply reconciliation adjustments based on the analysis before proceeding.

## 4. Local CI Pre-Flight Verification
Run configured verification commands from `.agent-guard.json` (`lint`, `typecheck`, `test`, `build`).
- **Hard Blocker:** If ANY check fails, fix the issue locally and re-run. DO NOT push broken code or create pull requests.

## 5. Dual-Tier Risk Review & Conditional Merging
Execute `python scripts/evaluate-risk.py` to evaluate the diff relative to `dev` and `main`:

### Decision Matrix for Auto-Merging into `dev`
- **Squash and Merge Policy:** All merges to `dev` MUST be squashed into a single commit formatted as: `<type>(<scope>): <summary> (#<issue-id>)`.

| Dev Risk (1-5) | Blast Radius | Revert Cost | Merge Action (`dev`) |
| :--- | :--- | :--- | :--- |
| **1 – 3** | LOW / MEDIUM | LOW | **Auto-Merge Allowed** |
| **4** | LOW | LOW | **Auto-Merge Allowed** (Low blast/revert cost) |
| **4** | HIGH / ANY | HIGH | **REQUIRES HUMAN REVIEW** |
| **5** | ANY | ANY | **REQUIRES HUMAN REVIEW** |

> **`main` Direct Push Prohibition:** Merging into `main` requires human sign-off, passing remote CI, and promotion via Release Candidate (`release/vX.Y.Z`) or Feature Flags.

## Setup

1. Copy `references/.agent-guard.json.template` to `.agent-guard.json` in your repository root and fill in your stack-specific `lint_command`, `typecheck_command`, `test_command`, and `build_command`.
2. For first-time zero-config setup, follow `references/bootstrap.md`.
