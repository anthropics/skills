---
name: reviewer-committee
description: Multi-model code review committee using Codex (gpt-5.4) and Gemini (gemini-3.1-pro-preview) in parallel. TRIGGER when user runs /review, /review-diff, /review-commit, asks to "run the committee", "get committee feedback", "do a multi-model review", "committee review", or wants a thorough AI code review before merging or completing a task. Runs both CLIs simultaneously and synthesizes results into COMMITTEE_REVIEW.md in the current working directory. Use this whenever code review is requested - even if phrased as "just a quick check" or "sanity check the code".
license: Complete terms in LICENSE.txt
---

# Reviewer Committee

Run parallel code reviews using GPT-5.4 (Codex CLI) and Gemini-3.1-Pro-Preview (Gemini CLI), then synthesize into a `COMMITTEE_REVIEW.md` in the current directory.

## Prerequisites

| Dependency | Install | Purpose |
|-----------|---------|---------|
| **Codex CLI** | `npm install -g @openai/codex` | GPT-5.4 code review |
| **Gemini CLI** | `npm install -g @google/gemini-cli` | Gemini-3.1-Pro code review |
| **Python 3.9+** | System or package manager | Orchestration script |

Both CLIs must be authenticated before first use:
```bash
codex   # follow the auth prompts
gemini  # follow the OAuth flow
```

## When Invoked

1. Determine what to review (see "Review Modes" below)
2. Run the committee script (runs both models in parallel)
3. Read the resulting `COMMITTEE_REVIEW.md`
4. Present a brief synthesis: consensus issues first, then single-reviewer findings

## Review Modes

| Mode | Script flag | Use when |
|------|-------------|----------|
| Uncommitted changes | `--mode uncommitted` | Default — staged + unstaged |
| Vs base branch | `--mode base --param <branch>` | Before merging a PR |
| Specific commit | `--mode commit --param <sha>` | After a commit, /review-commit |
| Specific files | `--mode files --param "f1.py f2.py"` | Targeted file review |

## Running the Committee

Use the script at `scripts/run_committee_review.py`:

```bash
# From inside the project repo (recommended — both CLIs get the right context)
cd /path/to/project
python "$REVIEWER_COMMITTEE_DIR/scripts/run_committee_review.py" --mode uncommitted

# Or from anywhere, pointing at the project with --project-dir
python "$REVIEWER_COMMITTEE_DIR/scripts/run_committee_review.py" \
  --mode uncommitted --project-dir /path/to/project

# Review vs a base branch
python "$REVIEWER_COMMITTEE_DIR/scripts/run_committee_review.py" \
  --mode base --param main --project-dir /path/to/project

# Review a specific commit
python "$REVIEWER_COMMITTEE_DIR/scripts/run_committee_review.py" \
  --mode commit --param <SHA> --project-dir /path/to/project

# Review specific files
python "$REVIEWER_COMMITTEE_DIR/scripts/run_committee_review.py" \
  --mode files --param "src/foo.py src/bar.py" --project-dir /path/to/project
```

`COMMITTEE_REVIEW.md` is written to `--project-dir` by default (or `--output-dir` if specified).
Gemini runs with `--sandbox` for isolation.

## After the Script Completes

Read `COMMITTEE_REVIEW.md` and present a summary:

```
## Committee Summary

**Consensus issues** (both reviewers flagged): [list - highest confidence]
**Codex only:** [list]
**Gemini only:** [list]

**Recommendation:** [Approve / Approve with Changes / Needs Work / Major Revisions]
```

Then ask the user how they want to proceed.

## Processing the Review Feedback

- **Verify before implementing** — check each suggestion against the actual codebase
- **Consensus = high confidence** — if both models flag something, it's almost certainly real
- **Single-reviewer findings** — still worth checking, but apply more scrutiny
- **Push back technically** when a suggestion is wrong for this codebase
- **Prioritize**: Critical > Important > Minor

Fix Critical issues before proceeding. Fix Important issues before merging. Minor issues are optional.

## Slash Commands

These are registered for quick access:

| Command | Action |
|---------|--------|
| `/review` | Committee review of uncommitted changes |
| `/review-diff` | Committee review vs a base branch (prompts for branch name) |
| `/review-commit` | Committee review of a specific commit (prompts for SHA) |

## Troubleshooting

**"No diff content found"**: Ensure you have staged or unstaged changes (`git status`).

**Codex timeout**: Large diffs can be slow. Consider narrowing scope with `--mode files`.

**Gemini auth error**: Run `gemini` interactively once to ensure you're authenticated.

**Model not available**: Codex model can be overridden via `-c model="..."` in the script's `CODEX_CMD` list.

## Platform Support

Works on **macOS**, **Linux**, and **Windows (WSL only)**. PowerShell and CMD are not supported.
