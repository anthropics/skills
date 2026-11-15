---
name: review-gate
description: Enforce adversarial review before merge via a trusted pull_request_target gate and PreToolUse merge guard. Use when installing review gates on nevar* repos, when merge must wait for unresolved threads or unanswered P2s, or when doctoring whether a repo's ruleset and review-gate.yml are configured. Companion to adversarial-review and pr-merge-flow.
version: 3.1.1
author: Bernier LLC
---

# Review gate

Programmatic enforcement for the adversarial review loop. Ships:

1. **Workflow template** — `.github/workflows/review-gate.yml` (`pull_request_target`)
2. **Trusted checker** — `scripts/check-review-gate.py` (loaded only from the repo **default branch**)
3. **Doctor** — warns when the workflow, checker, ruleset conversation-resolution flag, or required `Review Gate` status check is missing
4. **PreToolUse merge guard** — blocks `gh pr merge` when the local gate check fails

## Install (per repo)

```bash
aec setup .                      # only if `aec install` says "Not in a tracked repo"
aec install skill review-gate
# copies workflow + trusted checker into the repo (run from the repo root; commit both to the default branch):
aec run-script skill:review-gate install-workflow.py
# or manually:
#   cp …/templates/review-gate.yml .github/workflows/review-gate.yml
#   cp …/scripts/check-review-gate.py scripts/check-review-gate.py
```

Upgrading an existing install: 3.1.0 accepts `codex` (a local Codex review, e.g. T3 Codex high) as an attestation reviewer; 2.0.0 tightened the fallback rule, and the repo's committed checker is a copy. Re-run `install-workflow.py --force` in each repo to pick it up; until then that repo still accepts the old looser fallback.

Then flip GitHub rulesets (no Actions minutes):

```bash
# For each ruleset that has a pull_request rule (usually staging + main):
gh api -X PUT "repos/<owner>/<repo>/rulesets/<id>" --input - <<'EOF'
{ ...keep existing fields..., "rules": [ { "type": "pull_request", "parameters": { "required_review_thread_resolution": true, ... } } ] }
EOF
```

Email_demo and Prevost already have `required_review_thread_resolution: true` (2026-10-17/18). Add **`Review Gate`** (the job display name / Checks API context — not the workflow file name alone) as a **required check** on those rulesets beside CI.

Doctor:

```bash
aec run-script skill:review-gate doctor-review-gate.py
# or: python3 review-gate/scripts/doctor-review-gate.py
```

## What the workflow does

Triggers **only** `pull_request_target` so the workflow YAML always comes from the PR **base** (trusted). Same-repo `pull_request_review` / `pull_request_review_comment` would execute PR-modified workflow code with write tokens — not used. After Codex completes, a new P2 thread, or a P2 closing reply with no push, **re-fire the gate** via a label toggle or PR body edit (agents: see `adversarial-review`); do not reintroduce review-event workflow triggers. A green Checks API run can otherwise go stale relative to later threads — the PreToolUse merge guard still re-evaluates live before `gh pr merge`.

### Job `gate` (display name / Checks API name `Review Gate`)

Loads `scripts/check-review-gate.py` from the repository **default branch** only (never the PR head or an untrusted PR base) and fails unless all hold:

1. A completed review from the exact Codex bot login `chatgpt-codex-connector` exists on the **current head** (not body text / substring logins), **or** the PR body's `## Review` section contains the explicit completed fallback-review attestation below on one line, bound to the current head.
2. PR body contains a `## Review` section.
3. Every review thread whose **root** comment matches `\bp2\b` has a reply with a closing token: Notion link, `fixed in <sha>`, or `not-a-finding: …` (all thread/comment pages are fetched).
4. When `base` is `main`: label `review:high` is present.

Fallback attestations use exactly this format (plain text on its own line inside `## Review`):

```text
Fallback review: <reviewer> on <sha> — verdict: <verdict>
```

- `reviewer`: `codex` (a local Codex review, such as T3 Codex high, that the GitHub Codex bot did not post), `agy`, `antigravity`, `superpowers`, or `claude-sonnet`.
- `sha`: the current `headRefOid` in full or a prefix of at least 7 hex characters. The entire supplied prefix must match.
- `verdict`: `clean` or `findings fixed`; attest only after the review completed and any findings were fixed.

Copy-pasteable example (replace `89cda061` with the head actually reviewed):

```text
## Review

Fallback review: claude-sonnet on 89cda061 — verdict: clean
```

Reviewer, SHA and verdict must all be on that same line. Lines containing `pending`, `running` or `TODO` (case-insensitive) are rejected. URLs, generated Claude Code footers and keyword-only prose do not count. After every push, rerun the review before replacing the attested SHA; copying the new SHA alone does not attest a review. Earlier free-form fallback summaries no longer satisfy this gate.

`pull_request_target` attaches the Actions job to the **base** SHA, so the job always publishes a Checks API run named `Review Gate` on the PR head (opened / synchronize / label / edit).

Unresolved threads are **not** checked here — that is GitHub's `required_review_thread_resolution` on the ruleset (free, instant on resolve).

Judgment/Jev triage is **out of scope** for v1 (still piloted in NevarMail per the 2026-10-16 enforcement plan).

## Merge guard

PreToolUse blocks `gh pr merge` (including `--auto`) when `check-review-gate.py` fails for that PR. **Required form for any compound shell command** (`&&`, `||`, `;`, newlines, subshells, `export`, …): `gh -R owner/repo pr merge <n>` (literal repo). The guard does **not** model cwd/`cd`/`export GH_REPO`/subshell interactions across segments — pass `-R` instead. A single-segment `gh pr merge <n>` in the tool cwd is still allowed. Override with `# review-gate-ok: <reason>` in the command only for Matt-approved escapes.

## Apply across nevar*

1. `aec install skill review-gate` + `install-workflow.py` in each repo (or a small apply PR series).
2. Doctor in CI or a weekly scheduled task; warn (do not hard-fail) until the first month of data.
3. Keep `adversarial-review` installed so agents post the inline comments the gate expects.

## Related

- Loop behavior: skill `adversarial-review` / `~/.claude/references/pr-review-loop.md`
- Base-sync discipline: skill `pr-merge-flow`
- Plan of record: `email_demo/plans/2026-10-16-dev-environment-enforcement-plan.md` §6

<!-- feedback-loop:begin -->
## Feedback

If the `feedback-loop` skill is installed, use it to improve this skill over time:

- When this skill's own instructions cause rework, a wrong default, a missed case or a needless
  pause, log it as it happens: subject `skill:review-gate`, with the phase or section at fault and the
  concrete fix to these instructions.
- When the project's own process causes friction during this skill's work (for example a flaky
  or slow CI job, a test that missed a regression, a plan that was wrong about the code), log it
  as subject `process:<project>` with `--area <ci|test|plan|review|deploy|dev>`.
- At the end of a run, check `skill:review-gate`; if a review is due, make the feedback-loop offer.

If `feedback-loop` is not installed, ignore this section.
<!-- feedback-loop:end -->
