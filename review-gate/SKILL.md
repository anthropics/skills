---
name: review-gate
description: Enforce adversarial review before merge via a trusted pull_request_target gate and PreToolUse merge guard. Use when installing review gates on nevar* repos, when merge must wait for unresolved threads or unanswered P2s, or when doctoring whether a repo's ruleset and review-gate.yml are configured. Companion to adversarial-review and pr-merge-flow.
version: 3.2.0
author: Bernier LLC
---

# Review gate

Programmatic enforcement for the adversarial review loop. Ships:

1. **Workflow template** — `.github/workflows/review-gate.yml` (`pull_request_target`)
2. **Trusted checker** — `scripts/check-review-gate.py` (loaded only from the repo **default branch**)
   plus the **forged-check detector** `scripts/check-forged-gate-names.py` (vendored byte-identical from
   `bernierllc/agents-environment-config@46580faae5150afbe7707987295b5bdaf8a9d884`, never edited here) and
   its wrapper `scripts/check-forged-review-gate.py`, also loaded from the default branch
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
#   cp …/scripts/check-review-gate.py …/scripts/check-forged-gate-names.py \
#      …/scripts/check-forged-review-gate.py scripts/
```

Upgrading to 3.2.0: re-run `install-workflow.py --force` and commit the workflow together with all three scripts. The new workflow fails closed until the scripts are on the default branch.

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
3. Every review thread whose **root** comment matches `\bp2\b` has a reply whose rendered text has a line starting with a closing token (optionally after a list bullet or `Tracked:`): a Notion link, `fixed in <sha>`, or `not-a-finding: …`. Quotes (lazy continuations and quotes inside list items included), code blocks, inline code spans (a span that is only a commit SHA keeps its text), comments and mid-sentence mentions do not count; the same rule applies to the `Fallback review:` line (all thread/comment pages are fetched). A clean Codex run posts no review, only a `codex-review-state:v1` marker in its summary comment; that marker counts when it is `completed` with no unresolved findings on the current head.
4. When `base` is `main`: label `review:high` is present.
5. **No forged `Review Gate`** (SEC-MVS-01 S5, PRs into every branch): the head SHA's check runs
   (`check-runs?filter=all`, paginated, under `pipefail`) go through `check-forged-review-gate.py`.
   Any Actions job named `Review Gate` that is not this workflow under `pull_request_target` fails the
   gate, and so does an unreadable listing or lookup (exit 2, fails closed). The wrapper checks only
   `Review Gate`: the vendored map also names `PRs into main must come from staging`, which several
   repos still publish from a plain `pull_request` job; that name stays with each repo's main-via-staging guard.
   Residual: a PR job with `checks: write` POSTing `Review Gate` straight to the Checks API looks the same as
   this workflow's own run and is not detected (plan options A/B in aec). A job publishing after the scan is
   caught by the cop's pre-merge run (pr-merge-flow rule 2).

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
