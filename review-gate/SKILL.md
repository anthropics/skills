---
name: review-gate
description: Enforce adversarial review before merge via a trusted pull_request_target gate and PreToolUse merge guard. Use when installing review gates on nevar* repos, when merge must wait for unresolved threads or unanswered P2s, or when doctoring whether a repo's ruleset and review-gate.yml are configured. Companion to adversarial-review and pr-merge-flow.
version: 3.2.6
author: Bernier LLC
---

# Review gate

Programmatic enforcement for the adversarial review loop. Ships:

1. **Workflow template** — `.github/workflows/review-gate.yml` (`pull_request_target`)
2. **Trusted checker** — `scripts/check-review-gate.py` (loaded only from the repo **default branch**)
   plus the **forged-check detector** `scripts/check-forged-gate-names.py` (vendored byte-identical from
   `bernierllc/agents-environment-config@dba592dbf5a95d89a19d7b4dfaf2ea11fdf44821`, never edited here; the
   installer never overwrites a repo's differing copy) and
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

Upgrading to 3.2.2: re-run `install-workflow.py --force` to pick up the fail-closed detector (aec dba592db). A repo whose `scripts/check-forged-gate-names.py` differs from the skill's copy keeps its own and gets a `KEPT` message. The merge guard no longer reads `pr-merge-flow` as `pr … merge`. Also in 3.2.2: a known older vendored detector (3.2.0/3.2.1 or any pre-dba592db aec copy) is now replaced on `--force`; only a newer or custom copy is KEPT, and an identical file is left untouched; each `Review Gate` check run carries `external_id: review-gate-pr-<n>` and is reused only by that PR, so two PRs on one head sha cannot complete each other's runs (pre-3.2.2 unmarked runs are left alone; push a new commit if one stays red); the PR that replaces a legacy review-gate.yml passes the forged-check step when its own legacy `Review Gate` job ran that file from the default branch under pull_request_target (needs `PR_NUMBER`); a `##` line with `Review` on the next line no longer counts as the `## Review` section. 3.2.3: `## Review-notes`, `## Reviewers` and other headings that only start with `Review` no longer count as the `## Review` section. A heading, list item, fence or thematic break after a `>` quote now ends the quote, so a `## Review` section that follows a quote is seen. 3.2.4: the vendored `check-forged-gate-names.py` is re-vendored from aec b4a8c9c (comment-only: the plan path now names the aec repo); `install-workflow.py --force` replaces the 3.2.2/3.2.3 copy. 3.2.5: only what CommonMark lets interrupt a paragraph ends a `>` quote's lazy continuation: an ATX heading, a thematic break, a real fence, a non-empty bullet item, or a non-empty ordered item starting at 1. `2. note`, an empty `-` and a ``` line whose info string holds a backtick stay inside the quote, so a quoted example can no longer satisfy the gate. A fenced block now ends the paragraph before it, so an attestation after a closed fence that follows a quote is seen. Re-run `install-workflow.py --force` to pick up `scripts/check-review-gate.py`. 3.2.6: every gate evaluation publishes a NEW `Review Gate` check run and completes all of this PR's runs on the head with the same result, because the Checks API cannot choose a suite and a reused run left in an older suite read "expected" (BLOCKED, all green) on claude-skills #90, nevar-logs #12 and nevar-audit #17. The exact trigger is unresolved: nevar-content #12 had runner-only suites and was not blocked. The gate fails closed, naming the fix, when a non-cancelled review-gate suite on the head holds none of this PR's runs (a 3.2.6 POST that missed its own suite); a cancelled duplicate suite is exempt. This template change is UNPROVEN until a live run, because `pull_request_target` runs the default branch's copy. Until it is proven, keep the interim author rule: set the `review:high` label and the `## Review` section in the `gh pr create` call itself (its opened + labeled pair cancels one run, which merged CLEAN on nevar-audit #18), and change neither the body nor the labels after the first gate run (an edit-triggered suite blocked nevar-logs #12 at d1c6e07); if a PR still reads BLOCKED with every check green, rerun the gate in place, then push a new head. The bootstrap exception for a legacy `Review Gate` job now requires the run's own head fields (sha, branch, repo) to equal this PR's head (never the run's `pull_requests` association), no other PR on that head, and the workflow file at the PR's base to equal the default branch's copy. A `>` line with nothing after the marker now ends a quote's lazy continuation, so `fixed in <sha>` after it closes a P2 thread. `doctor-review-gate.py` warns when the installed workflow differs from the template. Re-run `install-workflow.py --force`.

Upgrading to 3.2.1: the workflow now reuses the head's one `Review Gate` check run instead of adding a new one per evaluation (GitHub blocks the PR while any same-named run in the suite is red, so 3.2.0 heads that failed once could never go green). Re-run `install-workflow.py --force` and commit; the next evaluation completes every earlier run on the head.

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
   Any Actions job named `Review Gate` fails the gate, and so does an unreadable listing or lookup
   (exit 2, fails closed). The only legitimate `Review Gate` is the Checks API run this workflow publishes;
   its own job is named `review-gate-runner`, because a `pull_request_target` job attaches to the base SHA,
   and a stacked child PR's base is the outer PR's head. The wrapper checks only
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
