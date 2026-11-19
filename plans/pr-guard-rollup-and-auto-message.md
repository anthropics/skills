# pr-guard: superseded-check handling and the `--auto` block message

Status: planned. review-gate 3.2.8 (PR #105, d876413) has shipped. **No code until Matt or the Program Cop says go.** Reported by the nevar-secrets cop after it merged a promotion with `--auto` (Program Cop relay, 2026-11-17 03:17Z).

## What was reported

- **(A)** `pr-merge-flow/scripts/pr-guard.py` blocks a merge while `mergeStateStatus` is CLEAN, because a required check (Review Gate, after a label fix) failed once and re-ran green on the same head, and the failed entry is still in `statusCheckRollup`.
- **(B)** The guard's block message told the agent to run `gh pr merge <n> --auto --squash`, contradicting the skill ("never `--auto`") and `traffic-cop.md`, and talked the cop into the bypass.

## Incumbent check (what already exists on `origin/main`, pr-merge-flow 1.4.7)

- **(B) is already fixed on main, and #105 does not touch it.** `8d06530` (2026-11-15, `fix(pr-merge-flow): block --auto and require --match-head-commit`) made `--auto` always blocked, with a message that says to hand the PR to the traffic cop and merge with `--squash --match-head-commit <sha>`. Nothing on main's `pr-guard.py` recommends `--auto`. `git diff origin/main origin/pr105 -- pr-merge-flow` is empty. The message the nevar-secrets cop saw therefore came from an **older vendored copy** of the guard (pre-1.4.7), not from main. The gap is distribution: how did a repo keep a guard that recommends a bypass? Check what version nevar-secrets has installed and why `aec update` did not move it.
- **(A) is mostly implemented on main.** `not_green()` already collapses the rollup per (workflow file, job name): the newest run supersedes older runs by the run's first `startedAt`, ties count (fail closed), the workflow is identified by the Actions API (run path and event), never by the editable `name:`, and an entry counts as a run's job only when the jobs API lists that job id with the same name and conclusion. So `[FAILURE older run, SUCCESS newer run]` of a real Actions job already passes.
- **The remaining gap in (A):** entries that are not Actions job entries are *never* collapsed: status contexts, third-party check runs, and **check runs POSTed through the Checks API**. Review Gate 3.2.0 to 3.2.7 POSTed its result that way (job `review-gate-runner` plus an API check named `Review Gate`), so each re-fire leaves another `Review Gate` entry with no run id, the old FAILURE stays, and the guard blocks while GitHub says CLEAN. That fits the report. 3.2.8 removes the POST (the gate is a job named `Review Gate`), which the existing collapse handles.

## Root cause (hypothesis to verify first)

(A) is the 3.2.x POSTed-check shape meeting a deliberately fail-closed guard, plus possibly the same stale-vendored-copy problem as (B). It is not a missing collapse algorithm. Verify against the nevar-secrets PR's rollup (head sha, entries, `detailsUrl`, `startedAt`, `completedAt`) before changing code.

## Correct fix (3.2.8 has shipped)

1. Reproduce (A) from the real rollup JSON as a fixture. Decide from it whether the stuck entry is an API-posted check (then 3.2.8 plus re-vendoring fixes it and no guard change is needed) or an Actions job the collapse misses (then fix that case and name why).
2. **Do not** loosen the guard by name. Collapsing non-Actions entries "latest by name" lets a superseded failure, or a forged same-named check, mask a real one. If any non-Actions collapse is wanted, it needs an identity that cannot be spoofed (check run app id / `integration_id` from the Checks API; the Review Gate doctor satisfiability check that would prove the same identity is a 3.2.8 follow-up with no plan file yet, and `doctor-review-gate.py` has no such check today). That is a security change and gets the security review below.
3. (B): add a test that no block message the guard can emit contains `--auto` or `--admin` as advice (enumerate every message path), so the contradiction cannot return. Add a drift check so a vendored guard older than the skill's version is reported by `doctor` / `aec update` instead of silently kept.
4. Version bump for `pr-merge-flow`, `python3 scripts/generate-manifest.py`, tests in `pr-merge-flow/tests/test_pr_guard.py`.

## Security review checklist (required before merge; this loosens a guard)

The review must confirm a superseded failure cannot mask a real one, for each case:

- Same check name in a **different workflow** (a PR-added workflow named like a required job).
- A failed re-run that is older by `completedAt` but newer by run id (and the reverse).
- **In-progress** runs and a null or zero-time `startedAt`/`completedAt`: an in-progress or missing latest entry must block.
- An API-posted check with a forged name or a forged `detailsUrl` claiming another run.
- Ties on timestamp: all count (fail closed).
- Tests: `[FAILURE older, SUCCESS newer]` passes; `[SUCCESS older, FAILURE newer]` blocks; each case above has a failing-then-passing test.

## Vendored guard drift (added 2026-11-17, Program Cop 03:25Z)

Remembering to refresh vendored guards is the failure mode: a stale copy kept a guard that recommended `--auto`. Measured by REST on each default branch (Program Cop): pr-merge-flow **nevar-secrets 1.3.0** (guard still has `--auto`), **nevar-contacts 1.1.0**, nevar-fund 1.4.6, nevar-logs 1.4.6 (main is 1.4.7); nevar-api, nevar-auth, nevar-app, nevar-plan, nevar-notify, nevar-admin showed no version line at the path tried (layout may differ, not concluded). The secrets and contacts cops were asked to refresh that skill by hand; that is the stopgap, not the fix.

Measured 2026-11-17 03:30Z (Program Cop): aec's catalog source for `pr-merge-flow` is **1.4.1** while `main` is **1.4.7** (`db2355a5`). `aec install skill pr-merge-flow` on the Mini installed v1.4.1 and also silently rewrote `.claude/settings.json` (adds the `pmf-pr-guard` hook) and the AGENTS/GEMINI/QWEN blurbs. Interim stopgap: copy `pr-merge-flow/` byte-for-byte from `main`. So the first fix step is why aec's catalog lags `main`, and a refresh must not silently rewrite settings or blurbs.

Recorded-vs-local mismatch (Program Cop, 2026-11-17): `bernierllc/nevar-app`'s `.aec.json` records `pr-merge-flow` **1.3.0**, while the local ignored copy in that repo is the **1.4.7** byte copy from claude-skills main `db2355a5` (blobs: `SKILL.md` 26d5fd9e, `hooks.json` 0be3e4b8, `scripts/pr-guard.py` 792b72f6, `tests/test_pr_guard.py` 881c87e5). `.aec.json` is generated state and is not hand-edited, and nevar-app is not touched: the drift belongs to the generator fix. The generator and the doctor/verification check must therefore handle a repo whose recorded version differs from the version of the files on disk, in both directions: report it by name, state which side is wrong, and re-record from the installed files (or reinstall) through the generator, never by hand. A byte-copy refresh that bypasses `aec install` (the stopgap above) is what creates this case, so the stopgap must end in a re-record step.

Fix, in order of preference (Do it for us, Flag it):

1. **Do it for us:** `aec update` refreshes vendored guard skills (`pr-merge-flow`, `review-gate`) in a repo whenever the skill version moves, replacing only the skill's own files and never touching `LICENSE` or other repo files. Incumbent to check first: `aec` already installs a skill's whole directory and upgrades on the version (claude-skills `CLAUDE.md`); find out why these repos did not move (not enrolled, pinned, vendored by hand, different path) before adding anything.
2. **Flag it:** a doctor check (`review-gate/scripts/doctor-review-gate.py` and/or `aec doctor`) that fails loudly, naming the fix (`aec update`), when a repo's vendored `pr-merge-flow` or `review-gate` version is behind `main`. It must find the skill at every layout the installers use (the six repos with no version line show the lookup path cannot be assumed) and fail, not pass, when it cannot find the version.
3. Tests: a behaviour test with a vendored copy at an older version (doctor fails, names `aec update`), at the current version (passes), at an unknown layout (fails closed), and with `.aec.json` recording an older version than the files on disk (the nevar-app case: fails, names the mismatch, no hand edit). An `aec update` test proves LICENSE and unrelated files are untouched.

Done when every repo carrying either skill reports the current version, and a repo that falls behind fails doctor instead of staying quiet.

## Affected surfaces

`pr-merge-flow/scripts/pr-guard.py`, `pr-merge-flow/tests/test_pr_guard.py`, `pr-merge-flow/SKILL.md` (version), `skills-manifest.json`, and the vendored copies in repos that carry the guard (nevar-secrets first). Related: `review-gate/scripts/merge-guard.py` (#105's merge-guard changes are separate and do not cover this).

## Out of scope

The Review Gate doctor satisfiability check (a separate item on the 3.2.8 follow-up; no plan file yet) and the `cursor` reviewer token (`review-gate-cursor-reviewer-token.md`).

## Priority

High for (B)'s distribution gap (a guard that recommends a bypass is a live merge-safety hole in any repo with the old copy); medium for the (A) code change.
