---
name: orchata
description: Use when the user wants a task or project planned and executed end-to-end with multi-agent orchestration — "orchestrate this", "/orchata", "plan and build this", "run this with subagents", or any request to take a feature/project from intake through planning, parallel implementation, and verification while only involving the human for items that genuinely need their hands. Encodes intake questions, model-tier selection, escalation punch lists, and a self-improvement friction loop (through the feedback-loop skill).
version: 2.1.0
author: Bernier LLC
---

# Orchata

Plan and execute a task end-to-end: intake → plan → orchestrate → escalate → retro.
The human is brought in exactly twice by default: one batched question set at intake (only if
the repo can't answer), and the end-of-turn report. Everything else runs.

**Prime directive: never pause just to pause.** No mid-run approval requests. Reversible
actions proceed. Items matching the escalation contract go on the punch list and work routes
around them. If you are about to ask the user something mid-run, you are doing it wrong —
either proceed, or punch-list it.

## Phase 1 — Intake

**Resume check first.** If `<state-dir>/run-state.json` exists on the current branch with a
non-done run (see `references/run-state.md`; state dir per "State files" below): reconcile
it against reality (git log, open PRs, CI/deploy status, the external tracker row if one is
linked), report any drift in one line each, and continue from the first non-done step. Do
NOT re-plan a run that is already in flight. No run-state on the current branch → before
planning fresh, check other branches (`git branch -a --sort=-committerdate`, local and
remote-tracking) for a committed checkpoint via
`git show <branch>:<state-dir>/run-state.json`; only a checkpoint with an in-flight run
counts — one with at least one step whose status is neither `done` nor `skipped` (the
terminal statuses per `references/run-state.md`); a fully terminal run-state is history,
not an in-flight run. A live hit means the run lives on that branch —
switch to it when the tree is clean, otherwise surface the conflict and pause (same rule as
the resume skill).

Read before asking, in order:

1. Project `CLAUDE.md` / `AGENTINFO.md` / `AGENTS.md`, and any project profile in memory
2. Git state (branch, recent commits, cleanliness)
3. `.aec.json` if present; note any project override for where tasks/punch lists live
4. Capabilities cache — see "AEC awareness" below; refresh if stale

Baseline before writing code: run the repo's build/typecheck once at intake so a pre-existing
red baseline is a known punch-list item, not a discovery at first commit (pre-commit hooks
surface it at the worst moment). If the baseline build fails on a *different* target each
run, suspect a missing env file before suspecting the tree. And when acceptance for any item
requires a live authenticated check on a remote environment, confirm credential availability
now and punch-list the check upfront — never discover the gap at retro.

If the run uses a worktree, create it at intake, before the plan commit — pre-commit hooks
already run there. At creation:

- Dependencies: symlink `node_modules` from the primary checkout only while the branch
  leaves the dependency manifests untouched and no worktree installs into it; otherwise
  install per worktree (sharing only the package-manager cache). Install with an explicit
  `NODE_ENV=development` — unattended shells often export `NODE_ENV=production`, which
  silently skips devDependencies and makes the baseline look broken.
- Ensure `node_modules` is excluded, once, in the file every worktree shares:
  `x="$(git rev-parse --git-common-dir)/info/exclude"; grep -qx node_modules "$x" || echo
  node_modules >> "$x"`. A gitignore pattern with a trailing slash (`node_modules/`) matches
  directories, not a symlink; and git reads `info/exclude` from the common dir, not the
  per-worktree `--git-dir`.
- Copy or symlink the primary checkout's gitignored env files (`.env.local` and similar).
- If sibling worktrees share one local test database whose setup drops and re-creates it,
  give this worktree its own database URL when the repo supports an override. When it
  doesn't, never run two full suites from this run at once, treat failures that vanish on a
  clean rerun as collisions rather than defects, and punch-list per-worktree database
  support as the fix. Don't hand-roll a cross-session lock or rely on a process check —
  both race (and `pgrep -f` matches the invoking shell's own command line).

Then ask **at most one batched `AskUserQuestion`** covering only genuine unknowns that would
materially change the plan (e.g., prod posture when no profile exists, a real fork in scope).
If everything is answerable from the repo, ask nothing — state each assumption in one line and
proceed. Do not ask again until the retro.

### AEC awareness

All orchata state lives in `~/.claude/orchata/` — **never** in the skill's own directory
(skills are installed by copying; state in the skill dir would fragment and leak between
installs). First run: create the directory and write `capabilities.json` (`{}`).

Friction is no longer kept here: it goes to the `feedback-loop` skill as subject
`skill:orchata` (see the Feedback section). If a pre-2.0 register `~/.claude/orchata/friction.json`
still exists and `feedback-loop` is installed, run its `scripts/feedback.py import-orchata` once:
it moves every entry, the review date, the source repo and an opt-out into the shared store and
renames the old file to `friction.json.migrated`.
If that register exists and `feedback-loop` is not installed, nothing reads its entries: say
so once in the retro, with the install command (`aec install skill feedback-loop`).

`capabilities.json` is keyed by absolute project path (installed agents/skills differ per
project). Refresh this project's entry when missing, older than 7 days, `aec` errors, or a
lookup misses:

```bash
command -v aec && aec list
```

Record per project: `detected_at`, `aec` (bool), `aec_version`, `installed_agents`,
`relevant_skills`.
No `aec` → skip silently and use generic workers. If the AEC catalog has an agent or skill
that fits a stage better than anything installed, **suggest** `aec install <type> <name>` once
in the plan or retro — proceed generically if not taken up. **Never auto-install anything.**

## Phase 2 — Plan

- Delegate to installed planning skills instead of improvising: `superpowers:brainstorming`
  for unshaped ideas, `superpowers:writing-plans` for specced work. Missing → plan inline.
- Decompose into stages. Tag each stage with:
  - **model tier + effort** — read `references/model-tiers.md`
  - **dependencies** (what blocks what)
  - **covering agent/skill** — an installed agent type or skill that owns this kind of work
    (e.g., Code Reviewer for review stages, TDD skill named in implementation prompts)
  - **escalation flags** — does this stage touch the escalation contract? (see Phase 4)
- Write the plan to `plans/` (or the project's overriding location) per repo conventions.

### Task granularity

The plan file is the map; the task brief is all a worker gets. **Every task brief must be
executable from its brief + named file paths alone** — never "read the plan" or "check the
project docs". A runnable brief has: goal, inputs, constraints, and where the output lands.
Size tasks by the tier doing them:

| Tier | Task size |
|---|---|
| Low (haiku / low effort) | Larger mechanical batches — context reload cost dominates, fewer/bigger wins |
| Mid (sonnet) | One commit-able unit, ≤ ~15 tool calls — a usage-limit cut costs at most one unit |
| High (opus/fable reasoning) | Smallest possible brief + pointers; the model pulls threads itself |

**Docs and code never share a stage.** Documentation expansion is cheap and self-contained —
its own stage, tagged low-tier. Implementation stages get the full budget headroom.

**Tracker rows at plan time:** if an external tracker is configured (see "External tracker"
below), every stage gets a row/issue at plan time, linked to the branch when execution
starts on it. The plan seeds the queue.

## Phase 3 — Orchestrate

Author and run Workflow scripts; the orchestrator (you, the session model) plans, judges,
synthesizes, and integrates — it does not do fan-out work itself.

### Orchestration economy

Token cost is an explicit objective, not a side effect. The orchestrator's job is to get as
much of the project completed as possible through orchestration while executing as little of
the actual work as possible:

- Any unit of work a worker can do from a context-minimal brief is delegated — the
  orchestrator never "quickly does it inline" to save a dispatch.
- The orchestrator consumes conclusions and structured returns, never workers' file dumps or
  transcripts.
- Worker tier and effort are set per the tier table; mechanical batches go low-tier.
- Exception to "never inline": when one implementation unit's brief *is* the full loaded
  context (a spec plus a schema that just landed), re-sending that context to a worker
  costs more than building it. Build that unit inline and spend the worker budget on an
  adversarial reviewer of it instead — the independent check is never skipped.
- Cap concurrent fan-out to what the host can hold. On a laptop, run review fan-outs
  serially and never alongside implementation workers. A review whose consolidated result
  hasn't arrived: wait for the host's completion notification (read the journal only on
  completion or timeout, never in a polling loop); if it alone has died or stalled (several
  stalling at once is a usage limit — see Supervisor resilience),
  confirm it stopped (cancel it) before re-running it at lower parallelism — never
  hand-triage its raw finder output, and never run the replacement alongside it.
- A long local verification run (a full gate, a browser suite: anything over ~5 minutes) is
  fan-out too. Start it only after the independent review has returned and its fixes are
  applied, because a fix invalidates the run. Check host load first (`uptime`, or the host's
  equivalent) and wait while it is above the core count. Run one at a time, never beside
  another suite or a worker wave. A run that dies on timeouts under load is a host problem:
  re-run it only once the load has dropped.

### Shared-worktree mode

When the user asks for work against a single branch, or the stages are mostly serial, run
the whole fleet against **one worktree branch the orchestrator oversees**: workers propose
patches concurrently, the orchestrator applies and commits them serially in dependency
order (tests before each commit). The orchestrator owns the branch — workers never commit
to it directly. Per-worker worktree isolation remains the fallback for genuinely parallel
file mutation.

Worktree hygiene (either mode):

- Sequence environment moves **before** dispatching background agents: create the worktree
  and complete any `cd` first, then dispatch with worktree-absolute paths. An agent
  dispatched against a checkout that then moves gets its Bash calls refused.
- Creation-time setup (deps, `info/exclude`, env files, test DB) is listed in Phase 1;
  apply it whenever the run creates a worktree, including per-worker ones created here.

### Orchestration mechanics

- Use the **Workflow tool** where the host provides it (`agent()` accepts per-call `model`
  and `effort` overrides). If unavailable, fall back to the **Agent tool**: dispatch
  independent workers in parallel, `model` override only (no per-call effort), and note the
  degradation in the retro. The Agent tool is also fine by choice for ≤4 file-disjoint
  workers that need no per-stage effort tiers; reserve Workflow for larger or pipelined runs.
- Read `references/workflow-patterns.md` before writing the script.
- `pipeline()` by default; barriers only when a stage genuinely needs all prior results.
- Per-stage `model`/`effort` overrides per the tier table; omit when no tier clearly fits.
- Adversarial verification on risky stages: anything touching money, auth, data integrity, or
  a contract change gets independent verify agents prompted to refute.
- Worktree isolation only when workers mutate files in parallel.
- Every worker prompt names the skill it should invoke when installed (e.g.
  `superpowers:test-driven-development` for implementation,
  `superpowers:systematic-debugging` when a worker hits a bug).
- Workflow scripts whose `args` carries structure start with a defensive parse —
  `args = typeof args === 'string' ? JSON.parse(args) : args` — hosts may deliver args as a
  JSON string.
- Prefer absolute paths (or `git -C <path>`) in every Bash call — never rely on the shell's
  persisted cwd, which drifts across calls and environment moves.
- Never stream logs in a harness (`railway logs` without `-n`, `tail -f`, `kubectl logs -f`):
  a background task killed mid-stream loses its output, and some hosts lack coreutils
  `timeout`. Fetch bounded slices (`-n N`, `--since`) instead.
- Log friction as it happens — a wrong default in these instructions, an unnecessary pause, a
  missed case that caused rework → log it as `skill:orchata` with the phase at fault (see the
  Feedback section). Friction in the project's own process (flaky CI, a test that missed a
  regression, a plan wrong about the code) is logged as `process:<project>` instead.

### Checkpoint discipline

A usage-limit cut must cost at most one step, never the run. Read
`references/run-state.md` before the first stage executes, then after **every** completed
step, in this order (each layer is a fallback for the one after it):

1. Update `<state-dir>/run-state.json` (local write — always succeeds)
2. `git add <state-dir>/ && git commit` on the working branch (survives the machine) —
   run `git branch --show-current` immediately before **every** commit; never trust
   intake-phase branch state after compaction, a long run, or an environment move
3. Update the stage's row in the external tracker, if one is configured (visible outside
   the CLI)

Layer 3 is optional, and it failing (tracker down, permission-blocked) never blocks — note
the miss in run-state and move on. Checkpoint **early and after each step**, not at the
end: the whole point is that the tail of the run is the part that gets cut.

### Supervisor resilience

Fan-out runs assume workers die. Rules:

- **Worker contract:** every worker prompt ends with a required structured return —
  `{task_id, status: fixed|failed|blocked, files_changed, tests_passing, evidence, notes}`
  (use Workflow `schema` when available). A worker that returns anything else counts as
  `failed`.
- **Retry budget: 2** per task, then mark `blocked` with the last error as evidence and
  move on — never spin on one worker.
- **A stall is not a failure.** When several workers stall (no progress) at once, that is an
  account or usage limit, not a worker defect: abort the wave, checkpoint, and stop — never
  retry into it (one run burned ~1.6M tokens retrying stalled agents for zero output). Record
  the Workflow run id as `workflow_run_id` in run-state immediately after dispatch so a
  resume can read its journal first (see `references/run-state.md`).
- **Stream results:** append each verdict to `<state-dir>/fleet-results.json` as it
  arrives, not in a final batch. A supervisor cut mid-fleet loses zero completed verdicts.
- **Propose in parallel, merge serially:** workers produce branches/patches concurrently;
  the orchestrator integrates one at a time in dependency order, running tests before each
  merge commit.
- **Context-minimal prompts:** workers get their brief + exact file paths + expected
  return shape — never the conversation, the plan file, or "figure out the context".
- **Name cross-file contracts:** when splitting work by file ownership, the worker prompt
  states any contract its files must honor with files it doesn't own (e.g. "CI assumes a
  `packageManager` field in package.json") — or a smoke stage runs the consumer's setup
  after integration. Ownership splits hide exactly these seams.
- **Pinned output needs the whole suite:** when a change alters output that other tests may
  pin exactly (rendered markup, serialised bytes, snapshots, size budgets), the worker runs
  the owning package's whole suite once before returning, not a hand-picked set of related
  tests. Pins live in files that share no name with the change.

### Integration & shipping

Promotion PRs between long-lived branches (e.g. staging → main) use **merge commits, never
squash** — a squash leaves the branches' blobs divergent and the next promotion reports
false conflicts. If a squash promotion already exists in history, back-merge the target
into the source branch before opening the next promotion.

Re-read bot reviews **immediately before** the merge click, not only after the initial
wait: a review whose summary still says *Running* has not finished — wait for it. An empty
early window is not a clean review.

After any merge that touched a generated or aggregate file (an index, a manifest, a
hand-maintained table of contents), resolve by re-running the owning generator — never by
hand-splicing the conflict — and assert its shape (row count vs sources) before committing.
Git can auto-merge such a file "cleanly" into garbage. A hand-maintained aggregate with no
generator: take one side wholesale, re-derive the missing entries from their sources, and
run the same shape assertion — then propose a generator or guard test for it in the PR.

## Phase 4 — Escalate

The escalation contract. This list is canonical and applies even when no global instructions
exist; a user's global/project instructions may extend it, and their additions win:

- Destructive: `rm -rf`, `git reset --hard`, force push, drop table, delete unmerged branches
- Prod-visible shared state: pushing/merging to `main`, prod deploys, sending Slack/email,
  posting to issues, modifying CI
- Costs money or external quota
- Genuinely material ambiguity where the wrong branch wastes the run

When a stage hits the contract: **park it, don't ask.** Add a punch-list entry — what's
blocked, why, exactly what's needed from the human, priority — and route the workflow around
it. Punch list goes to `plans/<task>-punchlist.md`, unless a project or global instruction
names a task-tracking location (checked at intake), AND is summarized in the end-of-turn
report. The run never blocks on a punch-list item.

**Terminal condition — all work blocked.** If every remaining stage is on the punch list
(nothing runnable is left), stop and report the punch list as a needs-from-human list in
priority order: what's needed, why it blocks, what resumes when it lands. This is the only
legitimate mid-run stop. One blocker never stops the run while other work can progress.

## Phase 5 — Retro

1. **Verify with evidence.** Tests actually run, outputs shown, claims match reality; report
   failures plainly. Specifics:
   - Before opening a PR, run the CI workflow's lint/typecheck commands exactly as CI runs
     them (read `.github/workflows`) — whole-repo if CI is whole-repo, the changed-file set
     vs base if CI scopes it that way. Per-file spot checks miss files CI lints and cost a
     full CI round-trip.
   - Map the PR's added behavior (new files *and* new jobs/routes/exports in existing files)
     to new or modified tests — from the repo's coverage report when it has one, by reading
     the diff when it doesn't. Added behavior with no covering test goes back to
     implementation as a test task before the PR opens — a green suite proves existing
     coverage, not that new code has any. Punch-list it only when writing the test is
     genuinely blocked on the human.
   - Verifying an async trigger (queue enqueue, webhook, cron kick) means observing the
     consumer's completion evidence — a worker log line, a row delta — never just the
     producer's 200. A silent no-op enqueue returns 200 too.
   - A page load is not verification. Deploy verification asserts deployment **identity**
     (a new deployment id/commit visible in the provider's deployment list) plus a
     response-body match — never a bare HTTP status code, which a stale or placeholder
     deploy also returns.
   - Smoke-testing deployed tools: read the run's own schema/handoff doc first instead of
     guessing arg names.
   - Monorepo workspaces sharing one local database: run the suite with workspace
     concurrency 1 before diagnosing a timeout as a code defect.
   - Before waiting on bot reviews for a PR, check `.github/workflows` is non-empty or the
     repo has known review bots — if neither, skip the wait.
   - A gate that chains its steps (`a && b && c`) stops at the first failure and hides the
     rest. When it stops on a failure the diff did not cause, read the chain, run each
     remaining step on its own, and report every step's exit code. "The gate failed on a
     pre-existing test" says nothing about the steps after it.
2. **Report:** what shipped, what's on the punch list (inline summary + file path), what was
   assumed at intake.
3. **Feedback** — make sure this run's friction is logged (see the Feedback section), then
   check `skill:orchata` and `process:<project>` with feedback-loop's `status`. When either is
   due, make the feedback-loop review offer for it exactly as that skill describes. When folding
   an orchata lesson, land it in the section that owns the concern: tracker lessons in External
   tracker, git-integration lessons in Integration & shipping, verify lessons in the retro
   checklist above. A lesson that also governs a sibling skill (for example tracker queries
   used by `resume`) lands in both.

## State files

All state is user-global at `~/.claude/orchata/`, created lazily on first run (see Phase 1
for defaults): `capabilities.json` per Phase 1. Friction lives in the user-level
`feedback-loop` store, so turning it off (globally or for `skill:orchata`) is that skill's
setting, not orchata's.

**Per-run state is different:** it lives in the project at `<state-dir>/` (run-state.json,
fleet-results.json) and is committed to the working branch — see `references/run-state.md`.
Default state dir: **`.orchata/`**; the user's global or project instructions may name a
different directory — honor theirs. Global `~/.claude/orchata/` holds cross-project skill
state only.

## External tracker (optional checkpoint layer 3)

The third checkpoint layer is whatever system the user already tracks work in — an issue
tracker, a project database, a team wiki. Orchata never assumes one exists or names one.
At intake, use whatever the user's global/project instructions configure for work tracking;
if nothing is configured, run with layers 1–2 (local write + git commit are sufficient on
their own), and once — at retro, not mid-run — suggest the user name a tracker in their
global instructions if they want run state visible outside the CLI. Never block any step
on the tracker.

Before the first create against a tracker collection in a run, fetch its schema once and
cache the property names in run-state — never guess field names into a 400.

Resume queries against a tracker are bounded: filter to the repo **and** to a work-mode or
status subset, `LIMIT` the rows, and select a truncated notes column. An unbounded
"all non-done rows" query can overflow the tool result. Bounded is not truncated: filter
server-side to the branch/run so the row must be in the first page, and page through
matches only when no such filter exists — before concluding a row doesn't exist.

Tracker API down but a human's answer lives in a row: read it through any other surface
the host offers (e.g. the row's page text in a browser) before punch-listing it as
unreadable. Writes fall back per the user's instructions, or to run-state.

<!-- feedback-loop:begin -->
## Feedback

If the `feedback-loop` skill is installed, use it to improve this skill over time:

- When this skill's own instructions cause rework, a wrong default, a missed case or a needless
  pause, log it as it happens: subject `skill:orchata`, with the phase or section at fault and the
  concrete fix to these instructions.
- When the project's own process causes friction during this skill's work (for example a flaky
  or slow CI job, a test that missed a regression, a plan that was wrong about the code), log it
  as subject `process:<project>` with `--area <ci|test|plan|review|deploy|dev>`.
- At the end of a run, check `skill:orchata`; if a review is due, make the feedback-loop offer.

If `feedback-loop` is not installed, ignore this section.
<!-- feedback-loop:end -->
