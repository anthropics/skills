# Code Playbook v2 — Claude Code 适配

Claude Code 工具映射：`Read`/`Glob`/`Grep` 用于仓库落地，`Bash` 用于运行验证命令和 CLI 脚本，`Write`/`Edit` 用于代码修改和运行记录，`TaskCreate`/`TaskUpdate` 用于跟踪实现单元进度。

## Purpose

Use this playbook when the user explicitly asks ECL to continue from planning into implementation. `/code` exists to execute a frozen handoff, not to reinterpret product intent.

## Entry Conditions

Enter `/code` only when all of the following are true:

- the caller provides `--case <bundle-dir>` or `--handoff <absolute-path-to-90-code-handoff.md>`
- `ecl.code_handoff.code_ready=true`
- the referenced repo target exists
- the handoff has no unresolved high-impact gaps

If any gate fails:

- do not modify the repo
- write a run record anyway
- write a reentry request
- point planning back to the earliest affected A-H stage

## Handoff Surface That Must Already Be Frozen

Before coding starts, confirm the handoff explicitly contains:

- `repo_grounding`
- `frozen_product_decisions`
- `domain_model`
- `data_contract`
- `ui_contract`
- `function_contracts`
- `file_plan`
- `implementation_units`
- `verification_commands`
- `browser_checks`
- `acceptance_checks`

## Allowed Decisions

`/code` may decide only low-impact engineering details such as:

- helper decomposition inside already frozen scope
- import wiring
- package lockfile updates
- tiny file placement details that do not change behavior

`/code` must not decide:

- user goal meaning
- frozen product semantics
- data or state behavior omitted by planning
- validation meaning
- success criteria
- dependency behavior
- review conditions
- acceptance semantics
- visible UI choices that the handoff still phrases as alternatives

## Required Reading

Read only:

- `90-code-handoff.md`
- `97-code-preflight.md`
- the files explicitly listed under `read_first`
- the target repo files needed to execute the frozen units

Do not reopen stage notes for fresh product interpretation unless the handoff explicitly references them.

Use `97-code-preflight.md` as the shared execution workboard. It may be updated before coding starts and as coding progresses, but only for execution state such as current focus, progress, remaining work, mirrored task status, blockers, and pause reasons.

## Execution Rules

1. Resolve and validate
   - resolve the bundle from `--case` or `--handoff`
   - confirm `90-code-handoff.md` is the single entrypoint
   - fail closed if the handoff is not truthful
2. Ground in repo reality
   - inspect repo existence, current files, manifests, command availability, and relevant existing code
   - compare repo reality to the handoff before editing
3. Execute in order
   - follow `implementation_units` order exactly
   - do not silently skip or reorder units
4. Verify incrementally
   - run each unit's verification before moving on
   - run handoff-level verification before marking the run complete
5. Sync the shared workboard
   - update `97-code-preflight.md` before the first edit with the active context bundle, starting progress snapshot, and first unit or batch
   - update it again when a unit completes, when progress changes materially, and whenever the run pauses
   - if an exported OpenSpec `tasks.md` exists, mirror task completion there too
6. Protect UX quality
   - if the change is user-visible, confirm the first-open experience is not obviously broken
7. Write back
   - append `Runs/<run-id>/00-code-run.md`
   - append `Runs/<run-id>/01-verification.md`
   - append `Runs/<run-id>/02-reentry.md` when blocked or refused

## Reentry Mapping

- `goal_conflict` -> reopen `A`
- `option_space_gap` -> reopen `B`
- `requirement_conflict` -> reopen `C`
- `critique_conflict` -> reopen `D`
- `dependency_conflict` -> reopen `E`
- `probe_invalidated` -> reopen `F`
- `attack_surface_gap` -> reopen `G`
- `review_gate_conflict` -> reopen `H`
- `gate_refusal` -> reopen the earliest truthful stage named in the handoff
