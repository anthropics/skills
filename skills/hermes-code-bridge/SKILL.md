---
name: hermes-code-bridge
description: "Use when connecting Hermes Agent to local coding CLIs such as Codex, Kimi Code, Claude Code, OpenCode, Gemini CLI, or other terminal-based coding assistants. Provides a general bridge workflow for discovering agents, reusing sessions, dispatching prompts, monitoring execution, collecting evidence, and reporting results without pretending Hermes did the delegated work."
version: 1.0.0
author: Hermes Agent
license: MIT
platforms: [linux, macos, windows]
metadata:
  hermes:
    tags: [hermes, coding-agents, cli, codex, kimi-code, claude-code, opencode, orchestration, tmux, dispatch]
    related_skills: [hermes-agent, cli-agent-orchestrator, codex, claude-code, opencode]
---

# Hermes Code Bridge

## Overview

Hermes Code Bridge turns Hermes Agent into a control layer for local terminal-based coding agents. The goal is not to replace Codex, Kimi Code, Claude Code, OpenCode, Gemini CLI, or similar tools. The goal is to let Hermes coordinate them safely: choose the right tool, reuse the right session, send a precise task prompt, monitor the run, collect raw evidence, and report what actually happened.

Use this skill when the user wants Hermes to connect to one or more local coding CLIs and make them do implementation, review, debugging, research, experiment management, documentation, or repository maintenance work.

The bridge pattern is:

```text
User request
  -> Hermes clarifies scope and chooses an existing local coding agent/session
  -> Hermes sends a structured prompt through the real CLI
  -> Local coding CLI executes in its own workspace/session
  -> Hermes monitors output, verifies artifacts, and reports evidence
```

Hermes is the control plane. Local coding CLIs are execution backends. The terminal, tmux, session archives, and output files are the transport and evidence layer.

This is intentionally lighter than a full multi-agent workspace manager. Projects such as CCB (`claude_codex_bridge`) create visible tmux workspaces with configured panes, sidebars, team topology, worktrees, and inter-agent communication. Hermes Code Bridge is a Hermes skill: it does not require a new workspace system. It teaches Hermes how to drive whichever local coding CLIs are already installed, while preserving real sessions and verifiable outputs.

## When to Use

Use this skill when:

- The user asks Hermes to make Codex, Kimi Code, Claude Code, OpenCode, Gemini CLI, or another local coding agent do work.
- The user wants Hermes to coordinate several coding agents without manually copying prompts between terminals.
- A task should be executed inside an existing coding-agent session instead of by Hermes directly.
- The user needs background monitoring and a concise evidence-based report after a long agent run.
- The user wants a general workflow for experiments, coding, debugging, documentation, review, or repository operations through local coding CLIs.

Do not use this skill when:

- The user only wants Hermes to answer a normal question directly.
- The task can be handled by Hermes tools and the user did not ask for a specific coding CLI.
- The user wants a full tmux workspace product with persistent pane layout, sidebar UI, and project team config; in that case consider using or configuring a dedicated tool such as CCB.
- The requested CLI is not installed or not authenticated; report that honestly instead of substituting Hermes work.

## Core Principles

1. **Use the real CLI.** If the user asks for Codex, run Codex. If the user asks for Kimi Code, run Kimi Code. Do not use `delegate_task`, `execute_code`, or a Hermes subagent and claim that a different tool did the work.

2. **Preserve session ownership.** Existing coding-agent sessions contain context, decisions, tool history, and project assumptions. Reuse the correct session whenever possible. Do not create a new session just because it is easier.

3. **Hermes coordinates; workers execute.** Hermes can inspect, route, prompt, monitor, and summarize. The local coding CLI should own the actual code edits or experiment actions when the user requested that tool.

4. **Confirm before dispatch when side effects matter.** If the task may edit files, run expensive jobs, change git state, call external APIs, or resume an ambiguous session, show the chosen agent/session and prompt draft before sending it.

5. **Report evidence, not vibes.** Final reports should include the actual CLI invoked, working directory, session id when relevant, output summary, artifacts produced, verification checks, and any failure or uncertainty.

6. **Keep it general and private.** Public skills must not contain personal paths, private project names, private session IDs, credentials, private endpoints, or organization-specific assumptions.

## Architecture Model

Think of the bridge as four layers:

| Layer | Responsibility |
| --- | --- |
| Hermes control layer | Interpret user intent, choose backend, write prompt, monitor, verify, report. |
| Coding CLI backend | Codex, Kimi Code, Claude Code, OpenCode, Gemini CLI, or another terminal coding assistant. |
| Session/state layer | Existing CLI sessions, project directories, tmux panes, logs, JSONL archives, or CLI history files. |
| Evidence layer | Terminal output, final messages, diffs, generated files, test logs, screenshots, benchmark outputs. |

The skill should work with two operating styles:

- **Direct non-interactive dispatch:** Hermes runs a single CLI command with a prompt and waits or monitors in the background.
- **Interactive workspace dispatch:** Hermes sends prompts into an existing tmux pane or resumes a CLI session that the user also can observe manually.

## Pre-flight Checks

Before dispatching work to a local coding CLI, gather enough context to avoid sending the wrong task to the wrong backend.

### 1. Identify the requested backend

Map user language to a backend:

| User wording | Backend |
| --- | --- |
| Codex, OpenAI Codex | `codex` |
| Kimi Code, Kimi CLI | `kimi` or the user's configured Kimi command |
| Claude Code | `claude` |
| OpenCode | `opencode` |
| Gemini CLI | `gemini` or the user's configured Gemini command |
| coding agent, local agent, worker | Ask or infer from project/session context |

If the user names a backend, do not silently substitute another backend.

### 2. Check installation

```bash
command -v codex || true
command -v kimi || true
command -v claude || true
command -v opencode || true
command -v gemini || true
```

If a command is missing, report it and suggest installation/configuration. Do not pretend dispatch succeeded.

### 3. Confirm the working directory

Prefer the project root, not the user's home directory.

```bash
pwd
git rev-parse --show-toplevel 2>/dev/null || true
git status --short 2>/dev/null || true
```

For repository tasks, include the absolute working directory in the dispatch prompt and command.

### 4. Discover existing sessions

Use the backend's session list, history files, or project metadata. The exact storage paths and commands vary by tool version, so treat the examples below as patterns, not immutable API contracts.

Codex examples:

```bash
# If supported by the installed CLI
codex --help
codex exec --help
codex resume --help

# Common local archive patterns; inspect read-only
find ~/.codex -maxdepth 4 -type f \( -name '*.jsonl' -o -name '*.json' -o -name '*.toml' \) 2>/dev/null | head -50
```

Kimi Code examples:

```bash
kimi --help
find ~/.kimi -maxdepth 4 -type f \( -name '*.jsonl' -o -name '*.json' -o -name '*.toml' \) 2>/dev/null | head -50
```

Claude Code examples:

```bash
claude --help
find ~/.claude -maxdepth 4 -type f 2>/dev/null | head -50
```

OpenCode examples:

```bash
opencode --help
find ~/.opencode ~/.config/opencode -maxdepth 4 -type f 2>/dev/null | head -50
```

### 5. Decide whether confirmation is required

Require confirmation before dispatch when any of these are true:

- The target session is ambiguous.
- The command may modify files, run long experiments, spend money, push commits, open PRs, deploy, or delete data.
- The prompt includes assumptions not explicitly stated by the user.
- The requested backend is unavailable and an alternative is being proposed.
- The work is public-facing or could expose private information.

For read-only inspection or tiny status checks, it is usually acceptable to proceed directly and report results.

## Session Selection Protocol

When multiple sessions exist, choose the session by role and project, not by recency alone.

Recommended matching signals:

1. Current project directory or repository root.
2. Session title or first user prompt.
3. Recent conversation summary or archive content.
4. Files or artifacts the session has touched.
5. User-provided session name, id, or role.

Common session roles:

| Role | Use for |
| --- | --- |
| `main` / `lead` / `controller` | Planning, high-level coordination, final integration. |
| `implementation` / `worker` | Code edits, scripts, feature implementation. |
| `reviewer` | Code review, risk analysis, PR feedback. |
| `debugger` | Reproducing bugs, reading logs, root-cause analysis. |
| `research` | Literature, library, API, or benchmark research. |
| `data` / `experiments` | Dataset processing, experiment runs, result aggregation. |
| `docs` / `writer` | README, docs, release notes, design docs. |

If no session fits, ask whether to create a new one or run a one-shot command. Do not silently create a new long-lived session when the user's workflow depends on existing session memory.

## Dispatch Prompt Template

Use this template for non-trivial tasks:

```markdown
You are the <ROLE> coding agent for this project.

Working directory:
<ABSOLUTE_PROJECT_DIR>

Background:
- <Relevant project context>
- <Relevant prior decisions or files>
- <What the user wants and why>

Task:
1. <Concrete step 1>
2. <Concrete step 2>
3. <Concrete step 3>

Constraints:
- Do not make unrelated changes.
- Do not add new abstractions, dependencies, configs, or features unless required for this task.
- Do not silently guess important missing requirements. If blocked, state the ambiguity and propose the smallest safe default.
- Preserve existing style and project conventions.
- If you find unrelated issues, mention them in the final report but do not fix them unless necessary for this task.

Success criteria:
- <Measurable criterion 1>
- <Measurable criterion 2>
- <Expected artifact path or command output>

Verification:
- Run or explain: <test command / lint command / manual check>
- Report exact commands run and whether they passed.

Final report format:
- Summary
- Files changed or artifacts created
- Commands run
- Verification results
- Remaining risks or blockers
```

For read-only research or review tasks, replace file-edit constraints with scope and evidence requirements:

```markdown
Do not modify files. Read only the relevant files/logs/docs. Quote file paths, line numbers when possible, commands run, and confidence level for each conclusion.
```

## Confirmation Template

When confirmation is required, show a concise confirmation block:

```markdown
I understand the task as: <one-sentence summary>.

Proposed backend: <Codex/Kimi Code/Claude Code/OpenCode/...>
Working directory: <absolute path>
Session: <session name/id or "one-shot new run">
Reason: <why this backend/session fits>

Prompt draft:
---
<prompt>
---

Please confirm before I dispatch this to the local coding CLI.
```

Do not dispatch until the user confirms. If the user edits the prompt or selects a different backend, update the command accordingly.

## Command Recipes

CLI flags change over time. Always check `<command> --help` when a command fails or when using a new version.

### Codex

Common patterns:

```bash
# One-shot non-interactive
codex exec "<PROMPT>"

# One-shot with automatic approval if supported by the installed version
codex exec --ask-for-approval never "<PROMPT>"

# Run from a project directory if supported
codex exec -C <PROJECT_DIR> "<PROMPT>"

# Resume an explicit session if supported
codex exec resume <SESSION_ID> "<PROMPT>"

# JSON output for easier parsing if supported
codex exec --json -o <OUTPUT_JSONL> "<PROMPT>"
```

Automation notes:

- Prefer explicit session IDs over interactive pickers.
- Prefer non-interactive `exec` modes for Hermes terminal calls.
- If the CLI refuses due to repository trust or git checks, stop and report the exact error unless the user has already approved bypassing that guard.
- Use background execution for long tasks and monitor with Hermes process tools.

### Kimi Code

Common patterns:

```bash
# One-shot non-interactive
kimi --print -p "<PROMPT>"

# Automatic approval if supported and appropriate
kimi --print --yolo -p "<PROMPT>"

# Resume an explicit session if supported
kimi -S <SESSION_ID> --print -p "<PROMPT>"

# Continue the latest session for the current directory if supported
kimi --continue --print -p "<PROMPT>"

# Specify working directory if supported
kimi -w <PROJECT_DIR> --print -p "<PROMPT>"
```

Automation notes:

- Use `--print` or equivalent non-interactive output mode when calling from Hermes.
- Do not rely on interactive session pickers unless running inside a tracked PTY/tmux pane.
- Use `--yolo` or AFK-style modes only when the user has approved the risk.

### Claude Code

Common patterns:

```bash
# One-shot print mode
claude -p "<PROMPT>"

# With explicit working directory if supported
claude --cwd <PROJECT_DIR> -p "<PROMPT>"

# Inspect supported session/resume flags
claude --help
```

Automation notes:

- Claude Code often has rich interactive behavior. For Hermes automation, prefer print/non-interactive modes where possible.
- If using a persistent interactive Claude pane, use tmux send/capture rather than pretending the command is non-interactive.

### OpenCode

Common patterns:

```bash
# Inspect installed CLI first because command syntax varies
opencode --help

# Typical one-shot pattern, if supported by installed version
opencode run "<PROMPT>"

# Project directory pattern, if supported
opencode run --cwd <PROJECT_DIR> "<PROMPT>"
```

Automation notes:

- OpenCode command syntax has changed across versions; verify with `opencode --help` before dispatch.
- Capture stdout/stderr and report the exact command form used.

### Gemini CLI or other coding CLIs

Use the generic adapter pattern:

```bash
<AGENT_CMD> --help
<AGENT_CMD> <NON_INTERACTIVE_FLAGS> "<PROMPT>"
```

Record:

- command path from `command -v <AGENT_CMD>`
- version if available
- working directory
- exact prompt
- output file or terminal log

## Interactive tmux Bridge

For long-running interactive CLIs, tmux can provide a visible bridge. This is useful when the user wants to observe the agent, intervene manually, or keep multiple agents alive.

Create or attach a project tmux session:

```bash
tmux new-session -d -s <SESSION_NAME> -c <PROJECT_DIR>
tmux send-keys -t <SESSION_NAME> "<AGENT_CMD>" Enter
```

Send a prompt:

```bash
tmux send-keys -t <SESSION_NAME> "<PROMPT>" Enter
```

Capture output:

```bash
tmux capture-pane -t <SESSION_NAME> -p -S -200
```

Safety notes:

- Escape quotes and newlines carefully. For large prompts, write the prompt to a temporary file and paste/send it in a controlled way.
- Prefer one tmux session per project or per agent group.
- Do not kill an existing tmux session unless the user confirms it is safe.
- If using a dedicated workspace manager such as CCB, follow that tool's config and command model instead of manually fighting its panes.

## Background Monitoring

For bounded long-running tasks, run the CLI in the background with completion notification if available in the host environment.

Hermes tool pattern:

```python
terminal(command="cd <PROJECT_DIR> && <AGENT_CMD> <FLAGS> '<PROMPT>'", background=True, notify_on_complete=True)
process(action="poll", session_id="<HERMES_PROCESS_ID>")
process(action="log", session_id="<HERMES_PROCESS_ID>", limit=80)
process(action="wait", session_id="<HERMES_PROCESS_ID>", timeout=180)
```

Monitoring checklist:

- Poll soon after start to catch immediate authentication or syntax failures.
- For long jobs, report progress only when there is meaningful new output.
- If stuck at an interactive prompt, either answer only if the user already approved the choice, or ask the user.
- If the process fails, capture exit code and stderr. Do not hide failures behind a summary.

## Evidence Collection

Collect evidence before reporting success.

Minimum evidence:

- Exact backend and command used.
- Working directory.
- Session id, tmux pane, or output file when relevant.
- Final CLI output or a concise excerpt from raw output.
- Changed files or created artifacts, if any.
- Verification commands and results.

Useful commands:

```bash
# Git evidence
git status --short
git diff --stat
git diff -- <RELEVANT_PATHS>

# Artifact evidence
find <OUTPUT_DIR> -maxdepth 2 -type f -print
file <ARTIFACT_PATH>

# Test evidence
<TEST_COMMAND>
```

If the coding CLI claims it created a file, verify the file exists. If it claims tests passed, inspect the actual test command output. If the output is truncated, say so.

## Reporting Template

Use a report like this:

````markdown
Dispatched to: <backend>
Working directory: <path>
Session/process: <session id / tmux pane / Hermes process id>
Command: <exact command, with secrets redacted>

Result:
- <What completed>
- <Files changed or artifacts created>
- <Verification result>

Evidence:
```text
<short raw output excerpt>
```

Risks / blockers:
- <Anything unresolved, failed, ambiguous, or not verified>
````

For user-facing summaries, keep the report concise, but do not omit failure state or verification gaps.

## Safety Rules

Never do these:

- Do not claim a local coding CLI ran unless the actual CLI command was executed.
- Do not use Hermes `delegate_task` or `execute_code` as a fake substitute for Codex/Kimi/Claude/OpenCode.
- Do not directly edit the coding agent's session database, JSONL history, or internal state files.
- Do not modify project files directly when the user explicitly asked a coding CLI to own the work, unless the user separately authorizes Hermes to edit files.
- Do not create a new persistent session when an existing relevant session should be reused.
- Do not bypass sandbox, approval, git safety, or destructive-command prompts unless the user approved that risk.
- Do not paste secrets, private endpoints, personal paths, or private project names into a public skill or shareable prompt.

Recommended defaults:

- Prefer read-only inspection before write-heavy dispatch.
- Prefer explicit working directories and session IDs.
- Prefer non-interactive CLI flags for automation.
- Prefer tmux for long-lived interactive agents.
- Prefer worktrees for parallel agents editing the same repository.
- Prefer small, scoped prompts with clear success criteria over vague broad prompts.

## Open-source Sanitization

Before publishing or sharing this skill, inspect for private information.

Remove or replace:

- Personal names, usernames, organization names, lab names, and relationship details.
- Absolute paths such as `/Users/<name>/...` or `/home/<name>/...`.
- Private project names, paper names, dataset names, internal codenames, or unreleased features.
- Real session IDs, API keys, tokens, private base URLs, and account identifiers.
- Private communication habits, schedules, or user-specific preferences.

Use placeholders instead:

```text
<PROJECT_DIR>
<SESSION_ID>
<AGENT_CMD>
<PROMPT>
<OUTPUT_JSONL>
<TEST_COMMAND>
<ARTIFACT_PATH>
```

Run a quick privacy scan before release:

```bash
grep -RInE "(/Users/|/home/|API_KEY|TOKEN|SECRET|SESSION_ID_HERE|PRIVATE|@)" SKILL.md references templates scripts 2>/dev/null || true
```

A public skill should teach the workflow, not expose a particular user's workflow map.

## Relationship to Multi-Agent Workspace Tools

Hermes Code Bridge can coexist with workspace tools such as CCB.

Use a dedicated workspace tool when the user wants:

- A persistent tmux UI with multiple visible panes.
- Project-level team topology in a config file.
- Sidebar/status UI and inter-agent `/ask` routing.
- Managed worktrees and pane recovery.

Use Hermes Code Bridge when the user wants:

- A lightweight Hermes skill for dispatching to installed CLIs.
- One-shot or session-resume routing from Hermes conversations.
- Evidence-based reports back through Hermes.
- A portable pattern that works even without a full workspace manager.

If CCB is installed, Hermes can treat `ccb` as another bridge backend: inspect `.ccb/ccb.config`, start or attach the workspace, send prompts to the appropriate pane/agent, and capture output. Do not rewrite CCB configuration unless the user asked for that.

## Common Pitfalls

1. **Confusing Hermes with the worker.** Hermes may be capable of doing the task, but if the user requested Codex/Kimi/Claude/OpenCode, run that real tool.

2. **Using the wrong session.** Recent is not always correct. Match by project, role, title, and history.

3. **Trusting summaries without evidence.** Agent-maintained notes may be stale. Check actual terminal output, git diff, files, or test logs.

4. **Losing output from long jobs.** Run bounded long jobs in the background with process tracking or redirect JSON/text output to a file.

5. **Interactive picker in non-TTY.** Many CLIs fail when an interactive session picker runs without a terminal. Use explicit session IDs or tmux/PTY.

6. **Over-broad prompts.** Large vague prompts cause unnecessary rewrites. Use narrow tasks, constraints, and success criteria.

7. **Unsafe approval bypass.** Flags like `--yolo`, full-auto, or sandbox bypass are convenient but risky. Use only with user approval and appropriate repository state.

8. **Publishing private workflow details.** A reusable public skill should not include one user's project map, collaborators, filesystem paths, private endpoints, or real session IDs.

## Verification Checklist

Before reporting completion:

- [ ] The requested backend was actually executed.
- [ ] The working directory was correct.
- [ ] The selected session was correct or the run was intentionally one-shot.
- [ ] The prompt contained role, task, constraints, success criteria, and output requirements.
- [ ] Side-effectful dispatch was confirmed by the user when needed.
- [ ] Background process status and exit code were checked.
- [ ] Raw output or output file was inspected.
- [ ] Claimed artifacts/files were verified on disk.
- [ ] Tests, lint, benchmarks, or manual checks were run or explicitly marked not run.
- [ ] The final report includes command, evidence, result, and unresolved risks.
- [ ] No secrets or private information appear in shareable output.

## Minimal One-Shot Example

User asks: "Have Codex review this repository for risky changes."

Hermes should:

1. Confirm the repository root.
2. Check Codex is installed.
3. Decide whether this is read-only. If yes, dispatch without extra confirmation unless the user workflow requires it.
4. Run a real Codex command.
5. Capture and report evidence.

Example:

```bash
cd <PROJECT_DIR>
codex exec "Read-only review: inspect the current git diff and identify correctness, security, and maintainability risks. Do not modify files. Report file paths, line references when possible, severity, and recommended fixes."
```

Report:

```markdown
Dispatched to: Codex
Working directory: <PROJECT_DIR>
Command: codex exec "Read-only review: ..."

Result:
- Found <N> issues / no blocking issues.
- No files modified.

Evidence:
<raw output excerpt>

Risks:
- Tests were not run because this was review-only.
```

## Minimal Multi-Agent Example

User asks: "Ask one agent to implement and another to review."

Hermes should:

1. Choose separate sessions/backends, ideally separate worktrees if both may edit.
2. Confirm the plan and prompts.
3. Dispatch implementation first.
4. Verify diff/artifacts.
5. Dispatch review with the implementation context.
6. Report both outputs and any conflicts.

Implementation prompt should be scoped and surgical. Review prompt should be read-only unless the user asks for fixes.

```text
Codex worker: implement the smallest change that satisfies <goal>; run <tests>; report files changed.
Claude reviewer: read the resulting diff only; do not modify files; list blockers, non-blockers, and test gaps.
```

If both agents need to edit concurrently, use git worktrees or isolated branches to avoid file conflicts.
