---
name: ai-coding-ok
description: USE THIS SKILL FIRST on any coding task (feat, fix, bug, refactor, plan, design, brainstorm, code review, implement, add feature, write tests) when the project contains `.github/agent/memory/` or `AGENTS.md`. Loads three-tier project memory (project-memory, decisions-log, task-history) BEFORE writing code, then updates memory AFTER finishing via the PDCA Act phase — the guardrail that prevents "AI fixed bug X and broke feature Y" across iterations. Also handles INSTALL when the user says "install ai-coding-ok" or the project has no `.github/agent/memory/` yet. Also handles UPGRADE when the user says "upgrade ai-coding-ok".
license: MIT. Complete terms in LICENSE.txt
---

# ai-coding-ok — PDCA Memory Loop

A three-tier memory system with a closed PDCA loop (Plan → Do → Check → Act) that keeps project context accurate across sessions and iterations. Prevents the classic AI regression: "fixed bug X, silently deleted constraint Y that was added three sessions ago."

## The core problem this solves

AI coding tools are great within a session. Across sessions, Claude has no memory of past decisions, constraints, or what changed last week. Most tools add discipline to a single session (plan before code, TDD, review). None of them close the feedback loop — memory files written at setup time rot after 10 iterations because no one updates them.

ai-coding-ok fixes this with the **Act** step: after every task, Claude writes back to memory. Iteration 50 reads the same three files iteration 1 read — but they contain 50 entries of compounded context.

## Three-Tier Memory

| File | Tier | Content | Updated |
|------|------|---------|---------|
| `project-memory.md` | Long-term | Architecture, constraints, known issues | Rarely |
| `decisions-log.md` | Mid-term | ADRs — why decisions were made | On arch changes |
| `task-history.md` | Short-term | Last 30 task summaries | Every task |

## Modes

Determine which mode applies, then follow that mode's steps.

### Mode A — Install (one-time)

**Trigger:** User says "install ai-coding-ok" or project has no `.github/agent/memory/`

**Steps:**
1. Locate templates at `<skill-dir>/templates/{en|zh}/` (choose language based on user's message)
2. Check for conflicts: `AGENTS.md`, `CLAUDE.md`, `.github/copilot-instructions.md`, `.github/agent/`
3. If conflicts exist, stop and offer: overwrite / copy missing only / abort
4. Copy template directory into project root (`cp -rn <templates>/. <project-root>/`)
5. Ask one question: *"In one sentence, what are you building?"*
6. Infer tech stack, design principles, project type from the answer
7. Replace every `{{placeholder}}` across all copied files with inferred values
8. Bootstrap `task-history.md` with a TASK-001 install entry
9. Report: files installed, key inferred decisions, next steps

**Language detection:** if user's message is predominantly Chinese → use `templates/zh/`; otherwise → use `templates/en/`

---

### Mode B — PDCA Plan (before every coding task)

**Trigger:** Project has `.github/agent/memory/` + user requests any development work

**Steps (~30 seconds, before touching any code):**
1. Read `AGENTS.md`
2. Read `.github/agent/memory/project-memory.md`
3. Read `.github/agent/memory/decisions-log.md`
4. Read `.github/agent/memory/task-history.md`
5. Summarize key constraints internally to confirm understanding
6. **Continue with the user's original task** — do not stop here

> If another skill is also triggered (e.g. `writing-plans`), run Mode B first, then enter that skill.

---

### Mode C — PDCA Act (after every coding task)

**Trigger:** A coding/design task has just been completed

**Steps (must not skip):**
1. Update `.github/agent/memory/task-history.md` — record this task's summary
2. If architecture/technical decisions changed → update `.github/agent/memory/decisions-log.md`
3. If project facts changed (new modules, tech stack changes) → update `.github/agent/memory/project-memory.md`
4. Include a **Memory Updates** section in the final output listing which files were updated

> If context limits prevent direct file edits, output the required updates as text and tell the user to apply them manually.

---

### Mode D — Upgrade

**Trigger:** User says "upgrade ai-coding-ok" or "update ai-coding-ok"

**Steps:**
1. Read version markers from installed files (format: `<!-- ai-coding-ok: vX.Y -->`)
2. Read latest templates from `<skill-dir>/templates/<lang>/`
3. Diff at Markdown section level (##/###): identify added, removed, modified sections
4. Show change summary to user and ask confirmation
5. Apply changes: insert new sections, remove deprecated ones, merge modified ones
6. Replace `{{placeholders}}` in new content with values from existing project files
7. Bump all version markers to latest
8. Append TASK-00N upgrade entry to `task-history.md`

---

## What gets installed in the project

```
your-project/
├── AGENTS.md                          # Architecture cheatsheet (AI reads first)
├── CLAUDE.md                          # Claude Code auto-load shim → @AGENTS.md
├── .cursor/rules/ai-coding-ok.mdc     # Cursor: alwaysApply PDCA rule
└── .github/
    ├── copilot-instructions.md        # Copilot: auto-loaded behavior rules
    ├── project-metadata.yml
    ├── PULL_REQUEST_TEMPLATE.md
    ├── ISSUE_TEMPLATE/
    ├── workflows/                     # CI + memory-update reminder
    └── agent/
        ├── system-prompt.md
        ├── coding-standards.md
        ├── workflows.md
        ├── prompt-templates.md
        └── memory/
            ├── project-memory.md      # Long-term memory
            ├── decisions-log.md       # Mid-term memory (ADRs)
            └── task-history.md        # Short-term memory
```

## Composing with superpowers

ai-coding-ok and [superpowers](https://github.com/obra/superpowers) solve orthogonal problems:

- **superpowers** → per-session discipline (plan before code, TDD, structured review)
- **ai-coding-ok** → cross-session memory (context persists and grows across iterations)

Combined flow:
```
1. ai-coding-ok Mode B  (Plan: load memory)
2. superpowers          (brainstorming → planning → execution)
3. ai-coding-ok Mode C  (Act: write memory back)
```

## Template source

Templates (bilingual: `en/` and `zh/`) live at:
`https://github.com/Mark7766/ai-coding-ok/tree/master/templates`

Install script for non-Claude-Code users (Copilot, Cursor, OpenCode):
`https://github.com/Mark7766/ai-coding-ok/blob/master/install.sh`

## Verify installation

```bash
bash <(curl -sL https://raw.githubusercontent.com/Mark7766/ai-coding-ok/master/scripts/verify.sh)
```

Exit codes: `0` = clean, `1` = missing files, `2` = unfilled placeholders.
