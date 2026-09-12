# Plan & Task Persistence

Session-spanning plans and task tracking for Claude Code.

This directory supports two modes — see `/plan-task` skill for details.

## Git-tracked mode (default)

`.claude/tasks/` is committed to Git and serves as the shared source of truth.

### Structure

```
.claude/tasks/
├── readme.md                  # Index of all plans
├── <slug>-<account>-<date>/
│   ├── readme.md              # Purpose and current state
│   ├── plan-v1.md             # Plan (immutable once created)
│   ├── todo.md                # Task progress (frequently updated)
│   └── ...
```

### Quick Rules

- Check `readme.md` at session start for incomplete plans
- Update `todo.md` only during work — never edit `plan-vN.md`
- Task markers: `- [ ]` pending, `- [~]` in progress, `- [x]` done
- To revise a plan, create `plan-vN+1.md` (keep previous versions)
- On session end, update `<slug>/readme.md` with handoff notes
- See `/plan-task` skill for full procedures

## Issue-centric mode

`.claude/tasks/` is **gitignored** and serves as a local working memo. The issue tracker is the primary source of truth.

### Setup

Add to `.gitignore`:

```
.claude/tasks/
```

### Quick Rules

- At session start, check assigned issues in your tracker (not `readme.md`)
- Use `.claude/tasks/` freely as a local scratchpad — it will not be committed
- Anything worth sharing with the team belongs in the issue tracker
- Post progress, blockers, and decisions to the issue, not to local files
- See `/plan-task` skill for full procedures
