---
name: "git-worktree-manager"
description: "Run parallel feature work safely with Git worktrees. Standardizes branch isolation, port allocation, environment sync, and cleanup so each worktree behaves like an independent local app. Optimized for multi-agent workflows where each agent or terminal session owns one worktree. Use when running multiple feature branches simultaneously, isolating experimental work, or coordinating multi-agent development across the same repo."
---

# Git Worktree Manager

**Tier:** POWERFUL  
**Category:** Engineering  
**Domain:** Parallel Development & Branch Isolation

## Overview

Use this skill to run parallel feature work safely with Git worktrees. It standardizes branch isolation, port allocation, environment sync, and cleanup so each worktree behaves like an independent local app without stepping on another branch.

This skill is optimized for multi-agent workflows where each agent or terminal session owns one worktree.

## Core Capabilities

- Create worktrees from new or existing branches with deterministic naming
- Auto-allocate non-conflicting ports per worktree and persist assignments
- Copy local environment files (`.env*`) from main repo to new worktree
- Optionally install dependencies based on lockfile detection
- Detect stale worktrees and uncommitted changes before cleanup
- Identify merged branches and safely remove outdated worktrees

## When to Use

- You need 2+ concurrent branches open locally
- You want isolated dev servers for feature, hotfix, and PR validation
- You are working with multiple agents that must not share a branch
- Your current branch is blocked but you need to ship a quick fix now
- You want repeatable cleanup instead of ad-hoc `rm -rf` operations

## Key Workflows

### 1. Create a Fully-Prepared Worktree

1. Pick a branch name and worktree name.
2. Run the manager script (creates branch if missing).
3. Review generated port map.
4. Start app using allocated ports.

```bash
python scripts/worktree_manager.py \
  --repo . \
  --branch feature/new-auth \
  --name wt-auth \
  --base-branch main \
  --install-deps \
  --format text
```

If you use JSON automation input:

```bash
cat config.json | python scripts/worktree_manager.py --format json
# or
python scripts/worktree_manager.py --input config.json --format json
```

### 2. Run Parallel Sessions

Recommended convention:

- Main repo: integration branch (`main`/`develop`) on default port
- Worktree A: feature branch + offset ports
- Worktree B: hotfix branch + next offset

Each worktree contains `.worktree-ports.json` with assigned ports.

### 3. Cleanup with Safety Checks

1. Scan all worktrees and stale age.
2. Inspect dirty trees and branch merge status.
3. Remove only merged + clean worktrees, or force explicitly.

```bash
python scripts/worktree_cleanup.py --repo . --stale-days 14 --format text
python scripts/worktree_cleanup.py --repo . --remove-merged --format text
```

### 4. Docker Compose Pattern

Use per-worktree override files mapped from allocated ports. The script outputs a deterministic port map; apply it to `docker-compose.worktree.yml`.

See [docker-compose-patterns.md](references/docker-compose-patterns.md) for concrete templates.

### 5. Port Allocation Strategy

Default strategy is `base + (index * stride)` with collision checks:

- App: `3000`
- Postgres: `5432`
- Redis: `6379`
- Stride: `10`

See [port-allocation-strategy.md](references/port-allocation-strategy.md) for the full strategy and edge cases.

## Script Interfaces

- `python scripts/worktree_manager.py --help`
  - Create/list worktrees
  - Allocate/persist ports
  - Copy `.env*` files
  - Optional dependency installation
- `python scripts/worktree_cleanup.py --help`
  - Stale detection by age
  - Dirty-state detection
  - Merged-branch detection
  - Optional safe removal

Both tools support stdin JSON and `--input` file mode for automation pipelines.

## Common Pitfalls

1. Creating worktrees inside the main repo directory
2. Reusing `localhost:3000` across all branches
3. Sharing one database URL across isolated feature branches
4. Removing a worktree with uncommitted changes
5. Forgetting to prune old metadata after branch deletion
6. Assuming merged status without checking against the target branch

## Best Practices

1. One branch per worktree, one agent per worktree.
2. Keep worktrees short-lived; remove after merge.
3. Use a deterministic naming pattern (`wt-<topic>`).
4. Persist port mappings in file, not memory or terminal notes.
5. Run cleanup scan weekly in active repos.
6. Use `--format json` for machine flows and `--format text` for human review.
7. Never force-remove dirty worktrees unless changes are intentionally discarded.

## Validation Checklist

Before claiming setup complete:

1. `git worktree list` shows expected path + branch.
2. `.worktree-ports.json` exists and contains unique ports.
3. `.env` files copied successfully (if present in source repo).
4. Dependency install command exits with code `0` (if enabled).
5. Cleanup scan reports no unintended stale dirty trees.

## References

- [port-allocation-strategy.md](references/port-allocation-strategy.md)
- [docker-compose-patterns.md](references/docker-compose-patterns.md)
- [README.md](README.md) for quick start and installation details

## Decision Matrix

Use this quick selector before creating a new worktree:

- Need isolated dependencies and server ports -> create a new worktree
- Need only a quick local diff review -> stay on current tree
- Need hotfix while feature branch is dirty -> create dedicated hotfix worktree
- Need ephemeral reproduction branch for bug triage -> create temporary worktree and cleanup same day

## Operational Checklist

### Before Creation

1. Confirm main repo has clean baseline or intentional WIP commits.
2. Confirm target branch naming convention.
3. Confirm required base branch exists (`main`/`develop`).
4. Confirm no reserved local ports are already occupied by non-repo services.

### After Creation

1. Verify `git status` branch matches expected branch.
2. Verify `.worktree-ports.json` exists.
3. Verify app boots on allocated app port.
4. Verify DB and cache endpoints target isolated ports.

### Before Removal

1. Verify branch has upstream and is merged when intended.
2. Verify no uncommitted files remain.
3. Verify no running containers/processes depend on this worktree path.

## CI and Team Integration

- Use worktree path naming that maps to task ID (`wt-1234-auth`).
- Include the worktree path in terminal title to avoid wrong-window commits.
- In automated setups, persist creation metadata in CI artifacts/logs.
- Trigger cleanup report in scheduled jobs and post summary to team channel.

## Failure Recovery

- If `git worktree add` fails due to existing path: inspect path, do not overwrite.
- If dependency install fails: keep worktree created, mark status and continue manual recovery.
- If env copy fails: continue with warning and explicit missing file list.
- If port allocation collides with external service: rerun with adjusted base ports.
