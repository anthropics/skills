# Git Worktree Manager

Production workflow for parallel branch development with isolated ports, env sync, and cleanup safety checks. This skill packages practical CLI tooling and operating guidance for multi-worktree teams.

## Quick Start

```bash
# Create + prepare a worktree
python scripts/worktree_manager.py \
  --repo . \
  --branch feature/api-hardening \
  --name wt-api-hardening \
  --base-branch main \
  --install-deps \
  --format text

# Review stale worktrees
python scripts/worktree_cleanup.py --repo . --stale-days 14 --format text
```

## Included Tools

- `scripts/worktree_manager.py`: create/list-prep workflow, deterministic ports, `.env*` sync, optional dependency install
- `scripts/worktree_cleanup.py`: stale/dirty/merged analysis with optional safe removal

Both support `--input <json-file>` and stdin JSON for automation.

## References

- `references/port-allocation-strategy.md`
- `references/docker-compose-patterns.md`

## Installation

### Claude Code

```bash
cp -R engineering/git-worktree-manager ~/.claude/skills/git-worktree-manager
```

### OpenAI Codex

```bash
cp -R engineering/git-worktree-manager ~/.codex/skills/git-worktree-manager
```

### OpenClaw

```bash
cp -R engineering/git-worktree-manager ~/.openclaw/skills/git-worktree-manager
```
