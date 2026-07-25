# Git DAG Patterns for Multi-Agent Collaboration

## Core Concepts

### Directed Acyclic Graph (DAG)

Git's commit history is a DAG where:
- Each commit points to one or more parents
- No cycles exist (you can't be your own ancestor)
- Branches are just pointers to commit nodes

In AgentHub, the DAG represents all approaches ever tried:
- Base commit = task starting point
- Each agent creates a branch from the base
- Commits on each branch = incremental progress
- Frontier = branch tips with no children

### Frontier Detection

The **frontier** is the set of commits (branch tips) that have no children. These are the "leaves" of the DAG — the latest state of each agent's work.

Algorithm:
```
1. Collect all branch tips: T = {tip(b) for b in hub_branches}
2. For each tip t in T:
   a. Check if t is an ancestor of any other tip t' in T
   b. If yes: t is NOT on the frontier (it's been extended)
   c. If no: t IS on the frontier
3. Return frontier set
```

Git command equivalent:
```bash
# For each branch, check if it's an ancestor of any other
git merge-base --is-ancestor <commit-a> <commit-b>
```

### Branch Naming Convention

```
hub/{session-id}/agent-{N}/attempt-{M}
```

Components:
- `session-id`: YYYYMMDD-HHMMSS timestamp (unique per session)
- `agent-N`: Sequential agent number (1 to agent-count)
- `attempt-M`: Retry counter (starts at 1, increments on re-spawn)

This creates a natural namespace:
- `hub/*` — all AgentHub work
- `hub/{session}/*` — all work for one session
- `hub/{session}/agent-{N}/*` — all attempts by one agent

## Merge Strategies

### No-Fast-Forward Merge (Default)

```bash
git merge --no-ff hub/{session}/agent-{N}/attempt-1
```

Creates a merge commit that:
- Preserves the branch topology in the DAG
- Makes it clear which commits came from which agent
- Allows `git log --first-parent` to show only merge points

### Squash Merge (Alternative)

```bash
git merge --squash hub/{session}/agent-{N}/attempt-1
```

Use when:
- Agent made many small commits that aren't individually meaningful
- Clean history is preferred over detailed history
- The approach matters, not the journey

### Cherry-Pick (Selective)

```bash
git cherry-pick <specific-commits>
```

Use when:
- Only some of an agent's commits are wanted
- Combining work from multiple agents
- The agent solved a bonus problem along the way

## Archive Strategy

After merging the winner, losers are archived via tags:

```bash
# Create archive tag
git tag hub/archive/{session}/agent-{N} hub/{session}/agent-{N}/attempt-1

# Delete branch ref
git branch -D hub/{session}/agent-{N}/attempt-1
```

Why tags instead of branches:
- Tags are immutable (can't be moved or accidentally pushed to)
- Tags don't clutter `git branch --list` output
- Tags are still reachable by `git log` and `git show`
- Git GC won't collect tagged commits

## Immutability Rules

1. **Never rebase agent branches** — rewrites history, breaks DAG
2. **Never force-push** — could overwrite other agents' work
3. **Never delete commits** — only delete branch refs (commits preserved via tags)
4. **Never amend** agent commits — append-only history
5. **Board is append-only** — new posts only, no edits

## DAG Visualization

Use `git log` flags to see the multi-agent DAG:

```bash
# Full graph with branch decoration
git log --all --oneline --graph --decorate --branches=hub/*

# Commits since base, all agents
git log --all --oneline --graph base..HEAD --branches=hub/{session}/*

# Per-agent linear history
git log --oneline hub/{session}/agent-1/attempt-1
```

## Worktree Isolation

Git worktrees provide filesystem isolation:

```bash
# Create worktree for an agent
git worktree add /tmp/hub-agent-1 -b hub/{session}/agent-1/attempt-1

# List active worktrees
git worktree list

# Remove after merge
git worktree remove /tmp/hub-agent-1
```

Key properties:
- Each worktree has its own working directory and index
- All worktrees share the same `.git` object store
- Commits in one worktree are immediately visible in another
- Cannot check out the same branch in two worktrees
