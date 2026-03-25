---
name: git-workflow
description: Use this skill whenever the user wants help with Git operations, branching strategies, resolving merge conflicts, rebasing, cherry-picking commits, undoing changes, writing commit messages, setting up .gitignore, managing remotes, tagging releases, or understanding Git history. If the user mentions git commands, branches, commits, pull requests workflow, or asks how to undo/fix git mistakes, use this skill.
license: Proprietary. LICENSE.txt has complete terms
---

# Git Workflow Guide

## Overview

This guide covers common Git operations, best practices, and workflows for effective version control.

## Core Concepts

### Staging and Committing

```bash
# Stage specific files
git add file.txt
git add src/

# Stage all changes
git add .

# Commit with message
git commit -m "feat: add login functionality"

# Stage and commit tracked files in one step
git commit -am "fix: correct typo in header"

# Amend last commit (before pushing)
git commit --amend -m "corrected commit message"
```

### Branching

```bash
# Create and switch to new branch
git checkout -b feature/my-feature
# or (modern syntax)
git switch -c feature/my-feature

# List branches
git branch          # local
git branch -r       # remote
git branch -a       # all

# Delete branch
git branch -d feature/my-feature        # safe delete (merged only)
git branch -D feature/my-feature        # force delete

# Rename branch
git branch -m old-name new-name
```

### Merging and Rebasing

```bash
# Merge branch into current
git merge feature/my-feature

# Merge with no fast-forward (preserves merge commit)
git merge --no-ff feature/my-feature

# Rebase current branch onto main
git rebase main

# Interactive rebase (last 3 commits)
git rebase -i HEAD~3

# Abort a rebase in progress
git rebase --abort
```

### Resolving Merge Conflicts

```bash
# After conflict, edit the file to resolve, then:
git add conflicted-file.txt
git commit  # or git rebase --continue

# Use a merge tool
git mergetool

# Abort merge
git merge --abort
```

Conflict markers in files:
```
<<<<<<< HEAD
your changes
=======
their changes
>>>>>>> feature/branch
```

## Undoing Changes

```bash
# Unstage a file (keep changes in working tree)
git restore --staged file.txt

# Discard working tree changes (destructive)
git restore file.txt

# Undo last commit, keep changes staged
git reset --soft HEAD~1

# Undo last commit, keep changes unstaged
git reset HEAD~1

# Undo last commit, discard changes (destructive)
git reset --hard HEAD~1

# Revert a commit (safe, creates new commit)
git revert abc1234

# Cherry-pick a commit from another branch
git cherry-pick abc1234
```

## Stashing

```bash
# Stash current changes
git stash

# Stash with description
git stash push -m "WIP: feature work"

# List stashes
git stash list

# Apply most recent stash
git stash pop

# Apply specific stash
git stash apply stash@{2}

# Drop a stash
git stash drop stash@{0}
```

## Remote Operations

```bash
# Add remote
git remote add origin https://github.com/user/repo.git

# View remotes
git remote -v

# Fetch changes without merging
git fetch origin

# Pull (fetch + merge)
git pull origin main

# Push branch and set upstream
git push -u origin feature/my-feature

# Force push (use carefully)
git push --force-with-lease origin feature/my-feature
```

## Viewing History

```bash
# View log
git log --oneline
git log --oneline --graph --all  # visual branch graph

# Show changes in a commit
git show abc1234

# Show who changed each line
git blame file.txt

# Search commit messages
git log --grep="fix:"

# Find when a bug was introduced
git bisect start
git bisect bad                   # current commit is bad
git bisect good v1.0             # last known good tag
```

## Tags and Releases

```bash
# Create annotated tag
git tag -a v1.0.0 -m "Release version 1.0.0"

# Push tags
git push origin --tags

# List tags
git tag -l

# Delete tag
git tag -d v1.0.0
git push origin --delete v1.0.0
```

## .gitignore Patterns

```gitignore
# Ignore build output
dist/
build/
*.o
*.pyc

# Ignore dependencies
node_modules/
venv/
__pycache__/

# Ignore environment files
.env
.env.local

# Ignore OS files
.DS_Store
Thumbs.db

# Ignore IDE files
.vscode/
.idea/
*.swp
```

## Commit Message Convention

Follow [Conventional Commits](https://www.conventionalcommits.org/):

```
<type>(<scope>): <short description>

[optional body]

[optional footer]
```

Types: `feat`, `fix`, `docs`, `style`, `refactor`, `test`, `chore`, `perf`

Examples:
```
feat(auth): add OAuth2 login support
fix(api): handle null response from /users endpoint
docs: update README with setup instructions
chore: upgrade dependencies to latest versions
```

## Common Workflows

### Feature Branch Workflow
```bash
git checkout -b feature/new-feature main
# ... make changes ...
git add .
git commit -m "feat: implement new feature"
git push -u origin feature/new-feature
# Open pull request, get review, merge
```

### Hotfix Workflow
```bash
git checkout -b hotfix/critical-bug main
# ... fix bug ...
git commit -am "fix: resolve critical security issue"
git push -u origin hotfix/critical-bug
# Merge to main and tag release
```

## Quick Reference

| Task | Command |
|------|---------|
| New branch | `git switch -c branch-name` |
| Stage all | `git add .` |
| Commit | `git commit -m "message"` |
| Push new branch | `git push -u origin branch-name` |
| Undo last commit | `git reset HEAD~1` |
| Discard file changes | `git restore file.txt` |
| Stash changes | `git stash` |
| View log graph | `git log --oneline --graph --all` |
| Merge branch | `git merge branch-name` |
| Rebase onto main | `git rebase main` |
