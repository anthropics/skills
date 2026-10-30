# Example Session: Feature Branch → New PR

## Invocation

```
/pr-narrative
```

## What the skill does

1. Detects no existing PR for current branch `feat/repo-aware-context`
2. Reads git log: 3 commits — "add context scan phase", "fix topic inference table", "update SKILL.md docs"
3. Reads git diff: changes to `SKILL.md`, `plugin.json`
4. Detects change type: Documentation + configuration (no frontend files)
5. Generates and creates PR immediately

## Generated PR

**Title:** `Add repo-aware context scan to research-and-grill skill`

**Description:**
```markdown
## Why
The skill previously asked generic Socratic questions with no awareness of what the user was actually building. Questions are now grounded in the user's real tech stack.

## What changed
- Added Phase 0 context scan that infers relevant files based on the research topic
- Built topic-to-file mapping table covering deployment, database, frontend, auth, and queue patterns
- Skill now blends 2–3 repo-grounded questions into the grill session naturally

## How to test
1. Open a Claude Code session inside a Rails project
2. Run `/research-and-grill database indexing`
3. Verify the summary mentions your stack and 2–3 questions reference your models or schema
```

## Output

```
✔ PR created: https://github.com/awesome-agent-skills/skills/pull/4
```

---

# Example Session: Update Existing PR

## Invocation

```
/pr-narrative 4
```

## What the skill does

1. Fetches PR #4 — title was "WIP: context stuff"
2. Re-reads git diff and commits (same branch, more commits added since)
3. Replaces title and description entirely

## Output

```
✔ PR #4 updated: https://github.com/awesome-agent-skills/skills/pull/4
```
