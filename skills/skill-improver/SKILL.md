---
name: skill-improver
description: >
  Manages the full lifecycle of improving existing Claude Code skills —
  from feature request through implementation, automated E2E testing by
  a fresh agent, and deployment. Use this skill whenever the user wants
  to improve, update, fix, or add features to an existing skill. Also
  trigger when the user says "improve skill", "update skill", "fix the
  X skill", "add Y to the Z skill", "skill needs updating", or mentions
  wanting to change how a skill works. This skill ensures changes are
  always validated by an independent test agent before merging, preventing
  the "builder blind spot" where the author's context masks doc gaps.
  Requires Claude Code (uses Agent tool for subagent spawning and gh CLI for PRs).
argument-hint: "[skill-name] [describe the change]"
---

# Skill Improver

Automates the process of improving an existing skill with built-in quality
gates. Every change is validated by a fresh agent that follows the docs
cold — if it can't complete the workflow, the docs aren't good enough.

## Core Principle

**The builder and tester must never be the same agent.** The builder has
implicit context about what the docs *mean*, which masks gaps in what
they actually *say*. A fresh test agent reading the docs cold catches
exactly the issues a real user would hit.

---

## Configuration

On first use, ask the user for these values. Save them to a memory file
named `skill_improver_config.md` in the project's auto-memory directory
(the same directory as `MEMORY.md`) using this exact format:

```markdown
---
name: skill-improver-config
description: Configuration for skill-improver workflow — repo URL, paths, credentials
type: reference
---

repo_url: https://github.com/user/skills.git
repo_subdir: skills
ssot_path: /absolute/path/to/.agents/skills
env_path: /absolute/path/to/.env
```

Add a pointer to this file in `MEMORY.md`.

**On subsequent runs:** Read `skill_improver_config.md` from the memory
directory before starting. If it exists, use those values without asking.
If the user's `CLAUDE.md` already specifies these values, use those instead.

| Setting | What to ask | Notes |
|---------|-------------|-------|
| `{repo-url}` | "What's the Git repo URL for your skills?" | Must be a GitHub repo (for PR workflow) |
| `{repo-subdir}` | "What subdirectory are skills in? (or empty if repo root)" | No trailing slash. e.g., `skills` not `skills/` |
| `{ssot-path}` | "Where does Claude Code load skills from locally?" | Absolute path. e.g., `/Users/me/.agents/skills` |
| `{env-path}` | "Where's your `.env` with credentials for testing?" | The `.env` should contain whatever credentials the target skill needs |

The dev clone always goes to `/tmp/skills-dev`.

> **Note:** This workflow assumes GitHub and `gh` CLI for PRs. For other
> Git hosts, adapt Step 6 to your platform's CLI or web UI.

---

## Workflow

### Step 0: Search Memory

Before starting, check for past issues with the target skill.

If the `claude-mem` plugin is available, use the Skill tool:
```
Skill tool: skill: "claude-mem:mem-search", args: "issues with {skill-name} skill"
```

If `claude-mem` is not available, skip this step — it's helpful but not required.

Also read the skill's current state from the local SSOT:
```
Read {ssot-path}/{skill-name}/SKILL.md and its reference/ files
```

### Step 1: Understand Intent

Confirm the target skill by listing `{ssot-path}/` and matching the user's
request to the correct **directory name** (not the frontmatter `name` field,
which may differ). For example, if the user says "improve the atlassian skill",
check if the directory is `atlassian-rovo`.

Then read the actual skill files to understand:
- What the skill currently does
- How the requested change fits into the existing structure
- What files need to change

### Step 2: Plan

**Rule of thumb:** If the change affects behavior (commands, workflow steps,
auth, or config), present a plan. If it only affects documentation clarity
without changing what the user does, fast-track it.

**Plan** (significant changes — new features, workflow changes, multi-file edits):
- What files will change and how
- Any new files needed
- Potential risks or breaking changes
- Wait for user sign-off before proceeding

**Fast-track** (skip straight to Step 3):
- Typo fixes, broken links, clarification notes, single-command corrections

### Step 3: Build

Clone the repo and work on a feature branch:

```bash
# Clone (or pull if already cloned)
if [ -d "/tmp/skills-dev" ]; then
  cd /tmp/skills-dev && git checkout main && git pull origin main --ff-only
else
  git clone {repo-url} /tmp/skills-dev
fi

# Create feature branch (kebab-case, max ~30 chars for the description)
cd /tmp/skills-dev
BRANCH="fix/{skill-name}-{short-description}"
git checkout -b "$BRANCH" 2>/dev/null || git checkout "$BRANCH"
```

The target skill lives at `/tmp/skills-dev/{repo-subdir}/{skill-name}/`.
If `{repo-subdir}` is empty, the skill is at `/tmp/skills-dev/{skill-name}/`.

Make the changes. Commit with a descriptive message.

**Never commit directly to main.** Always use a feature branch so the PR
in Step 6 has a clean diff.

### Step 4: Test with Fresh Agent

Use the `Agent` tool to spawn a test agent. Build the prompt by reading
[reference/test-agent-prompt.md](reference/test-agent-prompt.md) and filling
in all `{placeholders}` with actual values.

**How to determine what the test agent needs:** Read the target skill's
`SKILL.md` to find what external services, URLs, project keys, or env vars
it requires. Include these in the Environment section of the prompt.

**Spawn the agent using Claude Code's Agent tool:**
```
Agent tool:
  name: "skill-e2e-tester"
  model: "sonnet"
  mode: "bypassPermissions"
  prompt: <the filled-in prompt from the template>
```

> This skill requires **Claude Code** (Anthropic's CLI agent). The Agent tool,
> subagent spawning, and `gh` CLI integration are Claude Code features. This
> skill does not work in Claude.ai, Cursor, or other environments.

Key rules for the test agent:
- It must NOT receive any context from the builder about what changed or why
- It gets the skill docs and credentials, nothing else
- It should attempt the full workflow the skill describes
- It must NOT execute irreversible or destructive operations (deletes, drops,
  sends to external users, merges to production). If the skill requires these,
  the test agent should document what it *would* have done and mark it as
  "untested — destructive operation"
- It writes its findings to `/tmp/skill-improver-test-results.md` (outside
  the git repo to avoid accidental commits)

### Step 5: Iterate (max 3 rounds)

Read the test agent's results from `/tmp/skill-improver-test-results.md`.

If issues were found:

1. Categorize by severity (High / Medium / Low)
2. Fix the issues in the same feature branch
3. Commit the fixes
4. Spawn a **new** test agent (Step 4 again) — don't reuse the old one
5. Repeat until clean or 3 rounds reached

**If still failing after 3 rounds:** Stop and surface the remaining issues
to the user. Something structural is likely wrong that needs human judgment.

### Step 6: Create PR and Merge

Once the test agent reports no issues (or only Low severity):

```bash
cd /tmp/skills-dev
git push -u origin fix/{skill-name}-{short-description}
```

Create the PR:
```bash
gh pr create \
  --title "fix({skill-name}): {short description}" \
  --body "$(cat <<'EOF'
## Summary
{what changed and why}

## Test Results
- Test iterations: {N}
- Final result: All tests passed / N issues remaining (Low severity)

## Test Artifacts
{List any external artifacts created during testing:}
- {e.g., Jira tickets, Confluence pages, files — or "None"}

🤖 Validated by independent test agent (Sonnet)
EOF
)"
```

For **fast-track PRs** (no test agent), use a simpler body:
```bash
gh pr create \
  --title "fix({skill-name}): {short description}" \
  --body "Fast-track fix: {what changed}. No test agent needed (typo/clarification)."
```

**Show the PR URL to the user and ask if they want to review before merging.**
If the user approves (or says to go ahead), merge:
```bash
gh pr merge --merge --delete-branch
```

### Step 7: Sync and Clean Up

After merging, sync the local SSOT and clean up:

```bash
# Pull latest
cd /tmp/skills-dev
git checkout main && git pull origin main --ff-only

# Sync just this skill to Claude Code's SSOT directory
rsync -av --delete \
  /tmp/skills-dev/{repo-subdir}/{skill-name}/ \
  {ssot-path}/{skill-name}/
```

> **Warning:** `--delete` removes files in `{ssot-path}/{skill-name}/` that
> aren't in the repo. If the user has local-only files there, they will be
> deleted. If unsure, do a dry-run first: `rsync -avn --delete ... | grep deleting`

```bash
# Clean up
rm -rf /tmp/skills-dev
rm -f /tmp/skill-improver-test-results.md
```

Confirm to the user: "Skill updated and synced. Changes will be active
in your next Claude Code session."

---

## When to Skip the Test Agent

Not every change needs a full E2E test. Use the rule from Step 2:

| Change type | Test agent? |
|-------------|-------------|
| New feature or workflow | Yes, always |
| Multi-file refactor | Yes |
| Command syntax changes | Yes |
| Setup/auth instructions | Yes |
| Adding a clarification note | No — fast-track |
| Fixing a typo | No — fast-track |
| Updating a URL | No — fast-track |

When skipping, go directly from Step 3 to Step 6 (use the fast-track PR template).

---

## Error Handling

**Git clone fails:** Check if the repo URL is correct. Ask the user.

**Branch already exists:** The Step 3 command handles this with a fallback
from `checkout -b` to `checkout`.

**Test agent can't authenticate:** Verify `{env-path}` exists and contains
the credentials the target skill requires. The test agent should follow the
skill's own setup docs — if they don't document required env vars, that's
a doc gap to fix.

**PR creation fails:** Check `gh auth status`. The user may need to run
`gh auth login` first.

**Merge conflicts:** If main has diverged, rebase the feature branch:
```bash
git fetch origin main
git rebase origin/main
```

---

## Key Constraints

- **Builder and tester are always separate agents** — this is non-negotiable
- **Feature branches only** — never commit directly to main
- **Max 3 test iterations** — escalate to user after that
- **Test agent uses Sonnet** — cheaper, and a "simpler reader" is a feature
- **No destructive operations in tests** — test agent must not delete, send, or merge
- **User approves merge** — always show PR URL and ask before merging
- **Clean up after merge** — remove `/tmp/skills-dev` and test results
- **Record test artifacts** — any external resources created during testing
  go in the PR description so they can be cleaned up later
