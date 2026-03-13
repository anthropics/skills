---
name: atlassian-rovo
description: >
  Manages Atlassian Jira and Confluence via ACLI (Jira CLI) and the
  Confluence REST API (curl). Handles setup, API token authentication,
  and troubleshooting. Runs agentic project management: Confluence plans,
  Jira Epics with child tickets, agent team coordination, and resuming
  interrupted work from Jira state. Supports uploading images/attachments
  to Confluence pages via REST API. Reads and writes Confluence page
  comments (footer, inline, reply threads). Creates git branches linked
  to Jira tickets (GitHub and Bitbucket). Use this skill whenever the
  user mentions Jira, Confluence, Atlassian, tickets, epics, sprints,
  project boards, wiki pages, or Confluence spaces. Also trigger when
  the user wants to plan a project, break work into tasks, track progress,
  resume interrupted work, upload images to wiki pages, manage comments
  on Confluence pages, or create git branches linked to tickets — even
  if they don't mention Atlassian by name.
argument-hint: "[describe project | resume PROJ-123 | setup | troubleshoot]"
---

# Atlassian ACLI + REST API Automation

## Configuration Discovery

Before starting any workflow, gather these from the user or discover via CLI:

| Setting | How to get it | Store as |
|---------|--------------|----------|
| **Site URL** | Ask user for `*.atlassian.net` URL | `{site}` |
| **Jira Project Key** | Ask user, or `acli jira project list` | `{projectKey}` |
| **Confluence Space** | Ask user, or query REST API | `{spaceKey}` |
| **Parent Page** | Ask user, or use space root | `{parentId}` |

Always ask the user which project/space to use. Never assume defaults.
Use `--limit 10` for all Jira list operations and `limit=10` for Confluence REST API calls.

---

## Setup & Authentication

For full setup, API token generation, and troubleshooting, see [setup.md](reference/setup.md).

Quick config — add a `.env` file to your project root:

```bash
ATLASSIAN_EMAIL="you@example.com"
ATLASSIAN_API_TOKEN="your-api-token-here"
ATLASSIAN_SITE="https://yoursite.atlassian.net"
```

Install ACLI and authenticate:

```bash
brew tap atlassian/homebrew-acli && brew install acli
source .env
acli jira auth login \
  --site "$ATLASSIAN_SITE" \
  --email "$ATLASSIAN_EMAIL" \
  --token < <(echo "$ATLASSIAN_API_TOKEN")
```

For Confluence, use the REST API via curl with basic auth:

```bash
curl -s -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN" \
  "$ATLASSIAN_SITE/wiki/rest/api/content" ...
```

See `reference/atlassian-helpers.sh` for convenience shell functions.

For image upload configuration, see [image-upload.md](reference/image-upload.md).
For git branch integration (GitHub/Bitbucket), see [git-integration.md](reference/git-integration.md).
For Confluence comment operations, see [confluence-comments.md](reference/confluence-comments.md).

---

## Agentic Project Management Workflow

Full lifecycle project management using Jira + Confluence.

### Execution Modes

This workflow supports two modes:

- **Multi-Agent Mode** (Claude Code with Agent Teams): Parallel execution with TeamCreate/TaskCreate orchestration. Requires `CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1` in `~/.claude/settings.json`.
- **Single-Agent Mode** (all agents): Sequential execution — one workstream at a time. Same Jira tracking and Confluence updates, no multi-agent dependencies.

### Prerequisites

- ACLI installed and authenticated (Jira)
- API token configured in `.env` (Confluence REST API)
- For multi-agent mode: Claude Code with `CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`

### The 4-Phase Cycle

```
Phase 1: INTAKE   -> User describes request -> Confluence plan + Jira Epic
Phase 2: EXECUTE  -> Agent team works tickets with Jira tracking
Phase 3: RESUME   -> New session resumes from Jira state (fully autonomous)
Phase 4: COMPLETE -> All tickets Done -> Epic closed -> summary delivered
```

### Phase 1: Intake & Planning

Classify the request, create Confluence plan page, Jira Epic with `[AI-PM]` prefix, child tickets per workstream, link dependencies, then present plan to user for confirmation.

See [phase-planning.md](reference/phase-planning.md) for step-by-step details and templates.

### Phase 2: Execution

**Multi-agent mode:** Create agent team, map tickets to tasks with dependency tracking, spawn teammates with standard prompt. Orchestrator monitors progress and updates Confluence plan page.
See [phase-execution.md](reference/phase-execution.md) for teammate prompt template and orchestrator duties.

**Single-agent mode:** Work each ticket sequentially, respecting dependency order. Track progress via Jira transitions and Confluence updates.
See [phase-execution-single.md](reference/phase-execution-single.md) for the sequential workflow.

Both modes share common protocols for transitions, branch creation, and publishing.
See [common-patterns.md](reference/common-patterns.md) for these shared procedures.

### Phase 3: Resume

Auto-detect open `[AI-PM]` Epics, read Confluence plan, query incomplete tickets, classify state.

**Multi-agent mode:** Spin up right-sized team for remaining work.
See [phase-resume.md](reference/phase-resume.md) for JQL patterns and resume protocol.

**Single-agent mode:** Pick up the next incomplete ticket and continue sequentially.
See [phase-resume-single.md](reference/phase-resume-single.md) for the sequential resume protocol.

### Phase 4: Completion

Update Confluence page status, transition Epic to Done, add final summary comment, report deliverables to user.

See [phase-completion.md](reference/phase-completion.md) for completion checklist.

### Team Sizing (Multi-Agent Mode)

| Request Type | Team Size | Roles |
|-------------|-----------|-------|
| Small change | 2 | lead + implementer |
| Feature dev | 3-4 | lead + backend + frontend + (tester) |
| Research | 3 | lead + 2 researchers |
| Content | 3 | lead + writer + reviewer |
| Multi-component | 4-5 | lead + 1 per component |

One ticket per teammate. Lead coordinates only (no workstream tasks). Min team = 2.

### Key Constraints

- **`[AI-PM]` prefix** on all managed Epics — the resume phase uses JQL `summary ~ '[AI-PM]'` to auto-detect managed Epics.
- **One writer per resource** — Confluence uses optimistic locking with version numbers. Concurrent writes cause version conflicts and data loss. Only one agent should update a given page/issue at a time.
- **`--limit 10`** on all Jira list operations; `limit=10` on all Confluence REST calls — larger result sets consume excessive tokens.
- **Transition to In Progress when work starts** — this signals to other agents (and the resume phase) that a ticket is actively being worked.
- **Assign tickets when starting work** — use `acli jira workitem edit --key {key} --assignee "@me"`. Unassigned tickets look abandoned during resume.
- **Publish findings as child pages** of the plan page (using `parentId`) — keeps all deliverables organized under one parent.
- **GET before PUT for Confluence** — the REST API PUT replaces the entire body. Always read the current version first, then PUT with incremented version number. Also check for inline/footer comments before updating — users leave review feedback as comments.
- **JQL `!=` workaround** — ACLI escapes `!` in JQL. Use `NOT IN (Done)` instead of `!= Done`.
- **Confluence search uses v1 API** — CQL search for pages must use `/wiki/rest/api/content/search`, not v2 `/search`.
- **Comment replies use v1 API** — creating threaded replies requires `POST /wiki/rest/api/content` with `ancestors` array. The v2 children endpoint returns 405. See [confluence-comments.md](reference/confluence-comments.md).
