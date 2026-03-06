---
name: atlassian-rovo
description: >
  Manages Atlassian Jira and Confluence via the Rovo MCP Server. Handles
  MCP setup, OAuth authentication, and troubleshooting. Runs agentic
  project management: Confluence plans, Jira Epics with child tickets,
  agent team coordination, and resuming interrupted work from Jira state.
  Supports uploading images/attachments to Confluence pages via REST API.
  Reads and writes Confluence page comments (footer, inline, reply threads).
  Creates git branches linked to Jira tickets (GitHub and Bitbucket).
  Use this skill whenever the user mentions Jira, Confluence, Atlassian,
  tickets, epics, sprints, project boards, wiki pages, or Confluence spaces.
  Also trigger when the user wants to plan a project, break work into tasks,
  track progress, resume interrupted work, upload images to wiki pages,
  manage comments on Confluence pages, or create git branches linked to
  tickets — even if they don't mention Atlassian by name.
argument-hint: "[describe project | resume PROJ-123 | setup | troubleshoot]"
---

# Atlassian Rovo MCP Automation

## Getting Started

Before starting any workflow, gather cloudId, projectKey, spaceId, and user info.
See [mcp-setup.md](reference/mcp-setup.md) for configuration discovery, MCP setup, OAuth flow, and troubleshooting.

For image upload configuration, see [image-upload.md](reference/image-upload.md).
For git branch integration (GitHub/Bitbucket), see [git-integration.md](reference/git-integration.md).
For Confluence comment operations, see [confluence-comments.md](reference/confluence-comments.md).

Always ask the user which project/space to use. Never assume defaults.

---

## Agentic Project Management Workflow

Full lifecycle project management using Jira + Confluence.

### Execution Modes

- **Multi-Agent Mode** (Claude Code with Agent Teams): Parallel execution with TeamCreate/TaskCreate orchestration. Requires `CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1` in `~/.claude/settings.json`.
- **Single-Agent Mode** (all agents): Sequential execution — one workstream at a time. Same Jira tracking and Confluence updates, no multi-agent dependencies.

### The 4-Phase Cycle

```
Phase 1: INTAKE   -> User describes request -> Confluence plan + Jira Epic
Phase 2: EXECUTE  -> Agent team works tickets with Jira tracking
Phase 3: RESUME   -> New session resumes from Jira state (fully autonomous)
Phase 4: COMPLETE -> All tickets Done -> Epic closed -> summary delivered
```

### Phase 1: Intake & Planning

Classify the request, create Confluence plan page as a draft, then **present to user for review before creating any Jira tickets**. Only after approval: create Jira Epic with `[AI-PM]` prefix, child tickets per workstream, and link dependencies.

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
**Single-agent mode:** Pick up the next incomplete ticket and continue sequentially.

See [phase-resume.md](reference/phase-resume.md) for JQL patterns and resume protocol (covers both modes).

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

- **Transition IDs vary by project** — each Jira project can have different workflow configurations, so hardcoding IDs will break across projects. Always call `getTransitionsForJiraIssue` before `transitionJiraIssue`.
- **`[AI-PM]` prefix on all managed Epics** — the resume phase uses JQL `summary ~ '[AI-PM]'` to auto-detect managed Epics. Without this prefix, resume cannot find prior work.
- **One writer per resource** — Confluence uses optimistic locking with version numbers. Concurrent writes cause version conflicts and data loss. Only one agent should update a given page/issue at a time.
- **`maxResults: 10` on all JQL/CQL searches** — larger result sets consume excessive tokens and slow down processing. 10 results is sufficient for most workflows.
- **Transition to In Progress when work starts** — this signals to other agents (and the resume phase) that a ticket is actively being worked. Use two-step protocol: `getTransitionsForJiraIssue` then `transitionJiraIssue`.
- **Assign tickets when starting work** — `editJiraIssue` with `{"assignee": {"accountId": "{currentUserAccountId}"}}`. Unassigned In Progress tickets look abandoned during resume.
- **Publish findings as child pages** of the plan page (using `parentId`) — keeps all deliverables organized under one parent for easy navigation and resume context.
- **Verify Epic linking** — `createJiraIssue` with `parentKey` may silently fail to set the Epic parent. Always verify with `getJiraIssue`, and if missing, fix with `editJiraIssue` using `{"parent": {"key": "{epicKey}"}}`.
- **`updateConfluencePage` replaces the entire body** — always `getConfluencePage` first to read current content, then append changes. Skipping the read will overwrite existing content.
