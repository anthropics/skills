---
name: atlassian-rovo
description: >
  Manages Atlassian Jira and Confluence via the Rovo MCP Server. Handles
  MCP setup, OAuth authentication, and troubleshooting. Runs agentic
  project management: Confluence plans, Jira Epics with child tickets,
  agent team coordination, and resuming interrupted work from Jira state.
  Use when working with Atlassian, planning projects, managing Jira tasks,
  or running agent team workflows.
argument-hint: "[describe project | resume PROJ-123 | setup | troubleshoot]"
---

# Atlassian Rovo MCP Automation

## Configuration Discovery

Before starting any workflow, gather these from the user or discover via MCP tools:

| Setting | How to get it | Store as |
|---------|--------------|----------|
| **Cloud Site** | Ask user for `*.atlassian.net` URL | `{cloudId}` |
| **Jira Project Key** | Ask user, or `getVisibleJiraProjects` | `{projectKey}` |
| **Confluence Space** | Ask user, or `getConfluenceSpaces` | `{spaceId}` |
| **Parent Page** | Ask user, or use space root | `{parentId}` |
| **User Account ID** | `mcp__atlassian__atlassianUserInfo` | `{currentUserAccountId}` |

Always ask the user which project/space to use. Never assume defaults.
Use `maxResults: 10` or `limit: 10` for all search operations.

---

## MCP Setup & Authentication

For full setup, OAuth flow, and troubleshooting, see [mcp-setup.md](reference/mcp-setup.md).

Quick config — single `.mcp.json` entry covers both Jira and Confluence:

```json
{
  "mcpServers": {
    "atlassian": {
      "command": "npx",
      "args": ["-y", "mcp-remote@latest", "https://mcp.atlassian.com/v1/mcp"]
    }
  }
}
```

Use `/mcp` endpoint (not `/sse` — deprecated after June 2026).

---

## Agentic Project Management Workflow

Full lifecycle project management using Agent Teams + Jira + Confluence.

### Prerequisites

- `CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1` in `~/.claude/settings.json`
- Atlassian MCP connected with both Jira and Confluence tools

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

Create agent team, map tickets to tasks with dependency tracking, spawn teammates with standard prompt. Orchestrator monitors progress and updates Confluence plan page.

See [phase-execution.md](reference/phase-execution.md) for teammate prompt template and orchestrator duties.

### Phase 3: Resume

Auto-detect open `[AI-PM]` Epics, read Confluence plan, query incomplete tickets, classify state, spin up right-sized team for remaining work. No user confirmation required.

See [phase-resume.md](reference/phase-resume.md) for JQL patterns and resume protocol.

### Phase 4: Completion

Update Confluence page status, transition Epic to Done, add final summary comment, shutdown teammates, report deliverables to user.

See [phase-completion.md](reference/phase-completion.md) for completion checklist.

### Team Sizing

| Request Type | Team Size | Roles |
|-------------|-----------|-------|
| Small change | 2 | lead + implementer |
| Feature dev | 3-4 | lead + backend + frontend + (tester) |
| Research | 3 | lead + 2 researchers |
| Content | 3 | lead + writer + reviewer |
| Multi-component | 4-5 | lead + 1 per component |

One ticket per teammate. Lead coordinates only (no workstream tasks). Min team = 2.

### Key Constraints

- **Transition IDs vary** — MUST call `getTransitionsForJiraIssue` before `transitionJiraIssue`
- **`[AI-PM]` prefix** on all managed Epics for auto-detection during resume
- **One writer per resource** — only one agent updates a given page/issue at a time
- **maxResults: 10** on all JQL/CQL searches
- Teammates MUST transition to **In Progress** when starting (not just Done at end)
- Teammates MUST publish findings as **child pages** of the plan page (using `parentId`)
- `updateConfluencePage` replaces the entire body — always `getConfluencePage` first, then append
