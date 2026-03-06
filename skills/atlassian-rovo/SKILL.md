---
name: atlassian-rovo
description: >
  Manages Atlassian Jira and Confluence via the Rovo MCP Server. Handles
  MCP setup, OAuth authentication, and troubleshooting. Runs agentic
  project management: Confluence plans, Jira Epics with child tickets,
  agent team coordination, and resuming interrupted work from Jira state.
  Supports uploading images/attachments to Confluence pages via REST API.
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
| **User Account ID** | `atlassian:atlassianUserInfo` | `{currentUserAccountId}` |
| **API Token** | `.env` file (`CONFLUENCE_API_TOKEN`) or ask user. Required only for image upload — see [image-upload.md](reference/image-upload.md) | `{apiToken}` |

Always ask the user which project/space to use. Never assume defaults.
Use `maxResults: 10` or `limit: 10` for all search operations.

---

## MCP Setup & Authentication

For full setup, OAuth flow, and troubleshooting, see [mcp-setup.md](reference/mcp-setup.md).

Quick config for Claude Code — single `.mcp.json` entry covers both Jira and Confluence:

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

For other agents (Cursor, Cline, Windsurf, etc.), see the agent-specific instructions in [mcp-setup.md](reference/mcp-setup.md).

---

## Agentic Project Management Workflow

Full lifecycle project management using Jira + Confluence.

### Execution Modes

This workflow supports two modes:

- **Multi-Agent Mode** (Claude Code with Agent Teams): Parallel execution with TeamCreate/TaskCreate orchestration. Requires `CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1` in `~/.claude/settings.json`.
- **Single-Agent Mode** (all agents): Sequential execution — one workstream at a time. Same Jira tracking and Confluence updates, no multi-agent dependencies.

### Prerequisites

- Atlassian MCP connected with both Jira and Confluence tools
- For multi-agent mode: Claude Code with `CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`

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

- **Transition IDs vary** — MUST call `getTransitionsForJiraIssue` before `transitionJiraIssue`
- **`[AI-PM]` prefix** on all managed Epics for auto-detection during resume
- **One writer per resource** — only one agent updates a given page/issue at a time
- **maxResults: 10** on all JQL/CQL searches
- **ALL tickets MUST be transitioned to In Progress when work starts** — whether done by teammates or the orchestrator directly. Use two-step protocol: `getTransitionsForJiraIssue` then `transitionJiraIssue`.
- **ALL tickets MUST be assigned** to the current user (`editJiraIssue` with `{"assignee": {"accountId": "{currentUserAccountId}"}}`) when moving to In Progress.
- Teammates MUST publish findings as **child pages** of the plan page (using `parentId`)
- **Epic linking:** `createJiraIssue` with `parentKey` may silently fail to set the Epic parent. Always verify with `getJiraIssue`, and if missing, fix with `editJiraIssue` using `{"parent": {"key": "{epicKey}"}}`.
- `updateConfluencePage` replaces the entire body — always `getConfluencePage` first, then append
