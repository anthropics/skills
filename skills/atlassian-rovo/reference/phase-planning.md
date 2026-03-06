# Phase 1: Intake & Planning — Detailed Reference

All examples use `{cloudId}`, `{projectKey}`, `{spaceId}`, and `{parentId}` as placeholders.

## Steps

1. **Classify** the request (feature, research, content, refactor, multi-component)

2. **Create Confluence plan page** (draft for review):
   ```
   atlassian:createConfluencePage:
     cloudId: "{cloudId}"
     spaceId: "{spaceId}"
     parentId: "{parentId}"       # optional
     title: "Project Plan: {Request Title}"
     contentFormat: "markdown"
     body: <use Confluence Plan Page Template below>
   ```
   Use "(pending)" placeholders for Epic and ticket keys — these don't exist yet.
   Verify: `getConfluencePage` with returned pageId — confirm title and content match.

3. **Present plan to user for review** — share the Confluence page link and summarize:
   - Objective and workstreams
   - Proposed team sizing
   - Dependencies
   - Ask for approval, changes, or additions
   **STOP HERE and wait for user approval before creating any Jira tickets.**

4. **After approval — Create Jira Epic** with `[AI-PM]` prefix and link to Confluence page:
   ```
   atlassian:createJiraIssue:
     cloudId: "{cloudId}"
     projectKey: "{projectKey}"
     issueTypeName: "Epic"
     summary: "[AI-PM] {Request Title}"
     description: <use Epic Description Template below>
     assignee_account_id: "{currentUserAccountId}"
   ```

5. **Create child tickets** (one Task per workstream) with `parent: "{projectKey}-{epic-number}"` and `assignee_account_id: "{currentUserAccountId}"`.

6. **Link dependencies** via `jiraWrite` action `createIssueLink` type `Blocks`.

7. **Update Confluence page** — replace "(pending)" placeholders with actual ticket keys and links, update Epic link in header, set status to IN PROGRESS, add progress log entries for ticket creation.
   Verify: `getConfluencePage` — confirm ticket keys appear in the workstreams table.

## Confluence Plan Page Template

```markdown
# Project Plan: {Request Title}

## Status: PLANNING | IN PROGRESS | REVIEW | COMPLETED
**Created:** {date}
**Last Updated:** {date}
**Epic:** [{projectKey}-{N}]({cloudId}/browse/{projectKey}-{N})
**Request:** {original user request, verbatim}

## Team Composition
| Role | Agent Name | Workstream |
|------|-----------|------------|
| Lead/Orchestrator | orchestrator | Coordination, Jira updates, plan updates |
| {role} | {name} | {workstream description} |

## Workstreams & Jira Tickets
| # | Workstream | Jira Ticket | Status | Agent |
|---|-----------|-------------|--------|-------|
| 1 | {description} | [{projectKey}-XX]({cloudId}/browse/{projectKey}-XX) | To Do | {agent} |

## Architecture / Approach
{High-level approach, key decisions, constraints}

## Dependencies
{Which workstreams depend on others, e.g. "Workstream 2 blocked by Workstream 1"}

## Progress Log
| Timestamp | Update |
|-----------|--------|
| {datetime} | Project plan created. Awaiting user review. |

## Deliverables
{What will be produced — updated as work completes}
```

## Epic Description Template

```markdown
**Plan:** [Confluence Plan Page]({confluence-page-url})
**Status:** {PLANNING | IN PROGRESS | COMPLETED}

## Workstreams
| # | Workstream | Ticket | Status |
|---|-----------|--------|--------|
| 1 | {description} | {projectKey}-XX | To Do |

## Progress Log
| Time | Update |
|------|--------|
| {datetime} | Project plan created. |
```

## Discovery Patterns

### Find user's Jira project
```
atlassian:getVisibleJiraProjects:
  cloudId: "{cloudId}"
```
Present the list and ask the user to pick one.

### Find user's Confluence space
```
atlassian:getConfluenceSpaces:
  cloudId: "{cloudId}"
  limit: 10
```
Present the list and ask the user to pick one. The response includes `id` (spaceId) and `key`.

### Find pages in a space (to offer as parent page)
```
atlassian:search:
  query: "space:{spaceKey} type:page"
```
