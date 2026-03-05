# Phase 1: Intake & Planning — Detailed Reference

All examples use `{cloudId}`, `{projectKey}`, `{spaceId}`, and `{parentId}` as placeholders.

## Steps

1. **Classify** the request (feature, research, content, refactor, multi-component)

2. **Create Confluence plan page:**
   ```
   mcp__atlassian__createConfluencePage:
     cloudId: "{cloudId}"
     spaceId: "{spaceId}"
     parentId: "{parentId}"       # optional
     title: "Project Plan: {Request Title}"
     contentFormat: "markdown"
     body: <use Confluence Plan Page Template below>
   ```
   Verify: `getConfluencePage` with returned pageId — confirm title and content match.

3. **Create Jira Epic** with `[AI-PM]` prefix and link to Confluence page:
   ```
   mcp__atlassian__createJiraIssue:
     cloudId: "{cloudId}"
     projectKey: "{projectKey}"
     issueTypeName: "Epic"
     summary: "[AI-PM] {Request Title}"
     description: <use Epic Description Template below>
   ```

4. **Create child tickets** (one Task per workstream) with `parent: "{projectKey}-{epic-number}"`.

5. **Link dependencies** via `jiraWrite` action `createIssueLink` type `Blocks`.

6. **Update Confluence page** — replace "(pending)" placeholders with actual ticket keys and links, update Epic link in header, set status to IN PROGRESS, add progress log entries for ticket creation.
   Verify: `getConfluencePage` — confirm ticket keys appear in the workstreams table.

7. **Present plan to user** — Confluence page link + Epic key. This is the **only mandatory confirmation point**.

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
mcp__atlassian__getVisibleJiraProjects:
  cloudId: "{cloudId}"
```
Present the list and ask the user to pick one.

### Find user's Confluence space
```
mcp__atlassian__getConfluenceSpaces:
  cloudId: "{cloudId}"
  limit: 10
```
Present the list and ask the user to pick one. The response includes `id` (spaceId) and `key`.

### Find pages in a space (to offer as parent page)
```
mcp__atlassian__search:
  query: "space:{spaceKey} type:page"
```
