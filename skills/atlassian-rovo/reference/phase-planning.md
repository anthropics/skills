# Phase 1: Intake & Planning — Detailed Reference

All examples use `{site}`, `{projectKey}`, `{spaceId}`, and `{parentId}` as placeholders.
Credentials come from environment variables: `$ATLASSIAN_EMAIL`, `$ATLASSIAN_API_TOKEN`.

## Steps

1. **Classify** the request (feature, research, content, refactor, multi-component)

2. **Create Confluence plan page:**
   ```
   curl -s -X POST "https://{site}/wiki/api/v2/pages" \
     -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN" \
     -H "Content-Type: application/json" \
     -d '{"spaceId": "{spaceId}", "parentId": "{parentId}", "status": "current", "title": "Project Plan: {Request Title}", "body": {"representation": "storage", "value": "<use Confluence Plan Page Template below>"}}'
   ```
   Verify: `curl -s "https://{site}/wiki/api/v2/pages/{pageId}?body-format=storage" -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN"` — confirm title and content match.

3. **Create Jira Epic** with `[AI-PM]` prefix and link to Confluence page:
   ```
   acli jira workitem create --project {projectKey} --type Epic --summary "[AI-PM] {Request Title}" --description "<use Epic Description Template below>" --json
   ```

4. **Create child tickets** (one Task per workstream):
   ```
   acli jira workitem create --project {projectKey} --type Task --summary "{workstream title}" --parent {projectKey}-{epic-number} --json
   ```

5. **Link dependencies** via `jiraWrite` action `createIssueLink` type `Blocks`.

6. **Update Confluence page** — replace "(pending)" placeholders with actual ticket keys and links, update Epic link in header, set status to IN PROGRESS, add progress log entries for ticket creation.
   Verify: `curl -s "https://{site}/wiki/api/v2/pages/{pageId}?body-format=storage" -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN"` — confirm ticket keys appear in the workstreams table.

7. **Present plan to user** — Confluence page link + Epic key. This is the **only mandatory confirmation point**.

## Confluence Plan Page Template

```markdown
# Project Plan: {Request Title}

## Status: PLANNING | IN PROGRESS | REVIEW | COMPLETED
**Created:** {date}
**Last Updated:** {date}
**Epic:** [{projectKey}-{N}](https://{site}/browse/{projectKey}-{N})
**Request:** {original user request, verbatim}

## Team Composition
| Role | Agent Name | Workstream |
|------|-----------|------------|
| Lead/Orchestrator | orchestrator | Coordination, Jira updates, plan updates |
| {role} | {name} | {workstream description} |

## Workstreams & Jira Tickets
| # | Workstream | Jira Ticket | Status | Agent |
|---|-----------|-------------|--------|-------|
| 1 | {description} | [{projectKey}-XX](https://{site}/browse/{projectKey}-XX) | To Do | {agent} |

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
acli jira project list --json
```
Present the list and ask the user to pick one.

### Find user's Confluence space
```
curl -s "https://{site}/wiki/api/v2/spaces?limit=10" \
  -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN"
```
Present the list and ask the user to pick one. The response includes `id` (spaceId) and `key`.

### Find pages in a space (to offer as parent page)
```
curl -s "https://{site}/wiki/rest/api/content/search?cql=space={spaceKey}+AND+type=page" \
  -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN"
```
