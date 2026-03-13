# Phase 2: Execution (Single-Agent Mode) — Detailed Reference

Sequential execution for agents without multi-agent orchestration (Cursor, Cline, Windsurf, etc.).
Same Jira tracking and Confluence updates as multi-agent mode, but one ticket at a time.

All examples use `{site}`, `{projectKey}`, `{spaceId}`, and `{parentId}` as placeholders.
Credentials come from environment variables: `$ATLASSIAN_EMAIL`, `$ATLASSIAN_API_TOKEN`.

## Workflow

Work each child ticket sequentially, respecting dependency order (blocked tickets last).

For each ticket:

### 1. Start the Ticket

Assign the ticket to yourself:
```
acli jira workitem edit --key {projectKey}-{N} --assignee "@me" --json
```

Transition to In Progress:
```
acli jira workitem transition --key {projectKey}-{N} --status "In Progress" --yes
```

### 2. Do the Work

Execute the workstream as described in the ticket.

### 3. Publish Findings

Create a Confluence child page under the plan page:
```
curl -s -X POST "https://{site}/wiki/api/v2/pages" \
  -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN" \
  -H "Content-Type: application/json" \
  -d '{"spaceId": "{spaceId}", "parentId": "{confluence-page-id}", "status": "current", "title": "{projectKey}-{N}: {workstream title}", "body": {"representation": "storage", "value": "<findings in HTML storage format>"}}'
```

### 4. Complete the Ticket

Add a comment with summary + link to Confluence child page:
```
acli jira workitem comment create --key {projectKey}-{N} --body "## Summary\n{brief summary}\n\nFindings: {confluence-child-page-url}"
```

Transition to Done:
```
acli jira workitem transition --key {projectKey}-{N} --status "Done" --yes
```

### 5. Update Progress

Read the Confluence plan page:
```
curl -s "https://{site}/wiki/api/v2/pages/{plan-page-id}?body-format=storage" \
  -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN"
```
Then update — change the ticket's status in the workstreams table, add a progress log entry:
```
curl -s -X PUT "https://{site}/wiki/api/v2/pages/{plan-page-id}" \
  -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN" \
  -H "Content-Type: application/json" \
  -d '{"id": "{plan-page-id}", "status": "current", "title": "...", "body": {"representation": "storage", "value": "<updated page with ticket marked Done + progress log entry>"}, "version": {"number": N, "message": "{projectKey}-{N} completed"}}'
```

### 6. Next Ticket

Move to the next ticket in dependency order. Repeat steps 1-5.

## Dependency Ordering

Query all child tickets and sort by dependencies:
```
acli jira workitem search --jql "parent = {projectKey}-{N} ORDER BY rank ASC" --json --limit 10
```

Work tickets in this order:
1. Tickets with no blockers (can start immediately)
2. Tickets blocked by completed tickets (blockers resolved)
3. Skip tickets whose blockers are still incomplete (come back later)

## Key Rules

- **Always transition to In Progress** before starting work (not just Done at the end)
- **Always publish findings as child pages** of the plan page
- **Always update the plan page** after completing each ticket
- **Respect dependency order** — don't start a blocked ticket until its blocker is Done
