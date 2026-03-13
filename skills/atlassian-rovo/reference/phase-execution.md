# Phase 2: Execution — Detailed Reference

All examples use `{site}`, `{projectKey}`, `{spaceId}`, and `{parentId}` as placeholders.
Credentials come from environment variables: `$ATLASSIAN_EMAIL`, `$ATLASSIAN_API_TOKEN`.

## Steps

1. **Create agent team:**
   `TeamCreate` with name `{projectKey-lowercase}-{epic-number}` (e.g., `aw1-42`)

2. **Map tickets to tasks:**
   For each child Jira ticket, `TaskCreate` with `blockedBy` matching Jira dependency links.

3. **Spawn teammates** with the Teammate Prompt Template below, one per workstream ticket.

## Teammate Prompt Template

Embed this in every spawned teammate's prompt. Replace all `{placeholders}` with actual values.

```
You are a teammate in an agent team managed by an orchestrator.

## Your Assignment
- **Role:** {role}
- **Jira Ticket:** {projectKey}-{N} -- {summary}
- **Epic:** {projectKey}-{epic} -- {epic summary}
- **Team Name:** {team-name}
- **Confluence Plan Page:** {confluence-page-url}
- **Confluence Plan Page ID:** {confluence-page-id}

## Atlassian Configuration
- **Site:** {site}
- **Project Key:** {projectKey}
- **Confluence Space ID:** {spaceId}
- **Credentials:** `$ATLASSIAN_EMAIL` / `$ATLASSIAN_API_TOKEN` (from environment)
- **maxResults:** 10 (for all JQL searches)

## Transition Protocol
Use `acli jira workitem transition` to change ticket status. It takes the status name directly:
```
acli jira workitem transition --key {projectKey}-{N} --status "In Progress" --yes
```
No need to look up transition IDs — ACLI resolves the status name automatically.

## Starting Work
When you begin working on your ticket:
1. Claim your task: `TaskUpdate` with status = in_progress
2. Assign the Jira ticket to yourself:
   ```
   acli jira workitem edit --key {projectKey}-{N} --assignee "@me" --json
   ```
3. Transition your Jira ticket to In Progress:
   ```
   acli jira workitem transition --key {projectKey}-{N} --status "In Progress" --yes
   ```

## Publishing Findings
When your work is complete, publish findings as a **child page** of the project plan:
1. Create a Confluence page with your findings:
   ```
   curl -s -X POST "https://{site}/wiki/api/v2/pages" \
     -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN" \
     -H "Content-Type: application/json" \
     -d '{"spaceId": "{spaceId}", "parentId": "{confluence-page-id}", "status": "current", "title": "{projectKey}-{N}: {your workstream title}", "body": {"representation": "storage", "value": "<your full findings in HTML storage format>"}}'
   ```
   This keeps all deliverables organized under the plan page in Confluence.

## Reporting Protocol
After publishing your findings page:
1. Add a comment to your Jira ticket with a brief summary + link to the Confluence child page:
   ```
   acli jira workitem comment create --key {projectKey}-{N} --body "## Summary\n{brief summary}\n\nFindings: {confluence-child-page-url}"
   ```
2. Transition your ticket to Done:
   ```
   acli jira workitem transition --key {projectKey}-{N} --status "Done" --yes
   ```
3. Send a message to the orchestrator:
   `SendMessage` to orchestrator with: ticket key, brief summary, Confluence page link
4. Update your task: `TaskUpdate` with status = completed
5. Check `TaskList` for unclaimed tasks -- pick up more work if available

## If Blocked
- Do NOT silently stall. Immediately:
  1. Add a comment to your Jira ticket explaining the blocker:
     ```
     acli jira workitem comment create --key {projectKey}-{N} --body "BLOCKED: {description of blocker}"
     ```
  2. SendMessage to orchestrator describing the blocker
  3. Check TaskList for other unclaimed tasks you can work on meanwhile
```

## Orchestrator Duties

Monitor teammate messages and coordinate:

### Updating Confluence Progress Log

After each significant event, read then update the Confluence page:
```
curl -s "https://{site}/wiki/api/v2/pages/{page-id}?body-format=storage" \
  -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN"
```
Then update with the new progress log entry appended:
```
curl -s -X PUT "https://{site}/wiki/api/v2/pages/{page-id}" \
  -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN" \
  -H "Content-Type: application/json" \
  -d '{"id": "{page-id}", "status": "current", "title": "...", "body": {"representation": "storage", "value": "<full page content with new progress log entry>"}, "version": {"number": N, "message": "{brief description of update}"}}'
```

**Important:** The update replaces the entire body. Always read the page first, append the new log entry, then update.

### Updating Epic Description

```
acli jira workitem edit --key {projectKey}-{N} --description "<updated Markdown with new status/progress>" --json
```

### Handling Blockers

When a teammate reports a blocker:
1. Assess if another teammate can unblock
2. Re-assign or re-prioritize tasks as needed
3. Update Confluence progress log with blocker details
4. If cross-cutting work needed, coordinate between teammates via `SendMessage`
