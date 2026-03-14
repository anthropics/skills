# Phase 2: Execution — Detailed Reference

All examples use `{site}`, `{projectKey}`, `{spaceId}`, and `{parentId}` as placeholders.
Credentials come from environment variables: `$ATLASSIAN_EMAIL`, `$ATLASSIAN_API_TOKEN`.

For shared protocols (starting a ticket, publishing findings, completing a ticket, dependency ordering), see [common-patterns.md](common-patterns.md).

---

## Multi-Agent Mode

Parallel execution using Claude Code Agent Teams.

### Steps

1. **Create agent team:**
   `TeamCreate` with name `{projectKey-lowercase}-{epic-number}` (e.g., `aw1-42`)

2. **Map tickets to tasks:**
   For each child Jira ticket, `TaskCreate` with `blockedBy` matching Jira dependency links.

3. **Spawn teammates** with the Teammate Prompt Template below, one per workstream ticket.

### Teammate Prompt Template

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

### Orchestrator Duties

Monitor teammate messages and coordinate:

#### Updating Confluence Progress Log

After each significant event, read then update the Confluence page.
See [common-patterns.md — Updating the Confluence Plan Page](common-patterns.md#updating-the-confluence-plan-page) for the read-then-update protocol.

#### Updating Epic Description

```
acli jira workitem edit --key {projectKey}-{N} --description "<updated Markdown with new status/progress>" --json
```

#### Handling Blockers

When a teammate reports a blocker:
1. Assess if another teammate can unblock
2. Re-assign or re-prioritize tasks as needed
3. Update Confluence progress log with blocker details
4. If cross-cutting work needed, coordinate between teammates via `SendMessage`

---

## Single-Agent Mode

Sequential execution for agents without multi-agent orchestration (Cursor, Cline, Windsurf, etc.).
Same Jira tracking and Confluence updates as multi-agent mode, but one ticket at a time.

### Workflow

Work each child ticket sequentially, respecting dependency order (blocked tickets last).
See [common-patterns.md — Dependency Ordering](common-patterns.md#dependency-ordering) for how to sort tickets.

For each ticket:

1. **Start the ticket** — assign and transition to In Progress.
   See [common-patterns.md — Starting a Ticket](common-patterns.md#starting-a-ticket).

2. **Do the work** — execute the workstream as described in the ticket.

3. **Publish findings** — create a Confluence child page under the plan page.
   See [common-patterns.md — Publishing Findings](common-patterns.md#publishing-findings).

4. **Complete the ticket** — add summary comment, transition to Done, update Epic.
   See [common-patterns.md — Completing a Ticket](common-patterns.md#completing-a-ticket).

5. **Update the plan page** — mark ticket Done in the workstreams table, add progress log entry.
   See [common-patterns.md — Updating the Confluence Plan Page](common-patterns.md#updating-the-confluence-plan-page).

6. **Next ticket** — move to the next ticket in dependency order. Repeat steps 1-5.

### Key Rules

- **Always transition to In Progress** before starting work (not just Done at the end)
- **Always publish findings as child pages** of the plan page
- **Always update the plan page** after completing each ticket
- **Respect dependency order** — don't start a blocked ticket until its blocker is Done
