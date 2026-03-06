# Phase 2: Execution — Detailed Reference

All examples use `{cloudId}`, `{projectKey}`, `{spaceId}`, `{parentId}`, and `{currentUserAccountId}` as placeholders.

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
- **cloudId:** {cloudId}
- **Project Key:** {projectKey}
- **Confluence Space ID:** {spaceId}
- **User Account ID:** {currentUserAccountId}
- **maxResults:** 10 (for all JQL searches)

## Transition Protocol
ALWAYS follow this two-step process to change ticket status:
1. Call `atlassian:getTransitionsForJiraIssue` to get available transitions and their IDs
2. Call `atlassian:transitionJiraIssue` with the correct transition ID
NEVER hardcode transition IDs -- they vary by project and workflow.

## Starting Work
When you begin working on your ticket:
1. Claim your task: `TaskUpdate` with status = in_progress
2. Assign the Jira ticket to the current user so Jira tracks ownership:
   `atlassian:editJiraIssue` with:
   - cloudId: {cloudId}
   - issueIdOrKey: "{projectKey}-{N}"
   - fields: {"assignee": {"accountId": "{currentUserAccountId}"}}
3. Transition your Jira ticket to **In Progress** (using two-step transition protocol above)
4. If the project has a git repo, create a branch for your ticket:
   ```bash
   git checkout -b feature/{projectKey}-{N}-{slug}
   git push -u origin feature/{projectKey}-{N}-{slug}
   ```
   Then add a Jira comment noting the branch name and repo link.
   The issue key in the branch name auto-links it to Jira's Development panel.

## Publishing Findings
When your work is complete, publish findings as a **child page** of the project plan:
1. Create a Confluence page with your findings:
   `atlassian:createConfluencePage` with:
   - cloudId: {cloudId}
   - spaceId: {spaceId}
   - parentId: "{confluence-page-id}"   <-- this makes it a CHILD of the plan page
   - title: "{projectKey}-{N}: {your workstream title}"
   - contentFormat: "markdown"
   - body: <your full findings in markdown>
   This keeps all deliverables organized under the plan page in Confluence.

## Reporting Protocol
After publishing your findings page:
1. Add a comment to your Jira ticket with a brief summary + link to the Confluence child page
2. Transition your ticket to Done (using two-step transition protocol above)
3. Send a message to the orchestrator:
   `SendMessage` to orchestrator with: ticket key, brief summary, Confluence page link
4. Update your task: `TaskUpdate` with status = completed
5. Check `TaskList` for unclaimed tasks -- pick up more work if available

## If Blocked
- Do NOT silently stall. Immediately:
  1. Add a comment to your Jira ticket explaining the blocker
  2. SendMessage to orchestrator describing the blocker
  3. Check TaskList for other unclaimed tasks you can work on meanwhile
```

## Orchestrator Duties

Monitor teammate messages and coordinate:

### Updating Confluence Progress Log

After each significant event, update the Confluence page:
```
atlassian:updateConfluencePage:
  cloudId: "{cloudId}"
  pageId: "{page-id}"
  contentFormat: "markdown"
  body: <full page content with new progress log entry appended>
  versionMessage: "{brief description of update}"
```

**Important:** `updateConfluencePage` replaces the entire body. Always `getConfluencePage` first, append the new log entry, then update.

### Updating Epic Description

```
atlassian:editJiraIssue:
  cloudId: "{cloudId}"
  issueIdOrKey: "{projectKey}-{N}"
  fields:
    description: <updated Markdown with new status/progress>
```

### Handling Blockers

When a teammate reports a blocker:
1. Assess if another teammate can unblock
2. Re-assign or re-prioritize tasks as needed
3. Update Confluence progress log with blocker details
4. If cross-cutting work needed, coordinate between teammates via `SendMessage`
