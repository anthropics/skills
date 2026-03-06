# Phase 2: Execution (Single-Agent Mode) — Detailed Reference

Sequential execution for agents without multi-agent orchestration (Cursor, Cline, Windsurf, etc.).
Same Jira tracking and Confluence updates as multi-agent mode, but one ticket at a time.

All examples use `{cloudId}`, `{projectKey}`, `{spaceId}`, `{parentId}`, and `{currentUserAccountId}` as placeholders.

## Workflow

Work each child ticket sequentially, respecting dependency order (blocked tickets last).

For each ticket:

### 1. Start the Ticket

```
atlassian:editJiraIssue
  cloudId: "{cloudId}"
  issueIdOrKey: "{projectKey}-{N}"
  fields: {"assignee": {"accountId": "{currentUserAccountId}"}}
```

Transition to In Progress (two-step):
```
atlassian:getTransitionsForJiraIssue
  cloudId: "{cloudId}"
  issueIdOrKey: "{projectKey}-{N}"
```
Then:
```
atlassian:transitionJiraIssue
  cloudId: "{cloudId}"
  issueIdOrKey: "{projectKey}-{N}"
  transitionId: "{in-progress-transition-id}"
```

### 2. Create a Branch (Optional)

If the project has a git repository, create a branch for this ticket:
```bash
# Detect remote type
git remote get-url origin
# github.com → GitHub, bitbucket.org → Bitbucket

# Create and push branch with issue key in the name
git checkout -b feature/{projectKey}-{N}-{slug}
git push -u origin feature/{projectKey}-{N}-{slug}
```

Add a Jira comment noting the branch:
```
atlassian:addCommentToJiraIssue
  cloudId: "{cloudId}"
  issueIdOrKey: "{projectKey}-{N}"
  commentBody: "Branch created: `feature/{projectKey}-{N}-{slug}` on {github.com|bitbucket.org}/{org}/{repo}"
```

The issue key in the branch name auto-links it to Jira's Development panel (requires GitHub for Jira app or Bitbucket integration).

### 3. Do the Work

Execute the workstream as described in the ticket.

### 4. Publish Findings

Create a Confluence child page under the plan page:
```
atlassian:createConfluencePage
  cloudId: "{cloudId}"
  spaceId: "{spaceId}"
  parentId: "{confluence-page-id}"
  title: "{projectKey}-{N}: {workstream title}"
  contentFormat: "markdown"
  body: <findings in markdown>
```

### 5. Complete the Ticket

Add a comment with summary + link to Confluence child page:
```
atlassian:addCommentToJiraIssue
  cloudId: "{cloudId}"
  issueIdOrKey: "{projectKey}-{N}"
  commentBody: "## Summary\n{brief summary}\n\nFindings: {confluence-child-page-url}"
```

Transition to Done (two-step):
```
atlassian:getTransitionsForJiraIssue
  cloudId: "{cloudId}"
  issueIdOrKey: "{projectKey}-{N}"
```
Then:
```
atlassian:transitionJiraIssue
  cloudId: "{cloudId}"
  issueIdOrKey: "{projectKey}-{N}"
  transitionId: "{done-transition-id}"
```

### 6. Update Progress

Update the Confluence plan page — change the ticket's status in the workstreams table, add a progress log entry:
```
atlassian:getConfluencePage
  cloudId: "{cloudId}"
  pageId: "{plan-page-id}"
```
Then:
```
atlassian:updateConfluencePage
  cloudId: "{cloudId}"
  pageId: "{plan-page-id}"
  contentFormat: "markdown"
  body: <updated page with ticket marked Done + progress log entry>
  versionMessage: "{projectKey}-{N} completed"
```

### 7. Next Ticket

Move to the next ticket in dependency order. Repeat steps 1-6.

## Dependency Ordering

Query all child tickets and sort by dependencies:
```
parent = {projectKey}-{N} ORDER BY rank ASC
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
