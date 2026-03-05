# Phase 4: Completion — Detailed Reference

## Completion Checklist

```
- [ ] Step 1: Update Confluence page status to COMPLETED
- [ ] Step 2: Add deliverables section to Confluence page
- [ ] Step 3: Update Epic description summary
- [ ] Step 4: Transition Epic to Done (two-step: getTransitions -> transition)
- [ ] Step 5: Add final summary comment to Epic
- [ ] Step 6: Shutdown teammates
- [ ] Step 7: Report to user
```

## Step-by-Step

### 1. Update Confluence Page

Set status to COMPLETED and add deliverables section:
```
mcp__atlassian__getConfluencePage:
  cloudId: "{cloudId}"
  pageId: "{page-id}"
```
Then update with completed status and deliverables:
```
mcp__atlassian__updateConfluencePage:
  cloudId: "{cloudId}"
  pageId: "{page-id}"
  contentFormat: "markdown"
  body: <full page with status = COMPLETED, deliverables filled in, final progress log entry>
  versionMessage: "Project completed"
```

### 2. Update Epic Description

```
mcp__atlassian__editJiraIssue:
  cloudId: "{cloudId}"
  issueIdOrKey: "{projectKey}-{N}"
  fields:
    description: <updated Markdown with status = COMPLETED>
```

### 3. Transition Epic to Done

Two-step — always discover transition ID first:
```
mcp__atlassian__getTransitionsForJiraIssue:
  cloudId: "{cloudId}"
  issueIdOrKey: "{projectKey}-{N}"
```
Then transition:
```
mcp__atlassian__transitionJiraIssue:
  cloudId: "{cloudId}"
  issueIdOrKey: "{projectKey}-{N}"
  transitionId: "{done-transition-id}"
```

### 4. Add Final Summary Comment

```
mcp__atlassian__addCommentToJiraIssue:
  cloudId: "{cloudId}"
  issueIdOrKey: "{projectKey}-{N}"
  commentBody: |
    ## Project Complete
    All {N} workstreams finished.
    ### Deliverables
    - {deliverable}: {location/description}
    ### Summary
    {Brief narrative}
```

### 5. Shutdown Teammates

`SendMessage` type `shutdown_request` to all active teammates.

### 6. Report to User

Deliver:
- Epic key and link
- Confluence plan page link
- Summary of deliverables (with links to child pages)

## Verification

- Confirm Epic status is "Done" via `getJiraIssue`
- Confirm all child tickets are "Done":
  ```
  parent = {projectKey}-{N} AND statusCategory != Done
  ```
  Should return 0 results.
- Confirm Confluence page shows COMPLETED status
