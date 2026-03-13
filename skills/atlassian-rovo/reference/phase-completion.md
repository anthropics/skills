# Phase 4: Completion — Detailed Reference

All examples use `{site}` and `{projectKey}` as placeholders.
Credentials come from environment variables: `$ATLASSIAN_EMAIL`, `$ATLASSIAN_API_TOKEN`.

## Completion Checklist

```
- [ ] Step 1: Update Confluence page status to COMPLETED
- [ ] Step 2: Add deliverables section to Confluence page
- [ ] Step 3: Update Epic description summary
- [ ] Step 4: Transition Epic to Done
- [ ] Step 5: Add final summary comment to Epic
- [ ] Step 6: Shutdown teammates (multi-agent mode only)
- [ ] Step 7: Report to user
```

## Step-by-Step

### 1. Update Confluence Page

Read the page:
```
curl -s "https://{site}/wiki/api/v2/pages/{page-id}?body-format=storage" \
  -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN"
```
Then update with completed status and deliverables:
```
curl -s -X PUT "https://{site}/wiki/api/v2/pages/{page-id}" \
  -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN" \
  -H "Content-Type: application/json" \
  -d '{"id": "{page-id}", "status": "current", "title": "...", "body": {"representation": "storage", "value": "<full page with status = COMPLETED, deliverables filled in, final progress log entry>"}, "version": {"number": N, "message": "Project completed"}}'
```

### 2. Update Epic Description

```
acli jira workitem edit --key {projectKey}-{N} --description "<updated Markdown with status = COMPLETED>" --json
```

### 3. Transition Epic to Done

```
acli jira workitem transition --key {projectKey}-{N} --status "Done" --yes
```

### 4. Add Final Summary Comment

```
acli jira workitem comment create --key {projectKey}-{N} --body "## Project Complete\nAll {N} workstreams finished.\n### Deliverables\n- {deliverable}: {location/description}\n### Summary\n{Brief narrative}"
```

### 5. Shutdown Teammates (Multi-Agent Mode Only)

If running in multi-agent mode, send shutdown to all active teammates.
In single-agent mode, skip this step.

### 6. Report to User

Deliver:
- Epic key and link
- Confluence plan page link
- Summary of deliverables (with links to child pages)

## Verification

- Confirm Epic status is "Done": `acli jira workitem view {projectKey}-{N} --json`
- Confirm all child tickets are "Done":
  ```
  acli jira workitem search --jql "parent = {projectKey}-{N} AND statusCategory != Done" --json --limit 10
  ```
  Should return 0 results.
- Confirm Confluence page shows COMPLETED status
