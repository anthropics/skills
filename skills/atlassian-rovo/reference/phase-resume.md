# Phase 3: Resume Protocol — Detailed Reference

Fully autonomous — no user confirmation required.

All examples use `{site}` and `{projectKey}` as placeholders.
Credentials come from environment variables: `$ATLASSIAN_EMAIL`, `$ATLASSIAN_API_TOKEN`.

## Trigger

User says "resume {projectKey}-{N}" or auto-detect open `[AI-PM]` Epics.

## Steps

1. **Find the Epic** — `acli jira workitem view {projectKey}-{N} --json`, extract Confluence page URL from description
2. **Read the plan:**
   ```
   curl -s "https://{site}/wiki/api/v2/pages/{plan-page-id}?body-format=storage" \
     -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN"
   ```
   Read full plan context.
3. **Query incomplete tickets:**
   ```
   acli jira workitem search --jql "parent = {projectKey}-{N} AND statusCategory != Done ORDER BY rank ASC" --json --limit 10
   ```
4. **Inspect each ticket** — `acli jira workitem view {projectKey}-{X} --json` for details + check comments for prior work
5. **Classify state:**
   - **To Do** = no prior work -> assign fresh agent
   - **In Progress** = has comments with partial work -> agent continues from last comment
6. **Spin up right-sized team** for remaining work only
7. **Add comment to Epic:**
   ```
   acli jira workitem comment create --key {projectKey}-{N} --body "Session resumed. N tickets remaining."
   ```
8. **Update Confluence progress log** with resume entry

## JQL Patterns

**Find open AI-managed Epics:**
```
acli jira workitem search --jql "project = {projectKey} AND issuetype = Epic AND summary ~ '[AI-PM]' AND statusCategory != Done ORDER BY updated DESC" --json --limit 10
```

**Find incomplete child tickets for an Epic:**
```
acli jira workitem search --jql "parent = {projectKey}-{N} AND statusCategory != Done ORDER BY rank ASC" --json --limit 10
```

**Find all tickets for an Epic (including done):**
```
acli jira workitem search --jql "parent = {projectKey}-{N} ORDER BY rank ASC" --json --limit 10
```

## Verification

After resume setup:
- Confirm team size matches number of remaining tickets
- Verify each teammate received correct ticket assignment via `TaskList`
- Check Confluence progress log shows resume entry
