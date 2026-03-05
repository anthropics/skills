# Phase 3: Resume Protocol — Detailed Reference

Fully autonomous — no user confirmation required.

## Trigger

User says "resume {projectKey}-{N}" or auto-detect open `[AI-PM]` Epics.

## Steps

1. **Find the Epic** — `getJiraIssue` on Epic, extract Confluence page URL from description
2. **Read the plan** — `getConfluencePage`, read full plan context
3. **Query incomplete tickets:**
   ```
   parent = {projectKey}-{N} AND statusCategory != Done ORDER BY rank ASC
   ```
4. **Inspect each ticket** — `getJiraIssue` for details + check comments for prior work
5. **Classify state:**
   - **To Do** = no prior work -> assign fresh agent
   - **In Progress** = has comments with partial work -> agent continues from last comment
6. **Spin up right-sized team** for remaining work only
7. **Add comment to Epic:** "Session resumed. N tickets remaining."
8. **Update Confluence progress log** with resume entry

## JQL Patterns

**Find open AI-managed Epics:**
```
project = {projectKey} AND issuetype = Epic AND summary ~ '[AI-PM]' AND statusCategory != Done ORDER BY updated DESC
```

**Find incomplete child tickets for an Epic:**
```
parent = {projectKey}-{N} AND statusCategory != Done ORDER BY rank ASC
```

**Find all tickets for an Epic (including done):**
```
parent = {projectKey}-{N} ORDER BY rank ASC
```

## Verification

After resume setup:
- Confirm team size matches number of remaining tickets
- Verify each teammate received correct ticket assignment via `TaskList`
- Check Confluence progress log shows resume entry
