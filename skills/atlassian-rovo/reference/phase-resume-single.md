# Phase 3: Resume (Single-Agent Mode) — Detailed Reference

Fully autonomous — no user confirmation required.

## Trigger

User says "resume {projectKey}-{N}" or auto-detect open `[AI-PM]` Epics.

## Steps

1. **Find the Epic** — `atlassian:getJiraIssue` on Epic, extract Confluence page URL from description

2. **Read the plan** — `atlassian:getConfluencePage`, read full plan context

3. **Query incomplete tickets:**
   ```
   parent = {projectKey}-{N} AND statusCategory != Done ORDER BY rank ASC
   ```

4. **Inspect each ticket** — `atlassian:getJiraIssue` for details + check Jira comments for prior work

5. **Read Confluence plan page comments** for additional context:
   ```
   atlassian:getConfluencePageFooterComments:
     cloudId: "{cloudId}"
     pageId: "{planPageId}"
     limit: 10
     sort: "-created-date"
   ```
   Footer comments may contain progress notes from the previous session.

   Also check for inline review feedback on deliverable child pages:
   ```
   atlassian:getConfluencePageInlineComments:
     cloudId: "{cloudId}"
     pageId: "{childPageId}"
     limit: 10
     resolutionStatus: "open"
   ```
   Open inline comments indicate unaddressed review feedback.

6. **Classify state:**
   - **To Do** = no prior work -> start fresh
   - **In Progress** = has Jira comments or Confluence comments with partial work -> continue from where it left off

7. **Pick up the first actionable ticket** (respecting dependency order) and continue with the single-agent execution workflow. See [phase-execution-single.md](phase-execution-single.md).

8. **Add comment to Epic:** "Session resumed. N tickets remaining."

9. **Update Confluence progress log** with resume entry

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

After resuming:
- Confirm the correct ticket was picked up (first unblocked incomplete ticket)
- Check Confluence progress log shows resume entry
