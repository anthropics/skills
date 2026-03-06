# Phase 3: Resume Protocol — Detailed Reference

Fully autonomous — no user confirmation required.

## Contents
- [Trigger](#trigger)
- [Steps](#steps)
- [Multi-Agent Mode](#multi-agent-mode)
- [Single-Agent Mode](#single-agent-mode)
- [Verification](#verification)

## Trigger

User says "resume {projectKey}-{N}" or auto-detect open `[AI-PM]` Epics.

## Steps

These steps are shared by both modes:

1. **Find the Epic** — `getJiraIssue` on Epic, extract Confluence page URL from description

2. **Read the plan** — `getConfluencePage`, read full plan context

3. **Query incomplete tickets:**
   ```
   parent = {projectKey}-{N} AND statusCategory != Done ORDER BY rank ASC
   ```

4. **Inspect each ticket** — `getJiraIssue` for details + check Jira comments for prior work

5. **Read Confluence plan page comments** for additional context:
   ```
   getConfluencePageFooterComments:
     cloudId: "{cloudId}"
     pageId: "{planPageId}"
     limit: 10
     sort: "-created-date"
   ```
   Footer comments may contain progress notes from the previous session.

   Also check for inline review feedback on deliverable child pages:
   ```
   getConfluencePageInlineComments:
     cloudId: "{cloudId}"
     pageId: "{childPageId}"
     limit: 10
     resolutionStatus: "open"
   ```
   Open inline comments indicate unaddressed review feedback.

6. **Classify state:**
   - **To Do** = no prior work -> assign fresh
   - **In Progress** = has Jira comments or Confluence comments with partial work -> continue from where it left off

7. **Add comment to Epic:** "Session resumed. N tickets remaining."

8. **Update Confluence progress log** with resume entry

## Multi-Agent Mode

After completing the shared steps above:

- **Spin up right-sized team** for remaining work only (see team sizing in SKILL.md)
- Confirm team size matches number of remaining tickets
- Verify each teammate received correct ticket assignment via `TaskList`

See [phase-execution.md](phase-execution.md) for teammate prompt template.

## Single-Agent Mode

After completing the shared steps above:

- **Pick up the first actionable ticket** (respecting dependency order) and continue with the single-agent execution workflow
- See [phase-execution-single.md](phase-execution-single.md) for the sequential workflow
- See [common-patterns.md](common-patterns.md) for transition protocol and dependency ordering

## Verification

After resuming:
- Confirm the correct ticket(s) were picked up
- Check Confluence progress log shows resume entry
- (Multi-agent) Verify team size matches remaining ticket count via `TaskList`

For JQL patterns used during resume, see [common-patterns.md](common-patterns.md#jql-patterns).
