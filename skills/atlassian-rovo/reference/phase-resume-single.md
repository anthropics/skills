# Phase 3: Resume (Single-Agent Mode) — Detailed Reference

Sequential resume for agents without multi-agent orchestration (Cursor, Cline, Windsurf, etc.).
Same resume logic as multi-agent mode, but picks up one ticket at a time instead of spawning a team.

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
   acli jira workitem search --jql "parent = {projectKey}-{N} AND statusCategory NOT IN (Done) ORDER BY rank ASC" --json --limit 10
   ```

4. **Inspect each ticket** — `acli jira workitem view {projectKey}-{X} --json` for details + check comments for prior work

5. **Classify state:**
   - **To Do** = no prior work → start fresh
   - **In Progress** = has comments with partial work → continue from last comment

6. **Add comment to Epic:**
   ```
   acli jira workitem comment create --key {projectKey}-{N} --body "Session resumed. N tickets remaining."
   ```

7. **Update Confluence progress log** with resume entry

8. **Pick up the next incomplete ticket** — choose the highest-priority unblocked ticket and start working it using the [phase-execution-single.md](phase-execution-single.md) workflow (assign, transition, do work, publish, complete).

9. **Repeat** for each remaining ticket in dependency order.

## Auto-Detect Open Epics

If the user doesn't specify an Epic, find open AI-managed Epics:
```
acli jira workitem search --jql "project = {projectKey} AND issuetype = Epic AND summary ~ '[AI-PM]' AND statusCategory NOT IN (Done) ORDER BY updated DESC" --json --limit 10
```

If multiple Epics are found, present the list and ask the user which one to resume.

## JQL Patterns

**Find incomplete child tickets for an Epic:**
```
acli jira workitem search --jql "parent = {projectKey}-{N} AND statusCategory NOT IN (Done) ORDER BY rank ASC" --json --limit 10
```

**Find all tickets for an Epic (including done):**
```
acli jira workitem search --jql "parent = {projectKey}-{N} ORDER BY rank ASC" --json --limit 10
```

> **Note:** Use `NOT IN (Done)` instead of `!= Done` — ACLI escapes the `!` character which breaks the query.

## Key Rules

- **Always read the plan page first** — understand the full context before resuming work
- **Check comments on In Progress tickets** — previous agents may have left partial work or blockers
- **Respect dependency order** — don't start a blocked ticket until its blocker is Done
- **Update the plan page** after completing each ticket (same as Phase 2)
