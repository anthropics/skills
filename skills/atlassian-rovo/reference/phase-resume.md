# Phase 3: Resume Protocol — Detailed Reference

Fully autonomous — no user confirmation required.

All examples use `{site}` and `{projectKey}` as placeholders.
Credentials come from environment variables: `$ATLASSIAN_EMAIL`, `$ATLASSIAN_API_TOKEN`.

For JQL patterns and dependency ordering, see [common-patterns.md](common-patterns.md).

## Trigger

User says "resume {projectKey}-{N}" or auto-detect open `[AI-PM]` Epics.

## Auto-Detect Open Epics

If the user doesn't specify an Epic, find open AI-managed Epics using the JQL pattern from [common-patterns.md — JQL Patterns](common-patterns.md#jql-patterns).

If multiple Epics are found, present the list and ask the user which one to resume.

## Steps (Shared by Both Modes)

1. **Find the Epic** — `acli jira workitem view {projectKey}-{N} --json`, extract Confluence page URL from description

2. **Read the plan:**
   ```
   curl -s "https://{site}/wiki/api/v2/pages/{plan-page-id}?body-format=storage" \
     -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN"
   ```
   Read full plan context.

3. **Query incomplete tickets** — use the "find incomplete child tickets" JQL from [common-patterns.md](common-patterns.md#jql-patterns).

4. **Inspect each ticket** — `acli jira workitem view {projectKey}-{X} --json` for details + check comments for prior work

5. **Classify state:**
   - **To Do** = no prior work → start fresh
   - **In Progress** = has comments with partial work → continue from last comment

6. **Add comment to Epic:**
   ```
   acli jira workitem comment create --key {projectKey}-{N} --body "Session resumed. N tickets remaining."
   ```

7. **Update Confluence progress log** with resume entry

---

## Multi-Agent Mode

After steps 1-7 above:

8. **Spin up right-sized team** for remaining work only
9. **Verify** — confirm team size matches remaining tickets, check `TaskList` for correct assignments, check Confluence progress log shows resume entry

---

## Single-Agent Mode

After steps 1-7 above:

8. **Pick up the next incomplete ticket** — choose the highest-priority unblocked ticket and start working it using the [phase-execution.md — Single-Agent Mode](phase-execution.md#single-agent-mode) workflow (assign, transition, do work, publish, complete).

9. **Repeat** for each remaining ticket in dependency order.

## Key Rules

- **Always read the plan page first** — understand the full context before resuming work
- **Check comments on In Progress tickets** — previous agents may have left partial work or blockers
- **Respect dependency order** — don't start a blocked ticket until its blocker is Done
- **Update the plan page** after completing each ticket (same as Phase 2)
