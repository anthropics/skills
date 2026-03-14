# Common Patterns — Shared Reference

Shared protocols used by both multi-agent and single-agent execution modes.
Phase-specific docs reference this file instead of repeating these patterns.

All examples use `{site}`, `{projectKey}` as placeholders.
Credentials are sourced from environment: `$ATLASSIAN_EMAIL`, `$ATLASSIAN_API_TOKEN`.

## Contents

- [Transition Protocol](#transition-protocol)
- [Starting a Ticket](#starting-a-ticket)
- [Publishing Findings](#publishing-findings)
- [Completing a Ticket](#completing-a-ticket)
- [Updating the Confluence Plan Page](#updating-the-confluence-plan-page)
- [Dependency Ordering](#dependency-ordering)
- [JQL Patterns](#jql-patterns)

**Confluence API versions:** Use v2 (`/wiki/api/v2/`) for page CRUD (create, read, update) and comments. Use v1 (`/wiki/rest/api/`) for CQL search and comment replies — the v2 equivalents have different behavior or return errors. See [confluence-comments.md](confluence-comments.md) for details on comment threading.

---

## Transition Protocol

ACLI resolves transitions by status name — no need to look up transition IDs:

```bash
acli jira workitem transition --key {projectKey}-{N} --status "In Progress" --yes
```

```bash
acli jira workitem transition --key {projectKey}-{N} --status "Done" --yes
```

---

## Starting a Ticket

1. **Assign** the ticket so Jira tracks ownership:
   ```bash
   acli jira workitem edit --key {projectKey}-{N} --assignee "@me"
   ```
   > **Note:** The `edit` response may show `null` for assignee even when assignment succeeded. Verify with `acli jira workitem view {projectKey}-{N} --json` if needed.

2. **Transition to In Progress:**
   ```bash
   acli jira workitem transition --key {projectKey}-{N} --status "In Progress" --yes
   ```

3. **Create a branch** (optional, if the project has a git repo):
   ```bash
   git remote get-url origin  # detect GitHub vs Bitbucket
   git checkout -b feature/{projectKey}-{N}-{slug}
   git push -u origin feature/{projectKey}-{N}-{slug}
   ```
   Add a Jira comment noting the branch:
   ```bash
   acli jira workitem comment create --key {projectKey}-{N} --body "Branch created: \`feature/{projectKey}-{N}-{slug}\` on {repoUrl}"
   ```
   The issue key in the branch name auto-links it to Jira's Development panel.
   See [git-integration.md](git-integration.md) for naming conventions and setup details.

---

## Publishing Findings

Create a Confluence child page under the plan page:
```bash
curl -s -X POST "https://{site}/wiki/api/v2/pages" \
  -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "spaceId": "{spaceId}",
    "parentId": "{confluence-page-id}",
    "status": "current",
    "title": "{projectKey}-{N}: {workstream title}",
    "body": {"representation": "storage", "value": "<findings in HTML>"}
  }'
```

This keeps all deliverables organized under the plan page in Confluence.

> **Shell escaping note:** When building curl payloads with shell variables containing HTML or special characters, use Python to safely JSON-encode the body:
> ```bash
> BODY_JSON=$(python3 -c "import json,sys; print(json.dumps(sys.stdin.read()))" <<'HTMLEOF'
> <h2>Findings</h2><p>Your HTML content here</p>
> HTMLEOF
> )
> curl -s -X POST "https://{site}/wiki/api/v2/pages" \
>   -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN" \
>   -H "Content-Type: application/json" \
>   -d "{\"spaceId\": \"...\", \"parentId\": \"...\", \"status\": \"current\", \"title\": \"...\", \"body\": {\"representation\": \"storage\", \"value\": $BODY_JSON}}"
> ```
> Alternatively, use the `confluence_create_page` helper from `atlassian-helpers.sh`, which handles JSON encoding automatically.

---

## Completing a Ticket

1. **Add a comment** with summary + link to Confluence child page:
   ```bash
   acli jira workitem comment create --key {projectKey}-{N} --body "## Summary
   {brief summary}

   Findings: {confluence-child-page-url}"
   ```

2. **Transition to Done:**
   ```bash
   acli jira workitem transition --key {projectKey}-{N} --status "Done" --yes
   ```

3. **Update the Epic description** — change the ticket's status in the workstreams table:
   ```bash
   acli jira workitem view {epicKey} --json --fields "description"
   ```
   Read the current description, update the workstream status, then:
   ```bash
   acli jira workitem edit --key {epicKey} --description "<updated description>"
   ```

---

## Updating the Confluence Plan Page

The REST API PUT replaces the entire body. Before ANY update, read the page AND its comments:

1. **Read the page body:**
   ```bash
   curl -s "https://{site}/wiki/api/v2/pages/{pageId}?body-format=storage" \
     -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN"
   ```

2. **Read inline comments** (review feedback on highlighted text):
   ```bash
   curl -s "https://{site}/wiki/api/v2/pages/{pageId}/inline-comments?body-format=storage" \
     -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN"
   ```

3. **Read footer comments** (general discussion):
   ```bash
   curl -s "https://{site}/wiki/api/v2/pages/{pageId}/footer-comments?body-format=storage" \
     -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN"
   ```

4. **Address any open comments** before updating — incorporate feedback into the page content.

5. **Update the page** (increment version number):
   ```bash
   curl -s -X PUT "https://{site}/wiki/api/v2/pages/{pageId}" \
     -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN" \
     -H "Content-Type: application/json" \
     -d '{
       "id": "{pageId}",
       "status": "current",
       "title": "{title}",
       "body": {"representation": "storage", "value": "<full updated content>"},
       "version": {"number": {currentVersion + 1}, "message": "{description}"}
     }'
   ```

---

## Dependency Ordering

Query all child tickets and sort by dependencies:
```bash
acli jira workitem search --jql "parent = {projectKey}-{N} ORDER BY rank ASC" --json --limit 10
```

Work tickets in this order:
1. Tickets with no blockers (can start immediately)
2. Tickets blocked by completed tickets (blockers resolved)
3. Skip tickets whose blockers are still incomplete (come back later)

---

## JQL Patterns

**Find open AI-managed Epics:**
```bash
acli jira workitem search --jql "project = {projectKey} AND issuetype = Epic AND summary ~ "\\[AI-PM\\]" AND statusCategory NOT IN (Done) ORDER BY updated DESC" --json --limit 10
```

**Find incomplete child tickets for an Epic:**
```bash
acli jira workitem search --jql "parent = {projectKey}-{N} AND statusCategory NOT IN (Done) ORDER BY rank ASC" --json --limit 10
```

**Find all tickets for an Epic (including done):**
```bash
acli jira workitem search --jql "parent = {projectKey}-{N} ORDER BY rank ASC" --json --limit 10
```

> **Note:** Use `NOT IN (Done)` instead of `!= Done` — ACLI escapes the `!` character which breaks the query.

> **Note:** Square brackets `[` `]` are JQL range-query operators. In `summary ~` queries, escape them as `\[AI-PM\]`. Unescaped `[AI-PM]` causes a parse error.
