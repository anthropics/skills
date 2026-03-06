# Common Patterns — Shared Reference

Shared protocols used by both multi-agent and single-agent execution modes.

All examples use `{cloudId}`, `{projectKey}`, `{currentUserAccountId}` as placeholders.

---

## Transition Protocol

Jira transition IDs vary by project and workflow — never hardcode them. Always use this two-step process:

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
  transitionId: "{transition-id-from-step-1}"
```

---

## Starting a Ticket

1. **Assign** the ticket so Jira tracks ownership:
   ```
   atlassian:editJiraIssue
     cloudId: "{cloudId}"
     issueIdOrKey: "{projectKey}-{N}"
     fields: {"assignee": {"accountId": "{currentUserAccountId}"}}
   ```

2. **Transition to In Progress** using the two-step transition protocol above.

3. **Create a branch** (optional, if the project has a git repo):
   ```bash
   git remote get-url origin  # detect GitHub vs Bitbucket
   git checkout -b feature/{projectKey}-{N}-{slug}
   git push -u origin feature/{projectKey}-{N}-{slug}
   ```
   Add a Jira comment noting the branch:
   ```
   atlassian:addCommentToJiraIssue
     cloudId: "{cloudId}"
     issueIdOrKey: "{projectKey}-{N}"
     commentBody: "Branch created: `feature/{projectKey}-{N}-{slug}` on {repoUrl}"
   ```
   The issue key in the branch name auto-links it to Jira's Development panel.
   See [git-integration.md](git-integration.md) for naming conventions and setup details.

---

## Publishing Findings

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

This keeps all deliverables organized under the plan page in Confluence.

---

## Completing a Ticket

1. **Add a comment** with summary + link to Confluence child page:
   ```
   atlassian:addCommentToJiraIssue
     cloudId: "{cloudId}"
     issueIdOrKey: "{projectKey}-{N}"
     commentBody: "## Summary\n{brief summary}\n\nFindings: {confluence-child-page-url}"
   ```

2. **Transition to Done** using the two-step transition protocol.

3. **Update the Epic description** — change the ticket's status in the workstreams table from "In Progress" to "Done":
   ```
   atlassian:getJiraIssue
     cloudId: "{cloudId}"
     issueIdOrKey: "{epicKey}"
   ```
   Read the current description, update the workstream status, then:
   ```
   atlassian:editJiraIssue
     cloudId: "{cloudId}"
     issueIdOrKey: "{epicKey}"
     fields: {"description": "<updated description with new status>"}
   ```
   This keeps the Epic's workstream table in sync with actual ticket states.

---

## Updating the Confluence Plan Page

`updateConfluencePage` replaces the entire body. Before ANY update, read the page AND its comments — the user may have left inline review feedback:

1. **Read the page body:**
   ```
   atlassian:getConfluencePage
     cloudId: "{cloudId}"
     pageId: "{plan-page-id}"
   ```

2. **Read inline comments** (review feedback on highlighted text):
   ```
   atlassian:getConfluencePageInlineComments
     cloudId: "{cloudId}"
     pageId: "{plan-page-id}"
     limit: 50
     resolutionStatus: "open"
   ```

3. **Read footer comments** (general discussion):
   ```
   atlassian:getConfluencePageFooterComments
     cloudId: "{cloudId}"
     pageId: "{plan-page-id}"
     limit: 50
     sort: "-created-date"
   ```

4. **Address any open comments** before updating — incorporate feedback into the page content.

5. **Update the page:**
   ```
   atlassian:updateConfluencePage
     cloudId: "{cloudId}"
     pageId: "{plan-page-id}"
     contentFormat: "markdown"
     body: <full updated page content>
     versionMessage: "{brief description of update}"
   ```

---

## Dependency Ordering

Query all child tickets and sort by dependencies:
```
parent = {projectKey}-{N} ORDER BY rank ASC
```

Work tickets in this order:
1. Tickets with no blockers (can start immediately)
2. Tickets blocked by completed tickets (blockers resolved)
3. Skip tickets whose blockers are still incomplete (come back later)

---

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
