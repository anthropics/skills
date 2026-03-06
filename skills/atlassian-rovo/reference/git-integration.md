# Git Branch Integration — Reference

## Overview

Create git branches linked to Jira tickets. Jira's Development panel auto-detects branches, commits, and PRs when the issue key appears in the branch name.

## Branch Naming Convention

```
{prefix}/{issueKey}-{slug}
```

| Prefix | Use |
|--------|-----|
| `feature/` | New features |
| `bugfix/` | Bug fixes |
| `hotfix/` | Urgent fixes |
| `chore/` | Maintenance tasks |

Examples:
- `feature/AW1-25-git-branch-integration`
- `bugfix/AW1-42-fix-null-pointer`

The issue key **MUST** appear in the branch name for Jira auto-detection.

---

## Creating a Branch

```bash
# 1. Create and switch to the new branch
git checkout -b feature/{issueKey}-{slug}

# 2. Push to remote and set upstream
git push -u origin feature/{issueKey}-{slug}
```

After creating the branch, add a Jira comment:
```
addCommentToJiraIssue:
  cloudId: "{cloudId}"
  issueIdOrKey: "{issueKey}"
  commentBody: "Branch created: `feature/{issueKey}-{slug}` on {repoUrl}"
```

---

## Detecting Remote Type

Check the git remote URL to determine the provider:

```bash
git remote get-url origin
```

| URL pattern | Provider |
|-------------|----------|
| `github.com` | GitHub |
| `bitbucket.org` | Bitbucket |

---

## How Jira Auto-Linking Works

Jira's Development panel is populated by integration apps, not API calls:

- **GitHub:** The "GitHub for Jira" app (Atlassian Marketplace) scans branches, commits, and PRs for issue keys
- **Bitbucket:** Native integration (both Atlassian products) — configure in Project settings → Development tools

Once the integration is set up, any branch/commit/PR containing a Jira issue key automatically appears in the issue's Development panel.

### What Gets Detected

| Artifact | Where the key must appear |
|----------|--------------------------|
| Branch | Branch name (e.g., `feature/AW1-25-slug`) |
| Commit | Commit message (e.g., `AW1-25 fix login`) |
| Pull Request | PR title (e.g., `AW1-25: Add login feature`) |

---

## Setup Requirements

Both GitHub and Bitbucket can be connected **simultaneously** — they run as independent integrations.

### GitHub

1. Install "GitHub for Atlassian" from [Atlassian Marketplace](https://marketplace.atlassian.com/apps/1219592/github-for-atlassian) or [GitHub Marketplace](https://github.com/marketplace/jira-software-github)
2. Connect your GitHub organization (requires Org owner permission)
3. Select repositories to give Jira access to

Reference: [Connect GitHub Cloud to Jira](https://support.atlassian.com/jira-cloud-administration/docs/integrate-with-github/)

### Bitbucket

1. In Jira project → Project settings → Development tools
2. Click "Link Bitbucket Repository"
3. Choose repository and configure branch tracking

**Bitbucket authentication for CLI:** Bitbucket uses **app passwords** (not Atlassian API tokens). Create one at [Bitbucket Account Settings](https://bitbucket.org/account/settings/) → App passwords. Use your Bitbucket **username** (found at the same settings page), not your email.

Bitbucket also supports **smart commits**:
- `AW1-25 #done` — transitions the issue to Done
- `AW1-25 #comment Fixed the bug` — adds a comment
- `AW1-25 #time 2h` — logs work time

Reference: [Connect Jira to Bitbucket](https://support.atlassian.com/jira-cloud-administration/docs/connect-jira-cloud-to-bitbucket/)

---

## Reading Development Links

### Via MCP: `getJiraIssueRemoteIssueLinks`

Returns **web links** (manually added), NOT Development panel data:
```
getJiraIssueRemoteIssueLinks:
  cloudId: "{cloudId}"
  issueIdOrKey: "{issueKey}"
```

Returns `[]` if no remote links exist. The `getTeamworkGraphContext` tool (mentioned in `getJiraIssue` description) is not available in the current MCP tool set.

### Via REST API: Dev-Status Endpoint

The Jira dev-status REST API can read Development panel data (branches, PRs, commits):

**Summary** (counts only):
```bash
curl -u "{email}:{apiToken}" \
  "https://{site}.atlassian.net/rest/dev-status/1.0/issue/summary?issueId={issueId}"
```

**Detail** (full branch/PR/commit info):
```bash
curl -u "{email}:{apiToken}" \
  "https://{site}.atlassian.net/rest/dev-status/1.0/issue/detail?issueId={issueId}&applicationType=GitHub&dataType=branch"
```

`applicationType` options: `GitHub`, `Bitbucket`. `dataType` options: `branch`, `pullrequest`, `repository`.

**Note:** This endpoint uses the internal issue **ID** (numeric), not the issue key. Get the ID from `getJiraIssue` response.

---

## Workflow Integration

Branch creation is an **optional step** in the execution phase. It fits between "Start the Ticket" and "Do the Work":

1. Start ticket (assign + transition to In Progress)
2. **Create branch** (if project has a git repo)
3. Do the work
4. Publish findings
5. Complete the ticket

See [phase-execution-single.md](phase-execution-single.md) and [phase-execution.md](phase-execution.md) for full workflow.

---

## Gotchas

1. **Integration app required:** Branches only appear in Jira's Development panel if the GitHub for Jira app or Bitbucket integration is set up. Without it, branch creation still works but Jira won't show it.

2. **Issue key format matters:** The key must match exactly (e.g., `AW1-25`, not `aw1-25` or `AW1 25`). Case-sensitive.

3. **Multiple repos:** If the same issue key appears in branches across multiple repos, all branches show in the Development panel.

4. **Branch cleanup:** After merging, deleting the branch does not remove it from the Development panel — the history is preserved.
