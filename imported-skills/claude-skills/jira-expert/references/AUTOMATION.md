# Jira Automation Reference

Comprehensive guide to Jira automation rules: triggers, conditions, actions, smart values, and production-ready recipes.

## Rule Structure

Every automation rule follows this pattern:
```
TRIGGER → [CONDITION(s)] → ACTION(s)
```

- **Trigger**: The event that starts the rule (required, exactly one)
- **Condition**: Filters to narrow when the rule fires (optional, multiple allowed)
- **Action**: What the rule does (required, one or more)

## Triggers

### Issue Triggers

| Trigger | Fires When | Use For |
|---------|------------|---------|
| **Issue created** | New issue is created | Auto-assignment, notifications, SLA start |
| **Issue transitioned** | Status changes | Workflow automation, notifications |
| **Issue updated** | Any field changes | Field sync, cascading updates |
| **Issue commented** | Comment is added | Auto-responses, SLA tracking |
| **Issue assigned** | Assignee changes | Workload notifications |
| **Issue linked** | Link is added/removed | Dependency tracking |
| **Issue deleted** | Issue is deleted | Cleanup, audit logging |

### Sprint & Board Triggers

| Trigger | Fires When |
|---------|------------|
| **Sprint started** | Sprint is activated |
| **Sprint completed** | Sprint is closed |
| **Issue moved between sprints** | Issue is moved |
| **Backlog item moved to sprint** | Item is pulled into sprint |

### Scheduled Triggers

| Trigger | Fires When |
|---------|------------|
| **Scheduled** | Cron-based (daily, weekly, custom) |
| **Issue stale** | No updates for X days |

### Version Triggers

| Trigger | Fires When |
|---------|------------|
| **Version created** | New version added |
| **Version released** | Version is released |

## Conditions

### Issue Conditions

| Condition | Matches When |
|-----------|-------------|
| **Issue fields condition** | Field matches value (e.g., priority = High) |
| **JQL condition** | Issue matches JQL query |
| **Related issues condition** | Linked/sub-task issues match criteria |
| **User condition** | Actor matches (reporter, assignee, group) |
| **Advanced compare** | Complex field comparisons |

### Condition Operators

```
Field = value           # Exact match
Field != value          # Not equal
Field > value           # Greater than (numeric/date)
Field is empty          # Field has no value
Field is not empty      # Field has a value
Field changed           # Field was modified in this event
Field changed to        # Field changed to specific value
Field changed from      # Field changed from specific value
```

## Actions

### Issue Actions

| Action | Does |
|--------|------|
| **Edit issue** | Update any field on the current issue |
| **Transition issue** | Move to a new status |
| **Assign issue** | Change assignee |
| **Comment on issue** | Add a comment |
| **Create issue** | Create a new linked issue |
| **Create sub-tasks** | Create child issues |
| **Clone issue** | Duplicate the issue |
| **Delete issue** | Remove the issue |
| **Link issues** | Add issue links |
| **Log work** | Add time tracking entry |

### Notification Actions

| Action | Does |
|--------|------|
| **Send email** | Send custom email to users/groups |
| **Send Slack message** | Post to Slack channel (requires integration) |
| **Send Microsoft Teams message** | Post to Teams (requires integration) |
| **Send web request** | HTTP call to external service |

### Lookup & Branch Actions

| Action | Does |
|--------|------|
| **Lookup issues (JQL)** | Find issues matching JQL, iterate over them |
| **Create branch** | Branch logic (if/then/else) |
| **For each** | Loop over found issues |

## Smart Values

Smart values are dynamic placeholders that resolve at runtime.

### Issue Smart Values

```
{{issue.key}}                    # PROJ-123
{{issue.summary}}                # Issue title
{{issue.description}}            # Full description
{{issue.status.name}}            # Current status
{{issue.priority.name}}          # Priority level
{{issue.assignee.displayName}}   # Assignee name
{{issue.reporter.displayName}}   # Reporter name
{{issue.issuetype.name}}         # Issue type
{{issue.project.key}}            # Project key
{{issue.created}}                # Creation date
{{issue.updated}}                # Last update date
{{issue.fixVersions}}            # Fix versions
{{issue.labels}}                 # Labels array
{{issue.components}}             # Components array
```

### Transition Smart Values

```
{{transition.from_status}}       # Previous status
{{transition.to_status}}         # New status
{{transition.transitionName}}    # Transition name
```

### User Smart Values

```
{{initiator.displayName}}        # Who triggered the rule
{{initiator.emailAddress}}       # Their email
{{initiator.accountId}}          # Their account ID
```

### Date Smart Values

```
{{now}}                          # Current timestamp
{{now.plusDays(7)}}              # 7 days from now
{{now.minusHours(24)}}          # 24 hours ago
{{issue.created.plusBusinessDays(3)}}  # 3 business days after creation
```

### Conditional Smart Values

```
{{#if issue.priority.name == "High"}}
  This is high priority
{{/if}}

{{#if issue.assignee}}
  Assigned to {{issue.assignee.displayName}}
{{else}}
  Unassigned
{{/if}}
```

## Production-Ready Recipes

### 1. Auto-Assign by Component

```yaml
Trigger: Issue created
Condition: Issue has component
Action: Edit issue
  - Assignee = Component lead

Rule Logic:
  IF component = "Backend" → assign to @backend-lead
  IF component = "Frontend" → assign to @frontend-lead
  IF component = "DevOps" → assign to @devops-lead
```

### 2. SLA Warning — Stale Issues

```yaml
Trigger: Scheduled (daily at 9am)
Condition: JQL = "status != Done AND updated <= -5d AND priority in (High, Highest)"
Action: 
  - Add comment: "⚠️ This {{issue.priority.name}} issue hasn't been updated in 5+ days."
  - Send Slack: "#engineering-alerts: {{issue.key}} is stale ({{issue.assignee.displayName}})"
```

### 3. Auto-Close Resolved Issues After 7 Days

```yaml
Trigger: Scheduled (daily)
Condition: JQL = "status = Resolved AND updated <= -7d"
Action:
  - Transition: Resolved → Closed
  - Comment: "Auto-closed after 7 days in Resolved status."
```

### 4. Sprint Spillover Notification

```yaml
Trigger: Sprint completed
Condition: Issue status != Done
Action:
  - Comment: "Spilled over from Sprint {{sprint.name}}. Reason needs review."
  - Add label: "spillover"
  - Send email to: {{issue.assignee.emailAddress}}
```

### 5. Sub-Task Completion → Parent Transition

```yaml
Trigger: Issue transitioned (to Done)
Condition: Issue is sub-task AND all sibling sub-tasks are Done
Action (on parent):
  - Transition: In Progress → In Review
  - Comment: "All sub-tasks completed. Ready for review."
```

### 6. Bug Priority Escalation

```yaml
Trigger: Scheduled (every 4 hours)
Condition: JQL = "type = Bug AND priority = High AND status = Open AND created <= -24h"
Action:
  - Edit: priority = Highest
  - Comment: "⚡ Auto-escalated: High-priority bug open for 24+ hours."
  - Send email to: project lead
```

### 7. Auto-Link Duplicate Detection

```yaml
Trigger: Issue created
Condition: JQL finds issues with similar summary (fuzzy)
Action:
  - Comment: "Possible duplicate of {{lookupIssues.first.key}}: {{lookupIssues.first.summary}}"
  - Add label: "possible-duplicate"
```

### 8. Release Notes Generator

```yaml
Trigger: Version released
Condition: None
Action:
  - Lookup: JQL = "fixVersion = {{version.name}} AND status = Done"
  - Create Confluence page:
    Title: "Release Notes — {{version.name}}"
    Content: List of resolved issues with types and summaries
```

### 9. Workload Balancer — Round-Robin Assignment

```yaml
Trigger: Issue created
Condition: Issue type = Story AND assignee is empty
Action:
  - Lookup: JQL = "assignee in (dev1, dev2, dev3) AND sprint in openSprints() AND status != Done"
  - Assign to team member with fewest open issues
```

### 10. Blocker Notification Chain

```yaml
Trigger: Issue updated (priority changed to Blocker)
Action:
  - Send email to: project lead, scrum master
  - Send Slack: "#blockers: 🚨 {{issue.key}} marked as Blocker by {{initiator.displayName}}"
  - Comment: "Blocker escalated. Notified: PM + SM."
  - Edit: Add label "blocker-active"
```

## Best Practices

1. **Name rules descriptively** — "Auto-assign Backend bugs to @dev-lead" not "Rule 1"
2. **Add conditions before actions** — prevent unintended execution
3. **Use JQL conditions** for precision — field conditions can miss edge cases
4. **Test in a sandbox project first** — automation mistakes can be destructive
5. **Set rate limits** — avoid infinite loops (Rule A triggers Rule B triggers Rule A)
6. **Monitor rule execution** — check Automation audit log weekly
7. **Document business rules** — explain WHY the rule exists, not just WHAT it does
8. **Use branches (if/else)** over separate rules — reduces rule count, easier to maintain
9. **Disable before deleting** — observe for a week to ensure no side effects
10. **Version your automation** — export rules as JSON backup before major changes
