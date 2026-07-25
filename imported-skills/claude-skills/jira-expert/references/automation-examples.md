# Jira Automation Examples

## Auto-Assignment Rules

### Auto-assign by component
**Trigger:** Issue created
**Conditions:**
- Component is not EMPTY
**Actions:**
- Assign issue to component lead

### Auto-assign to reporter for feedback
**Trigger:** Issue transitioned to "Waiting for Feedback"
**Actions:**
- Assign issue to reporter
- Add comment: "Please provide additional information"

### Round-robin assignment
**Trigger:** Issue created
**Conditions:**
- Project = ABC
- Assignee is EMPTY
**Actions:**
- Assign to next team member in rotation (use smart value)

---

## Status Sync Rules

### Sync subtask status to parent
**Trigger:** Issue transitioned
**Conditions:**
- Issue type = Sub-task
- Transition is to "Done"
- Parent issue exists
- All subtasks are Done
**Actions:**
- Transition parent issue to "Done"

### Sync parent to subtasks
**Trigger:** Issue transitioned
**Conditions:**
- Issue type has subtasks
- Transition is to "Cancelled"
**Actions:**
- For each: Sub-tasks
  - Transition issue to "Cancelled"

### Epic progress tracking
**Trigger:** Issue transitioned
**Conditions:**
- Epic link is not EMPTY
- Transition is to "Done"
**Actions:**
- Add comment to epic: "{{issue.key}} completed"
- Update epic custom field "Progress"

---

## Notification Rules

### Slack notification for high-priority bugs
**Trigger:** Issue created
**Conditions:**
- Issue type = Bug
- Priority IN (Highest, High)
**Actions:**
- Send Slack message to #engineering:
  ```
  🚨 High Priority Bug Created
  {{issue.key}}: {{issue.summary}}
  Reporter: {{issue.reporter.displayName}}
  Priority: {{issue.priority.name}}
  {{issue.url}}
  ```

### Email assignee when mentioned
**Trigger:** Issue commented
**Conditions:**
- Comment contains @mention of assignee
**Actions:**
- Send email to {{issue.assignee.emailAddress}}:
  ```
  Subject: You were mentioned in {{issue.key}}
  Body: {{comment.author.displayName}} mentioned you:
  {{comment.body}}
  ```

### SLA breach warning
**Trigger:** Scheduled - Every hour
**Conditions:**
- Status != Done
- SLA time remaining < 2 hours
**Actions:**
- Send email to {{issue.assignee}}
- Add comment: "⚠️ SLA expires in <2 hours"
- Set priority to Highest

---

## Field Automation Rules

### Auto-set due date
**Trigger:** Issue created
**Conditions:**
- Issue type = Bug
- Priority = Highest
**Actions:**
- Set due date to {{now.plusDays(1)}}

### Clear assignee when in backlog
**Trigger:** Issue transitioned
**Conditions:**
- Transition is to "Backlog"
- Assignee is not EMPTY
**Actions:**
- Assign issue to Unassigned
- Add comment: "Returned to backlog, assignee cleared"

### Auto-populate sprint field
**Trigger:** Issue transitioned
**Conditions:**
- Transition is to "In Progress"
- Sprint is EMPTY
**Actions:**
- Add issue to current sprint

### Set fix version based on component
**Trigger:** Issue created
**Conditions:**
- Component = "Mobile App"
**Actions:**
- Set fix version to "Mobile v2.0"

---

## Escalation Rules

### Auto-escalate stale issues
**Trigger:** Scheduled - Daily at 9:00 AM
**Conditions:**
- Status = "Waiting for Response"
- Updated < -7 days
**Actions:**
- Add comment: "@{{issue.reporter}} This issue needs attention"
- Send email to project lead
- Add label: "needs-attention"

### Escalate overdue critical issues
**Trigger:** Scheduled - Every hour
**Conditions:**
- Priority IN (Highest, High)
- Due date < now()
- Status != Done
**Actions:**
- Transition to "Escalated"
- Assign to project manager
- Send Slack notification

### Auto-close inactive issues
**Trigger:** Scheduled - Daily at 10:00 AM
**Conditions:**
- Status = "Waiting for Customer"
- Updated < -30 days
**Actions:**
- Transition to "Closed"
- Add comment: "Auto-closed due to inactivity"
- Send email to reporter

---

## Sprint Automation Rules

### Move incomplete work to next sprint
**Trigger:** Sprint closed
**Conditions:**
- Issue status != Done
**Actions:**
- Add issue to next sprint
- Add comment: "Moved from {{sprint.name}}"

### Auto-remove completed items from active sprint
**Trigger:** Issue transitioned
**Conditions:**
- Transition is to "Done"
- Sprint IN openSprints()
**Actions:**
- Remove issue from sprint
- Add comment: "Removed from active sprint (completed)"

### Sprint start notification
**Trigger:** Sprint started
**Actions:**
- Send Slack message to #team:
  ```
  🚀 Sprint {{sprint.name}} Started!
  Goal: {{sprint.goal}}
  Committed: {{sprint.issuesCount}} issues
  ```

---

## Approval Workflow Rules

### Request approval for large stories
**Trigger:** Issue created
**Conditions:**
- Issue type = Story
- Story points >= 13
**Actions:**
- Transition to "Pending Approval"
- Assign to product owner
- Send email notification

### Auto-approve small bugs
**Trigger:** Issue created
**Conditions:**
- Issue type = Bug
- Priority IN (Low, Lowest)
**Actions:**
- Transition to "Approved"
- Add comment: "Auto-approved (low-priority bug)"

### Require security review
**Trigger:** Issue transitioned
**Conditions:**
- Transition is to "Ready for Release"
- Labels contains "security"
**Actions:**
- Transition to "Security Review"
- Assign to security-team
- Send email to security@company.com

---

## Integration Rules

### Create GitHub issue
**Trigger:** Issue transitioned
**Conditions:**
- Transition is to "In Progress"
- Labels contains "needs-tracking"
**Actions:**
- Send webhook to GitHub API:
  ```json
  {
    "title": "{{issue.key}}: {{issue.summary}}",
    "body": "{{issue.description}}",
    "assignee": "{{issue.assignee.name}}"
  }
  ```

### Update Confluence page
**Trigger:** Issue transitioned
**Conditions:**
- Issue type = Epic
- Transition is to "Done"
**Actions:**
- Send webhook to Confluence:
  - Update epic status page
  - Add completion date

---

## Quality & Testing Rules

### Require test cases for features
**Trigger:** Issue transitioned
**Conditions:**
- Issue type = Story
- Transition is to "Ready for QA"
- Custom field "Test Cases" is EMPTY
**Actions:**
- Transition back to "In Progress"
- Add comment: "❌ Test cases required before QA"

### Auto-create test issue
**Trigger:** Issue transitioned
**Conditions:**
- Issue type = Story
- Transition is to "Ready for QA"
**Actions:**
- Create linked issue:
  - Type: Test
  - Summary: "Test: {{issue.summary}}"
  - Link type: "tested by"
  - Assignee: QA team

### Flag regression bugs
**Trigger:** Issue created
**Conditions:**
- Issue type = Bug
- Affects version is in released versions
**Actions:**
- Add label: "regression"
- Set priority to High
- Add comment: "🚨 Regression in released version"

---

## Documentation Rules

### Require documentation for features
**Trigger:** Issue transitioned
**Conditions:**
- Issue type = Story
- Labels contains "customer-facing"
- Transition is to "Done"
- Custom field "Documentation Link" is EMPTY
**Actions:**
- Reopen issue
- Add comment: "📝 Documentation required for customer-facing feature"

### Auto-create doc task
**Trigger:** Issue transitioned
**Conditions:**
- Issue type = Epic
- Transition is to "In Progress"
**Actions:**
- Create subtask:
  - Type: Task
  - Summary: "Documentation for {{issue.summary}}"
  - Assignee: {{issue.assignee}}

---

## Time Tracking Rules

### Log work reminder
**Trigger:** Issue transitioned
**Conditions:**
- Transition is to "Done"
- Time spent is EMPTY
**Actions:**
- Add comment: "⏱️ Reminder: Please log your time"

### Warn on high time spent
**Trigger:** Work logged
**Conditions:**
- Time spent > original estimate * 1.5
**Actions:**
- Add comment: "⚠️ Time spent exceeds estimate by 50%"
- Send notification to assignee and project manager

---

## Advanced Conditional Rules

### Conditional assignee based on priority
**Trigger:** Issue created
**Conditions:**
- Issue type = Bug
**Actions:**
- If: Priority = Highest
  - Assign to on-call engineer
- Else if: Priority = High
  - Assign to team lead
- Else:
  - Assign to next available team member

### Multi-step approval flow
**Trigger:** Issue transitioned
**Conditions:**
- Transition is to "Request Approval"
- Budget estimate > $10,000
**Actions:**
- If: Budget > $50,000
  - Assign to CFO
  - Send email to executive team
- Else if: Budget > $10,000
  - Assign to Director
  - Add comment: "Director approval required"
- Add label: "pending-approval"

---

## Smart Value Examples

### Dynamic assignee based on component
```
{{issue.components.first.lead.accountId}}
```

### Days since created
```
{{issue.created.diff(now).days}}
```

### Conditional message
```
{{#if(issue.priority.name == "Highest")}}
  🚨 CRITICAL
{{else}}
  ℹ️ Normal priority
{{/}}
```

### List all subtasks
```
{{#issue.subtasks}}
  - {{key}}: {{summary}} ({{status.name}})
{{/}}
```

### Calculate completion percentage
```
{{issue.subtasks.filter(item => item.status.statusCategory.key == "done").size.divide(issue.subtasks.size).multiply(100).round()}}%
```

---

## Best Practices

1. **Test in sandbox** - Always test rules on test project first
2. **Start simple** - Begin with basic rules, add complexity incrementally
3. **Use conditions wisely** - Narrow scope to reduce unintended triggers
4. **Monitor audit log** - Check automation execution history regularly
5. **Limit actions** - Keep rules focused, don't chain too many actions
6. **Name clearly** - Use descriptive names: "Auto-assign bugs to component lead"
7. **Document rules** - Add description explaining purpose and owner
8. **Review regularly** - Audit rules quarterly, disable unused ones
9. **Handle errors** - Add error handling for webhooks and integrations
10. **Performance** - Avoid scheduled rules that query large datasets hourly
