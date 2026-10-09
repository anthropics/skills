---
name: gog-tasks
description: Create, manage, and prioritize tasks and todo items. Convert emails to tasks, set priorities (P0-P3) and categories (Work/Personal/Errands/Admin), review daily priorities, track blocked and overdue tasks. Use when user mentions tasks, todos, action items, or wants to convert emails to tasks. Requires confirmation before creating or deleting tasks.
compatibility: Requires gog CLI tool with tasks access
metadata:
  author: gog-skills
  version: "1.0"
allowed-tools: Bash(gog:*) Read
---

# Task Management & Prioritization

Create, organize, and track tasks with smart prioritization and daily review.

## When to Use

Use this skill when:
- User mentions "create a task" or "add to my todo list"
- User wants to "convert this email to a task"
- User asks "what's on my task list" or "what should I do today"
- User mentions "task review" or "daily priorities"
- User wants to update or complete tasks

## Dynamic Context

The following live data is available:

**Open tasks:**
```
!`TASKLIST_ID=$(gog tasks lists --json 2>/dev/null | jq -r '.tasklists[0].id' 2>/dev/null) && [ -n "$TASKLIST_ID" ] && gog tasks list "$TASKLIST_ID" --json 2>/dev/null || echo "GOG_NOT_CONFIGURED"`
```

**Important**: All task operations require a task list ID. Get it with:
```bash
TASKLIST_ID=$(gog tasks lists --json | jq -r '.tasklists[0].id')
```

## Task Taxonomy

### Priority Levels (P0-P3)

- **P0 (Critical)**: Drop everything, do now
  - Blocking others' work
  - System outages or emergencies
  - Hard deadline within hours
  - High-impact and high-urgency

- **P1 (High)**: Important, do soon
  - Deadline within 1-3 days
  - Stakeholder requests
  - Significant impact if delayed
  - Part of current sprint/focus

- **P2 (Medium)**: Normal priority
  - Deadline within 1-2 weeks
  - Routine work items
  - Moderate impact
  - Can be scheduled flexibly

- **P3 (Low)**: Nice to have
  - No specific deadline
  - Low impact if delayed
  - Backlog items
  - Ideas or improvements

### Categories

- **Work**: Professional/job-related tasks
  - Project work, meetings prep, emails, reports

- **Personal**: Personal life tasks
  - Hobbies, self-care, family, learning

- **Errands**: Out-of-office tasks
  - Shopping, appointments, calls, pickups

- **Admin**: Bureaucratic tasks
  - Paperwork, taxes, bills, legal matters

## Workflow

### Creating Tasks

#### From Email

When user says "create a task for email [id]" or "turn this into a task":

1. **Fetch email if not in context**:
   ```bash
   gog gmail get <email_id> --json
   ```

2. **Extract task details**:
   - Title: Email subject (may need shortening)
   - Description: Key points from email body
   - Priority: Infer from urgency (default: P2)
   - Category: Infer from content (default: Work)
   - Due date: Extract if mentioned, otherwise ask
   - Related email ID: Store for reference

3. **Present proposed task**:
   ```markdown
   ## Proposed Task

   **Title**: [Derived from email subject]
   **Description**: [Key points from email]
   **Priority**: [P0/P1/P2/P3] (rationale: [why])
   **Category**: [Work/Personal/Errands/Admin]
   **Due date**: [Date or "Not specified"]
   **Source**: Email from [sender] on [date]

   Does this look correct? Adjustments needed?
   ```

4. **Iterate** if user wants changes

5. **Request confirmation**: "Ready to create this task?"

6. **Create** when user confirms:
   ```bash
   # Get task list ID (first time or cache it)
   TASKLIST_ID=$(gog tasks lists --json | jq -r '.tasklists[0].id')

   # Create task
   gog tasks add "$TASKLIST_ID" \
     --title "Task title" \
     --notes "Task description" \
     --due 2026-02-05 \
     --json
   ```

   **Note**: GOG CLI v0.9.0 task commands require a task list ID. Priority and category are tracked in the notes field or as custom metadata.

7. **Confirm creation**:
   ```markdown
   ✅ **Task Created**

   Task ID: task_abc123
   Title: [title]
   Priority: [P1]
   Due: [date]

   View all tasks: "Show my tasks"
   ```

#### From Scratch

When user says "create a task to [X]":

1. **Gather details** by asking:
   ```markdown
   Let me create that task. A few questions:

   1. **Title**: "[Suggested based on user input]" - is this good?
   2. **Priority**: P0 (critical), P1 (high), P2 (medium), or P3 (low)?
   3. **Category**: Work, Personal, Errands, or Admin?
   4. **Due date**: When does this need to be done?
   5. **Additional details**: Anything else to note?
   ```

2. **Accept shorthand answers**: e.g., "1: yes, 2: P1, 3: Work, 4: Friday"

3. **Present and confirm** before creating

### Reviewing Tasks

#### Daily Task Review

When user says "task review" or "what should I do today":

1. **Fetch open tasks**:
   ```bash
   # Get task list ID
   TASKLIST_ID=$(gog tasks lists --json | jq -r '.tasklists[0].id')

   # List all tasks
   gog tasks list "$TASKLIST_ID" --json
   ```

2. **Analyze and categorize**:
   - Today's priorities (P0/P1 tasks due soon)
   - Overdue tasks
   - Blocked tasks (if status indicates)
   - Tasks waiting on others

3. **Present structured review**:
   ```markdown
   # Daily Task Review — [Day], [Date]

   ## 🔥 Top 5 Tasks for Today

   1. **[Task Title]** (P0, due today)
      - Category: Work
      - Details: [Brief description]
      - Task ID: task_abc123

   2. [...]

   ## ⚠️  Overdue Tasks ([N] total)

   - **[Task Title]** (P1, due [date])
     - [Why it's overdue context]
     - Task ID: task_def456

   ## 🚧 Blocked / Waiting on Others ([N] total)

   - **[Task Title]** (P2)
     - Blocked by: [What/who]
     - Task ID: task_ghi789

   ## 📅 This Week (Non-urgent)

   [List of P2/P3 tasks due this week]

   ---

   **Suggested Focus**:
   1. Start with: [Task title] (highest priority)
   2. Then tackle: [Task title]
   3. If blocked, move to: [Task title]

   **Actions**:
   - To complete a task: "Mark task_abc123 as done"
   - To update priority: "Change task_def456 to P0"
   - To see task details: "Show task task_ghi789"
   ```

#### List All Tasks

When user says "show my tasks" or "list tasks":

1. **Fetch and display**:
   ```markdown
   # Your Tasks ([N] open)

   ## By Priority

   ### P0 (Critical) — [N] tasks
   - [Task title] (due: [date], category: [category])

   ### P1 (High) — [N] tasks
   - [Task title] (due: [date], category: [category])

   [etc.]

   ## By Category

   ### Work — [N] tasks
   - [List]

   ### Personal — [N] tasks
   - [List]

   [etc.]
   ```

### Updating Tasks

#### Mark as Complete

When user says "complete task [id]" or "mark done":

1. **Fetch task details** for confirmation:
   ```bash
   # Get task list ID
   TASKLIST_ID=$(gog tasks lists --json | jq -r '.tasklists[0].id')

   # Get task details
   gog tasks list "$TASKLIST_ID" --json | jq '.tasks[] | select(.id == "task_abc123")'
   ```

2. **Confirm**:
   ```markdown
   Mark this task as complete?

   **Task**: [title]
   **Priority**: [P1]
   **Due**: [date]

   Reply "yes" to complete.
   ```

3. **Update**:
   ```bash
   # Get task list ID
   TASKLIST_ID=$(gog tasks lists --json | jq -r '.tasklists[0].id')

   # Mark task as done
   gog tasks done "$TASKLIST_ID" task_abc123 --json
   ```

4. **Celebrate**:
   ```markdown
   ✅ **Task Completed!**

   [Task title] is done.

   Remaining open tasks: [N]
   ```

#### Update Priority or Details

When user says "change task [id] to P0" or "update task [id]":

1. **Show current state**
2. **Confirm changes**
3. **Update** (Note: GOG CLI doesn't support direct priority updates. Use task notes):
   ```bash
   # Get task list ID
   TASKLIST_ID=$(gog tasks lists --json | jq -r '.tasklists[0].id')

   # Update task with priority in notes
   # Note: v0.9.0 requires using patch or updating the task with new notes
   # Priority and category should be tracked in the notes field
   # Example: gog tasks patch "$TASKLIST_ID" task_abc123 --notes "[P0] Updated task description"
   ```

   **Note**: Priority and category updates may require updating the task's notes field to include priority markers like `[P0]`, `[Work]`, etc.

#### Delete Task

When user says "delete task [id]":

1. **⚠️  Warning**:
   ```markdown
   ⚠️  **Delete Task?**

   This will permanently delete:

   **Task**: [title]
   **Priority**: [P1]
   **Created**: [date]

   This cannot be undone. Are you sure? Reply "yes, delete" to confirm.
   ```

2. **Only delete with explicit confirmation**: "yes, delete" or "delete it"

3. **Delete**:
   ```bash
   # Get task list ID
   TASKLIST_ID=$(gog tasks lists --json | jq -r '.tasklists[0].id')

   # Delete task
   gog tasks delete "$TASKLIST_ID" task_abc123 --json
   ```

## Output Format (Strict)

### Task Creation Confirmation

```markdown
✅ **Task Created**

Task ID: [task_id]
Title: [title]
Priority: [P0/P1/P2/P3]
Category: [category]
Due: [date or "Not set"]
```

### Daily Review Structure

```markdown
# Daily Task Review — [Date]

## 🔥 Top 5 Tasks for Today
[Prioritized list with IDs]

## ⚠️  Overdue Tasks ([N] total)
[List with context]

## 🚧 Blocked / Waiting on Others ([N] total)
[List with blocker info]

## 📅 This Week (Non-urgent)
[P2/P3 tasks due this week]

---

**Suggested Focus**: [Ordered recommendations]

**Actions**: [Next step options]
```

### Task List Format

```markdown
# Your Tasks ([N] open)

## By Priority
[Grouped by P0/P1/P2/P3]

## By Category
[Grouped by Work/Personal/Errands/Admin]
```

## Examples

### Example 1: Create Task from Email

**User**: "Create a task for email msg_abc123"

**Assistant**:
```
[Fetches email...]

## Proposed Task

**Title**: Review Q2 contract proposal
**Description**: Legal team needs feedback on vendor contract by Friday. Check sections 3.2 (payment terms) and 5.1 (liability).
**Priority**: P1 (High) — Rationale: Deadline in 2 days, blocking legal team
**Category**: Work
**Due date**: 2026-01-31 (Friday)
**Source**: Email from legal@company.com on 2026-01-28

Does this look correct? Any adjustments?
```

**User**: "Looks good"

**Assistant**:
```
Ready to create this task?
```

**User**: "Yes"

**Assistant**:
```
[Creates task...]

✅ **Task Created**

Task ID: task_xyz789
Title: Review Q2 contract proposal
Priority: P1
Due: 2026-01-31

You now have [N] open tasks. Run "task review" to see your daily priorities.
```

### Example 2: Daily Task Review

**User**: "What should I focus on today?"

**Assistant**:
```
Let me review your tasks for today.

[Fetches tasks...]

# Daily Task Review — Tuesday, January 28

## 🔥 Top 5 Tasks for Today

1. **Budget approval - sign off by noon** (P0, due today)
   - Category: Work
   - Details: Finance needs approval for Q2 budget allocation
   - Task ID: task_aaa111

2. **Prepare client demo slides** (P1, due tomorrow)
   - Category: Work
   - Details: Acme Corp demo at 2pm Wednesday
   - Task ID: task_bbb222

3. **Code review for authentication PR** (P1, due today)
   - Category: Work
   - Details: PR #456 blocking deployment
   - Task ID: task_ccc333

4. **Schedule dentist appointment** (P2, due this week)
   - Category: Errands
   - Details: Overdue for cleaning, need to call
   - Task ID: task_ddd444

5. **Review team feedback doc** (P2, due Friday)
   - Category: Work
   - Details: Performance review cycle input
   - Task ID: task_eee555

## ⚠️  Overdue Tasks (1 total)

- **Submit expense report** (P2, due last Friday)
  - Category: Admin
  - Context: Waiting for receipt from vendor
  - Task ID: task_fff666

## 🚧 Blocked / Waiting on Others (2 total)

- **Finalize hiring decision** (P1)
  - Blocked by: Waiting for reference checks from HR
  - Task ID: task_ggg777

- **Deploy new feature** (P1)
  - Blocked by: Waiting for security review completion
  - Task ID: task_hhh888

---

**Suggested Focus**:
1. Start with: Budget approval (P0, hard deadline at noon)
2. Then tackle: Code review (blocking team)
3. If time: Client demo slides (important for tomorrow)

**Actions**:
- To complete a task: "Mark task_aaa111 as done"
- To update priority: "Change task_ddd444 to P3"
- To see task details: "Show task task_bbb222"

Which task would you like to start with?
```

### Example 3: Quick Task Creation

**User**: "Add a task to call vendor about invoice, high priority, due Friday"

**Assistant**:
```
## Proposed Task

**Title**: Call vendor about invoice
**Priority**: P1 (High)
**Category**: Work (or Errands? Let me know)
**Due date**: 2026-01-31 (Friday)

Ready to create this task?
```

**User**: "Yes, make it Admin category"

**Assistant**:
```
[Creates task with category: Admin...]

✅ **Task Created**

Task ID: task_ijk012
Title: Call vendor about invoice
Priority: P1
Category: Admin
Due: 2026-01-31
```

## Failure Modes / Troubleshooting

### Cannot Determine Priority

**Symptom**: Unclear whether task is P0, P1, P2, or P3

**Resolution**:
1. Ask directly: "Is this urgent (P0/P1) or can it wait (P2/P3)?"
2. Provide examples: "P0 = must do today, P1 = this week, P2 = this month, P3 = someday"
3. Default to P2 if truly uncertain and user doesn't clarify

### Task from Email Missing Due Date

**Symptom**: Email doesn't mention when task is due

**Resolution**:
1. Check for implicit cues: "by EOD", "before the meeting", etc.
2. Ask user: "When does this need to be done?"
3. If no deadline, leave due date empty or set far in future (30 days)

### Too Many Open Tasks

**Symptom**: User has 100+ open tasks, daily review is overwhelming

**Resolution**:
1. Filter aggressively: Show only P0/P1 or only tasks due this week
2. Suggest: "You have many open tasks. Let's focus on top priorities only. Want to archive completed or low-priority tasks?"
3. Help user triage: "Let's do a batch review of P3 tasks—any we can delete or defer?"

### Task Already Exists (Duplicate)

**Symptom**: User tries to create task that seems duplicate

**Resolution**:
1. Check existing tasks for similar titles
2. Warn: "You already have a similar task: '[Title]' (task_xxx). Create anyway?"
3. If confirmed, create as new task

### GOG Not Configured

**Symptom**: Dynamic context shows `GOG_NOT_CONFIGURED`

**Resolution**:
1. Inform: "GOG CLI is not configured. See: skills/gog/_shared/references/gog-interface.md"
2. Suggest: "Run `gog auth login` to authenticate"
3. Offer: "I can still help you plan tasks manually (without saving to GOG)"

## Safety Rules

1. **Confirmation for creates/deletes** - Always confirm before creating or deleting tasks
2. **No auto-completion** - Don't mark tasks done without explicit user instruction
3. **Preserve context** - When creating tasks from emails, always link back (related_email_id)
4. **Priority inflation prevention** - Don't mark everything P0/P1; use full range
5. **Privacy** - Don't include sensitive details in task titles (visible in list views)

## Safe Test

To safely test this skill using only `user@example.com`:

**Test 1: Create and Complete Task (Safe)**

In Claude Code:
1. Load gog-tasks skill
2. Say: "Create a task: Test task for GOG, priority P2, category Personal, due tomorrow"
3. Confirm creation
4. Verify task is created via:
   ```bash
   TASKLIST_ID=$(gog tasks lists --json | jq -r '.tasklists[0].id')
   gog tasks list "$TASKLIST_ID" --json
   ```
5. Say: "Mark that task as done"
6. Confirm completion
7. Verify task is completed

**Test 2: Daily Review (Read-Only, Safe)**

1. Say: "Task review" or "What should I do today?"
2. Verify output includes:
   - Top 5 tasks section
   - Overdue section (if any)
   - Blocked section (if any)
   - Suggested focus
3. Confirm no tasks are auto-completed or modified

**Test 3: Create Task from Email (Safe)**

1. Get an email ID from your inbox
2. Say: "Create a task for email [id]"
3. Review proposed task
4. Confirm creation
5. Verify task links back to email (related_email_id field)

See `skills/gog/_shared/references/testing.md` for complete test plan.

## Notes

- This skill integrates with:
  - `gog-email-triage`: Often creates tasks for action-required emails
  - `gog-email-draft`: Task notes can inform email replies
  - `gog-calendar`: Tasks may become calendar events
  - `gog-followups`: Completed tasks may spawn follow-ups

- Consider creating task templates for recurring tasks (weekly reports, monthly reviews)

- For large projects, break into multiple tasks with clear dependencies

- Use tags (if GOG supports) for additional organization beyond categories

- Daily review is most effective when done at consistent time each day (morning standup with yourself)
