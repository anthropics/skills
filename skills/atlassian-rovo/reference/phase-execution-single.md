# Phase 2: Execution (Single-Agent Mode) — Detailed Reference

Sequential execution for agents without multi-agent orchestration (Cursor, Cline, Windsurf, etc.).
Same Jira tracking and Confluence updates as multi-agent mode, but one ticket at a time.

For shared protocols (transitions, branch creation, publishing, completing tickets), see [common-patterns.md](common-patterns.md).

## Workflow

Work each child ticket sequentially, respecting dependency order (blocked tickets last).
See [common-patterns.md](common-patterns.md#dependency-ordering) for ordering logic.

For each ticket:

### 1. Start the Ticket

Assign and transition to In Progress. See [common-patterns.md](common-patterns.md#starting-a-ticket).

### 2. Create a Branch (Optional)

If the project has a git repository, create a branch for this ticket.
See [common-patterns.md](common-patterns.md#starting-a-ticket) step 3 for the commands.

### 3. Do the Work

Execute the workstream as described in the ticket.

### 4. Publish Findings

Create a Confluence child page under the plan page.
See [common-patterns.md](common-patterns.md#publishing-findings).

### 5. Complete the Ticket

Add summary comment and transition to Done.
See [common-patterns.md](common-patterns.md#completing-a-ticket).

### 6. Update Progress

Update the Confluence plan page — change the ticket's status in the workstreams table, add a progress log entry.
See [common-patterns.md](common-patterns.md#updating-the-confluence-plan-page).

### 7. Next Ticket

Move to the next ticket in dependency order. Repeat steps 1-6.

## Key Rules

- **Always transition to In Progress** before starting work (not just Done at the end)
- **Always publish findings as child pages** of the plan page
- **Always update the plan page** after completing each ticket
- **Respect dependency order** — don't start a blocked ticket until its blocker is Done
