---
name: gog-email-triage
description: Triage and prioritize inbox emails. Summarize unread messages, classify by urgency and category, propose actions (reply, archive, schedule, create task). Use when user wants to review inbox, process unread emails, or needs help prioritizing messages. Outputs structured summary with top priorities and suggested next actions.
compatibility: Requires gog CLI tool with email access
metadata:
  author: gog-skills
  version: "1.0"
allowed-tools: Bash(gog:*) Read
---

# Email Triage & Prioritization

Efficiently review and prioritize your inbox by classifying emails and suggesting actions.

## When to Use

Use this skill when:
- User wants to "review my inbox" or "check my email"
- User asks to "triage emails" or "prioritize messages"
- User mentions "what's urgent" or "what needs my attention"
- User wants help deciding what to do with emails
- At the start of workday for inbox review

**Important**: This skill is READ-ONLY. It analyzes and proposes actions but NEVER sends, archives, or modifies emails.

## Dynamic Context

The following live data is available:

**Unread emails:**
```
!`gog gmail search "is:unread" --max 25 --json 2>/dev/null || echo "GOG_NOT_CONFIGURED"`
```

## Inputs You Need

Before triaging:
1. **User preferences** (ask if not known):
   - Categories of interest (work vs personal filter)
   - Urgency threshold (show only high/urgent, or include all)
   - Any auto-archive patterns (newsletters, notifications)

2. **Context clues** (extract from conversation):
   - Current projects or priorities
   - Upcoming deadlines
   - People user is waiting to hear from

## Workflow

### Step 1: Fetch Unread Emails

If dynamic context shows `GOG_NOT_CONFIGURED`:
- Inform user that GOG is not configured
- Point to: `skills/gog/_shared/references/gog-interface.md`
- Offer to help with configuration
- STOP here until configured

If email list is empty:
- Inform user: "No unread emails! Inbox Zero achieved."
- Ask if they want to review recent emails instead
- If yes, fetch: `gog gmail search "is:inbox" --max 25 --json`

### Step 2: Analyze Each Email

For each email, determine:

**Urgency Level:**
- **urgent**: Immediate attention required (< 2 hours)
  - Keywords: "urgent", "ASAP", "immediately", "emergency"
  - From: Boss, critical clients, system alerts
  - Context: Blocking your work or others
- **high**: Should respond today
  - Action required by EOD
  - Meeting invitations for soon
  - Client/stakeholder requests
- **medium**: Can respond within 2-3 days
  - FYI with potential follow-up
  - Non-urgent requests
  - Team updates that may need input
- **low**: No time pressure
  - Newsletters, automated reports
  - Social correspondence
  - Informational only

**Category:**
- **action-required**: Needs a decision or action from you
- **fyi**: Informational only, no action needed
- **meeting**: Meeting invitation or scheduling
- **social**: Personal correspondence
- **newsletter**: Automated newsletters/updates
- **spam**: Likely spam or unwanted

**Suggested Action:**
- **reply**: Draft a reply (use gog-email-draft skill)
- **reply-all**: Draft reply-all
- **forward**: Forward to someone else
- **archive**: No action needed, remove from inbox
- **create-task**: Convert to task (use gog-tasks skill)
- **schedule-meeting**: Set up meeting (use gog-calendar skill)
- **block-sender**: Mark as spam/block
- **delete**: Junk, delete immediately

### Step 3: Generate Triage Summary

Output in this format:

```markdown
# Email Triage Summary

📧 **Total Unread**: [N] messages
⚠️  **Urgent**: [N] | 🔴 **High**: [N] | 🟡 **Medium**: [N] | 🟢 **Low**: [N]

## Top 3 Priorities

1. **[Subject]** from [Sender]
   - Urgency: [urgent/high/medium/low]
   - Reason: [1-line rationale]
   - Suggested action: [action]

2. [...]

3. [...]

## All Messages

| ID (last 6) | From | Subject (truncated) | Urgency | Category | Action | Rationale |
|-------------|------|---------------------|---------|----------|--------|-----------|
| abc123 | sender@example.com | Meeting tomorrow? | high | meeting | reply | Needs response by EOD |
| def456 | newsletter@... | Weekly update | low | newsletter | archive | FYI only |
| [...] | [...] | [...] | [...] | [...] | [...] | [...] |

## Suggested Next Actions

- [ ] **Reply to [N] urgent/high priority emails** (IDs: abc123, def456)
- [ ] **Create tasks for [N] action items** (IDs: ghi789)
- [ ] **Schedule meeting for [topic]** (ID: jkl012)
- [ ] **Archive [N] newsletters and FYI messages**
- [ ] **Block [N] spam senders**

---

**Next Steps**:
- To draft a reply: "Draft a reply to [email ID or subject]"
- To create task: "Create a task for [email ID or subject]"
- To schedule meeting: "Schedule meeting about [topic]"
- To see email content: "Show me email [ID]"
```

### Step 4: Offer Follow-Up

After presenting the triage:
- Ask: "Which email would you like to tackle first?"
- Or: "Would you like me to draft replies for the top priorities?"
- Or: "Should I create tasks for the action items?"

**Do NOT** proceed to take actions without user confirmation.

## Output Format (Strict)

The triage summary MUST include:

1. **Header stats**: Total count + urgency breakdown
2. **Top 3 priorities**: Most urgent/important emails with rationale
3. **Complete table**: All emails with classifications
4. **Suggested next actions**: Checklist of proposed actions grouped by type
5. **Next steps prompt**: Clear options for follow-up

**Table columns** (in order):
1. ID (last 6 chars) - for reference
2. From - sender email or name
3. Subject (truncated to ~40 chars)
4. Urgency - urgent/high/medium/low
5. Category - action-required/fyi/meeting/social/newsletter/spam
6. Action - reply/archive/create-task/etc
7. Rationale - 1-line explanation

## Examples

### Example 1: Morning Inbox Review

**User**: "Review my inbox"

**Assistant**:
```
Let me triage your unread emails.

[Fetches emails...]

# Email Triage Summary

📧 **Total Unread**: 12 messages
⚠️  **Urgent**: 1 | 🔴 **High**: 3 | 🟡 **Medium**: 5 | 🟢 **Low**: 3

## Top 3 Priorities

1. **Budget approval needed** from sarah@company.com
   - Urgency: urgent
   - Reason: Blocks Q2 planning, needs approval by noon today
   - Suggested action: reply

2. **Client demo tomorrow** from client@acme.com
   - Urgency: high
   - Reason: Meeting in < 24h, needs confirmation of attendees
   - Suggested action: reply

3. **Code review request** from dev@company.com
   - Urgency: high
   - Reason: Blocking deployment, requested 2 days ago
   - Suggested action: create-task

## All Messages

| ID | From | Subject | Urgency | Category | Action | Rationale |
|----|------|---------|---------|----------|--------|-----------|
| 7a3f2e | sarah@company.com | Budget approval needed | urgent | action-required | reply | Blocks Q2 planning |
| 9b4c1d | client@acme.com | Client demo tomorrow | high | meeting | reply | Needs confirmation |
| 2e8f6a | dev@company.com | Code review request | high | action-required | create-task | Review needed |
| [...] | [...] | [...] | [...] | [...] | [...] | [...] |

## Suggested Next Actions

- [ ] **Reply to 4 urgent/high emails** (IDs: 7a3f2e, 9b4c1d, 5d7e3c, 8f1a9b)
- [ ] **Create task for code review** (ID: 2e8f6a)
- [ ] **Archive 3 newsletters** (IDs: 4c9e2f, 6a3d8b, 1f7c5e)

---

**Next Steps**: Which email would you like to tackle first? I can draft replies for the top priorities or create tasks for follow-up items.
```

### Example 2: Filtered Triage

**User**: "Show me only urgent and high priority emails"

**Assistant**:
```
Let me filter for urgent and high priority emails only.

[Fetches and filters...]

# Email Triage Summary (Urgent + High Only)

📧 **Total Unread**: 12 messages (showing 4 urgent/high)
⚠️  **Urgent**: 1 | 🔴 **High**: 3

## Top Priorities

1. **Budget approval needed** from sarah@company.com
   - Urgency: urgent
   - Action: reply
   [...]

[Table with only urgent/high priority emails]

The remaining 8 emails are medium/low priority. Want to see those too?
```

## Failure Modes / Troubleshooting

### GOG Not Configured

**Symptom**: Dynamic context shows `GOG_NOT_CONFIGURED`

**Resolution**:
1. Inform user: "GOG CLI is not configured. Let me help you set it up."
2. Point to: `skills/gog/_shared/references/gog-interface.md`
3. Suggest: "Run `gog auth login` to authenticate"
4. Do not proceed with triage until configured

### No Unread Emails

**Symptom**: Email list is empty `[]`

**Resolution**:
1. Celebrate: "Inbox Zero! No unread emails."
2. Ask: "Want to review recent emails instead?"
3. If yes, fetch last 25 emails without unread filter

### Invalid JSON from GOG

**Symptom**: `jq parse error` or non-JSON output

**Resolution**:
1. Try without `--json` flag
2. Parse human-readable output (less reliable)
3. Or inform user: "GOG output format unexpected. Please check GOG version."

### Too Many Emails (> 25)

**Symptom**: User has 100+ unread emails

**Resolution**:
1. Inform: "You have [N] unread emails. Showing top 25."
2. Suggest: "Want to filter by sender, date, or keyword?"
3. Or: "Let's focus on urgent/high priority only"
4. Consider batching: "Let's triage in batches of 25"

### Classification Uncertainty

**Symptom**: Can't determine urgency or category from email metadata

**Resolution**:
1. Fetch full email with `gog email get --id <id>`
2. Read first ~200 chars of body for context
3. If still uncertain, default to "medium" urgency and "action-required" category
4. Note in rationale: "Needs review to determine priority"

## Safety Rules

1. **Never send, archive, or delete emails** - This skill is READ-ONLY
2. **Never modify email labels or folders** - Only analyze and propose
3. **Always propose, never execute** - Present options, user decides
4. **Privacy-aware output** - Truncate email subjects in output if they appear sensitive
5. **No automation without consent** - Even for "obvious" spam, ask before suggesting block/delete

## Safe Test

To safely test this skill using only `user@example.com`:

**Read-only test (always safe):**
```bash
gog gmail search "is:unread (to:user@example.com OR from:user@example.com)" --max 10 --json
```

**In Claude Code**:
1. Load the gog-email-triage skill
2. Say: "Triage my inbox"
3. Skill will fetch unread emails
4. Verify output includes:
   - Email count and urgency breakdown
   - Top 3 priorities with rationale
   - Complete table with all emails
   - Suggested next actions checklist
5. Confirm NO emails are sent, archived, or modified

See `skills/gog/_shared/references/testing.md` for complete test plan.

## Notes

- This skill integrates with:
  - `gog-email-draft`: For drafting replies to prioritized emails
  - `gog-tasks`: For converting emails to tasks
  - `gog-calendar`: For scheduling meetings mentioned in emails
  - `gog-followups`: For tracking emails awaiting responses

- Consider user's timezone when assessing urgency (EOD means their EOD)

- If email subject/sender contains obvious credentials or secrets, redact in output

- For recurring newsletters, suggest creating a filter/rule rather than manual archiving
