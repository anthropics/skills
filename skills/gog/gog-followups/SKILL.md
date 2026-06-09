---
name: gog-followups
description: Track follow-ups from sent emails, detect stale threads, and generate reminder drafts. Maintains local store of pending follow-ups with nudge dates. Identifies emails awaiting responses and suggests gentle reminder messages. Use when user wants to track responses, follow up on sent emails, or review what's waiting for replies. Requires confirmation before updating follow-up store.
compatibility: Requires gog CLI tool with email access
metadata:
  author: gog-skills
  version: "1.0"
allowed-tools: Bash(gog:*) Read Write
---

# Follow-up & Nudge Tracking

Never lose track of emails awaiting responses. Track follow-ups, detect stale threads, and generate timely reminders.

## When to Use

Use this skill when:
- User wants to "track follow-up" for a sent email
- User asks "what emails am I waiting on"
- User mentions "check pending follow-ups"
- User wants to "send a reminder" or "nudge [person]"
- User says "review stale threads"

## Follow-up Store

Follow-ups are tracked in a local JSON file:

```
~/.gog-assistant/followups.json
```

**Structure**:
```json
[
  {
    "id": "followup_001",
    "email_id": "msg_abc123",
    "thread_id": "thread_xyz",
    "person": "client@acme.com",
    "topic": "Q2 pricing proposal",
    "context": "Sent proposal on Jan 20, they said they'd review by end of week",
    "last_touch": "2026-01-20T16:00:00Z",
    "next_nudge_date": "2026-01-30",
    "nudge_count": 0,
    "status": "pending",
    "priority": "high",
    "created_at": "2026-01-20T16:05:00Z"
  }
]
```

**Dynamic Context** (if file exists):
```
!`cat ~/.gog-assistant/followups.json 2>/dev/null || echo "[]"`
```

## Workflow

### Adding Follow-up Tracking

When user says "track follow-up for email [id]" or "remind me to follow up with [person]":

1. **Fetch email if ID provided**:
   ```bash
   gog gmail get <email_id> --json
   ```

2. **Extract follow-up details**:
   - Person: Primary recipient (or user specifies)
   - Topic: Email subject
   - Last touch: Email send date
   - Context: Key points from email

3. **Ask for follow-up parameters**:
   ```markdown
   Let me set up follow-up tracking. A few questions:

   1. **Who are you waiting to hear from?** [Extracted: client@acme.com]
   2. **What's this about?** [Extracted: Q2 pricing proposal]
   3. **When should I remind you?**
      - In 3 days (standard)
      - In 1 week
      - Custom date
   4. **Priority**: High, Medium, or Low?
   5. **Any context?** Brief note about what you're waiting for.
   ```

4. **Present proposed follow-up**:
   ```markdown
   ## Proposed Follow-up

   **Person**: client@acme.com (John Doe)
   **Topic**: Q2 pricing proposal
   **Context**: Sent detailed proposal on Jan 20, awaiting their review and feedback
   **Last contact**: January 20, 2026
   **Next nudge**: January 30, 2026 (10 days from now)
   **Priority**: High
   **Email**: msg_abc123

   Does this look correct?
   ```

5. **Request confirmation**: "Ready to add this follow-up?"

6. **Add to store** when user confirms:
   ```bash
   # Read existing store
   STORE=~/.gog-assistant/followups.json
   if [ ! -f "$STORE" ]; then
     echo "[]" > "$STORE"
     chmod 600 "$STORE"
   fi

   # Generate new follow-up entry
   NEW_ENTRY=$(jq -n \
     --arg id "followup_$(date +%s)" \
     --arg email_id "msg_abc123" \
     --arg person "client@acme.com" \
     --arg topic "Q2 pricing proposal" \
     --arg context "Sent proposal..." \
     --arg last_touch "2026-01-20T16:00:00Z" \
     --arg nudge_date "2026-01-30" \
     --arg status "pending" \
     --arg priority "high" \
     --arg created "2026-01-20T16:05:00Z" \
     '{id:$id, email_id:$email_id, person:$person, topic:$topic, context:$context, last_touch:$last_touch, next_nudge_date:$nudge_date, nudge_count:0, status:$status, priority:$priority, created_at:$created}')

   # Append to store
   jq ". + [$NEW_ENTRY]" "$STORE" > "$STORE.tmp" && mv "$STORE.tmp" "$STORE"
   ```

7. **Confirm addition**:
   ```markdown
   ✅ **Follow-up Added**

   Tracking ID: followup_001
   Person: client@acme.com
   Next reminder: January 30, 2026

   I'll remind you to follow up in 10 days.

   View all follow-ups: "Show pending follow-ups"
   ```

### Reviewing Follow-ups

#### Show All Pending

When user says "show pending follow-ups" or "what am I waiting on":

1. **Read follow-up store**:
   ```bash
   jq '.[] | select(.status == "pending")' ~/.gog-assistant/followups.json
   ```

2. **Present formatted list**:
   ```markdown
   # Pending Follow-ups ([N] total)

   ## High Priority

   1. **Q2 pricing proposal** → client@acme.com
      - Last contact: Jan 20 (8 days ago)
      - Next nudge: Jan 30 (in 2 days)
      - Context: Awaiting review and feedback on proposal
      - Email: msg_abc123

   2. **Contract review** → legal@vendor.com
      - Last contact: Jan 18 (10 days ago)
      - Next nudge: **OVERDUE** (was Jan 25)
      - Context: Sent redlined contract, need their signoff
      - Email: msg_def456

   ## Medium Priority

   3. **Feature request feedback** → product@company.com
      - Last contact: Jan 22 (6 days ago)
      - Next nudge: Feb 1 (in 4 days)
      - Context: Asked about roadmap for feature X
      - Email: msg_ghi789

   ---

   **Summary**:
   - Total pending: 3
   - Overdue: 1 (legal@vendor.com)
   - Due this week: 1 (client@acme.com)

   **Suggested actions**:
   - Send nudge to legal@vendor.com (overdue)
   - Prepare nudge draft for client@acme.com (due soon)
   ```

#### Show Follow-ups Due This Week

When user says "review follow-ups due this week":

1. **Filter by next_nudge_date**:
   ```bash
   TODAY=$(date +%Y-%m-%d)
   WEEK_FROM_NOW=$(date -v+7d +%Y-%m-%d)
   jq --arg today "$TODAY" --arg week "$WEEK_FROM_NOW" \
     '.[] | select(.status == "pending" and .next_nudge_date >= $today and .next_nudge_date <= $week)' \
     ~/.gog-assistant/followups.json
   ```

2. **Present list** (similar format as above)

### Generating Nudge Drafts

When user says "generate nudge for [person/topic]" or "draft follow-up for [id]":

1. **Identify follow-up**:
   - By person: `jq '.[] | select(.person == "client@acme.com")'`
   - By topic: `jq '.[] | select(.topic | contains("pricing"))'`
   - By ID: `jq '.[] | select(.id == "followup_001")'`

2. **Fetch original email thread**:
   ```bash
   gog gmail get <email_id> --json
   # Or for full thread context:
   gog gmail thread get <thread_id> --json
   ```

3. **Analyze timing**:
   - Days since last contact
   - Nudge count (first reminder vs follow-up)
   - Priority/urgency

4. **Draft nudge email** with appropriate tone:

   **First nudge (nudge_count == 0)**: Gentle, assumes they're busy
   **Second nudge (nudge_count == 1)**: Slightly more direct, mentions timing
   **Third+ nudge (nudge_count >= 2)**: Direct but polite, offers to clarify

5. **Present draft variants**:
   ```markdown
   # Nudge Draft: Q2 Pricing Proposal

   **To**: client@acme.com
   **Subject**: Re: Q2 Pricing Proposal

   ---

   ## Variant A: Gentle (Recommended for first nudge)

   Hi John,

   I wanted to follow up on the Q2 pricing proposal I sent over on January 20th. I know you're busy, so no rush—just wanted to make sure it didn't get lost in the shuffle.

   If you have any questions or need clarification on any part of the proposal, I'm happy to jump on a quick call.

   Thanks!

   ---

   ## Variant B: Direct

   Hi John,

   Following up on the Q2 pricing proposal from January 20th. We're starting to finalize our Q2 budget, so it would be helpful to hear your thoughts when you have a chance.

   Do you have an ETA on when you might be able to review it?

   Thanks!

   ---

   ## Context

   - **Original sent**: Jan 20 (10 days ago)
   - **Nudge count**: 0 (this is first reminder)
   - **Priority**: High
   - **Suggested tone**: Gentle (they have reasonable time to respond)

   ---

   **Next steps**:
   - Edit as needed
   - Say "Save as draft" to create draft
   - Or say "Send this nudge" (requires "YES, SEND" confirmation)
   ```

6. **After draft is approved**:
   ```markdown
   Should I:
   1. Save this as a draft (you send it when ready)
   2. Send it now (requires "YES, SEND" confirmation)
   3. Update follow-up tracking (mark as nudged, set next reminder)
   ```

7. **Update follow-up store**:
   ```bash
   # Increment nudge_count, update last_touch, set new next_nudge_date
   jq '(.[] | select(.id == "followup_001") | .nudge_count) += 1 |
       (.[] | select(.id == "followup_001") | .last_touch) = "2026-01-30T10:00:00Z" |
       (.[] | select(.id == "followup_001") | .next_nudge_date) = "2026-02-07" |
       (.[] | select(.id == "followup_001") | .status) = "contacted"' \
     ~/.gog-assistant/followups.json > ~/.gog-assistant/followups.json.tmp
   mv ~/.gog-assistant/followups.json.tmp ~/.gog-assistant/followups.json
   ```

### Closing Follow-ups

When user receives response or no longer needs follow-up:

**User**: "Close follow-up for client@acme.com" or "Mark [id] as responded"

1. **Identify follow-up**
2. **Confirm closure**:
   ```markdown
   Close this follow-up?

   **Topic**: Q2 pricing proposal
   **Person**: client@acme.com
   **Reason**: [Ask: "Did they respond, or no longer needed?"]

   Reply "yes, close" to confirm.
   ```

3. **Update status**:
   ```bash
   jq '(.[] | select(.id == "followup_001") | .status) = "closed" |
       (.[] | select(.id == "followup_001") | .closed_at) = "2026-01-31T14:00:00Z"' \
     ~/.gog-assistant/followups.json > ~/.gog-assistant/followups.json.tmp
   mv ~/.gog-assistant/followups.json.tmp ~/.gog-assistant/followups.json
   ```

4. **Confirm**:
   ```markdown
   ✅ **Follow-up Closed**

   Topic: Q2 pricing proposal
   Person: client@acme.com
   Closed: Jan 31, 2026

   Remaining pending follow-ups: [N]
   ```

## Output Format (Strict)

### Follow-up List

```markdown
# Pending Follow-ups ([N] total)

## [Priority]

[Number]. **[Topic]** → [Person]
   - Last contact: [Date] ([X days ago])
   - Next nudge: [Date] ([in X days | OVERDUE])
   - Context: [Brief context]
   - Email: [msg_id]

---

**Summary**:
- Total pending: [N]
- Overdue: [N]
- Due this week: [N]

**Suggested actions**: [What to do next]
```

### Nudge Draft

```markdown
# Nudge Draft: [Topic]

**To**: [person]
**Subject**: Re: [topic]

---

## Variant A: [Tone]
[Draft text]

## Variant B: [Tone]
[Draft text]

---

## Context
- **Original sent**: [Date] ([X days ago])
- **Nudge count**: [N]
- **Priority**: [High/Medium/Low]
- **Suggested tone**: [Rationale]

---

**Next steps**: [Options for saving/sending]
```

## Examples

### Example 1: Add Follow-up

**User**: "Track follow-up for email msg_abc123"

**Assistant**:
```
[Fetches email...]

Let me set up follow-up tracking for this email.

**Email**: Q2 Pricing Proposal
**Sent to**: client@acme.com (John Doe)
**Sent on**: January 20, 2026

A few questions:

1. When should I remind you to follow up?
   - In 3 days (Jan 23)
   - In 1 week (Jan 27)
   - In 2 weeks (Feb 3)
   - Custom date

2. Priority? (High/Medium/Low)

3. Any context to note?
```

**User**: "1 week, high priority, waiting for their review and decision"

**Assistant**:
```
## Proposed Follow-up

**Person**: client@acme.com (John Doe)
**Topic**: Q2 Pricing Proposal
**Context**: Sent pricing proposal on Jan 20, awaiting their review and decision
**Last contact**: January 20, 2026
**Next nudge**: January 27, 2026 (7 days)
**Priority**: High
**Email**: msg_abc123

Ready to add this follow-up?
```

**User**: "Yes"

**Assistant**:
```
✅ **Follow-up Added**

Tracking ID: followup_001
Person: client@acme.com
Next reminder: January 27, 2026

I'll remind you to follow up in 7 days. You can check status anytime with "show pending follow-ups".
```

### Example 2: Review Pending Follow-ups

**User**: "What am I waiting on?"

**Assistant**:
```
# Pending Follow-ups (3 total)

## High Priority

1. **Q2 pricing proposal** → client@acme.com
   - Last contact: Jan 20 (10 days ago)
   - Next nudge: Jan 30 (TODAY)
   - Context: Awaiting review and decision on proposal
   - Email: msg_abc123

2. **Contract signoff** → legal@vendor.com
   - Last contact: Jan 15 (15 days ago)
   - Next nudge: **OVERDUE** (was Jan 25)
   - Context: Sent redlined contract, awaiting signature
   - Email: msg_def456

## Medium Priority

3. **Feature roadmap inquiry** → product@company.com
   - Last contact: Jan 22 (8 days ago)
   - Next nudge: Feb 5 (in 6 days)
   - Context: Asked about timeline for feature X
   - Email: msg_ghi789

---

**Summary**:
- Total pending: 3
- Overdue: 1 (legal@vendor.com)
- Due today: 1 (client@acme.com)

**Suggested actions**:
- Send nudge to legal@vendor.com (overdue by 5 days)
- Send nudge to client@acme.com (due today)

Want me to draft reminder emails for these?
```

### Example 3: Generate Nudge

**User**: "Draft a follow-up for the pricing proposal"

**Assistant**:
```
[Finds follow-up...]
[Fetches original email...]

# Nudge Draft: Q2 Pricing Proposal

**To**: client@acme.com
**Subject**: Re: Q2 Pricing Proposal

---

## Variant A: Gentle (Recommended)

Hi John,

I wanted to follow up on the Q2 pricing proposal I sent over on January 20th. I know you're busy, so no rush—just wanted to make sure it didn't get lost in your inbox.

If you have any questions or need clarification on any part of the proposal, I'm happy to jump on a quick call to discuss.

Thanks!

---

## Variant B: Direct

Hi John,

Following up on the Q2 pricing proposal from January 20th. We're starting to finalize our Q2 budget planning, so it would be helpful to hear your thoughts when you have a chance.

Do you have an ETA on when you might be able to review it? Happy to clarify anything that's unclear.

Thanks!

---

## Context

- **Original sent**: Jan 20 (10 days ago)
- **Nudge count**: 0 (this is first reminder)
- **Priority**: High
- **Suggested tone**: Gentle (10 days is reasonable response time)

---

**Next steps**:
- Edit as needed
- Say "Save as draft" to create in GOG
- Or "Send this nudge" (requires "YES, SEND")

Which variant do you prefer?
```

## Failure Modes / Troubleshooting

### Follow-up Store Doesn't Exist

**Symptom**: File ~/.gog-assistant/followups.json not found

**Resolution**:
1. This is expected on first use
2. Initialize store:
   ```bash
   mkdir -p ~/.gog-assistant
   echo "[]" > ~/.gog-assistant/followups.json
   chmod 600 ~/.gog-assistant/followups.json
   ```
3. Inform user: "Created follow-up tracking store at ~/.gog-assistant/followups.json"

### Follow-up Store Corrupted

**Symptom**: Invalid JSON in followups.json

**Resolution**:
1. Backup corrupted file:
   ```bash
   cp ~/.gog-assistant/followups.json ~/.gog-assistant/followups.json.backup.$(date +%s)
   ```
2. Attempt to repair with jq
3. If irreparable, warn user: "Follow-up store is corrupted. Backed up to [path]. Starting fresh."
4. Initialize new store

### Cannot Determine When to Nudge

**Symptom**: User doesn't specify nudge date

**Resolution**:
1. Offer defaults based on priority:
   - High: 3-5 days
   - Medium: 7-10 days
   - Low: 14-21 days
2. Explain: "For high-priority emails, 3-7 days is typical. What works for you?"

### Nudge Too Soon

**Symptom**: User tries to set nudge for tomorrow but email was sent today

**Resolution**:
1. Warn: "That's very soon. Give them at least 24-48 hours to respond?"
2. Suggest: "How about [+2 days]?"
3. Allow override if user insists

### Too Many Overdue Follow-ups

**Symptom**: User has 10+ overdue nudges

**Resolution**:
1. Acknowledge: "You have [N] overdue follow-ups. Let's prioritize."
2. Show only highest priority or most overdue
3. Suggest: "Which 2-3 are most important? We can focus on those first."
4. Offer batch nudge: "Want me to draft nudges for all high-priority items?"

## Safety Rules

1. **Confirm before creating follow-ups** - Show proposed tracking before adding
2. **Confirm before updating store** - Any modification requires user approval
3. **Backup store on corruption** - Never delete without backup
4. **Privacy in context** - Don't store sensitive details in follow-up context
5. **Nudge drafts, don't send** - Generate drafts only; use gog-email-send for sending

## Safe Test

To safely test this skill using only `user@example.com`:

**Test 1: Add Follow-up (Safe)**

In Claude Code:
1. Send yourself an email or use existing email ID
2. Load gog-followups skill
3. Say: "Track follow-up for email [id]"
4. Answer prompts (person: user@example.com, nudge: tomorrow)
5. Confirm creation
6. Verify file exists: `cat ~/.gog-assistant/followups.json`
7. Verify JSON is valid: `jq . ~/.gog-assistant/followups.json`

**Test 2: Review Follow-ups (Read-Only, Safe)**

1. Say: "Show pending follow-ups"
2. Verify output lists the follow-up created in Test 1
3. Confirm no modifications made

**Test 3: Generate Nudge Draft (Safe, No Send)**

1. Say: "Draft a follow-up for [person or topic]"
2. Verify draft is generated with both variants
3. Confirm NO email is sent (only draft created)

**Test 4: Close Follow-up (Safe)**

1. Say: "Close follow-up for user@example.com"
2. Confirm closure
3. Verify status updated in store: `jq '.[] | select(.person == "user@example.com") | .status' ~/.gog-assistant/followups.json`

See `skills/gog/_shared/references/testing.md` for complete test plan.

## Notes

- This skill integrates with:
  - `gog-email-triage`: After triage, suggest tracking follow-ups for sent replies
  - `gog-email-draft`: Nudge drafts flow into drafting skill
  - `gog-email-send`: Nudge drafts can be sent via send skill
  - `gog-tasks`: Overdue follow-ups can become tasks

- Follow-up store management:
  - Consider archiving closed follow-ups after 30 days
  - Provide export/backup functionality
  - Add search/filter by date range

- Smart nudge timing:
  - Adjust based on person (executives: longer wait, vendors: shorter)
  - Consider timezone (don't nudge international contacts on weekends)
  - Respect out-of-office replies

- Nudge tone guidance:
  - First nudge: Gentle, assume they're busy
  - Second nudge: More direct, reference timeline
  - Third+ nudge: Direct but polite, offer alternatives (call instead?)

- Future enhancements:
  - Auto-detect responses (read inbox for replies to tracked threads)
  - Suggest follow-up tracking when user sends important emails
  - Weekly digest: "You have [N] follow-ups due this week"
