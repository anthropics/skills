---
name: gog-email-send
description: Send email messages with explicit user confirmation. Requires the exact confirmation string "YES, SEND" before executing send operations. Logs all sends to audit trail. Use ONLY when user explicitly confirms they want to send an email, never auto-invoke. This is a critical write operation requiring human approval.
compatibility: Requires gog CLI tool with email send permissions
metadata:
  author: gog-skills
  version: "1.0"
  disable-model-invocation: true
  requires-explicit-confirmation: true
allowed-tools: Bash(gog:*) Read
---

# Email Sending with Confirmation

**⚠️  CRITICAL: This skill sends emails. It MUST NOT be invoked without explicit user confirmation.**

Send emails only after receiving the exact confirmation string: **"YES, SEND"**

## When to Use

Use this skill **ONLY** when:
- User has reviewed a draft and explicitly confirms they want to send it
- User provides the confirmation string "YES, SEND" in their message
- All draft content has been approved by the user

**NEVER** use this skill:
- Automatically after drafting an email
- Based on implied intent ("sounds good", "ok", "sure")
- Without showing the user exactly what will be sent
- Without receiving "YES, SEND" confirmation

## Confirmation Requirements

### The ONLY Acceptable Confirmation

User MUST type exactly: **"YES, SEND"**

**Acceptable variations** (all must include "YES, SEND"):
- "YES, SEND this email"
- "YES, SEND it"
- "YES, SEND the draft"
- "Confirmed. YES, SEND"

**NOT acceptable**:
- "Yes" / "OK" / "Sure" / "Go ahead" / "Send it"
- "Looks good, send it"
- "Please send"
- Any paraphrase that doesn't include the exact phrase "YES, SEND"

## Workflow

### Step 1: Verify Confirmation String

Before ANY sending operation, check:

```
Does the user's message contain the EXACT string "YES, SEND"?
  - YES → Proceed to Step 2
  - NO → STOP and request confirmation
```

If confirmation is missing, respond:

```markdown
⚠️  **Confirmation Required**

To send this email, please confirm by typing exactly:

**YES, SEND**

I need this explicit confirmation to ensure you've reviewed the email and want it sent.

**Reminder**: This will send email to:
- [List recipients]
- Subject: [Subject line]
```

**STOP HERE.** Do not proceed until confirmation is received.

### Step 2: Display Final Summary

Show the user exactly what will be sent:

```markdown
📧 **Ready to Send**

**From**: [Your email address, if known]
**To**: [recipient1@example.com, recipient2@example.com]
**CC**: [cc recipients, if any]
**Subject**: [Subject line]

**Body**:
```
[First 200 characters of body...]
[Body continues for N more characters...]
```

**Attachments**: [List attachments if any, or "None"]

---

Is this correct? If yes, I'll send it now.
```

### Step 3: Execute Send

Determine send method:

**Option A: Send existing draft**

If user has a draft_id:

```bash
gog gmail drafts send <draft_id> --json
```

**Option B: Direct send**

If composing directly (less common):

```bash
# Save body to temp file
cat > /tmp/email_body_$$.txt << 'EOF'
Email body content
EOF

gog gmail send \
  --to "recipient1@example.com,recipient2@example.com" \
  --cc "cc@example.com" \
  --subject "Subject line" \
  --body /tmp/email_body_$$.txt \
  --json

# Clean up temp file
rm /tmp/email_body_$$.txt
```

### Step 4: Log to Audit Trail

Immediately after sending (success or failure), log the action:

```bash
# Source logging utility
source "$(dirname "$0")/../../_shared/scripts/log.sh"

# Log successful send
log_action "gog-email-send" "email-send" "success" "$MESSAGE_ID" \
  "{\"to\":[\"recipient@example.com\"],\"subject\":\"$SUBJECT\",\"confirmation\":\"YES, SEND\"}"

# OR log failed send
log_action "gog-email-send" "email-send" "failure" "" \
  "{\"to\":[\"recipient@example.com\"],\"subject\":\"$SUBJECT\",\"error\":\"$ERROR_MSG\"}"
```

Audit log entry should include:
- Timestamp (automatic)
- Skill name: "gog-email-send"
- Action: "email-send"
- Status: "success" or "failure"
- Entity ID: message_id (if successful)
- Details: to addresses, subject, confirmation string

### Step 5: Confirm Completion

**If successful:**

```markdown
✅ **Email Sent Successfully**

Message ID: msg_abc123
Sent at: [timestamp]
Recipients: [list]

The email has been sent and logged to your audit trail.

Next steps:
- Track response with follow-up? (gog-followups skill)
- Send another email?
```

**If failed:**

```markdown
❌ **Send Failed**

Error: [Error message from GOG]

The email was NOT sent. Common issues:
- Authentication expired (run: gog auth login)
- Invalid recipient email address
- Network connectivity issues
- Insufficient permissions

Would you like to:
- Retry sending?
- Save as draft for later?
- Edit the email?
```

## Output Format (Strict)

### Before Sending (Awaiting Confirmation)

```markdown
⚠️  **Confirmation Required**

To send this email, please type: **YES, SEND**

**Email Summary**:
- To: [recipients]
- Subject: [subject]
- Body: [snippet...]

I'm waiting for your explicit confirmation before sending.
```

### After Sending (Success)

```markdown
✅ **Email Sent**

Message ID: [msg_id]
Recipients: [list]
Timestamp: [ISO8601]

Logged to: ~/.gog-assistant/audit.log
```

### After Sending (Failure)

```markdown
❌ **Send Failed**

Error: [error message]

The email was NOT sent. [Troubleshooting guidance]
```

## Examples

### Example 1: Send Draft (Correct Flow)

**User**: "I've reviewed the draft. YES, SEND"

**Assistant**:
```
[Confirmation string detected: "YES, SEND" ✓]

📧 **Ready to Send**

**To**: client@acme.com
**Subject**: Re: Q2 Proposal

**Body**:
```
Hi Sarah,

Thank you for your patience. I've reviewed the Q2 proposal and have a few questions...
```
[287 more characters]
```

Sending now...

[Executes: gog gmail drafts send draft_abc123 --json]
[Logs to audit trail]

✅ **Email Sent Successfully**

Message ID: msg_xyz789
Sent at: 2026-01-28T15:30:00Z
Recipients: client@acme.com

The email has been sent and logged to your audit trail.

Would you like to set up a follow-up reminder for this email?
```

### Example 2: User Doesn't Confirm (Correct Block)

**User**: "Looks good, please send it"

**Assistant**:
```
⚠️  **Confirmation Required**

To send this email, please confirm by typing exactly:

**YES, SEND**

I need this explicit confirmation to ensure you've reviewed the email and want it sent.

**Reminder**: This will send email to:
- client@acme.com
- Subject: Re: Q2 Proposal
```

[STOPS HERE. Does not send.]

### Example 3: Send Fails

**User**: "YES, SEND"

**Assistant**:
```
[Confirmation string detected: "YES, SEND" ✓]

📧 **Ready to Send**

[Displays summary...]

Sending now...

[Executes: gog gmail drafts send draft_abc123 --json]

❌ **Send Failed**

Error: Authentication token expired

The email was NOT sent.

Fix: Run `gog auth login` to re-authenticate, then try again.

Would you like me to save this draft so you can send it after re-authenticating?
```

### Example 4: Testing Confirmation Blocking

**User**: "Send the draft to the test address"

**Assistant**:
```
⚠️  **Confirmation Required**

To send this email, please confirm by typing exactly:

**YES, SEND**

I need this explicit confirmation before sending any email.

**Email Summary**:
- To: test@example.com
- Subject: [subject]
- Body: [snippet]

Please review the email details above and confirm if you want to proceed.
```

[Does NOT send without "YES, SEND"]

## Failure Modes / Troubleshooting

### User Forgets Confirmation String

**Symptom**: User says "send it" or "go ahead" without "YES, SEND"

**Resolution**:
1. DO NOT send
2. Remind user of exact confirmation string required
3. Explain: "For safety, I need you to type 'YES, SEND' exactly"
4. Wait for proper confirmation

### Authentication Expired

**Symptom**: `gog email send` returns authentication error

**Resolution**:
1. Inform user: "Authentication expired. Run: gog auth login"
2. Offer: "Would you like me to save this as a draft so you can send it after re-authenticating?"
3. If user confirms, save draft and provide draft_id

### Invalid Recipient

**Symptom**: Error about invalid email address format

**Resolution**:
1. Identify which recipient address is invalid
2. Ask user: "The email address [X] appears invalid. Please provide a corrected address."
3. Update draft with corrected address
4. Request confirmation again before sending

### Network Failure

**Symptom**: Timeout or network error during send

**Resolution**:
1. Inform user: "Network error during send. The email may or may not have been sent."
2. Check sent folder: `gog gmail search "in:sent" --max 1`
3. If found, confirm: "Email was sent successfully despite error"
4. If not found, offer: "Would you like to retry?"

### Audit Log Write Failure

**Symptom**: Email sent but logging fails

**Resolution**:
1. Prioritize: Email was sent (user is informed)
2. Log error: Write to stderr about audit log failure
3. Manual log entry: Provide command for user to manually log:
   ```
   echo '{"timestamp":"...","skill":"gog-email-send","action":"email-send","status":"success","entity_id":"msg_xyz","details":{...}}' >> ~/.gog-assistant/audit.log
   ```

## Safety Rules

1. **"YES, SEND" is mandatory** - No exceptions, no paraphrases, no implied consent
2. **Always show what will be sent** - Complete summary before execution
3. **Log every send attempt** - Success and failure both logged
4. **Never auto-send** - Even if previous draft was approved, require fresh confirmation for each send
5. **Privacy in logs** - Log metadata (recipients, subject), not full body content
6. **Fail safe** - If any doubt about confirmation, DO NOT SEND

## Safe Test

To safely test this skill using only `user@example.com`:

**Test 1: Confirmation Blocking (Always Safe)**

In Claude Code:
1. Load gog-email-send skill
2. Create a draft to self via gog-email-draft skill
3. Say: "Send this draft" (without "YES, SEND")
4. **Expected**: Skill REFUSES and requests "YES, SEND" confirmation
5. **Verify**: No email is sent

**Test 2: Successful Send to Self (Safe)**

1. Create a draft to user@example.com with subject "[TEST] GOG Send Test"
2. Say: "YES, SEND"
3. **Expected**: Skill sends email to self
4. **Verify**:
   - Email arrives in your inbox
   - Audit log contains entry: `~/.gog-assistant/audit.log`
   - Entry includes: timestamp, skill, action, status=success, recipients

**Test 3: Failed Send (Safe)**

1. Create a draft to invalid@invalid (invalid address)
2. Say: "YES, SEND"
3. **Expected**: Send fails with error about invalid recipient
4. **Verify**:
   - No email sent
   - Error message displayed to user
   - Audit log contains entry with status=failure

See `skills/gog/_shared/references/testing.md` for complete test plan.

## Notes

- This skill integrates with:
  - `gog-email-draft`: Typically invoked after draft is created
  - `gog-followups`: Can suggest adding follow-up tracking after send
  - `gog-tasks`: Can create task for "follow up in N days"

- **Why "YES, SEND" exactly?**
  - Distinctive phrase unlikely to occur accidentally
  - Requires user to consciously type it (not auto-complete)
  - Clear signal of intent
  - Easy to search in conversation logs

- **Audit log importance**:
  - Required for compliance and accountability
  - Helps debug "did this email actually send?" questions
  - Provides history for follow-up tracking
  - Can be used to generate reports or analytics

- Consider adding to audit log:
  - Draft iterations (how many times edited before sending)
  - Time from draft creation to send
  - Thread context (was this a reply?)

- For production use, consider:
  - Rate limiting (prevent accidental mass sends)
  - Undo/recall within 30 seconds
  - Preview in rendered HTML (not just plain text)
  - Spellcheck pass before sending
