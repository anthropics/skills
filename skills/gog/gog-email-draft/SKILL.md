---
name: gog-email-draft
description: Draft email replies and compose new messages. Given email ID(s) or message context, generate professional email drafts in user's preferred tone. Offers multiple variants (concise, warmer) and includes assumptions/questions for confirmation. Use when user wants to reply to emails, compose new messages, or needs help with email writing. Does NOT send emails.
compatibility: Requires gog CLI tool with email access
metadata:
  author: gog-skills
  version: "1.0"
allowed-tools: Bash(gog:*) Read
---

# Email Drafting Assistant

Generate professional, context-aware email drafts with tone variants and confirmation prompts.

## When to Use

Use this skill when:
- User wants to "reply to [email]" or "draft a reply"
- User asks to "compose an email to [person]"
- User mentions "write an email about [topic]"
- User provides email ID(s) from triage and wants to respond
- User needs help with email phrasing or tone

**Important**: This skill creates DRAFTS only. It NEVER sends emails. Use `gog-email-send` skill for sending (with explicit confirmation).

## Inputs You Need

Before drafting, gather:

### 1. Email Context (choose one)

**Option A - Reply to existing email(s):**
- Email ID(s) from `gog gmail search` or triage output
- Fetch full email content: `gog gmail get <messageId> --json`

**Option B - Compose new email:**
- Recipient(s): email address(es)
- Subject: what the email is about
- Context: key points to include

### 2. User's Tone Preference

If not previously known, ask:
```
What tone would you like for this email?
- Professional (formal, business-standard)
- Friendly (warm but professional)
- Concise (brief and to-the-point)
- Detailed (thorough, includes context)

Or describe your preferred style.
```

**Remember preference** for future drafts in the session.

### 3. Missing Information

Identify what's needed to draft effectively:
- Specific facts or data to include
- Deadline or timeline to mention
- Attachments to reference
- People to CC
- Action items or next steps

**Ask clarifying questions** before drafting if critical info is missing.

## Workflow

### Step 1: Fetch Original Email (if replying)

For replies:

```bash
gog gmail get <email_id> --json
```

Parse:
- From / To / CC
- Subject
- Body content
- Date
- Thread context

If email has a thread, consider reading previous messages in thread for context.

### Step 2: Identify Required Content

Analyze what the reply should address:

**Questions asked**: Direct questions that need answers
**Action items**: Tasks or requests that need response
**Context needed**: Background or explanation to provide
**Next steps**: Proposed follow-up or timeline
**Tone match**: Match or adjust based on sender's tone

### Step 3: Draft Initial Assumptions

Before drafting, list assumptions being made:

```markdown
## Assumptions

- [Assumption 1: e.g., Budget is approved for this project]
- [Assumption 2: e.g., Timeline of 2 weeks is acceptable]
- [Assumption 3: e.g., Legal review is not required]
- [...]
```

### Step 4: Draft Questions for User

List clarifying questions if any:

```markdown
## Questions to Confirm

1. [Question 1: e.g., Should we include pricing in this email?]
2. [Question 2: e.g., Do you want to propose a specific meeting time?]
3. [Question 3: e.g., Is there a deadline we should mention?]
```

If questions are critical, ask now and wait for answers. If minor, include in output for user to address.

### Step 5: Generate Draft Variants

Create TWO versions:

**Variant A: Concise**
- Brief and to-the-point
- ~3-5 sentences or ~100-150 words
- Covers essentials only
- Good for quick responses

**Variant B: Warmer/Detailed**
- More conversational or thorough
- ~7-10 sentences or ~200-300 words
- Includes context and reasoning
- Good for important stakeholders

### Step 6: Present Drafts

Output in this format:

```markdown
# Email Draft: [Subject]

**To**: [recipient(s)]
**CC**: [if applicable]
**Subject**: [subject line]

---

## Variant A: Concise

[Draft text here]

---

## Variant B: Warmer

[Draft text here]

---

## Assumptions

- [List assumptions made]

## Questions to Confirm

1. [List questions if any]

---

**Next Steps**:
- Edit either variant as needed
- Confirm assumptions are correct
- Answer any questions listed
- When ready: "Send this draft" (will invoke gog-email-send with confirmation)
```

### Step 7: Iterative Refinement

After presenting drafts:
- User may request edits: "Make it more formal" / "Add mention of X"
- User may answer questions: "Yes, include pricing"
- User may choose one variant and refine it

**Iterate** until user is satisfied.

When user approves final draft, offer:
```
Ready to send? Say "Save as draft" to create in GOG, or "Send this email" to proceed with sending (requires explicit confirmation).
```

### Step 8: Save Draft in GOG

When user says "Save as draft" or "Create draft":

```bash
# Create draft body file first
cat > /tmp/draft_body.txt << 'EOF'
[Draft email body content]
EOF

# Create draft
gog gmail drafts create \
  --to "recipient@example.com" \
  --cc "cc@example.com" \
  --subject "Subject line" \
  --body /tmp/draft_body.txt \
  --json

# Clean up temp file
rm /tmp/draft_body.txt
```

**Note**: Reply threading is handled automatically by Gmail when replying to a thread. If creating a standalone draft, omit reply-related flags.

Return draft ID to user:
```
✅ Draft created successfully!
Draft ID: draft_abc123

You can:
- Review it in your email client
- Edit it further there
- Send it via: "Send draft draft_abc123"
```

## Output Format (Strict)

Every draft output MUST include:

1. **Header**: To, CC (if any), Subject
2. **Variant A**: Concise version
3. **Variant B**: Warmer/detailed version
4. **Assumptions**: Bulleted list of assumptions
5. **Questions**: Numbered list (or "None" if all info is clear)
6. **Next steps**: Clear guidance on what to do next

**Email body format**:
- Professional greeting (Hi [Name], / Hello [Name], / [Name],)
- Clear paragraphs with line breaks
- Signature closer (Best, / Thanks, / Regards, / etc.)
- NO signature block (assume GOG or email client adds this)

## Examples

### Example 1: Reply to Meeting Request

**User**: "Draft a reply to email msg_abc123"

**Assistant**:
```
[Fetches email msg_abc123...]

Original email from sarah@company.com:
"Hi, can we schedule a meeting to discuss Q2 budget? I'm available Tuesday or Thursday afternoon."

---

# Email Draft: Re: Q2 Budget Meeting

**To**: sarah@company.com
**Subject**: Re: Q2 Budget Meeting

---

## Variant A: Concise

Hi Sarah,

Tuesday afternoon works for me. How about 2pm? I'll send a calendar invite.

Thanks,

---

## Variant B: Warmer

Hi Sarah,

Thanks for reaching out about the Q2 budget discussion. I'd be happy to meet.

Tuesday afternoon works well for me. Would 2pm work for you? I can send a calendar invite with a Zoom link if that's convenient, or we can meet in person if you prefer.

Looking forward to discussing the budget plans!

Thanks,

---

## Assumptions

- 2pm is a reasonable time for "afternoon"
- Virtual meeting is acceptable (can offer in-person)
- User has authority to discuss Q2 budget

## Questions to Confirm

1. Do you have any specific time preferences for Tuesday afternoon?
2. Should I propose an agenda or specific topics to cover?

---

**Next Steps**: Which variant do you prefer, or would you like me to adjust anything?
```

### Example 2: Compose New Email

**User**: "Compose an email to vendor@acme.com asking about the pricing proposal status"

**Assistant**:
```
# Email Draft: Pricing Proposal Follow-up

**To**: vendor@acme.com
**Subject**: Following up on pricing proposal

---

## Variant A: Concise

Hi [Vendor Name],

I wanted to follow up on the pricing proposal we discussed. Have you had a chance to review it?

Please let me know if you need any additional information.

Thanks,

---

## Variant B: Warmer

Hi [Vendor Name],

I hope this email finds you well. I wanted to check in regarding the pricing proposal we sent over on [date, if known].

We're working on finalizing our Q2 budget and would greatly appreciate an update on where things stand. If you need any clarification or additional details from our side, please don't hesitate to reach out.

Thank you for your time, and I look forward to hearing from you soon.

Best regards,

---

## Assumptions

- Vendor contact name is known (replace [Vendor Name])
- Previous proposal was sent and vendor is aware of it
- There's no hard deadline pressuring the follow-up

## Questions to Confirm

1. Do you know the vendor contact's name? (Replace [Vendor Name])
2. When was the original proposal sent? (Can mention specific date)
3. Is there a deadline by which you need their response?
4. Should I mention the next steps if they accept?

---

**Next Steps**: Please provide the vendor contact's name and any other details, then I can finalize the draft.
```

### Example 3: Multiple Drafts

**User**: "Draft replies for emails msg_123 and msg_456"

**Assistant**:
```
Let me draft replies for both emails.

---

# Draft 1: Re: [Subject of msg_123]

[Full draft for email 1...]

---

# Draft 2: Re: [Subject of msg_456]

[Full draft for email 2...]

---

Would you like to review and refine these individually, or are they ready to save as drafts?
```

## Failure Modes / Troubleshooting

### Cannot Fetch Original Email

**Symptom**: `gog gmail get <messageId>` fails or returns error

**Resolution**:
1. Verify message ID is correct (ask user to confirm)
2. Check if email was deleted or moved
3. Try fetching full thread: `gog gmail thread get <threadId>`
4. Ask user to describe email context manually

### Missing Critical Information

**Symptom**: Cannot draft effectively without key facts

**Resolution**:
1. List what's missing in "Questions to Confirm"
2. Suggest: "I need more information to draft this effectively. Can you provide [X, Y, Z]?"
3. Offer placeholder draft: "Here's a template you can fill in..."
4. Do NOT guess facts (dates, numbers, commitments)

### Tone Mismatch

**Symptom**: User says "Too formal" or "Too casual"

**Resolution**:
1. Ask: "What tone would you prefer? More [formal/casual/friendly/brief]?"
2. Regenerate with adjusted tone
3. Learn preference for future drafts in session

### Large Email Threads

**Symptom**: Original email is part of long thread

**Resolution**:
1. Summarize thread context: "This is part of a 12-message thread about [topic]"
2. Ask: "Should the reply reference earlier messages?"
3. Focus reply on most recent message unless user requests broader context

### Multiple Recipients / Reply-All Ambiguity

**Symptom**: Original email has many recipients

**Resolution**:
1. Default to "Reply" (sender only) unless clear that Reply-All is needed
2. Ask: "Should this be Reply-All (to all [N] recipients) or just to [sender]?"
3. List recipients so user can decide

## Safety Rules

1. **Never send emails** - Only create drafts
2. **Always show drafts first** - Never create drafts without user seeing content
3. **Explicit confirmation for saving** - Ask "Ready to save this draft?" before invoking `gog gmail drafts create`
4. **Protect sensitive info** - Don't include passwords, credentials, or highly sensitive data unless explicitly instructed
5. **Two-variant rule** - Always offer Concise + Warmer variants (user choice improves over time)
6. **Assumptions transparency** - Always list assumptions so user can catch errors

## Safe Test

To safely test this skill using only `user@example.com`:

**Test 1: Draft to self (safe)**

In Claude Code:
1. Load gog-email-draft skill
2. Say: "Compose an email to user@example.com with subject 'Test Draft' and a brief greeting"
3. Verify output includes:
   - Both variants (Concise + Warmer)
   - Assumptions section
   - Questions section (if applicable)
   - Next steps guidance
4. Say: "Save as draft"
5. Verify draft is created via `gog gmail drafts create` command
6. Confirm draft is NOT sent

**Test 2: Reply to self (safe)**

1. Send yourself an email first (or use existing)
2. Get email ID: `gog gmail search "from:user@example.com" --max 1 --json`
3. Say: "Draft a reply to [email_id]"
4. Verify skill fetches original email and generates appropriate reply

See `skills/gog/_shared/references/testing.md` for complete test plan.

## Notes

- This skill integrates with:
  - `gog-email-triage`: Often invoked after triage to reply to prioritized emails
  - `gog-email-send`: Invoked after draft is finalized to send (with confirmation)
  - `gog-followups`: Can suggest adding follow-up tracking for sent emails

- Draft quality improves with:
  - More context about user's role, projects, and communication style
  - Examples of past successful emails
  - Feedback on tone preferences over time

- For recurring email types (status updates, meeting requests), consider creating templates in `references/` directory

- Consider reading the last 2-3 messages in a thread for better context, not just the immediate message

- When replying to automated emails (notifications, alerts), adjust tone to be more brief/transactional
