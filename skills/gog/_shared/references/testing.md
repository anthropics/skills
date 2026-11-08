# GOG Skills Safe Testing Guide

This document describes how to safely test GOG skills using only the email identity **user@example.com**.

## Overview

All tests must be:
- **Read-only by default**: No sends, deletions, or modifications unless explicitly enabled
- **Self-contained**: If write actions are included, they must only target user@example.com
- **Auditable**: All actions must be logged to the audit log
- **Privacy-respecting**: Never log full email bodies; use IDs, subjects, and snippets only

## Preconditions

Before running tests:

1. **GOG must be authenticated**: Run `gog version` or `gog email list --limit 1` to verify
2. **User identity must be user@example.com**: Confirm with `gog email list --query "to:me" --limit 1`
3. **No additional auth steps**: Assume already logged in via OAuth

If authentication fails, run `gog auth login` first.

## Safe Test Plan

### Phase 1: Read-Only Tests (ALWAYS SAFE)

These tests never modify any data and can be run anytime.

#### Test 1: Verify GOG is Reachable

**Objective**: Confirm GOG CLI is installed and responding.

```bash
gog version --json 2>/dev/null || gog version 2>/dev/null
```

**Expected**: Version information or error message.

**Pass Criteria**: Command executes without "command not found" error.

#### Test 2: List Emails (Read-Only)

**Objective**: Retrieve a small list of emails involving only user@example.com.

```bash
gog email list --query "to:user@example.com OR from:user@example.com" --limit 5 --json
```

**Expected**: JSON array of up to 5 email messages.

**Pass Criteria**:
- Command succeeds (exit code 0)
- Output is valid JSON
- Each message has `id`, `from`, `to`, `subject`, `date` fields

**Privacy**: Only IDs and subjects are used; full bodies are not retrieved in this test.

#### Test 3: Read One Email (Read-Only)

**Objective**: Fetch details of a single email message.

**Prerequisites**: Obtain an email ID from Test 2.

```bash
# Extract first email ID from previous test
EMAIL_ID=$(gog email list --query "to:user@example.com" --limit 1 --json 2>/dev/null | jq -r '.[0].id')

# Fetch that email
gog email get --id "$EMAIL_ID" --json 2>/dev/null
```

**Expected**: JSON object with full email details.

**Pass Criteria**:
- Command succeeds
- Output contains `id`, `from`, `subject`, `date`, `body_text` fields
- `id` matches the requested ID

**Privacy Note**: Full email body is retrieved but NOT printed to logs. Only print:
- Email ID
- From/To addresses
- Subject
- Date
- First 100 characters of body (snippet)

#### Test 4: Calendar Agenda (Read-Only)

**Objective**: Retrieve today's calendar events.

```bash
gog calendar agenda --today --json 2>/dev/null
```

**Expected**: JSON array of calendar events for today.

**Pass Criteria**:
- Command succeeds or returns empty array if no events
- Output is valid JSON
- Each event has `id`, `title`, `start`, `end` fields

#### Test 5: List Tasks (Read-Only)

**Objective**: Retrieve open tasks.

```bash
gog tasks list --status open --limit 10 --json 2>/dev/null
```

**Expected**: JSON array of up to 10 open tasks.

**Pass Criteria**:
- Command succeeds or returns empty array if no tasks
- Output is valid JSON
- Each task has `id`, `title`, `status` fields

#### Test 6: Follow-ups Store (Read-Only)

**Objective**: Validate follow-up data store if it exists.

```bash
# Check if follow-ups store exists
if [ -f ~/.gog-assistant/followups.json ]; then
  cat ~/.gog-assistant/followups.json | jq . >/dev/null && echo "VALID JSON"
else
  echo "NO FOLLOWUP STORE (OK)"
fi
```

**Expected**: Either valid JSON or file doesn't exist yet.

**Pass Criteria**:
- If file exists, it must be valid JSON
- If file doesn't exist, that's OK (not an error)

### Phase 2: Draft-Only Test (SAFE, OPT-IN)

This test creates a draft email addressed ONLY to user@example.com. It does NOT send the email.

**IMPORTANT**: Only run this test if explicitly requested by setting environment variable:

```bash
export RUN_DRAFT_TEST=1
```

#### Test 7: Create Draft to Self (Draft-Only, NO SEND)

**Objective**: Create a draft email to verify write operations work, without sending.

```bash
if [ "$RUN_DRAFT_TEST" = "1" ]; then
  gog email draft \
    --to "user@example.com" \
    --subject "[GOG TEST DRAFT — DO NOT SEND] Test Draft at $(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    --body "This is a test draft created by the GOG smoke test script.

This draft was created at: $(date -u)

This is NOT a real email. It should NOT be sent. If you are reading this, the test worked correctly.

To delete this draft, use your email client or run:
  gog email draft-delete --id <DRAFT_ID>

" \
    --json
else
  echo "SKIPPED: RUN_DRAFT_TEST not set"
fi
```

**Expected**: JSON object with `draft_id` and `status: "created"`.

**Pass Criteria**:
- Command succeeds
- Draft is created with correct recipient (user@example.com only)
- Subject starts with "[GOG TEST DRAFT — DO NOT SEND]"
- Draft ID is returned

**CRITICAL**: The script must STOP here and NOT attempt to send the draft.

**Output**: Print the draft ID and a reminder:

```
✓ Draft created successfully: draft_abc123
⚠ REMINDER: This is a TEST DRAFT. Do NOT send it.
⚠ To send this draft, you would need to explicitly confirm with "YES, SEND"
```

### Phase 3: Confirmation Refusal Test (SAFE)

This test verifies that send operations are properly gated by confirmation.

#### Test 8: Verify Send Requires Confirmation

**Objective**: Confirm that attempting to send without explicit confirmation is refused.

**Method**: This is a manual test. In a Claude Code session:

1. Load the `gog-email-send` skill
2. Provide a draft ID from Test 7
3. Ask to send the email WITHOUT providing the "YES, SEND" confirmation string
4. Verify the skill refuses and asks for explicit confirmation

**Pass Criteria**:
- Skill does not send the email
- Skill requests explicit "YES, SEND" confirmation
- User is reminded this is a test draft addressed to self

## Running the Smoke Test Script

A complete automated smoke test script is available at:

```
skills/gog/_shared/scripts/smoke_test.sh
```

### Basic Usage (Read-Only)

```bash
cd /path/to/skills/repo
bash skills/gog/_shared/scripts/smoke_test.sh
```

This runs only Phase 1 (read-only tests).

### With Draft Test (Opt-In)

```bash
RUN_DRAFT_TEST=1 bash skills/gog/_shared/scripts/smoke_test.sh
```

This runs Phase 1 + Phase 2 (creates a test draft to self).

### Expected Output

```
=== GOG Skills Smoke Test ===
Test 1: Verify GOG is reachable... PASS
Test 2: List emails (read-only)... PASS (found 3 messages)
Test 3: Read one email (read-only)... PASS (msg_abc123)
Test 4: Calendar agenda (read-only)... PASS (2 events today)
Test 5: List tasks (read-only)... PASS (5 open tasks)
Test 6: Follow-ups store validation... PASS (no store yet)
Test 7: Create draft to self... SKIPPED (set RUN_DRAFT_TEST=1 to enable)

=== ALL TESTS PASSED ===
```

### Failure Handling

If a test fails, the script:
- Prints a clear failure message
- Exits with non-zero status
- Suggests troubleshooting steps

Example failure output:

```
Test 2: List emails (read-only)... FAIL
  Error: gog email list returned exit code 1
  Output: Authentication expired. Run 'gog auth login'.
  Fix: Run 'gog auth login' to re-authenticate.

=== TESTS FAILED ===
```

## Interpreting Results

### All Tests Pass

Your GOG CLI is configured correctly and all read operations work. Skills should function properly.

### Some Tests Fail

Check the specific error messages:

- **"command not found"**: GOG not installed or not on PATH. See [gog-interface.md](./gog-interface.md) for setup.
- **"Authentication failed"**: Run `gog auth login` to re-authenticate.
- **"Permission denied"**: Check OAuth scopes include necessary permissions.
- **"Invalid JSON"**: GOG may have changed output format; update skills or report issue.

### Draft Test Creates Draft Successfully

Write operations work! You can now safely test skills that create drafts. Remember:
- Always review drafts before sending
- Use "YES, SEND" confirmation for all sends
- Delete test drafts after testing: `gog email draft-delete --id <draft_id>`

## Privacy & Safety Guidelines

When running tests:

1. **Never paste full email bodies into test output**: Use snippets (first 50-100 chars) only
2. **Redact sensitive info**: If email subjects contain credentials, IDs, or personal info, redact them
3. **Use only self-addressed emails**: Test sends and drafts must ONLY go to user@example.com
4. **Clean up after testing**: Delete test drafts when done
5. **Check audit log**: Review `~/.gog-assistant/audit.log` after testing to verify actions were logged correctly

## Privacy-Safe Output Format

When printing test results, use this format:

```
✓ Test 3: Read one email
  ID: msg_abc123
  From: sender@example.com
  Subject: Meeting tomorrow
  Date: 2026-01-28T14:30:00Z
  Body snippet: "Hi team, I wanted to schedule our..."
  [Full body NOT printed for privacy]
```

**Never print**:
- Full email bodies
- Passwords or tokens
- Sensitive personal information (SSN, credit card numbers, etc.)

## Troubleshooting

### GOG not found

**Symptom**: `bash: gog: command not found`

**Fix**:
1. Check if GOG is installed: `which gog`
2. If not, install GOG or add it to PATH
3. If GOG is hypothetical, see [gog-interface.md](./gog-interface.md) for implementation guidance

### Authentication errors

**Symptom**: `Error: Authentication failed` or `OAuth token expired`

**Fix**:
```bash
gog auth login
# Follow browser prompts to re-authenticate
```

### Permission errors

**Symptom**: `Error: Permission denied` or `Insufficient scopes`

**Fix**:
- Check that OAuth scopes include: `gmail.modify`, `calendar.events`, `tasks`
- Re-run `gog auth login` with `--scopes` flag if needed

### Invalid JSON output

**Symptom**: `jq parse error` or `invalid JSON`

**Fix**:
- Run command without `--json` flag to see human-readable output
- Check if GOG CLI version is compatible
- Report issue if output format has changed

### No emails found

**Symptom**: Test 2 returns empty array `[]`

**Fix**:
- This may be expected if inbox is empty or all emails are from others
- Send yourself a test email: `gog email draft --to user@example.com --subject "Test" --body "Test" | xargs gog email send --draft-id`
- Wait a few seconds and retry

## Advanced Testing

### Testing Individual Skills

Each skill should include a "Safe Test" section in its SKILL.md. Refer to:

- **gog-email-triage**: Test with `gog email list --query "to:user@example.com" --limit 10`
- **gog-email-draft**: Test by drafting to self only
- **gog-email-send**: Test by verifying confirmation string is required
- **gog-tasks**: Test by creating/updating a test task
- **gog-calendar**: Test by reading today's agenda
- **gog-followups**: Test by validating followups.json structure

### Testing Error Handling

Intentionally trigger errors to verify graceful failure:

```bash
# Invalid email ID
gog email get --id "invalid_id" --json
# Should return error JSON, not crash

# Invalid date format
gog calendar agenda --range "not-a-date" --json
# Should return error JSON, not crash

# Missing required field
gog tasks create --priority P1 --json
# Should return error about missing --title
```

## Continuous Testing

Consider running smoke tests:
- Before deploying new skill versions
- After updating GOG CLI
- Weekly to catch configuration drift
- Before demos or presentations

Set up a cron job (optional):

```bash
# Run smoke tests daily at 9 AM
0 9 * * * /path/to/skills/gog/_shared/scripts/smoke_test.sh >> /var/log/gog-smoke-test.log 2>&1
```

## Reporting Issues

If tests consistently fail:

1. Capture full error output
2. Check GOG version: `gog version`
3. Check skill versions: `ls -la skills/gog/*/SKILL.md`
4. Review audit log: `tail -n 50 ~/.gog-assistant/audit.log`
5. Report with all above information
