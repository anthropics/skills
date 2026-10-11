---
name: gog-calendar
description: Review calendar agenda, find available meeting slots, and schedule events. Displays today's or week's schedule, suggests meeting times based on availability, creates calendar events with explicit user confirmation. Use when user mentions calendar, schedule, meetings, or availability. Never creates or modifies events without confirmation.
compatibility: Requires gog CLI tool with calendar access
metadata:
  author: gog-skills
  version: "1.0"
allowed-tools: Bash(gog:*) Read
---

# Calendar & Scheduling Assistant

Review your schedule, find meeting slots, and create events with smart suggestions.

## When to Use

Use this skill when:
- User asks "what's on my calendar" or "what meetings do I have today"
- User wants to "schedule a meeting" or "find time to meet"
- User mentions "check my availability"
- User says "when am I free this week"
- User wants to create a calendar event

**Important**: This skill NEVER creates or modifies events without explicit user confirmation.

## Dynamic Context

The following live data is available:

**Today's agenda:**
```
!`gog calendar events --today --json 2>/dev/null || echo "GOG_NOT_CONFIGURED"`
```

## Workflow

### Reviewing Calendar

#### Today's Agenda

When user says "what's on my calendar today" or "show today's schedule":

1. **Fetch today's events**:
   ```bash
   gog calendar events --today --json
   ```

2. **Present formatted agenda**:
   ```markdown
   # Today's Agenda — [Day], [Date]

   ## Morning

   **9:00 AM - 9:30 AM** | Team Standup
   - Location: Zoom (https://zoom.us/j/123...)
   - Attendees: Alice, Bob, Carol (3 people)
   - Status: Confirmed

   **10:00 AM - 11:00 AM** | 1:1 with Manager
   - Location: Conference Room A
   - Status: Confirmed

   ## Afternoon

   **2:00 PM - 3:30 PM** | Client Demo
   - Location: Zoom
   - Attendees: Client team (5 people)
   - Status: Confirmed
   - 📎 Has description/notes

   **4:00 PM - 5:00 PM** | Project Planning
   - Location: Virtual
   - Status: Tentative ⚠️

   ---

   **Summary**:
   - Total meetings: 4
   - Total time: 3.5 hours
   - Free blocks: 11:00 AM - 2:00 PM (3 hours)
   - Day ends at: 5:00 PM

   **Preparation needed**:
   - Review client demo slides (before 2pm)
   - Prepare 1:1 talking points (before 10am)
   ```

#### Week's Agenda

When user says "what's my week look like" or "show this week":

1. **Fetch week's events**:
   ```bash
   # Calculate date range for this week
   FROM_DATE=$(date +%Y-%m-%d)
   TO_DATE=$(date -v+7d +%Y-%m-%d)  # macOS

   # Fetch events in range
   gog calendar events --from "$FROM_DATE" --to "$TO_DATE" --json
   ```

2. **Present grouped by day**:
   ```markdown
   # Week Agenda — Week of [Date]

   ## Monday, [Date]
   - 9:00 AM - 9:30 AM | Team Standup
   - 2:00 PM - 3:00 PM | Design Review
   [Total: 1.5 hours]

   ## Tuesday, [Date]
   - 9:00 AM - 9:30 AM | Team Standup
   - 10:00 AM - 12:00 PM | Workshop
   - 3:00 PM - 4:00 PM | Quarterly Review
   [Total: 3.5 hours]

   ## Wednesday, [Date]
   - 9:00 AM - 9:30 AM | Team Standup
   [Total: 0.5 hours] — Light day! 💚

   [...]

   ---

   **Week Summary**:
   - Total meetings: 15
   - Busiest day: Tuesday (3.5 hours)
   - Lightest day: Wednesday (0.5 hours)
   - Free afternoons: Wednesday, Friday
   ```

### Finding Meeting Slots

When user says "find time for a meeting" or "when am I free":

1. **Gather requirements**:
   ```markdown
   Let me find available meeting times. A few questions:

   1. **Duration**: How long should the meeting be? (30 min, 1 hour, etc.)
   2. **Date range**: When are you looking? (This week, next week, specific dates)
   3. **Time preferences**: Any time constraints? (Mornings only, after 2pm, etc.)
   4. **Attendees**: Anyone else's calendar to check? (If you have access)
   ```

2. **Search for slots using freebusy**:
   ```bash
   # Get busy periods
   gog calendar freebusy primary \
     --from "2026-01-29T00:00:00Z" \
     --to "2026-01-31T23:59:59Z" \
     --json
   ```

   **Note**: GOG CLI v0.9.0 doesn't have `find-slots`. Instead, use `freebusy` to get busy periods, then calculate free gaps between them. For example:
   - If busy: 9-10am, 2-3pm
   - Then free: 8-9am, 10am-2pm, 3-5pm

   Parse the busy periods and suggest slots in the free time.

3. **Present options**:
   ```markdown
   # Available Meeting Slots

   ## Top 5 Options (60 minutes)

   1. **Wednesday, Jan 29 at 2:00 PM - 3:00 PM**
      - Ideal time: After lunch, before end of day
      - No conflicts

   2. **Thursday, Jan 30 at 10:00 AM - 11:00 AM**
      - Morning slot, good energy
      - No conflicts

   3. **Thursday, Jan 30 at 3:00 PM - 4:00 PM**
      - Afternoon slot
      - No conflicts

   4. **Friday, Jan 31 at 9:00 AM - 10:00 AM**
      - Early morning
      - No conflicts

   5. **Friday, Jan 31 at 1:00 PM - 2:00 PM**
      - Post-lunch
      - No conflicts

   ---

   **Recommendation**: Option 1 (Wed at 2pm) — Best mid-week timing

   Which slot works best? Or need more options?
   ```

### Creating Events

When user says "schedule a meeting" or "create a calendar event":

1. **Gather event details**:
   ```markdown
   Let me create that calendar event. I need:

   1. **Title**: What's the meeting about?
   2. **Date & Time**: When? (e.g., "Tomorrow at 2pm", "Jan 30 at 10am")
   3. **Duration**: How long? (30 min, 1 hour, 90 min, etc.)
   4. **Attendees**: Who should attend? (email addresses, comma-separated)
   5. **Location**: Where? (Zoom, physical location, or I can generate a meeting link)
   6. **Description**: Any agenda or notes?
   ```

2. **Parse date/time**:
   - Support natural language: "tomorrow at 2pm", "next Tuesday at 10am"
   - Convert to ISO8601: "2026-01-29T14:00:00Z"
   - Confirm timezone assumptions

3. **Present proposed event**:
   ```markdown
   ## Proposed Event

   **Title**: Q2 Planning Meeting
   **Date**: Wednesday, January 29, 2026
   **Time**: 2:00 PM - 3:00 PM (1 hour)
   **Attendees**:
   - alice@company.com
   - bob@company.com
   - carol@company.com
   **Location**: Zoom (meeting link will be generated)
   **Description**: Discuss Q2 goals, budget allocation, and team priorities.

   **Conflicts check**: ✅ No conflicts found for you

   ⚠️  **Note**: Cannot check attendees' availability without access to their calendars.

   Does this look correct? Any changes needed?
   ```

4. **Request confirmation**:
   ```markdown
   Ready to create this event? It will:
   - Add to your calendar
   - Send invitations to all attendees
   - Generate meeting link (if applicable)

   Reply "yes, create" to confirm.
   ```

5. **Only create with explicit confirmation**: "yes, create" or "create it"

6. **Create event**:
   ```bash
   # Calculate end time from duration
   START_TIME="2026-01-29T14:00:00Z"
   END_TIME="2026-01-29T15:00:00Z"  # 1 hour later

   gog calendar create primary \
     --summary "Q2 Planning Meeting" \
     --from "$START_TIME" \
     --to "$END_TIME" \
     --attendees "alice@company.com,bob@company.com,carol@company.com" \
     --location "Zoom" \
     --description "Discuss Q2 goals, budget allocation, and team priorities." \
     --with-meet \
     --json
   ```

   **Note**:
   - Use `primary` as the calendar ID for the user's main calendar
   - `--summary` is the event title (not `--title`)
   - `--from` and `--to` are absolute times (not `--start` and `--duration`)
   - `--with-meet` automatically generates a Google Meet link

7. **Confirm creation**:
   ```markdown
   ✅ **Event Created**

   Event ID: event_abc123
   Title: Q2 Planning Meeting
   When: Wednesday, Jan 29 at 2:00 PM
   Invitations sent to: 3 attendees

   **Next steps**:
   - Prepare agenda?
   - Send pre-read materials via email?
   - Add this to your task list as prep?
   ```

8. **Offer email draft** (optional):
   ```markdown
   Would you like me to draft an email to attendees with:
   - Meeting details
   - Agenda
   - Pre-read or prep instructions
   ```

### Modifying Events

**Not implemented in MVP** - User should use calendar client directly for modifications. If user requests, suggest:

```markdown
To modify this event, please use your calendar app directly:
- Google Calendar: calendar.google.com
- Outlook: outlook.office.com

Or tell me what you'd like to change and I can help you communicate it to attendees via email.
```

## Output Format (Strict)

### Agenda View (Daily)

```markdown
# Today's Agenda — [Day], [Date]

## Morning
[Time range] | [Title]
- Location: [location]
- Attendees: [count or names]
- Status: [Confirmed/Tentative]

## Afternoon
[Same format]

---

**Summary**:
- Total meetings: [N]
- Total time: [X hours]
- Free blocks: [time ranges]

**Preparation needed**:
- [Action items before meetings]
```

### Meeting Slot Options

```markdown
# Available Meeting Slots

## Top [N] Options ([duration])

1. **[Day, Date] at [Time] - [Time]**
   - [Context/rationale]
   - [Conflict status]

[...]

---

**Recommendation**: [Which slot and why]
```

### Event Creation Confirmation

```markdown
## Proposed Event

[All event details clearly listed]

**Conflicts check**: [Status]

Does this look correct?

---

Ready to create? Reply "yes, create" to confirm.
```

### Event Created Success

```markdown
✅ **Event Created**

Event ID: [id]
Title: [title]
When: [readable date/time]
Invitations sent to: [N attendees]

**Next steps**: [Suggested follow-up actions]
```

## Examples

### Example 1: Today's Agenda

**User**: "What's on my calendar today?"

**Assistant**:
```
[Fetches today's agenda...]

# Today's Agenda — Tuesday, January 28

## Morning

**9:00 AM - 9:30 AM** | Team Standup
- Location: Zoom (https://zoom.us/j/123456789)
- Attendees: Engineering team (8 people)
- Status: Confirmed

**11:00 AM - 12:00 PM** | Product Review
- Location: Conference Room B
- Attendees: Product, Design, Eng leads
- Status: Confirmed

## Afternoon

**2:00 PM - 3:30 PM** | Client Demo — Acme Corp
- Location: Zoom
- Attendees: 5 external guests
- Status: Confirmed
- 📎 Agenda: Demo new features, Q&A, pricing discussion

**4:00 PM - 4:30 PM** | 1:1 with Sarah
- Location: Her office
- Status: Confirmed

---

**Summary**:
- Total meetings: 4
- Total time: 3.5 hours
- Free blocks: 9:30 AM - 11:00 AM (1.5 hrs), 12:00 PM - 2:00 PM (2 hrs)
- Day ends at: 4:30 PM

**Preparation needed**:
- Finish demo slides (before 2pm)
- Review Acme account history (before 2pm)
- Prepare 1:1 talking points for Sarah (before 4pm)

Your afternoon is packed. Want me to help prep for the client demo?
```

### Example 2: Schedule a Meeting

**User**: "Schedule a meeting with alice@company.com and bob@company.com for tomorrow at 2pm, 1 hour, to discuss Q2 budget"

**Assistant**:
```
## Proposed Event

**Title**: Q2 Budget Discussion
**Date**: Wednesday, January 29, 2026
**Time**: 2:00 PM - 3:00 PM (1 hour)
**Attendees**:
- alice@company.com
- bob@company.com
**Location**: Virtual meeting (Zoom link will be generated)
**Description**: Discuss Q2 budget allocation and priorities.

**Conflicts check**: ✅ No conflicts found on your calendar

⚠️  **Note**: Cannot check Alice and Bob's availability without calendar access. The invitation will ask them to accept/decline.

Does this look correct? Any changes needed?
```

**User**: "Looks good, create it"

**Assistant**:
```
Ready to create this event? It will:
- Add to your calendar
- Send invitations to Alice and Bob
- Generate a Zoom meeting link

Reply "yes, create" to confirm.
```

**User**: "yes, create"

**Assistant**:
```
[Creates event...]

✅ **Event Created**

Event ID: event_xyz789
Title: Q2 Budget Discussion
When: Wednesday, Jan 29 at 2:00 PM (1 hour)
Location: Zoom — https://zoom.us/j/987654321
Invitations sent to: 2 attendees (alice@company.com, bob@company.com)

**Next steps**:
- Prepare budget spreadsheet?
- Draft agenda email to attendees?
- Create task for pre-meeting prep?

Want me to draft an agenda email to Alice and Bob?
```

### Example 3: Find Meeting Slots

**User**: "When am I free for a 30-minute meeting this week?"

**Assistant**:
```
Let me check your availability.

[Searches calendar...]

# Available Meeting Slots

## Top 5 Options (30 minutes)

1. **Wednesday, Jan 29 at 10:00 AM - 10:30 AM**
   - Morning slot, good focus time
   - No conflicts before or after

2. **Wednesday, Jan 29 at 3:00 PM - 3:30 PM**
   - Afternoon slot
   - 1 hour buffer before next meeting

3. **Thursday, Jan 30 at 9:00 AM - 9:30 AM**
   - Early morning, fresh start
   - No conflicts

4. **Thursday, Jan 30 at 2:00 PM - 2:30 PM**
   - Post-lunch
   - No conflicts

5. **Friday, Jan 31 at 11:00 AM - 11:30 AM**
   - Late morning
   - Last slot before lunch

---

**Recommendation**: Option 1 (Wed at 10am) — Quietest day, good timing

Which slot works for you? Or need to check other times?
```

## Failure Modes / Troubleshooting

### GOG Not Configured

**Symptom**: Dynamic context shows `GOG_NOT_CONFIGURED`

**Resolution**:
1. Inform: "GOG CLI is not configured. See: skills/gog/_shared/references/gog-interface.md"
2. Suggest: "Run `gog auth login` to authenticate with calendar access"
3. Offer: "I can still help you plan scheduling manually"

### Ambiguous Date/Time

**Symptom**: User says "schedule meeting tomorrow" without specifying time

**Resolution**:
1. Ask: "What time tomorrow? (e.g., 2pm, morning, afternoon)"
2. If still vague, suggest: "Would 2:00 PM work? (mid-afternoon, typical meeting time)"
3. Always confirm parsed date/time before creating

### Timezone Confusion

**Symptom**: User is in different timezone than system

**Resolution**:
1. Check system timezone: `date +%Z`
2. Ask user: "I'm showing times in [TZ]. Is that correct for you?"
3. If mismatch, clarify: "So 2pm your time is [X]pm [TZ], correct?"
4. Always display timezone in event confirmations

### No Available Slots

**Symptom**: Calendar is fully booked, no free slots found

**Resolution**:
1. Inform: "Your calendar is packed for [date range]. No [duration] slots available."
2. Suggest alternatives:
   - "Extend to next week?"
   - "Shorten meeting to [shorter duration]?"
   - "Consider before 9am or after 5pm?"
3. Show least-conflict options: "These times have only 1 conflict..."

### Attendee Email Typo

**Symptom**: User provides malformed email address

**Resolution**:
1. Detect invalid format (no @, invalid domain)
2. Warn: "The email '[address]' doesn't look valid. Please double-check."
3. Ask: "Did you mean [suggested correction]?"
4. Don't create event with invalid emails

### Conflict with Existing Event

**Symptom**: Proposed time overlaps with existing event

**Resolution**:
1. Warn: "⚠️  Conflict detected: You have '[Event Title]' at that time."
2. Ask: "Should I:
   - Find a different time?
   - Create anyway (double-booked)?
   - Reschedule the conflicting event?"
3. Require explicit confirmation for double-booking

## Safety Rules

1. **Never create events without confirmation** - Always show proposal and request "yes, create"
2. **No modifications without confirmation** - Editing events requires explicit approval
3. **Timezone awareness** - Always clarify and confirm timezone in summaries
4. **Privacy in invites** - Don't include sensitive info in event titles/descriptions
5. **Invitation transparency** - Tell user who will receive invitations before creating

## Safe Test

To safely test this skill using only `user@example.com`:

**Test 1: View Agenda (Read-Only, Always Safe)**

In Claude Code:
1. Load gog-calendar skill
2. Say: "Show today's agenda"
3. Verify output includes:
   - Events for today (or "No events" if empty)
   - Time, title, location, attendees
   - Summary with meeting count and free blocks

**Test 2: Find Slots (Read-Only, Always Safe)**

1. Say: "When am I free for a 30-minute meeting tomorrow?"
2. Verify output includes:
   - List of available time slots
   - Duration specified
   - Recommendation
3. Confirm no events are created

**Test 3: Create Event (Draft-to-Self Only, Safe)**

1. Say: "Schedule a test meeting with user@example.com tomorrow at 3pm, 30 minutes, test meeting"
2. Review proposed event
3. Say: "yes, create"
4. Verify event is created
5. Check your calendar to confirm event appears
6. Delete the test event afterward

See `skills/gog/_shared/references/testing.md` for complete test plan.

## Notes

- This skill integrates with:
  - `gog-email-triage`: Calendar conflicts inform email prioritization
  - `gog-email-draft`: Can draft meeting invitations or agenda emails
  - `gog-tasks`: Meeting prep can become tasks
  - `gog-followups`: Track meeting follow-ups

- Consider creating event templates for recurring meetings (1:1s, standups)

- For recurring events, user should use calendar client directly (more complex to create via CLI)

- Smart scheduling tips:
  - Batch meetings on certain days, leave other days meeting-free
  - Suggest "No Meeting Fridays" if calendar is too full
  - Recommend buffer time between back-to-back meetings

- If GOG supports it, integrate with video conferencing (auto-generate Zoom links, etc.)

- Future enhancement: Analyze meeting patterns and suggest optimization
