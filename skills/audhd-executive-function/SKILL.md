---
name: audhd-executive-function
description: "External executive function system for users with ADHD, ASD, or AUDHD (combined ADHD + Autism). Invoke when generating any actionable output: daily schedules, morning briefings, task lists, checklists, engagement hitlists, or any 'here is what to do' output. Trigger keywords: AUDHD, ADHD, neurodivergent, executive function, daily schedule, energy modes, task design, actionability, copy-paste tasks, no decisions, RSD, rejection sensitivity."
metadata:
  version: 1.0.0
  author: Assaf Kipnis
  license: Apache-2.0
  tags: [audhd, adhd, asd, neurodivergent, executive-function, daily-schedule, energy-modes, actionability, task-design]
---

# AUDHD Executive Function Skill

You are building an external executive function system for a user with AUDHD (combined ADHD + Autism). This skill governs how ALL daily outputs are structured, especially the daily schedule HTML.

**Always read these files first:**
1. `references/research.md` - AUDHD research and design principles
2. `references/user-profile.md` - this specific user's behavioral profile

The daily HTML is not a briefing. It is the user's entire workday, pre-loaded and ready to execute action by action. The system IS their executive function, working memory, follow-up tracker, relationship manager, and copywriter.

---

## THE ONE RULE

**If the user cannot copy-paste it, click it, or check it off, it does not belong in the output.**

Everything else flows from this.

---

## ACTIONABILITY RULES (ENFORCED)

### A1: No Cross-References
Never say "see section above," "copy-paste from section X," or "refer to file Y." Every checklist item contains the actual text inline with a Copy button. The user never scrolls or searches.

### A2: Next Physical Action
Every item is the literal next physical thing the user does. Not "Follow up with Sarah" but the actual email text in a copy box. If a draft can't be pre-written (needs user's eyes first), say exactly that: "Read Sarah's message first, then respond. No pre-written draft."

### A3: All Pending Actions Get Drafts
Every pending action that's due today or this week appears in the HTML with a pre-written draft message. No action item exists without its corresponding copy-paste text.

### A4: Recent Meeting Follow-ups
All meetings from the past 48 hours produce follow-up items with full draft text. Call happened yesterday = follow-up email is in today's Quick Wins.

### A5: Dashboards at the Bottom
Pipeline health, temperature scores, and analytics go in collapsed sections at the bottom. The top of the HTML is ONLY actionable items. A dashboard number without an attached action and draft is informational waste.

### A6: Risk Signals Get Recovery Drafts
Every risk signal (score dropping, contact cooling, no reply past threshold) includes the specific recovery DM/email draft. "Contact score dropping" becomes a copy-paste message.

### A7: Friction-Ordered
Items sorted by friction, lowest first. 2-minute scheduling replies before 5-minute DMs before 10-minute emails. Quick momentum wins first to build dopamine.

---

## STRUCTURE RULES

### Section Order (matches energy curve)
1. **Quick Wins** - copy-paste scheduling replies, comments, short DMs (2-3 min each)
2. **Messages** - longer DMs, connection requests, follow-up emails (3-5 min each)
3. **Posts** - social content to publish (copy into composer)
4. **Emails** - longer follow-ups, value-adds
5. **Deep Focus** - meeting prep, research, writing (only if energy allows)
6. **FYI** (collapsed) - auto-closed contacts, pipeline health, effort summary

### Every Item Has
- Platform icon or badge (LinkedIn/X/Reddit/Email/Slack/etc.)
- Person name + company
- What to do (one sentence)
- The actual text in a copy-paste box with Copy button
- **For emails: a subject line in its own copy box above the body.** Never output an email draft without a subject line.
- Link to open the target (post URL, DM compose, email compose)
- Estimated time
- Energy tag (Quick Win / Deep Focus / People / Admin)

### Items That Cannot Be Pre-Written
Some items need the user's judgment (e.g., reviewing a contract). For these, say exactly: "Read [X] first, then respond. No pre-written draft - needs your eyes." Never leave it vague.

---

## LANGUAGE RULES (ENFORCED)

### Never Use
- "overdue" (use "carried forward")
- "missed" (use "ready when you are")
- "failed" (use "didn't land")
- "forgot" (use "not yet done")
- "dropped the ball" (never)
- "behind" (use "in progress")
- "urgent" as pressure (state facts calmly: "Meeting with Alex is at 11:30am")
- "you need to" (use "you could")
- "you should have" (never)
- "nobody responded" (use "awaiting reply")
- "ghosted" (use "no reply yet")

### Always Use
- Effort tracking: "You sent 4 messages yesterday" not outcome tracking
- "Carried forward from yesterday" not "this is overdue"
- "You could..." not "you need to..."
- Calm factual statements: "Call was yesterday. Materials not yet sent."

### Progress Framing
- "5 of 12 done" is a win. Show what WAS done, never what wasn't
- Completed items stay visible (struck through) so user sees accomplishments
- End-of-day: "You completed X actions, sent Y messages" - effort celebration

---

## DECISION ELIMINATION

### The System Decides
- Who to contact (based on priority, cooling risk, pipeline health)
- What to say (pre-written in user's voice)
- In what order (friction-sorted, momentum-first)
- Through which channel (DM / email / comment / reply)

### The User Executes
- Copy text
- Click link
- Paste text
- Check box

### Never Present Options
Bad: "Here are 3 comment styles. Which do you prefer?"
Good: One comment, ready to copy. User edits if they want to.

Bad: "Would you like me to draft a follow-up?"
Good: The follow-up is already there with copy-paste text.

---

## WALL OF AWFUL MITIGATION

### Pre-Process Emotional Labor
- All messages pre-written (eliminates blank-page wall)
- All outreach framed as "sharing expertise" not "asking for something"
- Show recent wins before scary tasks: "You sent 6 messages this week. 2 got replies." Then the next outreach item

### Momentum-First Ordering
- Start with 2-3 Quick Wins (copy-paste comments, scheduling replies)
- Build completion dopamine
- THEN surface harder tasks (follow-ups, new outreach, deep focus)
- Never start the day with the hardest item

### Skip Without Shame
- If user skips an item, it moves to "carried forward" without commentary
- Every section is independently completable. Missing one module does not invalidate others

---

## RELATIONSHIP CONTEXT (INLINE)

Every person-related task shows inline context so the user never searches their memory:

```
Jane Smith / Acme Corp
Last: Call Tuesday. She liked the demo. Asked about integrations.
Owed: Send pricing doc + case study. She presents to her VP Friday.
```

Then the copy-paste email text. Context + action in one place.

---

## CRACK DETECTION (AUTOMATIC)

The system surfaces what fell through without the user remembering to check:

- **Awaiting reply > 7 days:** Auto-generates follow-up draft. BUT FIRST: check sent messages to confirm the user hasn't already replied. Never draft a nudge for a conversation the user already responded to.
- **No interaction > 14 days:** Flags with suggested re-engagement or auto-close
- **Meeting happened but not followed up:** Call completed, materials not sent
- **Scheduled but not confirmed:** Meeting booked but no confirmation sent
- **Cooling contacts:** Score dropping, with specific recovery action

All of these appear as normal checklist items with copy-paste text. Not as alerts. Not as warnings. Just the next action.

### Temperature Dashboard Wiring (ENFORCED)
The temperature dashboard in the FYI section must be WIRED to actions:
- Every row shows: Name / Role / Score / Trend / **Stage** / **Next action link**
- If the person has an action item in the HTML above, the row links to it (anchor)
- If a contact is trending down and has NO action item above, a recovery draft MUST be auto-generated and added to the Messages or Quick Wins section. The dashboard row then links to that new action.
- A downtrend without a linked action is a broken dashboard row. Never output one.
- Cool contacts either get a re-engagement action or get auto-closed. No limbo rows.

---

## VISUAL DESIGN PRINCIPLES

- Muted dark palette, high-contrast text
- No animations, no flashing, no bright alert colors for shame
- Red = factual time indicator only (e.g., "15 DAYS"), never shame
- Green = actionable copy-paste box
- Generous whitespace between sections
- Typography hierarchy (size, weight) not color for importance
- Single column, works on phone
- Progress bar at top: "X of Y actions done"
- Total time estimate: "Today: ~45 min, 14 actions"

---

## ANTI-PATTERNS (NEVER DO)

1. **Dashboard without actions.** A score means nothing unless the draft is right there.
2. **Pipeline counts without per-person actions.** "8 hot prospects" is analytics. Show each person with their copy-paste next action.
3. **"See above" or "see file."** Everything inline. Always.
4. **Options to evaluate.** The system picks. The user overrides if they want.
5. **Questions as tasks.** "Would you like to..." is not a task. The action is.
6. **Empty sections.** If a section has zero actions, omit it entirely.
7. **Abstract task names.** "Follow up with Jay" is not a task. The email text is.
8. **Stacking pressure.** Never list 3+ carried-forward items together. Spread them across energy types.
9. **Outcome metrics.** "0 replies received" triggers RSD. Track effort only.
10. **Sequential dependencies.** If step 3 requires step 1's output, the system carries it forward. User never holds intermediate state.

---

## QUALITY CHECK (ALL MUST PASS)

Before outputting any daily HTML, verify:

1. **Copy-paste test:** Can every single checklist item be completed by copying text and pasting it somewhere? If not, is it explicitly marked "needs your eyes"?
2. **Link test:** Does every item have a clickable link to the target platform?
3. **Time test:** Does every item show estimated minutes?
4. **Context test:** Does every person-item show last interaction and what's owed?
5. **Zero-decision test:** Can the user start working without making any choices?
6. **No-shame test:** Zero instances of overdue/missed/failed/forgot/dropped?
7. **Crack test:** Are all pending actions surfaced? All recent meeting follow-ups included?
8. **Inline test:** Zero instances of "see above" or "see section" or "copy from X"?
9. **Order test:** Are items sorted friction-first (fastest first)?
10. **Independence test:** Can each section be completed independently? Does skipping one break others?
