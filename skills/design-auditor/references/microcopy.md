# Microcopy Reference

Microcopy is the small functional text throughout a UI — button labels, error messages, tooltips, placeholders, confirmations, and empty states. It's often written by developers as an afterthought, but it has an outsized impact on usability and user trust.

---

## Button Labels

### The Verb Rule
Buttons should always be a **verb** (or verb phrase) that describes the action:

| ❌ Vague | ✅ Specific |
|---|---|
| OK | Got it / Save / Confirm |
| Submit | Send Message / Create Account / Place Order |
| Yes | Delete / Remove / Yes, cancel my plan |
| Cancel | Keep editing / Go back |
| Upload | Upload photo / Add file |
| Continue | Next: Shipping / Continue to payment |

### Rules
- **Be specific about what happens.** "Save Changes" is better than "Save" when the user might not know what they're saving.
- **Match the button to the outcome.** If clicking a button sends an email, say "Send Email" — not "Confirm."
- **Destructive buttons should name the thing being destroyed.** "Delete Project" not just "Delete." "Cancel Subscription" not just "Cancel."
- **Primary CTA should be 2–4 words max.** Longer labels don't scan well in buttons.
- **Sentence case, not Title Case.** "Create account" not "Create Account" (unless your brand style is Title Case throughout).

### Confirmation Dialogs
A good destructive confirmation dialog has:
```
Title:   Delete "Project Alpha"?
Body:    This will permanently delete the project and all its tasks.
         This action cannot be undone.
Buttons: [Cancel]  [Delete project]  ← specific, not just "Delete"
```

Never:
```
Title:   Are you sure?
Body:    This action cannot be undone.
Buttons: [No]  [Yes]
```

---

## Error Messages

### The Formula
A good error message answers three questions:
1. **What went wrong?**
2. **Why did it go wrong?** (if not obvious)
3. **How do I fix it?**

| ❌ Bad | ✅ Good |
|---|---|
| Invalid input | Please enter a valid email address |
| Error | We couldn't save your changes — check your connection and try again |
| Password incorrect | That password doesn't match — try again or reset your password |
| Required field | Please add a project name to continue |
| 500 Internal Server Error | Something went wrong on our end. We're looking into it — try again in a moment |
| File too large | This file is too large. Maximum size is 10MB |

### Rules
- **Don't blame the user.** Passive voice helps: "That email wasn't recognized" vs "You entered an invalid email."
- **Be specific.** "Something went wrong" is a last resort, not a default.
- **Tell them what to do next.** End with an action: "try again", "reset your password", "check your connection."
- **Match your brand's tone.** A playful app can say "Oops! That didn't work." An enterprise tool should stay neutral and professional.
- **Never expose technical details** to end users. No stack traces, no HTTP status codes, no "null pointer exception."
- **Keep error messages short.** 1–2 sentences max. If it needs more explanation, link to a help article.

### Validation Timing
- **Validate on blur** (when leaving a field) for format errors (email, URL, phone).
- **Validate on change** for things like password strength (give live feedback).
- **Validate on submit** for required field checks — don't interrupt typing.
- **Never validate on every keystroke** for format errors — showing "Invalid email" while the user is still typing is annoying.

---

## Placeholder Text

Placeholders appear inside empty inputs and disappear when the user starts typing. They are **not labels**.

### What Placeholders Are Good For
- Showing the expected format: `name@example.com`, `(555) 000-0000`, `YYYY-MM-DD`
- Giving a short hint: `Search by name or email`
- Example values: `e.g. Project Alpha`, `e.g. San Francisco`

### What Placeholders Are NOT Good For
- Replacing labels (they disappear, users forget what goes there)
- Long instructions (they get cut off)
- Required information (users skip it)

### Rules
- **Always have a visible label** in addition to placeholder text.
- **Keep placeholders short** — one phrase, max.
- **Use "e.g." prefix** for example values to make clear it's an example, not a required format.
- **Placeholder contrast** should be noticeably lighter than real input text — but still meet 3:1 contrast for readability.

---

## Tooltips & Helper Text

### When to Use Tooltips
- To explain an icon button with no label
- To clarify a non-obvious field ("API keys are case-sensitive")
- To explain why something is disabled ("You need admin access")

### When NOT to Use Tooltips
- For essential information — if it's critical, put it on the screen, not hidden in a hover
- For mobile (tooltips don't work on touch — use inline helper text or a modal instead)
- For long explanations — tooltips should be 1–2 sentences max

### Helper Text (Below Input)
Use static helper text below inputs for:
- Format hints: "Use 8+ characters with at least one number"
- Consequences: "This will be visible to everyone on your team"
- Counts: "0/280 characters"

Position: directly below the input, above where the error message will appear.

---

## Tone Guidelines

### Pick One Tone and Stick to It

| Tone | Best For | Example |
|---|---|---|
| **Friendly & casual** | Consumer apps, social, creative tools | "Looks great! Your changes are saved ✓" |
| **Warm & professional** | SaaS, productivity, HR tools | "Your changes have been saved." |
| **Neutral & clinical** | Finance, legal, healthcare, enterprise | "Transaction completed successfully." |
| **Playful** | Games, kids apps, lifestyle | "Woohoo! You crushed it 🎉" |

### Consistency Rules
- If you use contractions ("you're", "we'll") in one place, use them everywhere.
- If you use first person ("Your account") vs second person ("My account") — pick one.
- If you address users casually in empty states, don't suddenly switch to formal language in error messages.
- If your brand is friendly, never let technical/legal copy sneak in with a completely different voice.

---

## Terminology Consistency

One of the most common microcopy mistakes is calling the same concept different things in different parts of the app.

### How to Audit Terminology
Search for synonyms being used for the same thing. Common traps:

| Concept | Don't Mix These |
|---|---|
| The user's workspace | "workspace" / "project" / "team" / "organization" |
| Content items | "task" / "item" / "card" / "ticket" / "to-do" |
| Saving | "save" / "update" / "apply" / "confirm" |
| Removing | "delete" / "remove" / "archive" / "clear" |
| Members | "members" / "users" / "collaborators" / "teammates" |

### Rule: Pick One Word Per Concept
Create a short glossary and stick to it. Every button, label, confirmation, and error message should use the same word for the same thing.

---

## Numbers, Dates & Formatting

- **Dates**: Use unambiguous formats. "Jan 15, 2025" or "15 January 2025" beats "01/15/25" (is that Jan 15 or the 1st of the 15th month?).
- **Relative time**: "2 hours ago" is friendlier than a timestamp for recent events. But always show the full date on hover/focus.
- **Large numbers**: Use commas: 1,000,000 not 1000000. Or abbreviate for dashboards: 1.2M, 45K.
- **Percentages**: "You're 75% done" not "75% complete" — the possessive makes it feel personal.
- **File sizes**: Show in the most readable unit. 1.4 MB not 1,400,000 bytes.

---

## Confirmation & Success Messages

| Action | ✅ Good Confirmation |
|---|---|
| Saved | "Changes saved" or "Project saved" |
| Sent | "Message sent to Jamie" |
| Deleted | "Task deleted" + Undo option |
| Copied | "Link copied to clipboard" |
| Uploaded | "Photo uploaded successfully" |
| Invited | "Invitation sent to alex@example.com" |

### Rules
- **Be specific** — name the thing that was acted on when possible.
- **Offer undo** for destructive or hard-to-reverse actions.
- **Don't celebrate too hard** — "🎉 Amazing! You saved a file!" is patronizing. Save enthusiasm for genuinely exciting moments (first project created, subscription upgraded).
