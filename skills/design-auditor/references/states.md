# UI States Reference

Most beginner UIs only design the "happy path" — data loads perfectly and the user does everything right. In reality, users spend a surprising amount of time in other states. Each needs its own design.

## The 6 States Every UI Component Can Be In

| State | When | Design Priority |
|---|---|---|
| **Default** | Nothing has happened yet | ✅ Always designed |
| **Loading** | Waiting for data or an action to complete | ⚠️ Often forgotten |
| **Empty** | No data exists yet | ⚠️ Often forgotten |
| **Error** | Something went wrong | ⚠️ Often forgotten |
| **Success** | Action completed | ⚠️ Often forgotten |
| **Disabled** | Action not available | 🟡 Sometimes missing |

---

## Loading States

### When to use what

| Pattern | Best For |
|---|---|
| **Skeleton screen** | Content-heavy layouts (feeds, cards, tables) |
| **Spinner** | Short, action-triggered waits (button click, form submit) |
| **Progress bar** | Long operations where progress can be measured (upload, export) |
| **Shimmer / pulse** | Image placeholders and text blocks |

### Rules
- **Never show a blank screen.** Even a spinner is better than nothing.
- **Skeleton screens beat spinners** for perceived performance — the layout already exists, so content "appears" rather than "loading."
- **Show loading state immediately** — don't wait 500ms before showing anything. Users click again if nothing happens.
- **Skeleton shapes should match real content shapes.** A skeleton for a card should have lines where the title, description, and image will be — not generic rectangles.
- **Don't show too many spinners at once.** If five components all have their own spinner, the page feels broken. Consolidate into a page-level or section-level loading state.

### Loading State Checklist
- [ ] Every data fetch has a visual loading indicator
- [ ] Skeleton shapes match actual content layout
- [ ] Loading state matches the overall visual style (not plain gray boxes in an otherwise polished UI)
- [ ] Buttons show a loading state when clicked (spinner inside, disabled)
- [ ] Long operations have a progress indicator

---

## Empty States

Empty states are one of the most underdesigned parts of any product. They're the first thing a brand new user sees — and often the thing that determines whether they come back.

### Anatomy of a Good Empty State

```
[Illustration or icon]

[Friendly headline]
"You haven't added any tasks yet"

[Helpful context — optional]
"Tasks help you track work and stay on schedule."

[Clear call to action]
[+ Create your first task]
```

### Rules
- **Always include a CTA.** An empty state without an action leaves the user stranded.
- **Be specific.** "Nothing here yet" is useless. "You haven't connected any integrations — connect Slack to get started" is actionable.
- **Match the tone of the product.** A playful product can have a fun illustration. An enterprise tool should stay professional.
- **Don't use sad/broken imagery** (broken robots, crying faces) — it implies the product failed, not that the user just needs to add something.
- **Search empty states are different** — "No results for 'purple elephant'" needs different copy and a different CTA (clear search, refine filters) than a true empty state.

### Types of Empty States

| Type | Example | CTA |
|---|---|---|
| **First-use** | New user, no data created yet | Create first item |
| **Cleared** | User deleted everything | Undo or create new |
| **Search/filter** | No results match the query | Clear filters |
| **Error-caused** | Data failed to load | Retry |
| **Permission** | User can't see data | Request access |

### Empty State Checklist
- [ ] Every list, table, feed, or grid has a designed empty state
- [ ] Empty states include an illustration/icon, headline, and CTA
- [ ] Search/filter empty state is distinct from first-use empty state
- [ ] Copy is specific and helpful, not generic

---

## Error States

### Levels of Error

| Level | Examples | How to Handle |
|---|---|---|
| **Field validation** | Invalid email, password too short | Inline message below the field |
| **Form-level** | Missing required fields on submit | Summary at top + highlight fields |
| **Action failure** | "Save failed — try again" | Toast or inline error near the action |
| **Page-level** | 404, server error, network offline | Full error page with recovery action |
| **Partial failure** | 3 of 5 items loaded | Inline error on failed items, rest still usable |

### Rules
- **Say what went wrong AND what to do.** "Something went wrong" with no next step is a dead end.
- **Don't blame the user.** "You entered an invalid email" vs "The email address doesn't look right — check for typos." The second is kinder.
- **Error messages should be specific.** "Error 500" means nothing to a user. "We couldn't save your changes — check your connection and try again" is helpful.
- **Position errors close to the cause.** Field errors below the field. Form errors near the submit button. Don't show errors at the top of the page for a field at the bottom.
- **Preserve user input.** If a form fails, never clear the fields. Force the user to retype everything = guaranteed frustration.
- **Retry should be one click.** If something fails, a "Try again" button should be immediately available.

### Error State Checklist
- [ ] Field validation errors appear inline, below the field
- [ ] Error messages say what's wrong and how to fix it
- [ ] Failed actions have a retry option
- [ ] Page-level errors (404, 500) have a designed state, not a browser default
- [ ] Error messages never clear user's input
- [ ] Errors use both color AND text/icon (not color alone)

---

## Success States

Success states close the loop — they tell the user "yes, it worked." Without them, users click submit buttons twice, refresh pages, or simply don't know if their action completed.

### Patterns

| Pattern | Best For | Duration |
|---|---|---|
| **Toast / snackbar** | Non-critical confirmations ("Saved", "Copied") | 3–5 seconds, then auto-dismiss |
| **Inline confirmation** | Form submission, settings saved | Until next user action |
| **State change** | Button changes to "Saved ✓", item marked complete | Persistent until state changes |
| **Full screen** | Payment completed, account created | One-time, then redirect |
| **Email confirmation** | Account verification, order placed | The page becomes a holding state |

### Rules
- **Be specific.** "Saved" is fine. "Project 'Q4 Launch' saved" is better.
- **Auto-dismiss toasts after 3–5 seconds.** Persistent toasts that require manual dismissal block the UI.
- **Don't use green for everything.** Reserve green for genuine success. Confirmations that aren't "good news" (e.g., "Your account has been deleted") shouldn't be green.
- **Success states need to be accessible.** Toasts that appear and disappear must be announced to screen readers (`role="status"` or `aria-live="polite"`).

### Success State Checklist
- [ ] Every form submission has a visible success confirmation
- [ ] Toasts auto-dismiss and are screen-reader accessible
- [ ] Destructive actions (delete, cancel) confirm completion without using green

---

## Disabled States

### Rules
- **Look clearly different from enabled.** Reduced opacity (50–60%) is the standard pattern.
- **Never remove disabled elements entirely** — this is confusing. Show them, just make them unclickable.
- **Explain why when possible.** A tooltip on hover: "You need admin access to do this" is vastly better than a greyed-out button with no context.
- **Don't use color alone** to signal disabled — combine reduced opacity with `cursor: not-allowed` and `aria-disabled="true"`.
- **Disabled inputs** should still be readable (contrast ≥ 3:1 even in disabled state).

### Disabled State Checklist
- [ ] Disabled elements are visually distinct (opacity + cursor)
- [ ] Disabled state doesn't remove elements from the layout
- [ ] Where possible, a tooltip explains why the element is disabled
- [ ] `aria-disabled="true"` set for screen readers
