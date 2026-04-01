# Interaction Design Reference

## Table of Contents
1. Form Design
2. Focus Management
3. Loading Patterns
4. Empty States
5. Error Handling
6. UX Writing
7. Common Mistakes

---

## 1. Form Design

### Input Fields
- Use visible labels above inputs, not placeholder-only labels (placeholders disappear on focus)
- Input height: 40-48px for desktop, 48px minimum for touch
- Group related fields visually (name + email, street + city + zip)
- Show validation inline, not in an alert after submission
- Use `inputmode` attribute for mobile keyboards: `inputmode="email"`, `inputmode="numeric"`, `inputmode="tel"`
- Auto-focus the first field on page load when the form is the primary task

### Field States
Every input needs four visible states:
1. **Default**: subtle border, neutral background
2. **Focus**: accent border (2px), subtle glow or shadow
3. **Error**: error-colored border, inline error message below the field
4. **Disabled**: reduced opacity (0.5), `cursor: not-allowed`

### Buttons
- Primary action: filled, high contrast (accent color)
- Secondary action: outlined or ghost (border only)
- Destructive action: red/error color, requires confirmation for irreversible actions
- Button text: verb-first ("Save changes", "Create project"), never "Submit" or "Click here"
- Loading state: replace text with spinner or use `aria-busy="true"`, disable the button to prevent double-submission

---

## 2. Focus Management

### Focus Indicators
Never remove focus outlines without replacement. Use a visible, high-contrast focus ring:
```css
:focus-visible {
  outline: 2px solid var(--accent);
  outline-offset: 2px;
}
```

Use `:focus-visible` (not `:focus`) to show focus rings only for keyboard navigation, not mouse clicks.

### Focus Trapping
Modal dialogs must trap focus within them. When a modal opens:
1. Move focus to the first focusable element inside
2. Tab cycles within the modal
3. Escape closes the modal
4. Focus returns to the trigger element on close

### Skip Links
Add a skip-to-content link as the first focusable element:
```html
<a href="#main-content" class="skip-link">Skip to content</a>
```
```css
.skip-link {
  position: absolute;
  top: -100%;
  left: 0;
}
.skip-link:focus {
  top: 0;
  z-index: 1000;
}
```

---

## 3. Loading Patterns

### Skeleton Screens
Replace content with gray shapes that match the expected layout. This feels faster than a spinner because the user can see the structure forming.

### Progressive Loading
Show content as it arrives. Do not wait for everything to load before showing anything. Use `Suspense` boundaries in React to show parts of the page while others load.

### Optimistic Updates
For user-initiated actions (like, save, delete), update the UI immediately and reconcile with the server response. Show a subtle undo option if the server rejects the action.

### Spinner vs. Skeleton
- **Spinner**: Use for actions that take 1-3 seconds (button submissions, API calls). Place inside the triggering element.
- **Skeleton**: Use for content areas that take 0.5-5 seconds to load. Match the shape of the expected content.
- **Progress bar**: Use for operations that take 5+ seconds with measurable progress (file uploads, multi-step processes).

---

## 4. Empty States

Empty states are an opportunity, not a placeholder. They should:
1. Explain what this area will contain once populated
2. Provide a clear action to get started
3. Optionally include an illustration or icon for warmth

```
No projects yet.
Create your first project to get started.
[+ Create Project]
```

Never show a blank page, an error message, or raw "null" / "undefined" in place of empty content.

---

## 5. Error Handling

### Inline Errors
Show errors next to the element that caused them, not in a modal or toast. Use the error color for the field border and display the message directly below.

### Error Messages
- Be specific: "Email address must include an @ symbol" not "Invalid input"
- Be helpful: suggest the fix, not just the problem
- Be human: "We couldn't find that page" not "404 Not Found"

### Network Errors
Show a non-blocking banner or inline message with a retry action. Never show a raw error object or stack trace.

### Form Validation
Validate on blur (when the user leaves a field), not on every keystroke. Show success indicators for valid fields (subtle checkmark or green border).

---

## 6. UX Writing

### Buttons
- Use action verbs: "Save", "Send", "Create", "Delete"
- Be specific: "Save changes" > "Save", "Send message" > "Send"
- Match the action to the context: "Place order" not "Submit"

### Labels
- Clear and concise: "Full name" not "Please enter your full name"
- Avoid jargon: "Phone number" not "Primary contact number"

### Confirmations
- State what happened: "Project created successfully"
- Provide next step if relevant: "Project created. Add your first task?"

### Destructive Actions
- State what will happen: "This will permanently delete 3 files"
- Require explicit confirmation: "Type DELETE to confirm"
- Provide an out: "Cancel" should be more prominent than "Delete"

---

## 7. Common Mistakes

- Placeholder text as the only label (disappears on focus, inaccessible)
- Disabling the submit button before all fields are filled (users do not know which field is missing)
- Using toast notifications for errors (the user may not see them, they disappear)
- No loading feedback after clicking a button (user clicks again, causing duplicate submissions)
- Custom scrollbars that break native scroll behavior
- Hover-only interactions with no keyboard or touch equivalent
- Alert/confirm dialogs that block the entire page for minor confirmations
