# UI Pattern Implementation Guide

## Table of Contents
- [Modal Dialogs](#modal-dialogs)
- [Toast Notifications](#toast-notifications)
- [Dropdown Menus](#dropdown-menus)
- [Tabs](#tabs)
- [Accordion](#accordion)
- [Data Tables](#data-tables)
- [Form Validation](#form-validation)
- [Infinite Scroll and Pagination](#infinite-scroll-and-pagination)

---

## Modal Dialogs

### Accessibility Requirements
- Focus trapped inside modal when open
- `role="dialog"` and `aria-modal="true"` on the container
- `aria-labelledby` pointing to the modal title
- Close on Escape key
- Return focus to trigger element when modal closes
- Backdrop prevents interaction with underlying content

### Implementation Checklist
- [ ] Focus moves to first focusable element (or the modal itself) on open
- [ ] Tab cycles through modal content only (focus trap)
- [ ] Escape key closes the modal
- [ ] Click outside (backdrop) closes the modal (unless confirmation dialog)
- [ ] Focus returns to the element that opened the modal
- [ ] Background content has `aria-hidden="true"` and `inert` when modal is open
- [ ] Scrolling is locked on the body while modal is open

### Confirmation Dialog Pattern
For destructive actions (delete, discard):
- Title states the action clearly: "Delete project?"
- Description explains the consequence: "This will permanently delete all files."
- Primary button uses the destructive action verb: "Delete" (not "OK" or "Yes")
- Secondary button: "Cancel"
- Primary button is NOT auto-focused for destructive actions

---

## Toast Notifications

### Design Guidelines
- Position: top-right or bottom-right (consistent across the app)
- Auto-dismiss: 5 seconds for success, 8 seconds for warnings, no auto-dismiss for errors
- Max visible: 3-5 toasts stacked
- Include dismiss button on all toasts
- Include action button when relevant (e.g., "Undo")

### Accessibility
- Use `role="status"` for informational toasts (polite announcement)
- Use `role="alert"` for error toasts (assertive announcement)
- Don't rely solely on color to convey meaning — include an icon and text
- Ensure toast text has sufficient contrast against the background
- Respect `prefers-reduced-motion` — disable slide-in animation

---

## Dropdown Menus

### Keyboard Navigation
- Enter/Space on trigger: opens the menu
- Arrow Down: moves focus to next item
- Arrow Up: moves focus to previous item
- Home: moves focus to first item
- End: moves focus to last item
- Escape: closes the menu, returns focus to trigger
- Type-ahead: typing a character moves focus to the first matching item

### ARIA Pattern
```html
<button aria-haspopup="true" aria-expanded="false" aria-controls="menu-id">
  Options
</button>
<ul role="menu" id="menu-id">
  <li role="menuitem" tabindex="-1">Edit</li>
  <li role="menuitem" tabindex="-1">Duplicate</li>
  <li role="separator"></li>
  <li role="menuitem" tabindex="-1">Delete</li>
</ul>
```

### Positioning
- Default: below the trigger, left-aligned
- Flip to above if insufficient space below
- Flip to right-aligned if it would overflow the viewport on the right
- Use CSS anchor positioning or a positioning library (Floating UI)

---

## Tabs

### ARIA Pattern
```html
<div role="tablist" aria-label="Settings">
  <button role="tab" aria-selected="true" aria-controls="panel-1" id="tab-1">
    General
  </button>
  <button role="tab" aria-selected="false" aria-controls="panel-2" id="tab-2" tabindex="-1">
    Security
  </button>
</div>
<div role="tabpanel" id="panel-1" aria-labelledby="tab-1">
  <!-- General settings content -->
</div>
<div role="tabpanel" id="panel-2" aria-labelledby="tab-2" hidden>
  <!-- Security settings content -->
</div>
```

### Keyboard Navigation
- Arrow Left/Right: moves between tabs
- Home: first tab
- End: last tab
- Tab key: moves focus from the tab list into the active panel content
- Only the active tab has `tabindex="0"`; inactive tabs have `tabindex="-1"`

### Activation Pattern
- **Automatic activation** (recommended): Tab content appears immediately on arrow key navigation
- **Manual activation**: Tab content appears only after pressing Enter/Space (use for heavy content loading)

---

## Accordion

### ARIA Pattern
```html
<div>
  <h3>
    <button aria-expanded="true" aria-controls="section-1">
      Section Title
    </button>
  </h3>
  <div id="section-1" role="region" aria-labelledby="button-id">
    <!-- Section content -->
  </div>
</div>
```

### Behavior
- Toggle individual sections (multi-expand) by default
- Single-expand (only one section open) is an option for space-constrained layouts
- Animate with `max-height` transition or the `<details>/<summary>` element
- Arrow Up/Down navigates between accordion headers (optional)

---

## Data Tables

### Responsive Strategies
- **Horizontal scroll** — Wrap table in a scrollable container (best for data-heavy tables)
- **Stacked rows** — Each row becomes a card on mobile (best for few columns)
- **Priority columns** — Hide low-priority columns, show in expand/detail view

### Sorting
- Click column header to sort ascending; click again for descending; click again to remove sort
- Visual indicator: arrow icon showing sort direction
- `aria-sort="ascending"`, `"descending"`, or `"none"` on the `<th>`

### Accessibility
- Use proper `<table>`, `<thead>`, `<tbody>`, `<th>`, `<td>` elements
- `<th scope="col">` for column headers, `<th scope="row">` for row headers
- `<caption>` for table description
- Row selection: use checkboxes, not row background color alone

---

## Form Validation

### Validation Timing
- **On blur** — Validate when user leaves a field (best balance of UX and early feedback)
- **On submit** — Validate all fields at once (simpler, but delayed feedback)
- **On input** — Validate as user types (use sparingly — only for format hints like password strength)
- Don't show errors before the user has interacted with the field

### Error Display Pattern
- Show error message directly below the invalid field
- Use `aria-describedby` to link the error message to the input
- Use `aria-invalid="true"` on invalid inputs
- Icon + text (not just color) to indicate errors
- Focus the first invalid field after form submission fails

### Error Message Guidelines
- State what's wrong and how to fix it
- Good: "Password must be at least 8 characters"
- Bad: "Invalid password"
- Bad: "Error in field 3"

---

## Infinite Scroll and Pagination

### When to Use Which
- **Pagination**: Data tables, search results, admin panels (users need to find specific items)
- **Infinite scroll**: Social feeds, image galleries, discovery-focused content
- **Load more button**: Compromise — user-initiated loading without page changes

### Infinite Scroll Accessibility
- Announce new content loaded: `aria-live="polite"` region
- Provide a way to reach the footer (footer shouldn't be unreachable)
- Consider a "Back to top" button
- Preserve scroll position on back navigation
- Show loading indicator during fetch

### Pagination Pattern
- Show: First, Previous, [page numbers], Next, Last
- Current page: `aria-current="page"`
- Show total count: "Showing 1-20 of 342 results"
- Allow page size selection: 10 / 25 / 50 / 100
- Keyboard accessible: all page buttons are focusable
