# ARIA Patterns & Keyboard Interaction Reference

## Landmark Roles

Every page should have these landmarks:

```html
<header role="banner">         <!-- Site header — once per page -->
<nav role="navigation">         <!-- Navigation — can have multiple with aria-label -->
<main role="main">              <!-- Main content — once per page -->
<aside role="complementary">    <!-- Sidebar — related but not essential -->
<footer role="contentinfo">     <!-- Site footer — once per page -->
<form role="search">            <!-- Search form -->
```

**Semantic HTML equivalents:** `<header>`, `<nav>`, `<main>`, `<aside>`, `<footer>` provide implicit roles — no need to double up with explicit `role` attributes.

## Live Regions

### When to Use

| Pattern | Attribute | Use Case |
|---------|-----------|----------|
| Polite | `aria-live="polite"` | Toast notifications, status updates, search result counts |
| Assertive | `aria-live="assertive"` | Error messages, urgent alerts, form validation errors |
| Status | `role="status"` | Loading indicators, progress updates |
| Alert | `role="alert"` | Error dialogs, time-sensitive warnings |
| Log | `role="log"` | Chat messages, activity feeds |
| Timer | `role="timer"` | Countdown timers |

### Implementation

```html
<!-- Toast notifications -->
<div aria-live="polite" aria-atomic="true">
  <!-- Inject toast content here dynamically -->
</div>

<!-- Form validation errors -->
<div aria-live="assertive" role="alert">
  <p>Please enter a valid email address.</p>
</div>

<!-- Loading state -->
<div role="status" aria-live="polite">
  Loading results...
</div>
```

**Key rule:** The live region container must exist in the DOM *before* content is injected. Adding `aria-live` to a newly created element won't announce it.

## Focus Management

### Focus Trap (Modals)

```javascript
// Trap focus inside modal
const modal = document.querySelector('[role="dialog"]');
const focusable = modal.querySelectorAll(
  'a[href], button, textarea, input, select, [tabindex]:not([tabindex="-1"])'
);
const first = focusable[0];
const last = focusable[focusable.length - 1];

modal.addEventListener('keydown', (e) => {
  if (e.key === 'Tab') {
    if (e.shiftKey && document.activeElement === first) {
      e.preventDefault();
      last.focus();
    } else if (!e.shiftKey && document.activeElement === last) {
      e.preventDefault();
      first.focus();
    }
  }
  if (e.key === 'Escape') closeModal();
});
```

### Focus Restoration

```javascript
// Save focus before opening modal
const trigger = document.activeElement;
openModal();

// Restore focus on close
function closeModal() {
  modal.hidden = true;
  trigger.focus();
}
```

### Skip Link

```html
<a href="#main-content" class="skip-link">Skip to main content</a>
<!-- ... navigation ... -->
<main id="main-content" tabindex="-1">
```

```css
.skip-link {
  position: absolute;
  left: -9999px;
  z-index: 999;
}
.skip-link:focus {
  left: 10px;
  top: 10px;
  background: #000;
  color: #fff;
  padding: 8px 16px;
}
```

## Keyboard Interaction Patterns

### Tabs

```
Tab          → Move to tab list, then to tab panel
Arrow Left/Right → Switch between tabs
Home         → First tab
End          → Last tab
```

```html
<div role="tablist" aria-label="Settings">
  <button role="tab" aria-selected="true" aria-controls="panel-1" id="tab-1">General</button>
  <button role="tab" aria-selected="false" aria-controls="panel-2" id="tab-2" tabindex="-1">Security</button>
</div>
<div role="tabpanel" id="panel-1" aria-labelledby="tab-1">...</div>
<div role="tabpanel" id="panel-2" aria-labelledby="tab-2" hidden>...</div>
```

### Combobox / Autocomplete

```
Arrow Down   → Open list / next option
Arrow Up     → Previous option
Enter        → Select option
Escape       → Close list
Type         → Filter options
```

### Menu

```
Enter/Space  → Activate item
Arrow Down   → Next item
Arrow Up     → Previous item
Arrow Right  → Open submenu
Arrow Left   → Close submenu
Escape       → Close menu
```

### Accordion

```
Enter/Space  → Toggle section
Arrow Down   → Next header
Arrow Up     → Previous header
Home         → First header
End          → Last header
```

## Framework-Specific ARIA

### React

```jsx
// Announce route changes (SPA)
<div aria-live="polite" className="sr-only">
  {`Navigated to ${pageTitle}`}
</div>

// Error boundary with accessible error
<div role="alert">
  <h2>Something went wrong</h2>
  <p>{error.message}</p>
</div>
```

### Vue

```vue
<!-- Announce dynamic content -->
<div aria-live="polite">
  <p v-if="results.length">{{ results.length }} results found</p>
</div>

<!-- Accessible toggle -->
<button
  :aria-expanded="isOpen"
  :aria-controls="panelId"
  @click="toggle"
>
  {{ isOpen ? 'Collapse' : 'Expand' }}
</button>
```

### Angular

```html
<!-- cdkTrapFocus for modals -->
<div cdkTrapFocus cdkTrapFocusAutoCapture role="dialog" aria-labelledby="dialog-title">
  <h2 id="dialog-title">Confirm Action</h2>
</div>

<!-- LiveAnnouncer service -->
<!-- In component: this.liveAnnouncer.announce('Item added to cart'); -->
```

## Common ARIA Mistakes

| Mistake | Why It's Wrong | Fix |
|---------|---------------|-----|
| `<div role="button">` without keyboard | Div doesn't get keyboard events | Use `<button>` or add `tabindex="0"` + `onkeydown` |
| `aria-hidden="true"` on focusable element | Screen reader skips it but keyboard reaches it | Remove from tab order too: `tabindex="-1"` |
| `aria-label` overriding visible text | Confusing for sighted screen reader users | Use `aria-labelledby` pointing to visible text |
| Redundant ARIA on semantic HTML | `<nav role="navigation">` is redundant | Drop the `role` — `<nav>` implies it |
| `aria-live` on container that already has content | Initial content gets announced on load | Add `aria-live` to empty container, inject content after |
| Missing `aria-expanded` on toggles | Screen reader can't tell if section is open | Add `aria-expanded="true/false"` |
