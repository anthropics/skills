# Framework-Specific Accessibility Patterns

## React / Next.js

### Common Issues and Fixes

**Image alt text:**
```jsx
// ❌ Bad
<img src="/hero.jpg" />
<Image src="/hero.jpg" width={800} height={400} />

// ✅ Good
<img src="/hero.jpg" alt="Team collaborating in office" />
<Image src="/hero.jpg" width={800} height={400} alt="Team collaborating in office" />

// ✅ Decorative image
<img src="/divider.svg" alt="" role="presentation" />
```

**Form labels:**
```jsx
// ❌ Bad — placeholder as label
<input placeholder="Email" type="email" />

// ✅ Good — explicit label
<label htmlFor="email">Email</label>
<input id="email" type="email" placeholder="user@example.com" />

// ✅ Good — aria-label for icon-only inputs
<input type="search" aria-label="Search products" />
```

**Click handlers on divs:**
```jsx
// ❌ Bad — not keyboard accessible
<div onClick={handleClick}>Click me</div>

// ✅ Good — use button
<button onClick={handleClick}>Click me</button>

// ✅ If div is required — add keyboard support
<div
  role="button"
  tabIndex={0}
  onClick={handleClick}
  onKeyDown={(e) => { if (e.key === 'Enter' || e.key === ' ') handleClick(); }}
>
  Click me
</div>
```

**SPA route announcements (Next.js App Router):**
```jsx
// Layout component — announce page changes
'use client';
import { usePathname } from 'next/navigation';
import { useEffect, useState } from 'react';

export function RouteAnnouncer() {
  const pathname = usePathname();
  const [announcement, setAnnouncement] = useState('');

  useEffect(() => {
    const title = document.title;
    setAnnouncement(`Navigated to ${title}`);
  }, [pathname]);

  return (
    <div aria-live="assertive" role="status" className="sr-only">
      {announcement}
    </div>
  );
}
```

**Focus management after dynamic content:**
```jsx
// After adding item to list, announce it
const [items, setItems] = useState([]);
const statusRef = useRef(null);

const addItem = (item) => {
  setItems([...items, item]);
  // Announce to screen readers
  statusRef.current.textContent = `${item.name} added to list`;
};

return (
  <>
    <div ref={statusRef} aria-live="polite" className="sr-only" />
    {/* list content */}
  </>
);
```

### React-Specific Libraries
- `@radix-ui/*` — accessible primitives (Dialog, Tabs, Select, etc.)
- `@headlessui/react` — unstyled accessible components
- `react-aria` — Adobe's accessibility hooks
- `eslint-plugin-jsx-a11y` — lint rules for JSX accessibility

## Vue 3

### Common Issues and Fixes

**Dynamic content announcements:**
```vue
<template>
  <div aria-live="polite" class="sr-only">
    {{ announcement }}
  </div>
  <button @click="search">Search</button>
  <ul v-if="results.length">
    <li v-for="r in results" :key="r.id">{{ r.name }}</li>
  </ul>
</template>

<script setup>
import { ref } from 'vue';
const results = ref([]);
const announcement = ref('');

async function search() {
  results.value = await fetchResults();
  announcement.value = `${results.value.length} results found`;
}
</script>
```

**Conditional rendering with focus:**
```vue
<template>
  <button @click="showForm = true">Add Item</button>
  <form v-if="showForm" ref="formRef">
    <label for="name">Name</label>
    <input id="name" ref="nameInput" />
  </form>
</template>

<script setup>
import { ref, nextTick } from 'vue';
const showForm = ref(false);
const nameInput = ref(null);

watch(showForm, async (val) => {
  if (val) {
    await nextTick();
    nameInput.value?.focus();
  }
});
</script>
```

### Vue-Specific Libraries
- `vue-announcer` — route change announcements
- `@headlessui/vue` — accessible components
- `eslint-plugin-vuejs-accessibility` — lint rules

## Angular

### Common Issues and Fixes

**CDK accessibility utilities:**
```typescript
import { LiveAnnouncer } from '@angular/cdk/a11y';
import { FocusTrapFactory } from '@angular/cdk/a11y';

@Component({...})
export class MyComponent {
  constructor(
    private liveAnnouncer: LiveAnnouncer,
    private focusTrapFactory: FocusTrapFactory
  ) {}

  addItem(item: Item) {
    this.items.push(item);
    this.liveAnnouncer.announce(`${item.name} added`);
  }

  openDialog(element: HTMLElement) {
    const focusTrap = this.focusTrapFactory.create(element);
    focusTrap.focusInitialElement();
  }
}
```

**Template-driven forms:**
```html
<!-- ❌ Bad -->
<input [formControl]="email" placeholder="Email" />

<!-- ✅ Good -->
<label for="email">Email address</label>
<input id="email" [formControl]="email"
       [attr.aria-invalid]="email.invalid && email.touched"
       [attr.aria-describedby]="email.invalid ? 'email-error' : null" />
<div id="email-error" *ngIf="email.invalid && email.touched" role="alert">
  Please enter a valid email address.
</div>
```

### Angular-Specific Tools
- `@angular/cdk/a11y` — `FocusTrap`, `LiveAnnouncer`, `FocusMonitor`
- `codelyzer` — a11y lint rules for Angular templates

## Svelte / SvelteKit

### Common Issues and Fixes

```svelte
<!-- ❌ Bad — on:click without keyboard -->
<div on:click={handleClick}>Action</div>

<!-- ✅ Good — Svelte a11y warning built-in -->
<button on:click={handleClick}>Action</button>

<!-- ✅ Accessible toggle -->
<button
  on:click={() => isOpen = !isOpen}
  aria-expanded={isOpen}
  aria-controls="panel"
>
  {isOpen ? 'Close' : 'Open'} Details
</button>

{#if isOpen}
  <div id="panel" role="region" aria-labelledby="toggle-btn">
    Panel content
  </div>
{/if}
```

**Note:** Svelte has built-in a11y warnings in the compiler — it flags missing alt text, click-without-keyboard, and other common issues at build time.

## Plain HTML

### Checklist for Static Sites

```html
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Descriptive Page Title</title>
</head>
<body>
  <!-- Skip link -->
  <a href="#main" class="skip-link">Skip to main content</a>

  <header>
    <nav aria-label="Main navigation">
      <ul>
        <li><a href="/">Home</a></li>
        <li><a href="/about" aria-current="page">About</a></li>
      </ul>
    </nav>
  </header>

  <main id="main" tabindex="-1">
    <h1>Page Heading</h1>
    <!-- Only one h1 per page -->
    <!-- Heading levels don't skip (h1 → h2 → h3, never h1 → h3) -->
  </main>

  <footer>
    <p>&copy; 2026 Company Name</p>
  </footer>
</body>
</html>
```

## CSS Accessibility Patterns

### Focus Indicators

```css
/* ❌ Bad — removes focus indicator entirely */
:focus { outline: none; }

/* ✅ Good — custom focus indicator */
:focus-visible {
  outline: 2px solid #005fcc;
  outline-offset: 2px;
}

/* ✅ Good — enhanced for high contrast mode */
@media (forced-colors: active) {
  :focus-visible {
    outline: 2px solid ButtonText;
  }
}
```

### Reduced Motion

```css
/* ✅ Respect prefers-reduced-motion */
@media (prefers-reduced-motion: reduce) {
  *, *::before, *::after {
    animation-duration: 0.01ms !important;
    animation-iteration-count: 1 !important;
    transition-duration: 0.01ms !important;
  }
}
```

### Screen Reader Only

```css
.sr-only {
  position: absolute;
  width: 1px;
  height: 1px;
  padding: 0;
  margin: -1px;
  overflow: hidden;
  clip: rect(0, 0, 0, 0);
  white-space: nowrap;
  border-width: 0;
}
```

## Fix Patterns Catalog

### React / Next.js Fix Patterns

#### Missing Alt Text (1.1.1)

```tsx
// BEFORE
<img src={hero} />

// AFTER - Informational image
<img src={hero} alt="Team collaborating around a whiteboard" />

// AFTER - Decorative image
<img src={divider} alt="" role="presentation" />
```

#### Non-Interactive Element with Click Handler (2.1.1)

```tsx
// BEFORE
<div onClick={handleClick}>Click me</div>

// AFTER - If it navigates
<Link href="/destination">Click me</Link>

// AFTER - If it performs an action
<button type="button" onClick={handleClick}>Click me</button>
```

#### Missing Focus Management in Modals (2.4.3)

```tsx
// BEFORE
function Modal({ isOpen, onClose, children }) {
  if (!isOpen) return null;
  return <div className="modal-overlay">{children}</div>;
}

// AFTER
import { useEffect, useRef } from 'react';

function Modal({ isOpen, onClose, children, title }) {
  const modalRef = useRef(null);
  const previousFocus = useRef(null);

  useEffect(() => {
    if (isOpen) {
      previousFocus.current = document.activeElement;
      modalRef.current?.focus();
    } else {
      previousFocus.current?.focus();
    }
  }, [isOpen]);

  useEffect(() => {
    if (!isOpen) return;
    const handleKeydown = (e) => {
      if (e.key === 'Escape') onClose();
      if (e.key === 'Tab') {
        const focusable = modalRef.current?.querySelectorAll(
          'button, [href], input, select, textarea, [tabindex]:not([tabindex="-1"])'
        );
        if (!focusable?.length) return;
        const first = focusable[0];
        const last = focusable[focusable.length - 1];
        if (e.shiftKey && document.activeElement === first) {
          e.preventDefault();
          last.focus();
        } else if (!e.shiftKey && document.activeElement === last) {
          e.preventDefault();
          first.focus();
        }
      }
    };
    document.addEventListener('keydown', handleKeydown);
    return () => document.removeEventListener('keydown', handleKeydown);
  }, [isOpen, onClose]);

  if (!isOpen) return null;

  return (
    <div className="modal-overlay" onClick={onClose} aria-hidden="true">
      <div
        ref={modalRef}
        role="dialog"
        aria-modal="true"
        aria-label={title}
        tabIndex={-1}
        onClick={(e) => e.stopPropagation()}
      >
        <button
          onClick={onClose}
          aria-label="Close dialog"
          className="modal-close"
        >
          &times;
        </button>
        {children}
      </div>
    </div>
  );
}
```

#### Focus Appearance (2.4.11 -- NEW in WCAG 2.2)

```css
/* BEFORE */
button:focus {
  outline: none; /* Removes default focus indicator */
}

/* AFTER - Meets WCAG 2.2 Focus Appearance */
button:focus-visible {
  outline: 2px solid #005fcc;
  outline-offset: 2px;
}
```

```tsx
// Tailwind CSS pattern
<button className="focus-visible:outline focus-visible:outline-2 focus-visible:outline-offset-2 focus-visible:outline-blue-600">
  Submit
</button>
```

### Vue Fix Patterns

#### Missing Form Labels (1.3.1)

```vue
<!-- BEFORE -->
<input type="text" v-model="name" placeholder="Name" />

<!-- AFTER -->
<label for="user-name">Name</label>
<input id="user-name" type="text" v-model="name" autocomplete="name" />
```

#### Dynamic Content Without Live Region (4.1.3)

```vue
<!-- BEFORE -->
<div v-if="status">{{ statusMessage }}</div>

<!-- AFTER -->
<div aria-live="polite" aria-atomic="true">
  <p v-if="status">{{ statusMessage }}</p>
</div>
```

#### Vue Router Navigation Announcements (2.4.2)

```typescript
// router/index.ts
router.afterEach((to) => {
  const title = to.meta.title || 'Page';
  document.title = `${title} | My App`;

  // Announce route change to screen readers
  const announcer = document.getElementById('route-announcer');
  if (announcer) {
    announcer.textContent = `Navigated to ${title}`;
  }
});
```

```vue
<!-- App.vue - Add announcer element -->
<div
  id="route-announcer"
  role="status"
  aria-live="assertive"
  aria-atomic="true"
  class="sr-only"
></div>
```

### Angular Fix Patterns

#### Missing ARIA on Custom Components (4.1.2)

```typescript
// BEFORE
@Component({
  selector: 'app-dropdown',
  template: `
    <div (click)="toggle()">{{ selected }}</div>
    <div *ngIf="isOpen">
      <div *ngFor="let opt of options" (click)="select(opt)">{{ opt }}</div>
    </div>
  `
})

// AFTER
@Component({
  selector: 'app-dropdown',
  template: `
    <button
      role="combobox"
      [attr.aria-expanded]="isOpen"
      aria-haspopup="listbox"
      [attr.aria-label]="label"
      (click)="toggle()"
      (keydown)="handleKeydown($event)"
    >
      {{ selected }}
    </button>
    <ul *ngIf="isOpen" role="listbox" [attr.aria-label]="label + ' options'">
      <li
        *ngFor="let opt of options; let i = index"
        role="option"
        [attr.aria-selected]="opt === selected"
        [attr.id]="'option-' + i"
        (click)="select(opt)"
        (keydown)="handleOptionKeydown($event, opt, i)"
        tabindex="-1"
      >
        {{ opt }}
      </li>
    </ul>
  `
})
```

#### Angular CDK A11y Module Integration

```typescript
// Use Angular CDK for focus trap in dialogs
import { A11yModule } from '@angular/cdk/a11y';

@Component({
  template: `
    <div cdkTrapFocus cdkTrapFocusAutoCapture>
      <h2 id="dialog-title">Edit Profile</h2>
      <!-- dialog content -->
    </div>
  `
})
```

### Svelte Fix Patterns

#### Accessible Announcements (4.1.3)

```svelte
<!-- BEFORE -->
{#if message}
  <p class="toast">{message}</p>
{/if}

<!-- AFTER -->
<div aria-live="polite" class="sr-only">
  {#if message}
    <p>{message}</p>
  {/if}
</div>
<div class="toast" aria-hidden="true">
  {#if message}
    <p>{message}</p>
  {/if}
</div>
```

#### SvelteKit Page Titles (2.4.2)

```svelte
<!-- +page.svelte -->
<svelte:head>
  <title>Dashboard | My App</title>
</svelte:head>
```

### Plain HTML Fix Patterns

#### Skip Navigation Link (2.4.1)

```html
<!-- BEFORE -->
<body>
  <nav><!-- long navigation --></nav>
  <main><!-- content --></main>
</body>

<!-- AFTER -->
<body>
  <a href="#main-content" class="skip-link">Skip to main content</a>
  <nav aria-label="Main navigation"><!-- long navigation --></nav>
  <main id="main-content" tabindex="-1"><!-- content --></main>
</body>
```

```css
.skip-link {
  position: absolute;
  top: -40px;
  left: 0;
  padding: 8px 16px;
  background: #005fcc;
  color: #fff;
  z-index: 1000;
  transition: top 0.2s;
}
.skip-link:focus {
  top: 0;
}
```

#### Accessible Data Table (1.3.1)

```html
<!-- BEFORE -->
<table>
  <tr><td>Name</td><td>Email</td><td>Role</td></tr>
  <tr><td>Alice</td><td>alice@co.com</td><td>Admin</td></tr>
</table>

<!-- AFTER -->
<table aria-label="Team members">
  <caption class="sr-only">List of team members and their roles</caption>
  <thead>
    <tr>
      <th scope="col">Name</th>
      <th scope="col">Email</th>
      <th scope="col">Role</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <th scope="row">Alice</th>
      <td>alice@co.com</td>
      <td>Admin</td>
    </tr>
  </tbody>
</table>
```
