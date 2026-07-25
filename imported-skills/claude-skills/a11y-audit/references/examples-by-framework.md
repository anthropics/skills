# Accessibility Audit Examples by Framework

## Example 1: Vue SFC Form Audit

```vue
<!-- BEFORE: src/components/LoginForm.vue -->
<template>
  <form @submit="handleLogin">
    <input type="text" placeholder="Email" v-model="email" />
    <input type="password" placeholder="Password" v-model="password" />
    <div v-if="error" style="color: red">{{ error }}</div>
    <div @click="handleLogin">Sign In</div>
  </form>
</template>
```

**Violations detected:**

| # | WCAG | Severity | Issue |
|---|------|----------|-------|
| 1 | 1.3.1 | Critical | Inputs missing associated `<label>` elements |
| 2 | 3.3.2 | Major | Placeholder text used as only label (disappears on input) |
| 3 | 2.1.1 | Critical | `<div @click>` not keyboard accessible |
| 4 | 4.1.3 | Major | Error message not announced to screen readers |
| 5 | 3.3.1 | Major | Error not programmatically associated with input |

```vue
<!-- AFTER: src/components/LoginForm.vue -->
<template>
  <form @submit.prevent="handleLogin" aria-label="Sign in to your account">
    <div class="field">
      <label for="login-email">Email</label>
      <input
        id="login-email"
        type="email"
        v-model="email"
        autocomplete="email"
        required
        :aria-describedby="emailError ? 'email-error' : undefined"
        :aria-invalid="!!emailError"
      />
      <span v-if="emailError" id="email-error" role="alert">
        {{ emailError }}
      </span>
    </div>
    <div class="field">
      <label for="login-password">Password</label>
      <input
        id="login-password"
        type="password"
        v-model="password"
        autocomplete="current-password"
        required
        :aria-describedby="passwordError ? 'password-error' : undefined"
        :aria-invalid="!!passwordError"
      />
      <span v-if="passwordError" id="password-error" role="alert">
        {{ passwordError }}
      </span>
    </div>
    <div v-if="error" role="alert" aria-live="assertive" class="form-error">
      {{ error }}
    </div>
    <button type="submit">Sign In</button>
  </form>
</template>
```

## Example 2: Angular Template Audit

```html
<!-- BEFORE: src/app/dashboard/dashboard.component.html -->
<div class="tabs">
  <div *ngFor="let tab of tabs"
       (click)="selectTab(tab)"
       [class.active]="tab.active">
    {{ tab.label }}
  </div>
</div>
<div class="tab-content">
  <div *ngIf="selectedTab">{{ selectedTab.content }}</div>
</div>
```

**Violations detected:**

| # | WCAG | Severity | Issue |
|---|------|----------|-------|
| 1 | 4.1.2 | Critical | Tab widget missing ARIA roles (`tablist`, `tab`, `tabpanel`) |
| 2 | 2.1.1 | Critical | Tabs not keyboard navigable (arrow keys, Home, End) |
| 3 | 2.4.11 | Major | No visible focus indicator on active tab |

```html
<!-- AFTER: src/app/dashboard/dashboard.component.html -->
<div class="tabs" role="tablist" aria-label="Dashboard sections">
  <button
    *ngFor="let tab of tabs; let i = index"
    role="tab"
    [id]="'tab-' + tab.id"
    [attr.aria-selected]="tab.active"
    [attr.aria-controls]="'panel-' + tab.id"
    [attr.tabindex]="tab.active ? 0 : -1"
    (click)="selectTab(tab)"
    (keydown)="handleTabKeydown($event, i)"
    class="tab-button"
    [class.active]="tab.active">
    {{ tab.label }}
  </button>
</div>
<div
  *ngIf="selectedTab"
  role="tabpanel"
  [id]="'panel-' + selectedTab.id"
  [attr.aria-labelledby]="'tab-' + selectedTab.id"
  tabindex="0"
  class="tab-content">
  {{ selectedTab.content }}
</div>
```

**Supporting TypeScript for keyboard navigation:**

```typescript
// dashboard.component.ts
handleTabKeydown(event: KeyboardEvent, index: number): void {
  const tabCount = this.tabs.length;
  let newIndex = index;

  switch (event.key) {
    case 'ArrowRight':
      newIndex = (index + 1) % tabCount;
      break;
    case 'ArrowLeft':
      newIndex = (index - 1 + tabCount) % tabCount;
      break;
    case 'Home':
      newIndex = 0;
      break;
    case 'End':
      newIndex = tabCount - 1;
      break;
    default:
      return;
  }

  event.preventDefault();
  this.selectTab(this.tabs[newIndex]);
  // Move focus to the new tab button
  const tabElement = document.getElementById(`tab-${this.tabs[newIndex].id}`);
  tabElement?.focus();
}
```

## Example 3: Next.js Page-Level Audit

```tsx
// BEFORE: src/app/page.tsx
export default function Home() {
  return (
    <main>
      <div className="text-4xl font-bold">Welcome to Acme</div>
      <div className="mt-4">
        Build better products with our platform.
      </div>
      <div className="mt-8 bg-blue-600 text-white px-6 py-3 rounded cursor-pointer"
           onClick={() => router.push('/signup')}>
        Get Started
      </div>
    </main>
  );
}
```

**Violations detected:**

| # | WCAG | Severity | Issue |
|---|------|----------|-------|
| 1 | 1.3.1 | Major | Heading uses `<div>` instead of `<h1>` -- no semantic structure |
| 2 | 2.4.2 | Major | Page missing `<title>` (Next.js metadata) |
| 3 | 2.1.1 | Critical | CTA uses `<div onClick>` -- not keyboard accessible |
| 4 | 3.1.1 | Minor | `<html>` missing `lang` attribute (check `layout.tsx`) |

```tsx
// AFTER: src/app/page.tsx
import type { Metadata } from 'next';
import Link from 'next/link';

export const metadata: Metadata = {
  title: 'Acme - Build Better Products',
  description: 'Build better products with the Acme platform.',
};

export default function Home() {
  return (
    <main>
      <h1 className="text-4xl font-bold">Welcome to Acme</h1>
      <p className="mt-4">
        Build better products with our platform.
      </p>
      <Link
        href="/signup"
        className="mt-8 inline-block bg-blue-600 text-white px-6 py-3 rounded
                   hover:bg-blue-700 focus-visible:outline focus-visible:outline-2
                   focus-visible:outline-offset-2 focus-visible:outline-blue-600"
      >
        Get Started
      </Link>
    </main>
  );
}
```

```tsx
// Also fix: src/app/layout.tsx
export default function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html lang="en">
      <body>{children}</body>
    </html>
  );
}
```

## Example 4: Svelte Component Audit

```svelte
<!-- BEFORE: src/lib/components/Accordion.svelte -->
<script>
  let openIndex = -1;
  function toggle(i) { openIndex = openIndex === i ? -1 : i; }
</script>

{#each items as item, i}
  <div class="header" on:click={() => toggle(i)}>
    {item.title}
  </div>
  {#if openIndex === i}
    <div class="content">{item.body}</div>
  {/if}
{/each}
```

**Violations detected:**

| # | WCAG | Severity | Issue |
|---|------|----------|-------|
| 1 | 4.1.2 | Critical | Accordion missing ARIA roles and properties |
| 2 | 2.1.1 | Critical | Headers not keyboard accessible |
| 3 | 2.5.8 | Minor | Click targets may be smaller than 24x24px (NEW in WCAG 2.2) |

```svelte
<!-- AFTER: src/lib/components/Accordion.svelte -->
<script>
  export let items = [];
  let openIndex = -1;

  function toggle(i) {
    openIndex = openIndex === i ? -1 : i;
  }

  function handleKeydown(event, i) {
    if (event.key === 'Enter' || event.key === ' ') {
      event.preventDefault();
      toggle(i);
    }
  }
</script>

<div class="accordion">
  {#each items as item, i}
    <h3>
      <button
        class="accordion-header"
        aria-expanded={openIndex === i}
        aria-controls="panel-{i}"
        id="header-{i}"
        on:click={() => toggle(i)}
        on:keydown={(e) => handleKeydown(e, i)}
      >
        {item.title}
        <span class="icon" aria-hidden="true">
          {openIndex === i ? '−' : '+'}
        </span>
      </button>
    </h3>
    <div
      id="panel-{i}"
      role="region"
      aria-labelledby="header-{i}"
      class="accordion-content"
      class:open={openIndex === i}
      hidden={openIndex !== i}
    >
      {item.body}
    </div>
  {/each}
</div>

<style>
  .accordion-header {
    min-height: 44px; /* WCAG 2.5.8 Target Size */
    width: 100%;
    padding: 12px 16px;
    cursor: pointer;
    text-align: left;
  }
  .accordion-header:focus-visible {
    outline: 2px solid #005fcc;
    outline-offset: 2px;
  }
</style>
```
