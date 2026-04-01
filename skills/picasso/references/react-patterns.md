# React Patterns Reference

## Table of Contents
1. Component Architecture
2. React 19 Features
3. State Management
4. Performance
5. Composition Patterns
6. Data Fetching & Mutations
7. Styling & Tailwind v4
8. Dark Mode Toggle
9. Common Mistakes

---

## 1. Component Architecture

### Server vs. Client Components
Default to Server Components. Add `'use client'` only when the component needs:
- Event handlers (onClick, onChange, etc.)
- useState, useEffect, useRef, or other hooks
- Browser APIs (window, document, navigator)
- Third-party libraries that use hooks or browser APIs

### File Organization
Colocate related files. Keep components, styles, tests, and types in the same directory:
```
components/
  user-card/
    user-card.tsx
    user-card.test.tsx
    types.ts
```

### Naming
- Components: PascalCase (`UserCard`, `DashboardHeader`)
- Files: kebab-case (`user-card.tsx`, `dashboard-header.tsx`)
- Hooks: camelCase with `use` prefix (`useAuth`, `useMediaQuery`)
- Event handlers: `handle` + event (`handleClick`, `handleSubmit`)
- Boolean props: `is`/`has`/`should` prefix (`isLoading`, `hasError`)

### Export Patterns
- **Default export**: page/route components and layout components
- **Named export**: everything else (utilities, hooks, shared components)

---

## 2. React 19 Features

### The `use` Hook
Read promises and context directly in render. Works inside conditionals and loops unlike other hooks:
```tsx
function UserProfile({ userPromise }: { userPromise: Promise<User> }) {
  const user = use(userPromise); // suspends until resolved
  return <h1>{user.name}</h1>;
}
```

### `useActionState` for Form Actions
Manages form state, pending status, and server action results in one hook:
```tsx
'use client';
import { useActionState } from 'react';
import { submitForm } from './actions';

function ContactForm() {
  const [state, formAction, isPending] = useActionState(submitForm, { message: '' });
  return (
    <form action={formAction}>
      <input name="email" type="email" required />
      <button disabled={isPending}>{isPending ? 'Sending...' : 'Submit'}</button>
    </form>
  );
}
```

### `useFormStatus` for Submission State
Access the parent form's pending state from within child components:
```tsx
'use client';
import { useFormStatus } from 'react-dom';

function SubmitButton() {
  const { pending } = useFormStatus();
  return <button disabled={pending}>{pending ? 'Saving...' : 'Save'}</button>;
}
```

### `useOptimistic` for Instant Feedback
Show optimistic state while an async action completes:
```tsx
const [optimistic, addOptimistic] = useOptimistic(
  messages,
  (current, newMsg: string) => [...current, { text: newMsg, pending: true }]
);
// Call addOptimistic(value) before await -- renders instantly, reverts on error
```

### React Compiler
React 19 ships with an opt-in compiler that auto-memoizes components, hooks, and expressions. When the compiler is enabled, remove manual `React.memo`, `useMemo`, and `useCallback` calls -- the compiler handles it. Check your project's `react-compiler` config before deciding whether to memoize manually.

---

## 3. State Management

### Where State Lives
1. **URL state**: filters, pagination, search queries (use `searchParams`)
2. **Server state**: data from APIs (use server components or React Query/SWR for client)
3. **Local state**: form inputs, UI toggles, hover/focus state (use `useState`)
4. **Shared local state**: state needed by siblings (lift to parent, or use context)
5. **Global state**: rarely needed (auth user, theme preference, feature flags)

### Rules
- Do not store derived state. Compute it during render.
- Do not sync state between sources. Pick one source of truth.
- Prefer `useReducer` over `useState` when the next state depends on the previous state or when managing more than 3 related state variables.

```tsx
// Bad: derived state in useEffect      // Good: compute during render
const [filtered, setFiltered] = useState([]);  const filtered = items.filter(i => i.active);
useEffect(() => setFiltered(items.filter(i => i.active)), [items]);
```

---

## 4. Performance

### Rendering
- With React Compiler enabled: skip manual `React.memo`, `useMemo`, `useCallback`
- Without the compiler: use `React.memo` only for components that re-render often with the same props; use `useMemo` for expensive computations only; use `useCallback` for callbacks passed to memoized children
- Use `key` props correctly (stable, unique identifiers, never array indices for reorderable lists)

### Code Splitting
Use `React.lazy` + `Suspense` for client components (works in Next.js App Router and plain React):
```tsx
const Chart = lazy(() => import('./chart'));
// Wrap in <Suspense fallback={<ChartSkeleton />}><Chart /></Suspense>
```
Next.js App Router also provides automatic route-level splitting per `page.tsx`/`layout.tsx`.

### Virtualization
For lists with 100+ items, use `@tanstack/virtual` or `react-window`.

### Image Optimization
Use `next/image` in Next.js or `loading="lazy"` with explicit `width`/`height`. Always set `aspect-ratio` to prevent layout shift.

---

## 5. Composition Patterns

### Compound Components
Components that share implicit state through context (e.g., `<Select>`, `<Select.Trigger>`, `<Select.Item>` pattern). Parent holds state, children consume via context.

### Slot Pattern
Flexible composition through named children (`header`, `children`, `footer` as props). Avoids rigid component trees and enables flexible layouts without render props.

---

## 6. Data Fetching & Mutations

### Server Components (preferred for reads)
```tsx
async function UserList() {
  const users = await fetch('/api/users').then(r => r.json());
  return <ul>{users.map(u => <li key={u.id}>{u.name}</li>)}</ul>;
}
```

### Server Actions (preferred for mutations)
Define actions in a `'use server'` file and call from client components via form `action`:
```tsx
// actions.ts
'use server';
import { revalidatePath } from 'next/cache';

export async function createTodo(formData: FormData) {
  await db.todo.create({ data: { title: formData.get('title') as string } });
  revalidatePath('/todos');
}
```
```tsx
// todo-form.tsx -- 'use client'
import { createTodo } from './actions';
export default function TodoForm() {
  return <form action={createTodo}><input name="title" required /><button>Add</button></form>;
}
```

Server Actions handle serialization, error boundaries, and progressive enhancement. Prefer them over API route handlers for mutations.

### Client-Side with Suspense + Error Boundaries
Always wrap data-fetching components:
```tsx
<ErrorBoundary fallback={<ErrorMessage />}>
  <Suspense fallback={<Skeleton />}>
    <DataComponent />
  </Suspense>
</ErrorBoundary>
```

---

## 7. Styling & Tailwind v4

### Tailwind v4 Changes
Tailwind v4 uses a CSS-first configuration model. Key differences from v3:

- **No `tailwind.config.js`**: configuration lives in CSS using the `@theme` directive
- **New import**: use `@import "tailwindcss"` instead of `@tailwind base/components/utilities` directives
- **CSS variables for all tokens**: every design token is automatically exposed as a CSS custom property (`--color-blue-500`, `--spacing-4`, etc.)

```css
/* app/globals.css */
@import "tailwindcss";

@theme {
  --color-brand: #6366f1;
  --color-surface: #ffffff;
  --color-surface-dark: #0f172a;
  --font-display: "Inter", sans-serif;
  --breakpoint-3xl: 1920px;
}
```

You can reference these tokens anywhere in CSS or JS via `var(--color-brand)` without any build-step workaround.

### Tailwind Best Practices
- Use Tailwind's core utility classes (pre-defined classes only in Claude artifacts)
- Extract repeated patterns into component variants, not `@apply` rules
- Use CSS variables for theme values, Tailwind utilities for everything else
- Never use more than ~10 utility classes on a single element; extract a component instead

### CSS Modules
For non-Tailwind projects:
```tsx
import styles from './button.module.css';
<button className={styles.primary}>Click</button>
```

### Semantic HTML
Use the right element: `<nav>` for navigation, `<main>` for primary content, `<section>` for thematic grouping, `<article>` for self-contained content, `<button>` for actions, `<a>` for navigation. Do not use bare `div` where semantic elements apply.

---

## 8. Dark Mode Toggle

Complete dark mode implementation with localStorage persistence, system preference detection, and flash prevention.

### Blocking Script (prevents flash of wrong theme)
Place inline in `<head>` before stylesheets (in Next.js, use `<script dangerouslySetInnerHTML>` in `app/layout.tsx`):
```html
<script>
  (function() {
    var s = localStorage.getItem('theme');
    var theme = s || (matchMedia('(prefers-color-scheme:dark)').matches ? 'dark' : 'light');
    document.documentElement.setAttribute('data-theme', theme);
  })();
</script>
```

### Theme Toggle Hook
```tsx
'use client';
function useTheme() {
  const [theme, setThemeState] = useState<'light' | 'dark'>(() =>
    typeof window === 'undefined' ? 'light'
      : (document.documentElement.getAttribute('data-theme') as 'light' | 'dark') || 'light'
  );
  const setTheme = useCallback((next: 'light' | 'dark') => {
    document.documentElement.setAttribute('data-theme', next);
    localStorage.setItem('theme', next);
    setThemeState(next);
  }, []);
  const toggle = useCallback(() => setTheme(theme === 'dark' ? 'light' : 'dark'), [theme, setTheme]);
  // Listen for system preference changes when no explicit choice is stored
  useEffect(() => {
    const mq = matchMedia('(prefers-color-scheme: dark)');
    const h = (e: MediaQueryListEvent) => { if (!localStorage.getItem('theme')) setTheme(e.matches ? 'dark' : 'light'); };
    mq.addEventListener('change', h);
    return () => mq.removeEventListener('change', h);
  }, [setTheme]);
  return { theme, setTheme, toggle };
}
```

### CSS Setup with Tailwind v4
```css
@import "tailwindcss";

@theme {
  --color-bg: #ffffff;
  --color-text: #0f172a;
  --color-surface: #f8fafc;
}

[data-theme="dark"] {
  --color-bg: #0f172a;
  --color-text: #f8fafc;
  --color-surface: #1e293b;
}
```

---

## 9. Common Mistakes

- Using `useEffect` for derived state (compute during render instead)
- Putting everything in global state (most state should be local or server-derived)
- Using `index` as `key` for dynamic lists
- Wrapping every component in `React.memo` (let the React Compiler handle this)
- Using `any` in TypeScript (defeats the purpose of type safety)
- Fetching data in `useEffect` when a server component would suffice
- Not using Suspense boundaries (the whole page flashes instead of parts loading independently)
- Prop drilling through 5+ levels (use composition or context)
- Using API route handlers for mutations when Server Actions are simpler
- Not using `useOptimistic` for actions that need instant visual feedback
- Manual memoization when the React Compiler is enabled (causes unnecessary code noise)
- Using `@tailwind` directives or `tailwind.config.js` in Tailwind v4 projects (use `@import "tailwindcss"` and `@theme` instead)
