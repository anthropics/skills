# React Patterns Reference

## Table of Contents
1. Component Architecture
2. State Management
3. Performance
4. Composition Patterns
5. Data Fetching
6. Styling
7. Common Mistakes

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
    user-card.module.css
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

## 2. State Management

### Where State Lives
1. **URL state**: filters, pagination, search queries (use `searchParams`)
2. **Server state**: data from APIs (use React Query, SWR, or server components)
3. **Local state**: form inputs, UI toggles, hover/focus state (use `useState`)
4. **Shared local state**: state needed by siblings (lift to parent, or use context)
5. **Global state**: rarely needed (auth user, theme preference, feature flags)

### Rules
- Do not store derived state. Compute it during render.
- Do not sync state between sources. Pick one source of truth.
- Prefer `useReducer` over `useState` when the next state depends on the previous state or when managing more than 3 related state variables.

```tsx
// Bad: storing derived state
const [items, setItems] = useState(data);
const [filteredItems, setFilteredItems] = useState([]);
useEffect(() => {
  setFilteredItems(items.filter(i => i.active));
}, [items]);

// Good: compute during render
const [items, setItems] = useState(data);
const filteredItems = items.filter(i => i.active);
```

---

## 3. Performance

### Rendering
- Use `React.memo` only for components that re-render often with the same props
- Use `useMemo` for expensive computations, not for every variable
- Use `useCallback` for callbacks passed to memoized children
- Use `key` props correctly (stable, unique identifiers, never array indices for reorderable lists)

### Code Splitting
```tsx
import dynamic from 'next/dynamic';

const Chart = dynamic(() => import('./chart'), {
  loading: () => <ChartSkeleton />,
  ssr: false,
});
```

### Virtualization
For lists with 100+ items, use `react-window` or `@tanstack/virtual`:
```tsx
import { FixedSizeList } from 'react-window';

<FixedSizeList height={600} itemCount={items.length} itemSize={48} width="100%">
  {({ index, style }) => <Row style={style} item={items[index]} />}
</FixedSizeList>
```

### Image Optimization
Use `next/image` in Next.js or `loading="lazy"` with explicit `width`/`height` attributes. Always set `aspect-ratio` to prevent layout shift.

---

## 4. Composition Patterns

### Compound Components
Components that share implicit state through context:
```tsx
<Select value={value} onChange={setValue}>
  <Select.Trigger>Choose a fruit</Select.Trigger>
  <Select.Content>
    <Select.Item value="apple">Apple</Select.Item>
    <Select.Item value="banana">Banana</Select.Item>
  </Select.Content>
</Select>
```

### Slot Pattern
Flexible component composition through named children:
```tsx
function Card({ header, children, footer }) {
  return (
    <div className="card">
      {header && <div className="card-header">{header}</div>}
      <div className="card-body">{children}</div>
      {footer && <div className="card-footer">{footer}</div>}
    </div>
  );
}
```

### Render Props (when needed)
For components that need to share behavior, not UI:
```tsx
<DataFetcher url="/api/users">
  {({ data, isLoading }) => isLoading ? <Skeleton /> : <UserList users={data} />}
</DataFetcher>
```

---

## 5. Data Fetching

### Server Components (preferred)
```tsx
async function UserList() {
  const users = await fetch('/api/users').then(r => r.json());
  return <ul>{users.map(u => <li key={u.id}>{u.name}</li>)}</ul>;
}
```

### Client-Side with Suspense
```tsx
function Dashboard() {
  return (
    <Suspense fallback={<DashboardSkeleton />}>
      <DashboardContent />
    </Suspense>
  );
}
```

### Error Boundaries
Wrap data-fetching components in error boundaries:
```tsx
<ErrorBoundary fallback={<ErrorMessage />}>
  <Suspense fallback={<Skeleton />}>
    <DataComponent />
  </Suspense>
</ErrorBoundary>
```

---

## 6. Styling

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
Use the right element, not just `div` with classes:
- `<nav>` for navigation
- `<main>` for primary content
- `<section>` for thematic grouping
- `<article>` for self-contained content
- `<aside>` for tangentially related content
- `<header>` and `<footer>` for their semantic purpose
- `<button>` for clickable actions, `<a>` for navigation

---

## 7. Common Mistakes

- Using `useEffect` for derived state (compute during render instead)
- Putting everything in global state (most state should be local or server-derived)
- Using `index` as `key` for dynamic lists
- Wrapping every component in `React.memo`
- Using `any` in TypeScript (defeats the purpose of type safety)
- Fetching data in `useEffect` when a server component would suffice
- Not using Suspense boundaries (the whole page flashes instead of parts loading independently)
- Prop drilling through 5+ levels (use composition or context)
