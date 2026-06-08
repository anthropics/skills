# Frontend Frameworks (2025-2026)

## React 19 — What Actually Changed

React 19 shipped stable in December 2024. The headline changes that matter in production:

### React Compiler
The React Compiler (formerly React Forget) automatically memoizes components and hooks. It eliminates the need for manual `useMemo`, `useCallback`, and `memo()` wrapping by analyzing code at compile time. Enable in Next.js 15 via `next.config.ts`:
```ts
const nextConfig = {
  experimental: { reactCompiler: true }
};
```
Adoption strategy: enable globally, then use `"use no memo"` directive on components that break. The compiler understands JavaScript semantics and the Rules of React — it won't memoize incorrectly.

### New Hooks: useActionState, useFormStatus, useOptimistic, use()

**useActionState** — replaces the old useFormState pattern. Tracks the full action lifecycle:
```tsx
const [state, submitAction, isPending] = useActionState(
  async (prevState, formData) => {
    const result = await createPost(formData);
    if (!result.success) return { error: result.error };
    redirect('/posts');
  },
  { error: null }
);
```

**useFormStatus** — reads parent form submission state. Must be called in a child component of the `<form>`:
```tsx
function SubmitButton() {
  const { pending } = useFormStatus();
  return <button disabled={pending}>{pending ? 'Saving...' : 'Save'}</button>;
}
```

**useOptimistic** — show instant UI feedback before server confirmation:
```tsx
const [optimisticLikes, addOptimisticLike] = useOptimistic(
  likes,
  (state, newLike) => [...state, newLike]
);
// Call addOptimisticLike() immediately, confirm/revert after server responds
```

**use()** — reads Promises and Context, can be called conditionally (breaks rules-of-hooks convention):
```tsx
// In a Server Component:
const data = use(fetchData()); // suspends until resolved
const theme = use(ThemeContext); // reads context
```

### Server Actions
Form actions and mutations that run on the server. No API route needed:
```tsx
// actions.ts — 'use server' makes this a Server Action
'use server';
export async function createPost(formData: FormData) {
  const title = formData.get('title') as string;
  await db.insert(posts).values({ title });
  revalidatePath('/posts');
}

// Component:
<form action={createPost}>
  <input name="title" />
  <SubmitButton />
</form>
```

### Document Metadata (built-in)
React 19 can hoist `<title>`, `<meta>`, and `<link>` tags from anywhere in the component tree:
```tsx
function BlogPost({ post }) {
  return (
    <>
      <title>{post.title}</title>
      <meta name="description" content={post.excerpt} />
      <article>{post.content}</article>
    </>
  );
}
```

### React Server Components (RSC) — Stable Model
- **Server Components**: render on server, zero client JS, can be async, direct DB/filesystem access. Default in Next.js App Router.
- **Client Components**: marked with `'use client'`, hydrated in browser, have state/effects/events.
- **Key rule**: Server Components can import Client Components (they become "leaves"), but Client Components cannot import Server Components.
- Props crossing the server/client boundary must be serializable (no functions, class instances, Dates become strings).

---

## Next.js 15 — Production-Critical Changes

### Caching Defaults Reversed (Breaking)
In Next.js 15, GET Route Handlers and `fetch()` are **uncached by default** (previously cached by default). Opt into caching explicitly:
```ts
// Route handler — uncached by default in Next.js 15
export async function GET() { ... }

// To cache:
export const dynamic = 'force-static';
// or
export const revalidate = 3600; // ISR: revalidate every hour
```

### Partial Prerendering (PPR) — Incremental Adoption
PPR lets you mix static shells with dynamic streaming content per-route. Enable incrementally:
```ts
// next.config.ts
experimental: { ppr: 'incremental' }

// Per-route:
export const experimental_ppr = true;

// Wrap dynamic parts in Suspense:
<Suspense fallback={<CartSkeleton />}>
  <Cart /> {/* rendered dynamically, streamed in */}
</Suspense>
```
The static shell (outer layout, header, etc.) is served from CDN instantly. Dynamic holes stream in as they resolve. Next.js 16 makes PPR the default.

### Turbopack — Stable for Development
- Local dev server: 76% faster startup, 96% faster Hot Module Replacement
- `next dev --turbo` (or just `next dev` in newer setups)
- Production builds still use Webpack (Turbopack production builds in progress)

### Server Actions — Key Patterns
```ts
// Revalidate after mutation:
'use server';
import { revalidatePath, revalidateTag } from 'next/cache';
export async function updatePost(id: string, data: FormData) {
  await db.update(posts).set({ title: data.get('title') }).where(eq(posts.id, id));
  revalidatePath('/posts');
  revalidateTag('posts'); // tag-based revalidation
}
```

### `unstable_after` — Post-Response Work
Run code after the response is sent (logging, analytics, cleanup) without blocking TTFB:
```ts
import { unstable_after as after } from 'next/server';
export async function POST(req: Request) {
  const data = await processRequest(req);
  after(async () => {
    await logAnalytics(data); // runs after response is sent
  });
  return Response.json(data);
}
```

---

## Framework Decision Guide

### Use Next.js 15 when:
- React ecosystem, team already knows React
- Complex data fetching with mixed static/dynamic requirements
- Need SSR + SSG + ISR + streaming in one app
- Building a SaaS, e-commerce, dashboard, or marketing site
- Want Vercel deployment with zero config
- Need React ecosystem libraries (shadcn/ui, TanStack, etc.)

### Use SvelteKit / Svelte 5 when:
- Bundle size is critical (50-70% less JS than equivalent React app)
- Team is new to a framework and wants minimal ceremony
- Building public-facing content sites where INP score matters
- Don't need React's ecosystem breadth
- Svelte 5 Runes: `$state`, `$derived`, `$effect` replace the old store model with explicit reactivity

### Use Astro 5 when:
- Content-driven site (blog, docs, marketing, portfolio)
- Want maximum performance with minimal JS (zero-JS by default)
- Content Layer API for type-safe content collections from CMS/MDX/JSON
- Can use React/Vue/Svelte components via "islands" for interactive parts
- Note: Cloudflare acquired Astro in January 2026 — now has Cloudflare-native deployment

### Use Remix / React Router v7 when:
- Remix merged into React Router v7 (single package)
- Prefer web-platform-native patterns (Forms, fetch, Response objects)
- Nested routing with granular data loading per-segment
- Better at progressive enhancement than Next.js
- Remix 3 is emerging as a bundler-free, batteries-included framework

### Use Vue 3 / Nuxt 3 when:
- Team has Vue experience
- Want Options API or Composition API flexibility
- Nuxt 3 has excellent DX with auto-imports and file-based routing
- Strong in European enterprise market

---

## TypeScript Best Practices (2025)

- **Strict mode**: always. `"strict": true` in tsconfig.
- **satisfies operator**: validate shape without widening type: `const config = { ... } satisfies Config;`
- **Template literal types** for route/event typing
- **Discriminated unions** over optional props for variant components
- **Zod** for runtime validation — coerce and validate external data at boundaries
- **Type predicates** over `as` casts
- **Path aliases**: configure in `tsconfig.json` and tool configs to avoid `../../../` hell
- Avoid `any` — use `unknown` and narrow explicitly
- Use `NoInfer<T>` (TS 5.4) to prevent unwanted type inference in generic functions
