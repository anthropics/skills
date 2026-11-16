# Next.js and React checks

Apply these on top of the general review passes in SKILL.md when the code uses React or Next.js (App Router or Pages Router).

## Contents

- Next.js security and correctness
- React correctness
- Frontend performance

## Next.js security and correctness

- **Server Actions are public endpoints.** Every `"use server"` function must authenticate the user and authorize the action itself; hiding a button in the UI is not protection. Validate the arguments (for example with zod), because they come from the client.
- **Route handlers** (`app/api/**/route.ts`, `pages/api/**`): check auth, check the HTTP method, validate the body, and verify ownership of any ID in the params or body.
- **Middleware is not enough on its own** for authorization. Check again in the server action or route handler, and make sure the `matcher` config doesn't leave paths uncovered.
- **Server/client boundary:** secrets or server-only modules imported into `"use client"` files; `NEXT_PUBLIC_*` variables holding anything secret; whole database rows (or user objects with hashes and internal fields) passed as props to client components. Suggest `import "server-only"` for modules that must never ship to the browser.
- **Caching leaks:** per-user data fetched in a route that is statically rendered or cached (`fetch` cache, `unstable_cache`, ISR), so one user's data is served to another. After mutations, check for `revalidatePath`/`revalidateTag`, or the UI will show stale data.
- **Redirects:** open redirects through `redirect(searchParams.next)` or a `callbackUrl` with no allow-list.
- **Rendering bugs:** hydration mismatches (`Date.now()`, `Math.random()`, or `window` used during render), `useEffect` fetching that duplicates server work, missing `loading`/`error` boundaries, and `dangerouslySetInnerHTML` with CMS or user content that hasn't been sanitized.
- **No rate limiting by default.** Flag this on login, signup, OTP, password reset, contact forms, and expensive AI or email calls.

## React correctness

- `useEffect` dependency mistakes (stale closures, infinite loops); missing cleanup for subscriptions and listeners (including realtime channels and snapshot listeners); state updates after unmount; races where an older fetch overwrites a newer one (no abort controller or ignore flag).
- Derived state copied into `useState` and drifting out of sync; unstable `key` props (an array index on lists that reorder); forms that can be double-submitted.
- User-supplied URLs placed in `href` or `src` without blocking `javascript:` URLs.

## Frontend performance

- Components marked `"use client"` that could be Server Components, shipping extra JavaScript; large libraries imported for small tasks (moment, whole-package lodash imports); heavy components not lazy-loaded (`next/dynamic`, `React.lazy`).
- Hidden N+1: each row in a list fetching its own data. Fetch once in the parent or a Server Component and pass the data down.
- Request waterfalls in Server Components: independent `await`s in sequence. Use `Promise.all` or parallel data fetching.
- Caching turned off everywhere (`cache: 'no-store'`, `dynamic = 'force-dynamic'`) without a reason.
- Unnecessary re-renders: new objects or functions passed as props to memoized children, context values recreated every render, state lifted too high. Recommend `useMemo`/`useCallback`/`memo` only where re-renders are actually expensive, and suggest the React DevTools Profiler to confirm.
- Long lists rendered without virtualization; search or filter inputs firing a request on every keystroke (no debounce); images not using `next/image` or missing dimensions; layout shift from fonts or images.
