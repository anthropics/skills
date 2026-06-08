# Performance Optimization (2025-2026)

## Core Web Vitals — Current Targets

Google's Core Web Vitals (as of 2025-2026):
- **LCP (Largest Contentful Paint)**: ≤ 2.5s (loading) — only 47% of websites pass
- **INP (Interaction to Next Paint)**: ≤ 200ms (replaced FID in March 2024) — 43% of sites fail
- **CLS (Cumulative Layout Shift)**: ≤ 0.1 (visual stability)

INP is now the hardest to pass. It measures the worst interaction latency across the entire page session.

---

## LCP Optimization

LCP is usually the hero image, above-the-fold heading, or featured content block.

### Image Priority + next/image
```tsx
// Always use priority for LCP images:
import Image from 'next/image';

<Image
  src="/hero.webp"
  alt="Hero"
  width={1200}
  height={600}
  priority  // preloads, sets fetchpriority="high"
  sizes="(max-width: 768px) 100vw, 1200px"
/>
```

### Manual `fetchpriority` for non-Next.js
```html
<img src="/hero.webp" fetchpriority="high" loading="eager" decoding="sync" />
```

### Font Optimization
```tsx
// next/font — zero layout shift, self-hosted, preloaded:
import { Inter, Playfair_Display } from 'next/font/google';

const inter = Inter({ subsets: ['latin'], display: 'swap', variable: '--font-inter' });
const playfair = Playfair_Display({ subsets: ['latin'], variable: '--font-display' });
```

### Critical CSS + Server Components
Deliver critical CSS inline, defer non-critical. React Server Components render HTML on the server — HTML is sent before JS is parsed, eliminating render-blocking scripts from the critical path.

### CDN + Edge
- Vercel/Cloudflare automatically caches static assets at CDN edge nodes
- Use `Cache-Control: public, max-age=31536000, immutable` for content-hashed assets
- For ISR pages: `Cache-Control: s-maxage=60, stale-while-revalidate=300`

---

## INP Optimization

INP measures the latency from interaction to visual response. The main culprits: long JS tasks blocking the main thread.

### React Server Components for Heavy Logic
Move computation off the client entirely. No hydration overhead for static UI.

### Code Splitting + Dynamic Imports
```tsx
import dynamic from 'next/dynamic';

// Defer heavy components until needed:
const HeavyChart = dynamic(() => import('./HeavyChart'), {
  loading: () => <ChartSkeleton />,
  ssr: false,  // don't SSR if it's interaction-only
});

// Only load when user interacts:
const [showChart, setShowChart] = useState(false);
{showChart && <HeavyChart />}
```

### React Compiler for Automatic Memoization
Enable the React Compiler to eliminate unnecessary re-renders automatically — the biggest INP win with zero manual effort.

### Break Long Tasks
```ts
// Use scheduler.yield() to yield to browser between heavy operations:
async function processItems(items: Item[]) {
  for (const item of items) {
    processItem(item);
    if (navigator.scheduling?.isInputPending()) {
      await scheduler.yield(); // yield to pending input events
    }
  }
}
```

### Event Handler Optimization
```tsx
// Debounce search inputs:
import { useDeferredValue } from 'react';
const deferredSearch = useDeferredValue(search);
// deferredSearch updates at lower priority — input stays responsive

// useTransition for non-urgent state updates:
const [isPending, startTransition] = useTransition();
startTransition(() => setFilter(newFilter)); // doesn't block input
```

---

## CLS Optimization

CLS from layout shifts caused by: images without dimensions, dynamic content injected above existing content, fonts swapping.

```tsx
// Always specify dimensions for images:
<Image src="/product.jpg" width={400} height={300} alt="Product" />

// Reserve space for dynamic content (skeleton screens):
function PostList() {
  return (
    <Suspense fallback={<PostListSkeleton />}>
      <PostListData />
    </Suspense>
  );
}

// CSS containment for dynamic regions:
.ad-container { contain: layout; min-height: 250px; }
```

For fonts: `font-display: swap` in `next/font` by default. Always specify `size-adjust` if using fallback fonts.

---

## Bundle Optimization

### Analyze Your Bundle
```bash
# Next.js:
ANALYZE=true pnpm build
# Installs @next/bundle-analyzer, opens treemap in browser

# Vite:
npx vite-bundle-visualizer
```

### Tree Shaking — Named Imports
```ts
// BAD — imports entire library:
import _ from 'lodash';
const sorted = _.sortBy(arr, 'name');

// GOOD — imports only what's needed:
import sortBy from 'lodash/sortBy';
// Or use native alternatives:
const sorted = [...arr].sort((a, b) => a.name.localeCompare(b.name));
```

### Route-Based Code Splitting (Automatic in Next.js)
Next.js App Router automatically code-splits at the route level. Each route segment gets its own chunk. Server Components never contribute to the client bundle.

### Lazy Motion (Framer Motion)
```tsx
import { LazyMotion, domAnimation } from 'motion/react';
// ~30KB savings on initial load
<LazyMotion features={domAnimation}>
  <m.div animate={{ x: 100 }} />
</LazyMotion>
```

### Package Size Checks
Use `bundlephobia.com` or `pkg-size.dev` before adding dependencies. Prefer packages that are tree-shakeable (`sideEffects: false` in package.json).

---

## Image Optimization

### Formats: AVIF > WebP > JPEG/PNG
```tsx
// next/image automatically serves AVIF → WebP → original based on browser support
<Image src="/photo.jpg" ... />  // serves AVIF to Chrome, WebP to Safari
```

### `sizes` Attribute — Critical for LCP
```tsx
<Image
  src="/hero.jpg"
  fill
  sizes="(max-width: 768px) 100vw, (max-width: 1200px) 50vw, 800px"
/>
```
Without `sizes`, Next.js generates 100vw images — causing oversized downloads on desktop.

### Sharp for Server-Side Optimization
```bash
pnpm add sharp  # Next.js uses Sharp automatically when available
```

---

## Edge Computing Patterns

Move latency-sensitive work to edge:
- **Middleware** (Vercel/Cloudflare): auth checks, A/B testing, redirects, geolocation — runs in 0-5ms at user's nearest edge node
- **Edge API routes**: simple APIs without heavy Node.js APIs — `export const runtime = 'edge'`
- **ISR with CDN**: static pages served from CDN edge, revalidated on demand

```ts
// Next.js edge middleware:
export const config = { matcher: ['/dashboard/:path*', '/api/:path*'] };

export function middleware(req: NextRequest) {
  const sessionToken = req.cookies.get('session')?.value;
  if (!sessionToken) {
    return NextResponse.redirect(new URL('/login', req.url));
  }
  // JWT verification at edge — no DB call needed
  const payload = verifyJWT(sessionToken);
  if (!payload) return NextResponse.redirect(new URL('/login', req.url));
  return NextResponse.next();
}
```

---

## Monitoring & Measurement

- **Vercel Analytics**: automatic Core Web Vitals tracking per route
- **Google Search Console**: field data from real users (CrUX data)
- **Lighthouse** (`pnpm dlx lighthouse https://yourapp.com`): synthetic lab data
- **web-vitals library** for custom reporting:

```ts
import { onLCP, onINP, onCLS } from 'web-vitals';

function sendToAnalytics({ name, value, rating }) {
  fetch('/api/vitals', {
    method: 'POST',
    body: JSON.stringify({ name, value, rating, url: location.href }),
  });
}

onLCP(sendToAnalytics);
onINP(sendToAnalytics);
onCLS(sendToAnalytics);
```
