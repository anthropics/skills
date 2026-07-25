# Next.js Optimization Guide

Performance optimization techniques for Next.js 14+ applications.

---

## Table of Contents

- [Rendering Strategies](#rendering-strategies)
- [Image Optimization](#image-optimization)
- [Code Splitting](#code-splitting)
- [Data Fetching](#data-fetching)
- [Caching Strategies](#caching-strategies)
- [Bundle Optimization](#bundle-optimization)
- [Core Web Vitals](#core-web-vitals)

---

## Rendering Strategies

### Server Components (Default)

Server Components render on the server and send HTML to the client. Use for data-heavy, non-interactive content.

```tsx
// app/products/page.tsx - Server Component (default)
async function ProductsPage() {
  // This runs on the server - no client bundle impact
  const products = await db.products.findMany();

  return (
    <div className="grid grid-cols-3 gap-4">
      {products.map(product => (
        <ProductCard key={product.id} product={product} />
      ))}
    </div>
  );
}
```

### Client Components

Use `'use client'` only when you need:
- Event handlers (onClick, onChange)
- State (useState, useReducer)
- Effects (useEffect)
- Browser APIs (window, document)

```tsx
'use client';

import { useState } from 'react';

function AddToCartButton({ productId }: { productId: string }) {
  const [isAdding, setIsAdding] = useState(false);

  async function handleClick() {
    setIsAdding(true);
    await addToCart(productId);
    setIsAdding(false);
  }

  return (
    <button onClick={handleClick} disabled={isAdding}>
      {isAdding ? 'Adding...' : 'Add to Cart'}
    </button>
  );
}
```

### Mixing Server and Client Components

```tsx
// app/products/[id]/page.tsx - Server Component
async function ProductPage({ params }: { params: { id: string } }) {
  const product = await getProduct(params.id);

  return (
    <div>
      {/* Server-rendered content */}
      <h1>{product.name}</h1>
      <p>{product.description}</p>

      {/* Client component for interactivity */}
      <AddToCartButton productId={product.id} />

      {/* Server component for reviews */}
      <ProductReviews productId={product.id} />
    </div>
  );
}
```

### Static vs Dynamic Rendering

```tsx
// Force static generation at build time
export const dynamic = 'force-static';

// Force dynamic rendering at request time
export const dynamic = 'force-dynamic';

// Revalidate every 60 seconds (ISR)
export const revalidate = 60;

// Revalidate on-demand
import { revalidatePath, revalidateTag } from 'next/cache';

async function updateProduct(id: string, data: ProductData) {
  await db.products.update({ where: { id }, data });

  // Revalidate specific path
  revalidatePath(`/products/${id}`);

  // Or revalidate by tag
  revalidateTag('products');
}
```

---

## Image Optimization

### Next.js Image Component

```tsx
import Image from 'next/image';

// Basic optimized image
<Image
  src="/hero.jpg"
  alt="Hero image"
  width={1200}
  height={600}
  priority // Load immediately for LCP
/>

// Responsive image
<Image
  src="/product.jpg"
  alt="Product"
  fill
  sizes="(max-width: 768px) 100vw, (max-width: 1200px) 50vw, 33vw"
  className="object-cover"
/>

// With placeholder blur
import productImage from '@/public/product.jpg';

<Image
  src={productImage}
  alt="Product"
  placeholder="blur" // Uses imported image data
/>
```

### Remote Images Configuration

```js
// next.config.js
module.exports = {
  images: {
    remotePatterns: [
      {
        protocol: 'https',
        hostname: 'cdn.example.com',
        pathname: '/images/**',
      },
      {
        protocol: 'https',
        hostname: '*.cloudinary.com',
      },
    ],
    // Image formats (webp is default)
    formats: ['image/avif', 'image/webp'],
    // Device sizes for srcset
    deviceSizes: [640, 750, 828, 1080, 1200, 1920, 2048, 3840],
    // Image sizes for srcset
    imageSizes: [16, 32, 48, 64, 96, 128, 256, 384],
  },
};
```

### Lazy Loading Patterns

```tsx
// Images below the fold - lazy load (default)
<Image
  src="/gallery/photo1.jpg"
  alt="Gallery photo"
  width={400}
  height={300}
  loading="lazy" // Default behavior
/>

// Above the fold - load immediately
<Image
  src="/hero.jpg"
  alt="Hero"
  width={1200}
  height={600}
  priority
  loading="eager"
/>
```

---

## Code Splitting

### Dynamic Imports

```tsx
import dynamic from 'next/dynamic';

// Basic dynamic import
const HeavyChart = dynamic(() => import('@/components/HeavyChart'), {
  loading: () => <ChartSkeleton />,
});

// Disable SSR for client-only components
const MapComponent = dynamic(() => import('@/components/Map'), {
  ssr: false,
  loading: () => <div className="h-[400px] bg-gray-100" />,
});

// Named exports
const Modal = dynamic(() =>
  import('@/components/ui').then(mod => mod.Modal)
);

// With suspense
const DashboardCharts = dynamic(() => import('@/components/DashboardCharts'), {
  loading: () => <Suspense fallback={<ChartsSkeleton />} />,
});
```

### Route-Based Splitting

```tsx
// app/dashboard/analytics/page.tsx
// This page only loads when /dashboard/analytics is visited
import { Suspense } from 'react';
import AnalyticsCharts from './AnalyticsCharts';

export default function AnalyticsPage() {
  return (
    <Suspense fallback={<AnalyticsSkeleton />}>
      <AnalyticsCharts />
    </Suspense>
  );
}
```

### Parallel Routes for Code Splitting

```
app/
├── dashboard/
│   ├── @analytics/
│   │   └── page.tsx    # Loaded in parallel
│   ├── @metrics/
│   │   └── page.tsx    # Loaded in parallel
│   ├── layout.tsx
│   └── page.tsx
```

```tsx
// app/dashboard/layout.tsx
export default function DashboardLayout({
  children,
  analytics,
  metrics,
}: {
  children: React.ReactNode;
  analytics: React.ReactNode;
  metrics: React.ReactNode;
}) {
  return (
    <div className="grid grid-cols-2 gap-4">
      {children}
      <Suspense fallback={<AnalyticsSkeleton />}>{analytics}</Suspense>
      <Suspense fallback={<MetricsSkeleton />}>{metrics}</Suspense>
    </div>
  );
}
```

---

## Data Fetching

### Server-Side Data Fetching

```tsx
// Parallel data fetching
async function Dashboard() {
  // Start both requests simultaneously
  const [user, stats, notifications] = await Promise.all([
    getUser(),
    getStats(),
    getNotifications(),
  ]);

  return (
    <div>
      <UserHeader user={user} />
      <StatsPanel stats={stats} />
      <NotificationList notifications={notifications} />
    </div>
  );
}
```

### Streaming with Suspense

```tsx
import { Suspense } from 'react';

async function ProductPage({ params }: { params: { id: string } }) {
  const product = await getProduct(params.id);

  return (
    <div>
      {/* Immediate content */}
      <h1>{product.name}</h1>
      <p>{product.description}</p>

      {/* Stream reviews - don't block page */}
      <Suspense fallback={<ReviewsSkeleton />}>
        <Reviews productId={params.id} />
      </Suspense>

      {/* Stream recommendations */}
      <Suspense fallback={<RecommendationsSkeleton />}>
        <Recommendations productId={params.id} />
      </Suspense>
    </div>
  );
}

// Slow data component
async function Reviews({ productId }: { productId: string }) {
  const reviews = await getReviews(productId); // Slow query
  return <ReviewList reviews={reviews} />;
}
```

### Request Memoization

```tsx
// Next.js automatically dedupes identical requests
async function Layout({ children }) {
  const user = await getUser(); // Request 1
  return <div>{children}</div>;
}

async function Header() {
  const user = await getUser(); // Same request - cached!
  return <div>Hello, {user.name}</div>;
}

// Both components call getUser() but only one request is made
```

---

## Caching Strategies

### Fetch Cache Options

```tsx
// Cache indefinitely (default for static)
fetch('https://api.example.com/data');

// No cache - always fresh
fetch('https://api.example.com/data', { cache: 'no-store' });

// Revalidate after time
fetch('https://api.example.com/data', {
  next: { revalidate: 3600 } // 1 hour
});

// Tag-based revalidation
fetch('https://api.example.com/products', {
  next: { tags: ['products'] }
});

// Later, revalidate by tag
import { revalidateTag } from 'next/cache';
revalidateTag('products');
```

### Route Segment Config

```tsx
// app/products/page.tsx

// Revalidate every hour
export const revalidate = 3600;

// Or force dynamic
export const dynamic = 'force-dynamic';

// Generate static params at build
export async function generateStaticParams() {
  const products = await getProducts();
  return products.map(p => ({ id: p.id }));
}
```

### unstable_cache for Custom Caching

```tsx
import { unstable_cache } from 'next/cache';

const getCachedUser = unstable_cache(
  async (userId: string) => {
    const user = await db.users.findUnique({ where: { id: userId } });
    return user;
  },
  ['user-cache'],
  {
    revalidate: 3600, // 1 hour
    tags: ['users'],
  }
);

// Usage
const user = await getCachedUser(userId);
```

---

## Bundle Optimization

### Analyze Bundle Size

```bash
# Install analyzer
npm install @next/bundle-analyzer

# Update next.config.js
const withBundleAnalyzer = require('@next/bundle-analyzer')({
  enabled: process.env.ANALYZE === 'true',
});

module.exports = withBundleAnalyzer({
  // config
});

# Run analysis
ANALYZE=true npm run build
```

### Tree Shaking Imports

```tsx
// BAD - Imports entire library
import _ from 'lodash';
const result = _.debounce(fn, 300);

// GOOD - Import only what you need
import debounce from 'lodash/debounce';
const result = debounce(fn, 300);

// GOOD - Named imports (tree-shakeable)
import { debounce } from 'lodash-es';
```

### Optimize Dependencies

```js
// next.config.js
module.exports = {
  // Transpile specific packages
  transpilePackages: ['ui-library', 'shared-utils'],

  // Optimize package imports
  experimental: {
    optimizePackageImports: ['lucide-react', '@heroicons/react'],
  },

  // External packages for server
  serverExternalPackages: ['sharp', 'bcrypt'],
};
```

### Font Optimization

```tsx
// app/layout.tsx
import { Inter, Roboto_Mono } from 'next/font/google';

const inter = Inter({
  subsets: ['latin'],
  display: 'swap',
  variable: '--font-inter',
});

const robotoMono = Roboto_Mono({
  subsets: ['latin'],
  display: 'swap',
  variable: '--font-roboto-mono',
});

export default function RootLayout({ children }) {
  return (
    <html lang="en" className={`${inter.variable} ${robotoMono.variable}`}>
      <body className="font-sans">{children}</body>
    </html>
  );
}
```

---

## Core Web Vitals

### Largest Contentful Paint (LCP)

```tsx
// Optimize LCP hero image
import Image from 'next/image';

export default function Hero() {
  return (
    <section className="relative h-[600px]">
      <Image
        src="/hero.jpg"
        alt="Hero"
        fill
        priority // Preload for LCP
        sizes="100vw"
        className="object-cover"
      />
      <div className="relative z-10">
        <h1>Welcome</h1>
      </div>
    </section>
  );
}

// Preload critical resources in layout
export default function RootLayout({ children }) {
  return (
    <html>
      <head>
        <link rel="preload" href="/hero.jpg" as="image" />
        <link rel="preconnect" href="https://fonts.googleapis.com" />
      </head>
      <body>{children}</body>
    </html>
  );
}
```

### Cumulative Layout Shift (CLS)

```tsx
// Prevent CLS with explicit dimensions
<Image
  src="/product.jpg"
  alt="Product"
  width={400}
  height={300}
/>

// Or use aspect ratio
<div className="aspect-video relative">
  <Image src="/video-thumb.jpg" alt="Video" fill />
</div>

// Skeleton placeholders
function ProductCard({ product }: { product?: Product }) {
  if (!product) {
    return (
      <div className="animate-pulse">
        <div className="h-48 bg-gray-200 rounded" />
        <div className="h-4 bg-gray-200 rounded mt-2 w-3/4" />
        <div className="h-4 bg-gray-200 rounded mt-1 w-1/2" />
      </div>
    );
  }

  return (
    <div>
      <Image src={product.image} alt={product.name} width={300} height={200} />
      <h3>{product.name}</h3>
      <p>{product.price}</p>
    </div>
  );
}
```

### First Input Delay (FID) / Interaction to Next Paint (INP)

```tsx
// Defer non-critical JavaScript
import Script from 'next/script';

export default function Layout({ children }) {
  return (
    <html>
      <body>
        {children}

        {/* Load analytics after page is interactive */}
        <Script
          src="https://analytics.example.com/script.js"
          strategy="afterInteractive"
        />

        {/* Load chat widget when idle */}
        <Script
          src="https://chat.example.com/widget.js"
          strategy="lazyOnload"
        />
      </body>
    </html>
  );
}

// Use web workers for heavy computation
// app/components/DataProcessor.tsx
'use client';

import { useEffect, useState } from 'react';

function DataProcessor({ data }: { data: number[] }) {
  const [result, setResult] = useState<number | null>(null);

  useEffect(() => {
    const worker = new Worker(new URL('../workers/processor.js', import.meta.url));

    worker.postMessage(data);
    worker.onmessage = (e) => setResult(e.data);

    return () => worker.terminate();
  }, [data]);

  return <div>Result: {result}</div>;
}
```

### Measuring Performance

```tsx
// app/components/PerformanceMonitor.tsx
'use client';

import { useReportWebVitals } from 'next/web-vitals';

export function PerformanceMonitor() {
  useReportWebVitals((metric) => {
    switch (metric.name) {
      case 'LCP':
        console.log('LCP:', metric.value);
        break;
      case 'FID':
        console.log('FID:', metric.value);
        break;
      case 'CLS':
        console.log('CLS:', metric.value);
        break;
      case 'TTFB':
        console.log('TTFB:', metric.value);
        break;
    }

    // Send to analytics
    analytics.track('web-vital', {
      name: metric.name,
      value: metric.value,
      id: metric.id,
    });
  });

  return null;
}
```

---

## Quick Reference

### Performance Checklist

| Area | Optimization | Impact |
|------|-------------|--------|
| Images | Use next/image with priority for LCP | High |
| Fonts | Use next/font with display: swap | Medium |
| Code | Dynamic imports for heavy components | High |
| Data | Parallel fetching with Promise.all | High |
| Render | Server Components by default | High |
| Cache | Configure revalidate appropriately | Medium |
| Bundle | Tree-shake imports, analyze size | Medium |

### Config Template

```js
// next.config.js
/** @type {import('next').NextConfig} */
const nextConfig = {
  images: {
    remotePatterns: [{ hostname: 'cdn.example.com' }],
    formats: ['image/avif', 'image/webp'],
  },
  experimental: {
    optimizePackageImports: ['lucide-react'],
  },
  headers: async () => [
    {
      source: '/(.*)',
      headers: [
        { key: 'X-Content-Type-Options', value: 'nosniff' },
        { key: 'X-Frame-Options', value: 'DENY' },
      ],
    },
  ],
};

module.exports = nextConfig;
```
