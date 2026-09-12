# Agora RTC — Next.js / SSR

The Agora Web SDK (`agora-rtc-sdk-ng`) and `agora-rtc-react` are browser-only. They cannot run during server-side rendering and will throw errors if imported at the module level in a Next.js Server Component or during SSR.

## The Problem

`next/dynamic` with `ssr: false` works in Pages Router and in Client Components, but **does NOT work in Server Components** in Next.js 14+ App Router. A Server Component importing a dynamically-loaded client module that references Agora will still fail at build time if the import is not properly isolated.

## Pattern: Wrap Both the Provider and Component

The correct pattern for Next.js App Router is to dynamically import both your Agora component **and** the `AgoraRTCProvider` together, inside a Client Component:

```tsx
'use client';

import { useMemo, Suspense } from 'react';
import dynamic from 'next/dynamic';

// Dynamically import your RTC component with ssr disabled
const ConversationComponent = dynamic(() => import('./ConversationComponent'), {
  ssr: false,
});

// Dynamically import AgoraRTCProvider and create the client inside the same
// dynamic boundary — this keeps all Agora imports out of the SSR bundle
const AgoraProvider = dynamic(
  async () => {
    const { AgoraRTCProvider, default: AgoraRTC } =
      await import('agora-rtc-react');
    return {
      default: ({ children }: { children: React.ReactNode }) => {
        const client = useMemo(
          () => AgoraRTC.createClient({ mode: 'rtc', codec: 'vp8' }),
          [],
        );
        return <AgoraRTCProvider client={client}>{children}</AgoraRTCProvider>;
      },
    };
  },
  { ssr: false },
);

export default function Page() {
  return (
    <Suspense fallback={<div>Loading...</div>}>
      <AgoraProvider>
        <ConversationComponent />
      </AgoraProvider>
    </Suspense>
  );
}
```

**Why this works:** Both `AgoraRTCProvider` and `AgoraRTC.createClient` are inside the dynamic import callback, so they only execute in the browser. The `useMemo` ensures the client is created once per component mount, not on every render.

## Pattern: Simple Component Lazy Load (Pages Router / Client Components)

If you're in a Pages Router context or inside an existing `"use client"` boundary, the simpler pattern works:

```tsx
'use client';

import { useState, useEffect } from 'react';

export default function Page() {
  const [VideoCall, setVideoCall] = useState<React.ComponentType | null>(null);

  useEffect(() => {
    import('./VideoCall').then((m) => setVideoCall(() => m.default));
  }, []);

  if (!VideoCall) return <div>Loading...</div>;
  return <VideoCall />;
}
```

## Key Rules

- Mark any component that imports Agora with `"use client"`.
- Never import `agora-rtc-sdk-ng` or `agora-rtc-react` at the top level of a Server Component.
- Create the `AgoraRTC.createClient` instance inside a `useMemo` (or outside the component tree) — never in the render function directly.
- Wrap dynamic-loaded Agora components in `<Suspense>` to handle the async load state.

## Node.js Version Requirements

- Next.js 14 / 15: requires Node.js >= 18
- Next.js 16+: requires Node.js >= 20.9.0 (used in agent-samples clients)
