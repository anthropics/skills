# QueryClient Config + DevTools

## Production QueryClient Setup

```tsx
// src/components/providers/QueryProvider.tsx
import { QueryClient, QueryClientProvider } from "@tanstack/react-query";
import { ReactQueryDevtools } from "@tanstack/react-query-devtools";

const queryClient = new QueryClient({
  defaultOptions: {
    queries: {
      staleTime: 5 * 60_000,   // 5 min — data stays fresh, no background refetch
      gcTime: 10 * 60_000,     // 10 min — keep unused cache before GC (was cacheTime pre-v5)
      retry: 2,                // retry failed queries twice
      refetchOnWindowFocus: false, // disable noisy refetch on tab switch
    },
    mutations: {
      retry: 0, // never retry mutations by default
    },
  },
});

export function QueryProvider({ children }: { children: React.ReactNode }) {
  return (
    <QueryClientProvider client={queryClient}>
      {children}
      <ReactQueryDevtools initialIsOpen={false} />
    </QueryClientProvider>
  );
}
```

Install DevTools:

```bash
npm install @tanstack/react-query-devtools
```

`ReactQueryDevtools` tree-shakes out of production builds automatically — no `NODE_ENV` guard needed.

## Key Defaults Explained

| Option | Default | Recommended | Why |
|--------|---------|-------------|-----|
| `staleTime` | `0` (always stale) | `5 * 60_000` | Prevents background refetch on every mount |
| `gcTime` | `5 * 60_000` | `10 * 60_000` | Keeps cache longer for fast back-navigation |
| `retry` | `3` | `2` | 3 retries on flaky networks adds ~15s delay |
| `refetchOnWindowFocus` | `true` | `false` | Eliminates surprise re-fetches in most SPAs |

## Per-Query Override

Override defaults on individual hooks when needed:

```ts
export const useUserProfile = (id: string) => {
  const query = api.useQuery<UserProfile>({
    url: `/users/${id}`,
    key: ["user", id],
    staleTime: 0,            // always fresh
    retry: 0,                // fail fast
    refetchOnWindowFocus: true,
  });
  return { profile: query.data, isLoadingProfile: query.isLoading, ...query };
};
```

## Global Error Handler

Attach once to the QueryClient to handle all query/mutation errors centrally (e.g. toast notifications):

```tsx
import { QueryCache, MutationCache, QueryClient } from "@tanstack/react-query";
import toast from "react-hot-toast";

const queryClient = new QueryClient({
  queryCache: new QueryCache({
    onError: (error, query) => {
      // Only show toast for background refetch errors (not initial load)
      if (query.state.data !== undefined) {
        toast.error(`Refresh failed: ${(error as Error).message}`);
      }
    },
  }),
  mutationCache: new MutationCache({
    onError: (error) => {
      toast.error((error as Error).message ?? "Something went wrong");
    },
  }),
});
```
