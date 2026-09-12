---
name: react-query-ease
description: Sets up react-query-ease — a typed Axios + React Query wrapper — with API clients, typed useQuery/useMutation hooks, auto-invalidation, auth token refresh, and streaming hooks. Use this skill whenever the user asks about data fetching, API client setup, React Query, Axios, token refresh, auth interceptors, streaming/SSE hooks, or typed HTTP hooks in React or Next.js — even if they don't mention "react-query-ease" by name. Trigger on phrases like "set up API calls", "how do I fetch data in Next.js", "React Query setup", "Axios interceptor", "refresh token logic", "typed fetch hook", "useQuery hook", "useMutation hook", "streaming response React", "SSE hook", or "API client TypeScript".
license: MIT
---

# react-query-ease

Minimal typed wrapper combining Axios + React Query. Create per-service API clients and use `client.useQuery` / `client.useMutation` without repeating Axios boilerplate.

## Core Workflow

1. **Install** — add package + peer deps
2. **Create client** — `createApiClient` with `baseURL` in `src/config/apiClients.ts`
3. **Write typed hooks** — `useQuery` / `useMutation` wrappers in `src/hooks/`
4. **Add auth** — `createAuthInterceptor` in `configure` callback
5. **Add streaming** — `useStream` for chunked/SSE endpoints

## Installation

```bash
npm install react-query-ease @tanstack/react-query
```

Wrap app in `QueryClientProvider`:

```tsx
// src/components/providers/QueryProvider.tsx
"use client"; // required in Next.js App Router

import { QueryClient, QueryClientProvider } from "@tanstack/react-query";

const queryClient = new QueryClient();

export function QueryProvider({ children }: { children: React.ReactNode }) {
  return (
    <QueryClientProvider client={queryClient}>{children}</QueryClientProvider>
  );
}
```

**Next.js App Router** — add `QueryProvider` to your root layout:

```tsx
// app/layout.tsx
import { QueryProvider } from "@/components/providers/QueryProvider";

export default function RootLayout({
  children,
}: {
  children: React.ReactNode;
}) {
  return (
    <html lang="en">
      <body>
        <QueryProvider>{children}</QueryProvider>
      </body>
    </html>
  );
}
```

> All hooks and client files must include `"use client"` at the top. Server Components cannot use React Query hooks.

## Client Setup

Create one client per API service. Keep clients in `lib/api/config.ts`:

```ts
// lib/api/config.ts
import { createApiClient } from "react-query-ease";

export const api = createApiClient({
  baseURL: "https://api.example.com",
});
```

`createApiClient` accepts all standard Axios config (`headers`, `timeout`, `withCredentials`, etc.) plus an optional `configure` callback for interceptors.

## useQuery

```ts
// lib/api/hooks/useTodo.ts
import { api } from "../config";

export interface ApiError {
  message: string;
  status: number;
}

export interface Todo {
  id: number;
  title: string;
  completed: boolean;
}

export const useTodos = () => {
  const query = api.useQuery<Todo[]>({
    url: "/todos",
    key: ["todos"],
    // Optional:
    method: "GET", // defaults to GET
    params: { page: 1 }, // query string params
    staleTime: 5 * 60_000, // React Query options pass through
    enabled: true,
  });
  return {
    todos: query.data ?? [],
    isLoadingTodos: query.isLoading,
    ...query,
  };
};

const { todos, isLoadingTodos } = useTodos();
```

**Key rules:**

- `key` — React Query cache key; use arrays for namespacing
- `url` — resolved against client `baseURL`
- All Axios config props (`headers`, `params`, `timeout`) and React Query options (`staleTime`, `enabled`, `retry`, `select`, etc.) pass through directly

## useMutation

```ts
// lib/api/hooks/useTodo.ts
export interface NewTodo {
  title: string;
}

export interface UpdateInput {
  id: number;
  title?: string;
  completed?: boolean;
}

export const useCreateTodo = () => {
  const mutation = api.useMutation<Todo, ApiError, NewTodo>({
    url: "/todos",
    method: "POST",
    keyToInvalidate: ["todos"], // auto-invalidates after success
  });
  return {
    createTodo: mutation.mutate,
    isCreatingTodo: mutation.isPending,
    ...mutation,
  };
};

const { createTodo, isCreatingTodo } = useCreateTodo();
createTodo({ title: "Buy milk" });
```

**Dynamic URL** — pass a function when the URL depends on variables:

```ts
// lib/api/hooks/useTodo.ts
export const useUpdateTodo = () => {
  const mutation = api.useMutation<Todo, ApiError, UpdateInput>({
    url: (variables) => `/todos/${variables.id}`,
    method: "PATCH",
    keyToInvalidate: ["todos"],
  });
  return {
    updateTodo: mutation.mutate,
    isUpdatingTodo: mutation.isPending,
    ...mutation,
  };
};
```

**Key rules:**

- If `data` is not set, mutation variables become the request body automatically
- `keyToInvalidate` accepts a single key, a string, or an array of keys/strings — e.g. `keyToInvalidate: [["todos"], ["stats"]]` to bust multiple caches at once
- All React Query mutation options (`onSuccess`, `onError`, `onSettled`, `retry`) pass through

**Using `mutateAsync`** — for async/await with try/catch:

```ts
const { mutateAsync: createTodo, isPending } = useCreateTodo();

const handleSubmit = async () => {
  try {
    const newTodo = await createTodo({ title: "Buy milk" });
    console.log("Created:", newTodo);
  } catch (err) {
    console.error("Failed:", err);
  }
};
```

## Auth Interceptor

Wire up token auth in `configure`:

```ts
// lib/api/config.ts
import { createApiClient, createAuthInterceptor } from "react-query-ease";

const authInterceptor = createAuthInterceptor({
  getAccessToken: () => localStorage.getItem("accessToken"),
  getRefreshToken: () => localStorage.getItem("refreshToken"),
  refreshTokens: async ({ refreshToken }) => {
    const res = await fetch("/auth/refresh", {
      method: "POST",
      body: JSON.stringify({ refresh_token: refreshToken }),
    }).then((r) => r.json());
    localStorage.setItem("accessToken", res.accessToken);
    localStorage.setItem("refreshToken", res.refreshToken);
    return res; // must return { accessToken, refreshToken? }
  },
  onRefreshFailure: () => {
    window.location.assign("/login?session_expired=true");
  },
});

export const api = createApiClient({
  baseURL: "https://api.example.com",
  configure: authInterceptor,
});
```

`createAuthInterceptor` coalesces concurrent 401s into one refresh, retries queued requests with the fresh token, and covers both Axios requests and `useStream` calls.

See `references/auth-interceptor.md` for all options and chaining multiple interceptors.

## useStream

For LLM/SSE/chunked endpoints:

```tsx
// lib/api/hooks/useChat.ts
export const useChat = () => {
  const stream = api.useStream<{ prompt: string }>({
    url: "/chat",
    method: "POST",
    onComplete: () => console.log("Done"),
    onError: (err) => console.error(err),
  });
  return {
    chatData: stream.data,
    isChatLoading: stream.isLoading,
    isChatStreaming: stream.isStreaming,
    ...stream,
  };
};

const { chatData, isChatLoading, start, abort } = useChat();
await start({ prompt: "Hello" });
abort();
```

Return values:

- `data` — accumulated text from all chunks
- `isLoading` — connecting / auth checks
- `isStreaming` — active byte transmission
- `error` — connection error (abort does NOT set error)
- `start(variables?)` — launches stream; `variables` become request body
- `abort()` — cancels stream safely, releases reader lock

See `references/streaming.md` for full API table and async iterator usage.

## Recommended Project Structure

```
lib/
  api/
    config.ts              ← createApiClient instance (+ auth interceptor)
    hooks/
      useTodo.ts           ← typed hook wrappers (useQuery / useMutation)
src/
  components/
    Todos.tsx              ← UI; imports hooks, not clients directly
```

See `references/examples.md` for a complete CRUD walkthrough.

## QueryClient Config + DevTools

```tsx
// src/components/providers/QueryProvider.tsx
import { QueryClient, QueryClientProvider } from "@tanstack/react-query";
import { ReactQueryDevtools } from "@tanstack/react-query-devtools";

const queryClient = new QueryClient({
  defaultOptions: {
    queries: {
      staleTime: 5 * 60_000,
      gcTime: 10 * 60_000,
      retry: 2,
      refetchOnWindowFocus: false,
    },
    mutations: { retry: 0 },
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

Install: `npm install @tanstack/react-query-devtools`

See `references/query-client-config.md` for full defaults table and global error handler setup.

## Error Handling

```ts
export const useTodos = () => {
  const query = api.useQuery<Todo[], ApiError>({
    url: "/todos",
    key: ["todos"],
  });
  return {
    todos: query.data ?? [],
    todosError: query.error, // typed as ApiError | null
    isTodosError: query.isError,
    isLoadingTodos: query.isLoading,
    ...query,
  };
};
```

See `references/error-handling.md` for `mutateAsync` try/catch and `QueryErrorResetBoundary`.

## Optimistic Updates

```ts
onMutate: async (variables) => {
  await queryClient.cancelQueries({ queryKey: ["todos"] });
  const previousTodos = queryClient.getQueryData<Todo[]>(["todos"]);
  queryClient.setQueryData<Todo[]>(["todos"], (old = []) =>
    old.map((t) => t.id === variables.id ? { ...t, ...variables } : t)
  );
  return { previousTodos };
},
onError: (_err, _vars, context) => {
  queryClient.setQueryData(["todos"], context?.previousTodos);
},
onSettled: () => {
  queryClient.invalidateQueries({ queryKey: ["todos"] });
},
```

See `references/optimistic-updates.md` for full create/toggle/delete patterns.
