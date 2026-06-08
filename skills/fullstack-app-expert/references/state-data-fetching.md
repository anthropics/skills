# State Management, Data Fetching & Real-Time (2025-2026)

## Mental Model: Server State vs Client State

**Server state** (remote data, async, shared): use TanStack Query (React Query) or tRPC's TanStack integration. Don't put API data in Zustand.

**Client state** (local UI state, user preferences, shopping cart, ephemeral interactions): use Zustand or Jotai.

**Form state**: React Hook Form or Conform — dedicated form libraries outperform general state management for forms.

---

## TanStack Query v5 (React Query)

The standard for server state management. Works alongside any fetch mechanism.

```ts
// Setup:
import { QueryClient, QueryClientProvider } from '@tanstack/react-query';

const queryClient = new QueryClient({
  defaultOptions: {
    queries: {
      staleTime: 60 * 1000, // 1 minute — data stays fresh
      gcTime: 10 * 60 * 1000, // 10 minutes — garbage collection
    },
  },
});

// Basic query:
const { data, isLoading, error } = useQuery({
  queryKey: ['posts', { page, search }],
  queryFn: () => fetchPosts({ page, search }),
  placeholderData: keepPreviousData, // v5: replaces keepPreviousData option
});

// Mutation with optimistic update:
const mutation = useMutation({
  mutationFn: (newPost) => createPost(newPost),
  onMutate: async (newPost) => {
    await queryClient.cancelQueries({ queryKey: ['posts'] });
    const previous = queryClient.getQueryData(['posts']);
    queryClient.setQueryData(['posts'], (old) => [...old, { ...newPost, id: 'temp' }]);
    return { previous };
  },
  onError: (err, newPost, context) => {
    queryClient.setQueryData(['posts'], context.previous);
  },
  onSettled: () => queryClient.invalidateQueries({ queryKey: ['posts'] }),
});

// useSuspenseQuery — with React Suspense (v5):
const { data } = useSuspenseQuery({ queryKey: ['user'], queryFn: getUser });
```

### v5 Breaking Changes (from v4)
- `cacheTime` renamed to `gcTime`
- `isLoading` → `isPending` for mutations
- `keepPreviousData` is now `placeholderData: keepPreviousData`
- Removed all deprecated overloads — only object form accepted

---

## Zustand — Global Client State

Simple, hook-based, no boilerplate. The Redux replacement for most apps.

```ts
import { create } from 'zustand';
import { persist, devtools } from 'zustand/middleware';

interface CartStore {
  items: CartItem[];
  addItem: (item: CartItem) => void;
  removeItem: (id: string) => void;
  total: () => number;
}

export const useCartStore = create<CartStore>()(
  devtools(
    persist(
      (set, get) => ({
        items: [],
        addItem: (item) => set((state) => ({ items: [...state.items, item] })),
        removeItem: (id) => set((state) => ({ items: state.items.filter(i => i.id !== id) })),
        total: () => get().items.reduce((sum, item) => sum + item.price * item.quantity, 0),
      }),
      { name: 'cart-storage' } // persists to localStorage
    )
  )
);

// In component:
const { items, addItem, total } = useCartStore();
// Selector for performance (avoids re-render if unrelated state changes):
const itemCount = useCartStore((state) => state.items.length);
```

### SSR Hydration Pattern with Zustand
```ts
// Provider pattern to prevent hydration mismatch:
export function StoreProvider({ children, initialState }: { children: React.ReactNode; initialState: Partial<CartStore> }) {
  const storeRef = useRef<CartStore>();
  if (!storeRef.current) {
    storeRef.current = createCartStore(initialState);
  }
  return (
    <StoreContext.Provider value={storeRef.current}>
      {children}
    </StoreContext.Provider>
  );
}
```

---

## Jotai — Atomic State

Better than Zustand for: fine-grained reactivity (only components using specific atoms re-render), derived state, async atoms, and atom-based code splitting.

```ts
import { atom, useAtom, useAtomValue } from 'jotai';
import { atomWithStorage } from 'jotai/utils';

// Primitive atom:
const countAtom = atom(0);

// Derived (read-only) atom:
const doubledAtom = atom((get) => get(countAtom) * 2);

// Async atom:
const userAtom = atom(async () => {
  const res = await fetch('/api/user');
  return res.json();
});

// Persistent atom:
const themeAtom = atomWithStorage('theme', 'light');

// In component:
const [count, setCount] = useAtom(countAtom);
const doubled = useAtomValue(doubledAtom); // read-only
```

Choose Jotai when you need lots of independent pieces of state with derived relationships. Choose Zustand when you want a single store with actions (Redux-like mental model).

---

## Form Handling

### React Hook Form + Zod (Most Common Pattern)
```tsx
import { useForm } from 'react-hook-form';
import { zodResolver } from '@hookform/resolvers/zod';
import { z } from 'zod';

const postSchema = z.object({
  title: z.string().min(1, 'Title is required').max(255),
  content: z.string().min(10, 'Content must be at least 10 characters'),
  tags: z.array(z.string()).min(1, 'Add at least one tag'),
});

type PostForm = z.infer<typeof postSchema>;

function CreatePostForm() {
  const { register, handleSubmit, formState: { errors, isSubmitting } } = useForm<PostForm>({
    resolver: zodResolver(postSchema),
  });

  const onSubmit = handleSubmit(async (data) => {
    await createPost(data); // server action or API call
  });

  return (
    <form onSubmit={onSubmit}>
      <input {...register('title')} />
      {errors.title && <span>{errors.title.message}</span>}
      <button type="submit" disabled={isSubmitting}>Submit</button>
    </form>
  );
}
```

### Conform — For Server Actions
Conform is purpose-built for Next.js Server Actions. Handles progressive enhancement (works without JS), server-side validation, and action state feedback.

```tsx
import { useForm, getFormProps, getInputProps } from '@conform-to/react';
import { parseWithZod } from '@conform-to/zod';

// Server action:
'use server';
export async function createPost(prevState: unknown, formData: FormData) {
  const submission = parseWithZod(formData, { schema: postSchema });
  if (submission.status !== 'success') return submission.reply();
  await db.insert(posts).values(submission.value);
  redirect('/posts');
}

// Component:
const [lastResult, action] = useActionState(createPost, undefined);
const [form, fields] = useForm({
  lastResult,
  onValidate({ formData }) {
    return parseWithZod(formData, { schema: postSchema });
  },
});

<form {...getFormProps(form)} action={action}>
  <input {...getInputProps(fields.title, { type: 'text' })} />
  {fields.title.errors && <p>{fields.title.errors}</p>}
</form>
```

---

## Real-Time Communication

### Supabase Realtime — PostgreSQL Changes
```ts
import { createClient } from '@supabase/supabase-js';

const supabase = createClient(url, key);

// Listen to DB changes:
const channel = supabase
  .channel('posts-changes')
  .on('postgres_changes', {
    event: 'INSERT',
    schema: 'public',
    table: 'posts',
    filter: `org_id=eq.${orgId}`,
  }, (payload) => {
    setPosts(prev => [...prev, payload.new]);
  })
  .subscribe();

// Broadcast (ephemeral, peer-to-peer):
const roomChannel = supabase.channel('room-1');
roomChannel.on('broadcast', { event: 'cursor' }, ({ payload }) => {
  updateCursor(payload);
}).subscribe();
await roomChannel.send({ type: 'broadcast', event: 'cursor', payload: { x, y } });

// Presence (who's online):
await channel.track({ userId, displayName });
channel.on('presence', { event: 'sync' }, () => {
  const state = channel.presenceState();
});
```

### Server-Sent Events (SSE) — One-Way Streaming
Simpler than WebSockets for one-way server-to-client updates (notifications, progress updates, AI streaming):
```ts
// Next.js Route Handler:
export async function GET(req: Request) {
  const stream = new ReadableStream({
    async start(controller) {
      const send = (data: object) => {
        controller.enqueue(`data: ${JSON.stringify(data)}\n\n`);
      };
      send({ type: 'connected' });
      // Subscribe to events, send them:
      const unsubscribe = subscribeToUpdates((update) => send(update));
      req.signal.addEventListener('abort', () => {
        unsubscribe();
        controller.close();
      });
    },
  });
  return new Response(stream, {
    headers: { 'Content-Type': 'text/event-stream', 'Cache-Control': 'no-cache' },
  });
}

// Client:
const eventSource = new EventSource('/api/updates');
eventSource.onmessage = (e) => setUpdates(prev => [...prev, JSON.parse(e.data)]);
```

### PartyKit — Collaborative Real-Time
For multiplayer, collaborative features (like Figma/Notion-style collaboration):
```ts
// PartyKit server:
import type { Party } from 'partykit/server';

export default class MyParty implements Party.Server {
  onConnect(conn: Party.Connection) {
    this.party.broadcast(`user joined: ${conn.id}`, [conn.id]);
  }
  onMessage(message: string, sender: Party.Connection) {
    this.party.broadcast(message, [sender.id]);
  }
}

// Client (React):
import usePartySocket from 'partysocket/react';
const socket = usePartySocket({
  host: process.env.NEXT_PUBLIC_PARTYKIT_HOST,
  room: 'document-123',
  onMessage(event) { setMessages(prev => [...prev, JSON.parse(event.data)]); },
});
```
