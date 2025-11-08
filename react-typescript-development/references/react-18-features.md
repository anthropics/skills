# React 18 Features Guide

## Core Features

### useTransition and startTransition

Marks non-urgent updates as transitions, allowing React to maintain responsiveness during heavy computations.

**useTransition Hook**
```typescript
import { useTransition } from 'react';

interface SearchProps {
  results: string[];
}

export const SearchComponent: React.FC<SearchProps> = ({ results }) => {
  const [query, setQuery] = React.useState<string>('');
  const [isPending, startTransition] = useTransition();

  const handleSearch = (value: string) => {
    setQuery(value);
    startTransition(() => {
      // Non-urgent state update
      filterAndUpdateResults(value);
    });
  };

  return (
    <div>
      <input
        value={query}
        onChange={(e) => handleSearch(e.target.value)}
        placeholder="Search..."
      />
      {isPending && <p>Searching...</p>}
      <ul>
        {results.map((item) => (
          <li key={item}>{item}</li>
        ))}
      </ul>
    </div>
  );
};
```

**startTransition (Outside Components)**
```typescript
import { startTransition } from 'react';

const handleUpdate = (data: unknown) => {
  startTransition(() => {
    updateState(data);
  });
};
```

### useDeferredValue

Defers updating a value to keep the UI responsive. Useful for debouncing without useEffect.

```typescript
import { useDeferredValue } from 'react';

interface InputListProps {
  items: string[];
}

export const InputList: React.FC<InputListProps> = ({ items }) => {
  const [input, setInput] = React.useState<string>('');
  const deferredInput = useDeferredValue(input);

  const filteredItems = React.useMemo(
    () => items.filter((item) => item.includes(deferredInput)),
    [deferredInput, items]
  );

  return (
    <div>
      <input
        value={input}
        onChange={(e) => setInput(e.target.value)}
        placeholder="Filter items..."
      />
      <ul>
        {filteredItems.map((item) => (
          <li key={item}>{item}</li>
        ))}
      </ul>
    </div>
  );
};
```

### Suspense for Data Fetching

Enables declarative data fetching with proper TypeScript support.

```typescript
interface UserData {
  id: number;
  name: string;
  email: string;
}

const fetchUser = async (id: number): Promise<UserData> => {
  const response = await fetch(`/api/users/${id}`);
  if (!response.ok) throw new Error('Failed to fetch user');
  return response.json();
};

const UserProfileSuspend: React.FC<{ userId: number }> = ({ userId }) => {
  const [userData] = React.useState<UserData | null>(null);

  React.useEffect(() => {
    let isMounted = true;
    fetchUser(userId).then((data) => {
      if (isMounted) {
        // Handle data
      }
    });
    return () => {
      isMounted = false;
    };
  }, [userId]);

  if (!userData) return null;

  return (
    <div>
      <h2>{userData.name}</h2>
      <p>{userData.email}</p>
    </div>
  );
};

// Usage with Suspense
export const App: React.FC = () => (
  <React.Suspense fallback={<div>Loading user...</div>}>
    <UserProfileSuspend userId={1} />
  </React.Suspense>
);
```

### Concurrent Rendering

React now renders components in the background without blocking user interactions.

```typescript
interface ConcurrentListProps {
  items: number[];
}

export const ConcurrentList: React.FC<ConcurrentListProps> = ({ items }) => {
  const [selectedId, setSelectedId] = React.useState<number | null>(null);

  // This render can be interrupted if user interacts with input
  return (
    <div>
      <input
        type="text"
        placeholder="Type here - won't be blocked by list render"
      />
      <ul>
        {items.map((item) => (
          <li
            key={item}
            onClick={() => setSelectedId(item)}
            style={{
              backgroundColor: selectedId === item ? 'blue' : 'white',
            }}
          >
            {item}
          </li>
        ))}
      </ul>
    </div>
  );
};
```

### Automatic Batching

React 18 automatically batches multiple state updates together.

```typescript
interface BatchingExample {
  count: number;
  text: string;
}

export const BatchingDemo: React.FC = () => {
  const [state, setState] = React.useState<BatchingExample>({
    count: 0,
    text: '',
  });

  const handleClick = () => {
    // These are batched into a single re-render
    setState((prev) => ({ ...prev, count: prev.count + 1 }));
    setState((prev) => ({ ...prev, text: 'Updated' }));
  };

  const handleAsync = async () => {
    await Promise.resolve();
    // Even in async callbacks, updates are batched!
    setState((prev) => ({ ...prev, count: prev.count + 1 }));
    setState((prev) => ({ ...prev, text: 'Async Updated' }));
  };

  return (
    <div>
      <p>Count: {state.count}</p>
      <p>Text: {state.text}</p>
      <button onClick={handleClick}>Sync Update</button>
      <button onClick={handleAsync}>Async Update</button>
    </div>
  );
};
```

### flushSync (Bypass Batching When Needed)

```typescript
import { flushSync } from 'react-dom';

const handleFlushSync = () => {
  flushSync(() => {
    setState((prev) => ({ ...prev, count: prev.count + 1 }));
  });
  // State is guaranteed to be updated synchronously
  console.log('State:', state);
};
```

## Best Practices

1. **Use useTransition for UI feedback** - Show loading states during transitions
2. **Use useDeferredValue for heavy computations** - Keep input responsive
3. **Combine Suspense with code splitting** - Load components on demand
4. **Leverage automatic batching** - Reduces unnecessary re-renders
5. **Type your state updates** - Use TypeScript interfaces for clarity

## Performance Tips

- Memoize expensive computations with `useMemo`
- Use `React.memo` for child components that receive complex props
- Profile with React DevTools Profiler
- Keep component trees shallow when possible
