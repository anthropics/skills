# State Management Patterns Guide

## Context API + useReducer

Best for: Medium-sized apps, avoiding prop drilling, complex state logic.

### Basic Setup

```typescript
interface AppState {
  user: { id: number; name: string } | null;
  theme: 'light' | 'dark';
  notifications: string[];
}

type AppAction =
  | { type: 'SET_USER'; payload: AppState['user'] }
  | { type: 'TOGGLE_THEME' }
  | { type: 'ADD_NOTIFICATION'; payload: string }
  | { type: 'CLEAR_NOTIFICATIONS' };

const initialState: AppState = {
  user: null,
  theme: 'light',
  notifications: [],
};

const appReducer = (state: AppState, action: AppAction): AppState => {
  switch (action.type) {
    case 'SET_USER':
      return { ...state, user: action.payload };
    case 'TOGGLE_THEME':
      return { ...state, theme: state.theme === 'light' ? 'dark' : 'light' };
    case 'ADD_NOTIFICATION':
      return {
        ...state,
        notifications: [...state.notifications, action.payload],
      };
    case 'CLEAR_NOTIFICATIONS':
      return { ...state, notifications: [] };
    default:
      return state;
  }
};

// Create context with proper typing
interface AppContextType {
  state: AppState;
  dispatch: React.Dispatch<AppAction>;
}

const AppContext = React.createContext<AppContextType | undefined>(undefined);

export const AppProvider: React.FC<{ children: React.ReactNode }> = ({
  children,
}) => {
  const [state, dispatch] = React.useReducer(appReducer, initialState);

  return (
    <AppContext.Provider value={{ state, dispatch }}>
      {children}
    </AppContext.Provider>
  );
};

// Custom hook for using context
export const useAppContext = (): AppContextType => {
  const context = React.useContext(AppContext);
  if (!context) {
    throw new Error('useAppContext must be used within AppProvider');
  }
  return context;
};
```

### Usage in Components

```typescript
const UserProfile: React.FC = () => {
  const { state, dispatch } = useAppContext();

  const handleSetUser = () => {
    dispatch({
      type: 'SET_USER',
      payload: { id: 1, name: 'John Doe' },
    });
  };

  return (
    <div>
      <p>User: {state.user?.name || 'Not logged in'}</p>
      <button onClick={handleSetUser}>Set User</button>
    </div>
  );
};
```

### Pros & Cons

**Pros:**
- Built-in to React
- No external dependencies
- Good for moderately complex state
- Great for shared state across components

**Cons:**
- Can cause unnecessary re-renders if not optimized
- Verbose for simple state
- Need to split context/actions carefully

---

## Zustand with TypeScript

Best for: Global state management, simple API, minimal boilerplate.

### Setup

```typescript
import create from 'zustand';
import { devtools, persist } from 'zustand/middleware';

interface User {
  id: number;
  name: string;
  email: string;
}

interface Store {
  user: User | null;
  theme: 'light' | 'dark';
  setUser: (user: User | null) => void;
  toggleTheme: () => void;
}

export const useStore = create<Store>()(
  devtools(
    persist(
      (set) => ({
        user: null,
        theme: 'light',
        setUser: (user) => set({ user }),
        toggleTheme: () =>
          set((state) => ({
            theme: state.theme === 'light' ? 'dark' : 'light',
          })),
      }),
      {
        name: 'app-storage',
      }
    )
  )
);
```

### Usage

```typescript
const UserCard: React.FC = () => {
  // Only re-renders when selected state changes
  const user = useStore((state) => state.user);
  const setUser = useStore((state) => state.setUser);

  return (
    <div>
      <p>{user?.name || 'Not logged in'}</p>
      <button onClick={() => setUser({ id: 1, name: 'Jane', email: 'jane@example.com' })}>
        Set User
      </button>
    </div>
  );
};

const ThemeToggle: React.FC = () => {
  const { theme, toggleTheme } = useStore();

  return (
    <button onClick={toggleTheme}>
      Current theme: {theme}
    </button>
  );
};
```

### Advanced: Derived State

```typescript
const useUserWithDefaults = () => {
  const user = useStore((state) => state.user);

  return {
    name: user?.name || 'Guest',
    email: user?.email || 'no-email@example.com',
  };
};
```

### Pros & Cons

**Pros:**
- Simple and intuitive API
- Minimal boilerplate
- Good TypeScript support
- Small bundle size
- Excellent DevTools integration

**Cons:**
- Smaller ecosystem compared to Redux
- Middleware system less mature
- Single store (though can compose multiple)

---

## Jotai Atoms

Best for: Primitive-based state, fine-grained reactivity, complex state dependencies.

### Setup

```typescript
import { atom, useAtom, useAtomValue, useSetAtom } from 'jotai';

// Create atoms
const userAtom = atom<{ id: number; name: string } | null>(null);
const themeAtom = atom<'light' | 'dark'>('light');

// Derived atoms
const userNameAtom = atom((get) => {
  const user = get(userAtom);
  return user?.name || 'Guest';
});

const isDarkModeAtom = atom((get) => {
  return get(themeAtom) === 'dark';
});

// Atoms with async operations
const fetchUserAtom = atom(async (get) => {
  const id = get(userIdAtom);
  const response = await fetch(`/api/users/${id}`);
  return response.json();
});
```

### Usage

```typescript
// Read and write
const UserProfile: React.FC = () => {
  const [user, setUser] = useAtom(userAtom);

  return (
    <div>
      <p>{user?.name}</p>
      <button onClick={() => setUser({ id: 1, name: 'John' })}>
        Update
      </button>
    </div>
  );
};

// Read-only
const UserName: React.FC = () => {
  const userName = useAtomValue(userNameAtom);
  return <p>{userName}</p>;
};

// Write-only
const UserSetter: React.FC = () => {
  const setUser = useSetAtom(userAtom);

  return (
    <button onClick={() => setUser({ id: 2, name: 'Jane' })}>
      Set Jane
    </button>
  );
};
```

### Advanced: Atom Composition

```typescript
const counterAtom = atom(0);
const doubledAtom = atom(
  (get) => get(counterAtom) * 2,
  (get, set, newValue: number) => {
    set(counterAtom, newValue / 2);
  }
);

const Counter: React.FC = () => {
  const [doubled, setDoubled] = useAtom(doubledAtom);

  return (
    <div>
      <p>Doubled: {doubled}</p>
      <button onClick={() => setDoubled(10)}>Set to 10</button>
    </div>
  );
};
```

### Pros & Cons

**Pros:**
- Primitive-based model (atoms)
- Fine-grained reactivity
- Excellent for complex dependencies
- Easy async data fetching
- Good TypeScript support

**Cons:**
- Smaller community
- Learning curve for atom composition
- Might be overkill for simple apps

---

## Comparison Matrix

| Feature | Context + Reducer | Zustand | Jotai |
|---------|-------------------|---------|-------|
| Complexity | Medium | Low | Medium |
| Bundle Size | ~0kb | ~2kb | ~4kb |
| Dev Tools | Limited | Excellent | Good |
| Async Support | Manual | Via middleware | Built-in |
| Learning Curve | Moderate | Low | Steep |
| Persistence | Manual | Via middleware | Via middleware |
| DevX | Good | Excellent | Good |

## Decision Guide

### Use Context + Reducer when:
- Building small to medium apps
- You want zero dependencies
- State is deeply nested and complex
- Team is familiar with Redux patterns

### Use Zustand when:
- You want simplicity and minimal boilerplate
- Building a global store
- You like a simple, intuitive API
- You prefer hooks over render props

### Use Jotai when:
- You need fine-grained reactivity
- State has complex dependencies
- You frequently use async operations
- You prefer a primitive atom model

## Best Practices

1. **Keep store/context focused** - Don't mix unrelated state
2. **Use selectors** - Only subscribe to needed state
3. **Memoize components** - Prevent unnecessary renders
4. **Avoid deeply nested state** - Flatten when possible
5. **Use TypeScript** - Full type safety for all options
6. **Test state logic** - Use reducer/selector tests
7. **Profile performance** - Check for render thrashing

## Combining Patterns

```typescript
// Example: Context for theme + Zustand for user
const useUser = useStore((state) => state.user); // Global user
const { theme, setTheme } = useAppContext(); // Local theme context
```
