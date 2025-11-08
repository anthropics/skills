---
name: react-typescript-development
description: Build complex stateful user interfaces with React 18 and TypeScript 5.x for desktop applications. This skill should be used when creating React components with TypeScript, implementing state management, leveraging React 18 concurrent features, configuring TypeScript strict mode, optimizing React performance, or building type-safe component libraries.
---

# React + TypeScript Development

## Overview

This skill provides comprehensive guidance for building production-ready React applications with TypeScript 5.x, focusing on type safety, modern React 18 features (concurrent rendering, Suspense, transitions), and patterns specific to desktop application development.

**Latest Versions:** React 18.3.1, TypeScript 5.9.3
**Official Documentation:**
- React: https://react.dev
- TypeScript: https://www.typescriptlang.org

## When to Use This Skill

Use this skill when:
- Creating React components with full TypeScript type safety
- Implementing complex state management in desktop apps
- Leveraging React 18 concurrent features (transitions, Suspense)
- Configuring TypeScript for strict type checking
- Building reusable component libraries
- Optimizing React application performance
- Integrating React with desktop frameworks (Tauri)

## Core Capabilities

### 1. TypeScript Configuration

Use the strict configuration template from `assets/tsconfig.json-strict`:

```json
{
  "compilerOptions": {
    "target": "ES2020",
    "lib": ["ES2020", "DOM", "DOM.Iterable"],
    "module": "ESNext",
    "moduleResolution": "bundler",
    "jsx": "react-jsx",
    "strict": true,
    "noUnusedLocals": true,
    "noUnusedParameters": true,
    "noFallthroughCasesInSwitch": true,
    "paths": {
      "@/*": ["./src/*"]
    }
  }
}
```

### 2. Component Patterns

**Typed Functional Components:**

```typescript
import { FC, ReactNode } from 'react';

interface ButtonProps {
  variant: 'primary' | 'secondary';
  children: ReactNode;
  onClick?: () => void;
}

export const Button: FC<ButtonProps> = ({ variant, children, onClick }) => {
  return <button onClick={onClick}>{children}</button>;
};
```

**Generate components using:**
```bash
python scripts/create-component-template.py ComponentName
```

### 3. React 18 Features

**Transitions:**
```typescript
import { useState, useTransition } from 'react';

function SearchComponent() {
  const [query, setQuery] = useState('');
  const [isPending, startTransition] = useTransition();

  const handleSearch = (value: string) => {
    setQuery(value);
    startTransition(() => {
      // Non-urgent updates
    });
  };
}
```

**Suspense:**
```typescript
import { Suspense } from 'react';

<Suspense fallback={<Loading />}>
  <DataComponent />
</Suspense>
```

See `references/react-18-features.md` for comprehensive coverage.

### 4. State Management

**Context + Reducer:**

```typescript
interface State {
  user: User | null;
}

type Action = { type: 'SET_USER'; payload: User };

const AppContext = createContext<{
  state: State;
  dispatch: Dispatch<Action>;
} | undefined>(undefined);
```

**Zustand (Recommended):**

```typescript
import { create } from 'zustand';

interface StoreState {
  count: number;
  increment: () => void;
}

export const useStore = create<StoreState>((set) => ({
  count: 0,
  increment: () => set((state) => ({ count: state.count + 1 }))
}));
```

See `references/state-management-patterns.md` for complete patterns.

### 5. TypeScript 5.9 Features

Key improvements:
- Inferred type predicates
- Decorator stage 3 support
- Import attribute improvements
- Better type inference

See `references/typescript-5-9-features.md` for details.

### 6. Performance Optimization

**useMemo:**
```typescript
const sortedData = useMemo(() => {
  return [...data].sort();
}, [data]);
```

**useCallback:**
```typescript
const handleClick = useCallback(() => {
  setCount((c) => c + 1);
}, []);
```

**React.memo:**
```typescript
export const ExpensiveComponent = memo<Props>(({ title }) => {
  return <div>{title}</div>;
});
```

## Resources

### scripts/
- `create-component-template.py` - Generate typed React component boilerplate

### references/
- `react-18-features.md` - React 18 concurrent features guide
- `typescript-5-9-features.md` - TypeScript 5.9 features
- `state-management-patterns.md` - State management patterns

### assets/
- `tsconfig.json-strict` - Strict TypeScript configuration
