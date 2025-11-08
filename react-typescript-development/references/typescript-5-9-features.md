# TypeScript 5.9 Features Guide

## Key Features

### Inferred Type Predicates

TypeScript can now infer type predicates from function implementations automatically.

```typescript
// Before TS 5.9 - needed explicit return type
const isFish = (pet: unknown): pet is Fish => {
  return (pet as Fish).swim !== undefined;
};

// TypeScript 5.9 - can infer the predicate
const isCat = (pet: unknown) => {
  return (pet as Cat).meow !== undefined;
};

// Usage with type narrowing
interface Fish {
  swim: () => void;
}

interface Cat {
  meow: () => void;
}

type Pet = Fish | Cat;

const pets: Pet[] = [
  { swim: () => {} },
  { meow: () => {} },
];

const activeFish = pets.filter((pet): pet is Fish => isFish(pet));
const activeCats = pets.filter((pet): pet is Cat => isCat(pet));
```

### Stage 3 Decorator Support

Decorators are now officially supported at stage 3 of the TC39 proposal.

```typescript
// Enable in tsconfig.json:
// {
//   "compilerOptions": {
//     "experimentalDecorators": true,
//     "target": "ES2022"
//   }
// }

function Log(
  target: any,
  propertyKey: string,
  descriptor: PropertyDescriptor
) {
  const originalMethod = descriptor.value;

  descriptor.value = function (...args: unknown[]) {
    console.log(`Calling ${propertyKey} with`, args);
    return originalMethod.apply(this, args);
  };

  return descriptor;
}

class UserService {
  @Log
  getUser(id: number) {
    return { id, name: 'John' };
  }
}

// Class decorator
function Entity(constructor: Function) {
  constructor.prototype.entityName = 'BaseEntity';
}

@Entity
class User {
  name: string = '';
}
```

### Import Attributes

Import attributes provide metadata about imported modules.

```typescript
// Import JSON with attributes
import data from './data.json' with { type: 'json' };

// Import CSS modules
import styles from './button.module.css' with { type: 'css' };

// Type-safe usage
interface DataConfig {
  apiUrl: string;
  timeout: number;
}

const config: DataConfig = data;

// For CSS Modules
const buttonClass: string = styles.primary;

// The `with` clause helps bundlers understand module format
import module from './dynamic-module.wasm' with { type: 'wasm' };
```

### Type Inference Improvements

Better type inference in complex scenarios.

```typescript
// Improved const assertions
const config = {
  theme: 'dark',
  fontSize: 14,
  nested: {
    color: '#fff',
  },
} as const;

// Type is now inferred more precisely
type ThemeType = typeof config; // Literal types preserved

// Better inference for generics with constraints
interface Response<T extends { id: number }> {
  data: T;
  timestamp: Date;
}

const response: Response<{ id: number; name: string }> = {
  data: { id: 1, name: 'John' },
  timestamp: new Date(),
};

// Improved conditional type inference
type Flatten<T> = T extends Array<infer U> ? U : T;

const arr = [1, 2, 3];
type ArrElement = Flatten<typeof arr>; // number

// Better inference in mapped types
type GettersOnly<T> = {
  [K in keyof T as K extends `get${infer _}` ? K : never]: T[K];
};

interface Person {
  getName: () => string;
  getAge: () => number;
  email: string;
}

type PersonGetters = GettersOnly<Person>;
// { getName: () => string; getAge: () => number }
```

### New Compiler Options

#### `noImplicitReturns`

Ensures all code paths return a value.

```typescript
// With noImplicitReturns: true
function getValue(key: string): string {
  if (key === 'name') {
    return 'John';
  }
  // Error: not all code paths return a value
}

// Fix:
function getValue(key: string): string {
  if (key === 'name') {
    return 'John';
  }
  return 'default';
}
```

#### `strictNullChecks`

Enforces proper null/undefined handling.

```typescript
// With strictNullChecks: true
let value: string; // Error: must initialize
let nullable: string | null = null; // OK

function process(str: string | null) {
  if (str !== null) {
    console.log(str.toUpperCase()); // OK - str is narrowed
  }
}
```

#### `useDefineForClassFields`

Affects how class fields are compiled.

```typescript
class Component {
  // With useDefineForClassFields: true
  // Compiled as Object.defineProperty
  value: string = 'default';

  constructor() {
    this.value = 'initialized';
  }
}
```

## React + TypeScript 5.9 Patterns

### Generic Component with Improved Inference

```typescript
interface ComponentProps<T> {
  data: T;
  render: (item: T) => React.ReactNode;
}

// TypeScript 5.9 infers T automatically
export const DataRenderer = <T extends { id: string | number }>({
  data,
  render,
}: ComponentProps<T>): React.ReactElement => {
  return <div>{render(data)}</div>;
};

// Usage - no need to specify T
const list = [
  { id: 1, name: 'John' },
  { id: 2, name: 'Jane' },
];

const App = () => (
  <>
    {list.map((item) => (
      <DataRenderer
        key={item.id}
        data={item}
        render={(item) => item.name}
      />
    ))}
  </>
);
```

### Type Guards with Improved Predicates

```typescript
type Result<T> = { ok: true; value: T } | { ok: false; error: string };

// Inferred type predicate
const isOk = <T,>(result: Result<T>) => result.ok === true;

const results: Result<string>[] = [
  { ok: true, value: 'success' },
  { ok: false, error: 'failed' },
];

// Filtered values are properly typed
const successes = results.filter(isOk); // Result<string>[] with ok: true
```

## Migration Checklist

- [ ] Update TypeScript to 5.9+
- [ ] Enable `experimentalDecorators` if using decorators
- [ ] Review type inference for potential changes
- [ ] Test import attributes with bundler support
- [ ] Update compiler options based on project needs
- [ ] Run `tsc --noEmit` to check for new errors

## Compatibility Notes

- Import attributes require target ES2022 or newer
- Decorators still require `experimentalDecorators` flag
- Type inference changes may surface errors in existing code
- Ensure bundler supports new syntax
