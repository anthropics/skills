---
name: typescript-best-practices
description: Enforces TypeScript best practices and modern patterns
version: 1.0.0
tags: [typescript, best-practices, code-quality]
globs: ["**/*.ts", "**/*.tsx"]
---

# TypeScript Best Practices

## When to Use

Use this skill when:
- Writing new TypeScript code
- Reviewing TypeScript pull requests
- Refactoring JavaScript to TypeScript

## Triggers

Activated when editing `.ts` or `.tsx` files in the project.

## Rules

### Always
- Always use `const` for variables that won't be reassigned
- Always use explicit return types on exported functions
- Always prefer `interface` over `type` for object shapes

### Never
- Never use `any` — use `unknown` instead
- Never use `var` — use `const` or `let`
- Never ignore TypeScript errors with `@ts-ignore`

## Examples

```typescript
// Good: explicit return type
export function calculateTotal(items: Item[]): number {
  return items.reduce((sum, item) => sum + item.price, 0);
}
```

```typescript
// Good: discriminated union
type Result<T> =
  | { success: true; data: T }
  | { success: false; error: Error };
```

## Boundaries

- Do not modify `tsconfig.json` without explicit permission
- Do not add new dependencies without checking existing utilities
- Focus only on TypeScript patterns, not runtime behavior
