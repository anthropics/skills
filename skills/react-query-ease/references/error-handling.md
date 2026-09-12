# Error Handling Patterns

## Error State in Hooks

Always type `TError` on `useQuery` and `useMutation`:

```ts
// lib/api/hooks/useTodo.ts
export interface ApiError {
  message: string;
  status: number;
  code?: string;
}

export const useTodos = () => {
  const query = api.useQuery<Todo[], ApiError>({
    url: "/todos",
    key: ["todos"],
  });
  return {
    todos: query.data ?? [],
    todosError: query.error,       // typed as ApiError | null
    isTodosError: query.isError,
    isLoadingTodos: query.isLoading,
    ...query,
  };
};
```

Consume in component:

```tsx
export function Todos() {
  const { todos, isLoadingTodos, isTodosError, todosError } = useTodos();

  if (isLoadingTodos) return <p>Loading...</p>;
  if (isTodosError) return <p>Error: {todosError?.message}</p>;

  return <ul>{todos.map(t => <li key={t.id}>{t.title}</li>)}</ul>;
}
```

## Mutation Error Handling

```ts
export const useCreateTodo = () => {
  const mutation = api.useMutation<Todo, ApiError, NewTodo>({
    url: "/todos",
    method: "POST",
    keyToInvalidate: ["todos"],
    onError: (error) => {
      // Runs on this mutation only; does not suppress global handler
      console.error("Create failed:", error.message);
    },
  });
  return {
    createTodo: mutation.mutate,
    createTodoAsync: mutation.mutateAsync, // throws — use in try/catch
    createTodoError: mutation.error,
    isCreateTodoError: mutation.isError,
    isCreatingTodo: mutation.isPending,
    ...mutation,
  };
};
```

Using `mutateAsync` for inline error handling:

```tsx
const { createTodoAsync } = useCreateTodo();

const handleSubmit = async () => {
  try {
    const newTodo = await createTodoAsync({ title: "Buy milk" });
    toast.success(`Created: ${newTodo.title}`);
  } catch (err) {
    const apiErr = err as ApiError;
    if (apiErr.status === 409) {
      toast.error("Todo already exists");
    } else {
      toast.error(apiErr.message);
    }
  }
};
```

## QueryErrorResetBoundary

Wrap a subtree so users can retry after error:

```tsx
import { QueryErrorResetBoundary } from "@tanstack/react-query";
import { ErrorBoundary } from "react-error-boundary";

export function TodosPage() {
  return (
    <QueryErrorResetBoundary>
      {({ reset }) => (
        <ErrorBoundary
          onReset={reset}
          fallbackRender={({ resetErrorBoundary, error }) => (
            <div>
              <p>Failed to load: {error.message}</p>
              <button onClick={resetErrorBoundary}>Retry</button>
            </div>
          )}
        >
          <Todos />
        </ErrorBoundary>
      )}
    </QueryErrorResetBoundary>
  );
}
```

Install peer dep: `npm install react-error-boundary`

For `ErrorBoundary` to catch query errors, queries must use `throwOnError: true`:

```ts
api.useQuery<Todo[]>({
  url: "/todos",
  key: ["todos"],
  throwOnError: true, // propagates to nearest ErrorBoundary
});
```
