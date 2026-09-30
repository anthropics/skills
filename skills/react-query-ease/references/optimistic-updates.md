# Optimistic Updates

Update the cache immediately on mutate; roll back on error.

## Toggle (single item update)

```ts
// lib/api/hooks/useTodo.ts
import { useQueryClient } from "@tanstack/react-query";

export const useToggleTodo = () => {
  const queryClient = useQueryClient();

  const mutation = api.useMutation<Todo, ApiError, { id: string; completed: boolean }>({
    url: (variables) => `/todos/${variables.id}`,
    method: "PATCH",
    // No keyToInvalidate — we manage cache manually below
    onMutate: async (variables) => {
      // Cancel any in-flight refetches for this key
      await queryClient.cancelQueries({ queryKey: ["todos"] });

      // Snapshot current value for rollback
      const previousTodos = queryClient.getQueryData<Todo[]>(["todos"]);

      // Optimistically update
      queryClient.setQueryData<Todo[]>(["todos"], (old = []) =>
        old.map((t) =>
          t.id === variables.id ? { ...t, completed: variables.completed } : t
        )
      );

      return { previousTodos }; // context passed to onError
    },
    onError: (_error, _variables, context) => {
      // Roll back on failure
      if (context?.previousTodos) {
        queryClient.setQueryData(["todos"], context.previousTodos);
      }
    },
    onSettled: () => {
      // Sync with server regardless of outcome
      queryClient.invalidateQueries({ queryKey: ["todos"] });
    },
  });

  return {
    toggleTodo: mutation.mutate,
    isTogglingTodo: mutation.isPending,
    ...mutation,
  };
};
```

## Delete (remove from list)

```ts
export const useDeleteTodo = () => {
  const queryClient = useQueryClient();

  const mutation = api.useMutation<void, ApiError, { id: string }>({
    url: (variables) => `/todos/${variables.id}`,
    method: "DELETE",
    onMutate: async ({ id }) => {
      await queryClient.cancelQueries({ queryKey: ["todos"] });
      const previousTodos = queryClient.getQueryData<Todo[]>(["todos"]);

      queryClient.setQueryData<Todo[]>(["todos"], (old = []) =>
        old.filter((t) => t.id !== id)
      );

      return { previousTodos };
    },
    onError: (_error, _variables, context) => {
      if (context?.previousTodos) {
        queryClient.setQueryData(["todos"], context.previousTodos);
      }
    },
    onSettled: () => {
      queryClient.invalidateQueries({ queryKey: ["todos"] });
    },
  });

  return {
    deleteTodo: mutation.mutate,
    isDeletingTodo: mutation.isPending,
    ...mutation,
  };
};
```

## Create (append to list)

```ts
export const useCreateTodo = () => {
  const queryClient = useQueryClient();

  const mutation = api.useMutation<Todo, ApiError, NewTodo>({
    url: "/todos",
    method: "POST",
    onMutate: async (newTodo) => {
      await queryClient.cancelQueries({ queryKey: ["todos"] });
      const previousTodos = queryClient.getQueryData<Todo[]>(["todos"]);

      // Append temp item with placeholder id
      queryClient.setQueryData<Todo[]>(["todos"], (old = []) => [
        ...old,
        { id: `temp-${Date.now()}`, ...newTodo, completed: false },
      ]);

      return { previousTodos };
    },
    onError: (_error, _variables, context) => {
      if (context?.previousTodos) {
        queryClient.setQueryData(["todos"], context.previousTodos);
      }
    },
    onSettled: () => {
      // Replace temp item with real server response
      queryClient.invalidateQueries({ queryKey: ["todos"] });
    },
  });

  return {
    createTodo: mutation.mutate,
    isCreatingTodo: mutation.isPending,
    ...mutation,
  };
};
```

## Key Rules

- Always `cancelQueries` before `setQueryData` — prevents in-flight refetch overwriting your optimistic state
- Always snapshot before update — `getQueryData` before `setQueryData`
- Return snapshot from `onMutate` — React Query passes it as `context` to `onError`/`onSettled`
- Always `invalidateQueries` in `onSettled` — syncs temp state with real server data
