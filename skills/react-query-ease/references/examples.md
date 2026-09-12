# Full CRUD Example

Complete Todo app demonstrating the recommended project structure with `react-query-ease`.

## Project Structure

```
src/
  config/
    apiClients.ts    ← client instances
  hooks/
    todos.ts         ← typed hook wrappers
  components/
    Todos.tsx        ← UI
```

## 1. Client (`src/config/apiClients.ts`)

```ts
import { createApiClient } from "react-query-ease";

export const todosApi = createApiClient({
  baseURL: "https://api.example.com",
});
```

## 2. Types + Hooks (`src/hooks/todos.ts`)

```ts
import { todosApi } from "../config/apiClients";

export type ApiError = {
  message: string;
  status: number;
};

export type Todo = {
  id: string;
  title: string;
  completed: boolean;
};

export type NewTodo = Pick<Todo, "title">;
export type UpdateTodoInput = Partial<Omit<Todo, "id">> & { id: string };
export type TodoSearchFilters = { query: string };

export const useTodos = () => {
  const query = todosApi.useQuery<Todo[]>({
    url: "/todos",
    key: ["todos"],
  });
  return {
    todos: query.data ?? [],
    isTodoLoading: query.isLoading,
    ...query,
  };
};

export const useSearchTodos = (filters: TodoSearchFilters) => {
  const query = todosApi.useQuery<Todo[]>({
    url: "/todos/search",
    key: ["todos", "search", filters.query],
    params: { q: filters.query },
    enabled: filters.query.length > 0,
  });
  return {
    searchResults: query.data ?? [],
    isSearchLoading: query.isLoading,
    ...query,
  };
};

export const useCreateTodo = () => {
  const { mutate, isPending, ...rest } = todosApi.useMutation<
    Todo,
    ApiError,
    NewTodo
  >({
    url: "/todos",
    method: "POST",
    keyToInvalidate: ["todos"],
  });
  return { createTodo: mutate, isCreatingTodo: isPending, ...rest };
};

export const useUpdateTodo = () => {
  const { mutate, isPending, ...rest } = todosApi.useMutation<
    Todo,
    ApiError,
    UpdateTodoInput
  >({
    url: (variables) => `/todos/${variables.id}`,
    method: "PATCH",
    keyToInvalidate: ["todos"],
  });
  return { updateTodo: mutate, isUpdatingTodo: isPending, ...rest };
};

export const useDeleteTodo = () => {
  const { mutate, isPending, ...rest } = todosApi.useMutation<
    void,
    ApiError,
    { id: string }
  >({
    url: (variables) => `/todos/${variables.id}`,
    method: "DELETE",
    keyToInvalidate: ["todos"],
  });
  return { deleteTodo: mutate, isDeletingTodo: isPending, ...rest };
};
```

## 3. Component (`src/components/Todos.tsx`)

```tsx
import { useState } from "react";
import {
  useTodos,
  useCreateTodo,
  useUpdateTodo,
  useDeleteTodo,
  useSearchTodos,
} from "../hooks/todos";

export function Todos() {
  const [search, setSearch] = useState("");
  const { todos, isTodoLoading } = useTodos();
  const { createTodo, isCreatingTodo } = useCreateTodo();
  const { updateTodo, isUpdatingTodo } = useUpdateTodo();
  const { deleteTodo, isDeletingTodo } = useDeleteTodo();
  const { searchResults, isSearchLoading } = useSearchTodos({ query: search });

  if (isTodoLoading) return <p>Loading...</p>;

  return (
    <>
      <button
        disabled={isCreatingTodo}
        onClick={() => createTodo({ title: "New todo" })}
      >
        Add Todo
      </button>

      <input
        value={search}
        placeholder="Search todos"
        onChange={(e) => setSearch(e.target.value)}
      />

      {search &&
        (isSearchLoading ? (
          <p>Searching...</p>
        ) : (
          <ul>
            {searchResults.map((todo) => (
              <li key={todo.id}>{todo.title}</li>
            ))}
          </ul>
        ))}

      <ul>
        {todos.map((todo) => (
          <li key={todo.id}>
            <span>{todo.title}</span>
            <button
              disabled={isUpdatingTodo}
              onClick={() =>
                updateTodo({ id: todo.id, completed: !todo.completed })
              }
            >
              Toggle
            </button>
            <button
              disabled={isDeletingTodo}
              onClick={() => deleteTodo({ id: todo.id })}
            >
              Delete
            </button>
          </li>
        ))}
      </ul>
    </>
  );
}
```

## Key Patterns

- **Clients in `config/`** — one file per service, export named clients
- **Hooks in `hooks/`** — rename mutation/query values to domain names (`createTodo` not `mutate`)
- **Components only import hooks** — never import clients directly in components
- **`keyToInvalidate`** — use the same key string you pass to `useQuery`'s `key`
- **Dynamic URLs** — pass `(variables) => string` function when URL contains variable segments
- **TypeScript generics** — `useMutation<TData, TError, TVariables>` gives full type safety on `mutate` call sites
