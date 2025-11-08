---
name: tauri-react-integration
description: Integrate Tauri backend with React frontend via IPC. Use when implementing command invocation from React, handling Tauri events in React components, streaming progress updates, managing async operations, syncing frontend-backend state, or building type-safe IPC layers.
---

# Tauri + React Integration

## Overview

This skill provides comprehensive patterns and utilities for integrating Tauri's Rust backend with React frontends. It covers bidirectional communication, type safety, state synchronization, and advanced patterns for building responsive desktop applications.

## When to Use This Skill

- Invoking Tauri commands from React components
- Handling backend events in React with proper cleanup
- Streaming progress updates from Rust to React
- Managing complex async operations with loading/error states
- Keeping UI state synchronized with backend state
- Building type-safe IPC layers that prevent runtime errors
- Implementing request-response patterns with timeouts
- Creating custom React hooks for Tauri APIs

## Core Concepts

### IPC Patterns

Tauri provides two primary communication mechanisms:

1. **Command Invocation (Request-Response)**
   - React calls Rust command, waits for result
   - Ideal for one-off operations (file I/O, computations)
   - Returns typed Promise resolving to command result

2. **Events (Unidirectional Broadcasting)**
   - Backend emits events that frontend subscribes to
   - Multiple listeners receive same event
   - Perfect for progress updates, status changes, background events

3. **Streaming (Server-Sent Communication)**
   - Backend continuously sends data
   - Frontend listens and updates in real-time
   - Combine command invocation with event streaming

### Type Safety

Generate TypeScript types from Rust command signatures to prevent mismatches:
- Use `generate-tauri-command-types.py` to auto-generate types
- Ensures command names, parameters, and return types match
- Catch errors at compile time instead of runtime

### Error Handling

Implement robust error propagation:
- Define error types in both Rust and TypeScript
- Use Result types in Rust, typed error handling in TypeScript
- Implement retry logic for transient failures
- Provide meaningful error messages to users

### State Synchronization

Keep React state in sync with backend:
- Query backend on component mount for initial state
- Listen to backend events that modify state
- Batch updates to prevent excessive re-renders
- Implement optimistic updates for better UX

### Async Operations

Manage long-running operations properly:
- Use React hooks for loading/error/data states
- Implement cancellation tokens for early termination
- Handle timeouts gracefully
- Show progress updates via events

## Common Patterns

### Basic Command Invocation
```typescript
import { invoke } from '@tauri-apps/api/core';

// Single invocation
const result = await invoke<string>('greet', { name: 'World' });

// In React hook with error handling
const [data, setData] = useState(null);
const [error, setError] = useState(null);
const [loading, setLoading] = useState(false);

useEffect(() => {
  setLoading(true);
  invoke('fetch_data')
    .then(setData)
    .catch(setError)
    .finally(() => setLoading(false));
}, []);
```

### Event Listening
```typescript
import { listen } from '@tauri-apps/api/event';

useEffect(() => {
  const unlisten = listen('file_progress', (event) => {
    setProgress(event.payload);
  });

  return () => {
    unlisten.then(f => f());
  };
}, []);
```

### Type-Safe Command Invocation
```typescript
// Generated types file (tauri-commands.ts)
export interface Commands {
  process_file: {
    params: { path: string };
    result: ProcessResult;
  };
  calculate_sum: {
    params: { numbers: number[] };
    result: number;
  };
}

// Wrapper function
export async function invokeTyped<K extends keyof Commands>(
  command: K,
  params: Commands[K]['params']
): Promise<Commands[K]['result']> {
  return invoke(command, params);
}
```

### Progress Streaming
```typescript
// React component
useEffect(() => {
  const handleProgress = async () => {
    const unlistenProgress = await listen('process_progress', (event) => {
      setProgress(event.payload.percent);
    });

    try {
      await invoke('start_long_operation');
    } finally {
      await unlistenProgress();
    }
  };

  handleProgress();
}, []);
```

### State Synchronization
```typescript
// Custom hook for backend-synced state
function useSyncedState<T>(key: string, fetchCommand: string) {
  const [state, setState] = useState<T | null>(null);

  useEffect(() => {
    // Initial fetch
    invoke(fetchCommand).then(setState);

    // Listen for backend changes
    const unsubscribe = listen(`${key}_updated`, (event) => {
      setState(event.payload);
    });

    return () => {
      unsubscribe.then(f => f());
    };
  }, [key, fetchCommand]);

  return state;
}
```

## Best Practices

1. **Always Clean Up Listeners**: Unlisten from events in useEffect cleanup
2. **Type Everything**: Generate types from Rust to catch errors early
3. **Handle Errors**: Never leave errors unhandled; inform users
4. **Timeout Operations**: Set timeouts on long-running operations
5. **Batch Updates**: Combine multiple state updates to reduce re-renders
6. **Use Custom Hooks**: Abstract IPC logic into reusable hooks
7. **Implement Loading States**: Show progress for long operations
8. **Validate Input**: Validate parameters before sending to Rust
9. **Document Commands**: Keep Rust command docs synchronized with frontend
10. **Test Both Sides**: Test commands in isolation and integration tests

## Bundled Resources

- **scripts/generate-tauri-command-types.py**: Auto-generate TypeScript types from Rust commands
- **references/tauri-react-ipc-patterns.md**: Detailed IPC patterns with code examples
- **references/error-handling-strategies.md**: Error handling and recovery patterns
- **references/state-sync-patterns.md**: Strategies for keeping UI and backend in sync
- **assets/ipc-wrapper-template.ts**: Ready-to-use type-safe IPC client template

## Quick Start

1. Review `tauri-react-ipc-patterns.md` for communication patterns
2. Use `ipc-wrapper-template.ts` as a starting point for your IPC layer
3. Run `generate-tauri-command-types.py` to create types from Rust
4. Implement error handling using `error-handling-strategies.md`
5. Keep state synced using patterns from `state-sync-patterns.md`

## Dependencies

- `@tauri-apps/api`: Tauri JavaScript API
- `react`: For hooks and component patterns
- `typescript`: For type safety

## See Also

- [Tauri Documentation](https://tauri.app/)
- [React Hooks Documentation](https://react.dev/reference/react/hooks)
- Related skill: tauri-desktop-framework
