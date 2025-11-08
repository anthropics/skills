/**
 * Type-Safe IPC Wrapper for Tauri
 *
 * This template provides a foundation for building a type-safe IPC layer
 * between your React frontend and Tauri backend.
 *
 * Features:
 * - Type-safe command invocation
 * - Automatic error handling
 * - Retry logic with exponential backoff
 * - Timeout support
 * - Event subscription management
 * - Request/response tracking
 *
 * Usage:
 * 1. Replace TauriCommands interface with your actual commands
 * 2. Update error handling to match your error types
 * 3. Customize retry and timeout policies as needed
 */

import { invoke as tauriInvoke, Event } from '@tauri-apps/api/core';
import { listen, unlisten, UnlistenFn } from '@tauri-apps/api/event';

/**
 * Define your Tauri commands here
 * Auto-generate these types using generate-tauri-command-types.py
 */
export interface TauriCommands {
  // Example commands - replace with your actual commands
  greet: {
    params: { name: string };
    result: string;
  };
  read_file: {
    params: { path: string };
    result: string;
  };
  write_file: {
    params: { path: string; content: string };
    result: void;
  };
  // Add your commands here
}

/**
 * Tauri error response type
 */
export interface TauriError {
  code: string;
  message: string;
  details?: string;
}

/**
 * Invoke options
 */
export interface InvokeOptions {
  timeoutMs?: number;
  maxRetries?: number;
  retryDelayMs?: number;
}

/**
 * Default configuration
 */
const DEFAULT_TIMEOUT_MS = 30000;
const DEFAULT_MAX_RETRIES = 3;
const DEFAULT_RETRY_DELAY_MS = 1000;

/**
 * Type-safe invoke function with error handling and retry logic
 *
 * @param command - Command name
 * @param params - Command parameters
 * @param options - Invoke options (timeout, retries)
 * @returns Promise resolving to command result
 */
export async function invoke<K extends keyof TauriCommands>(
  command: K,
  params?: TauriCommands[K]['params'],
  options: InvokeOptions = {}
): Promise<TauriCommands[K]['result']> {
  const {
    timeoutMs = DEFAULT_TIMEOUT_MS,
    maxRetries = DEFAULT_MAX_RETRIES,
    retryDelayMs = DEFAULT_RETRY_DELAY_MS,
  } = options;

  let lastError: Error | null = null;

  for (let attempt = 1; attempt <= maxRetries; attempt++) {
    try {
      return await invokeWithTimeout<TauriCommands[K]['result']>(
        command as string,
        params,
        timeoutMs
      );
    } catch (error) {
      lastError = error instanceof Error ? error : new Error(String(error));

      // Don't retry on validation or not found errors
      const isRetryable = !lastError.message.includes(
        'VALIDATION_ERROR'
      ) && !lastError.message.includes('NOT_FOUND');

      if (!isRetryable || attempt === maxRetries) {
        break;
      }

      // Exponential backoff
      const delay = retryDelayMs * Math.pow(2, attempt - 1);
      await sleep(delay);
    }
  }

  throw lastError || new Error('Invocation failed');
}

/**
 * Invoke with timeout support
 */
async function invokeWithTimeout<T>(
  command: string,
  params: unknown,
  timeoutMs: number
): Promise<T> {
  return Promise.race([
    tauriInvoke<T>(command, params),
    new Promise<T>((_, reject) =>
      setTimeout(
        () => reject(new Error(`Command ${command} timed out after ${timeoutMs}ms`)),
        timeoutMs
      )
    ),
  ]);
}

/**
 * Listen to Tauri event with automatic cleanup tracking
 *
 * @param eventName - Event name
 * @param handler - Event handler
 * @returns Function to unlisten
 */
export async function onEvent<T = unknown>(
  eventName: string,
  handler: (payload: T) => void
): Promise<() => Promise<void>> {
  const unlisten = await listen<T>(eventName, (event: Event<T>) => {
    handler(event.payload);
  });

  // Return a function that unlistens
  return async () => {
    await unlisten();
  };
}

/**
 * Listen to multiple events
 *
 * @param handlers - Map of event names to handlers
 * @returns Function to unlisten all
 */
export async function onEvents(
  handlers: Record<string, (payload: unknown) => void>
): Promise<() => Promise<void>> {
  const unlisteners: Array<() => Promise<void>> = [];

  for (const [eventName, handler] of Object.entries(handlers)) {
    const unlisten = await onEvent(eventName, handler);
    unlisteners.push(unlisten);
  }

  return async () => {
    await Promise.all(unlisteners.map((fn) => fn()));
  };
}

/**
 * Create a reactive event listener that integrates with React
 *
 * @param eventName - Event name
 * @param initialValue - Initial value for the state
 * @returns Object with current value and setter
 */
export function createEventState<T>(
  eventName: string,
  initialValue: T
): { value: T; setValue: (value: T) => void; cleanup: () => Promise<void> } {
  let currentValue = initialValue;
  const setters: Set<(value: T) => void> = new Set();
  let unlistener: (() => Promise<void>) | null = null;

  const initialize = async () => {
    unlistener = await onEvent<T>(eventName, (payload) => {
      currentValue = payload;
      setters.forEach((setter) => setter(payload));
    });
  };

  const cleanup = async () => {
    if (unlistener) {
      await unlistener();
      unlistener = null;
    }
  };

  initialize().catch(console.error);

  return {
    get value() {
      return currentValue;
    },
    setValue(newValue: T) {
      currentValue = newValue;
      setters.forEach((setter) => setter(newValue));
    },
    cleanup,
  };
}

/**
 * React hook for Tauri commands
 *
 * Usage:
 * const { data, loading, error, refetch } = useCommand('greet', { name: 'World' });
 */
export function useCommand<K extends keyof TauriCommands>(
  command: K,
  params?: TauriCommands[K]['params'],
  options: InvokeOptions & { autoFetch?: boolean } = {}
) {
  const { autoFetch = true, ...invokeOptions } = options;
  const [data, setData] = React.useState<TauriCommands[K]['result'] | null>(null);
  const [loading, setLoading] = React.useState(autoFetch);
  const [error, setError] = React.useState<Error | null>(null);

  const refetch = React.useCallback(async () => {
    setLoading(true);
    setError(null);

    try {
      const result = await invoke(command, params, invokeOptions);
      setData(result);
    } catch (err) {
      const error = err instanceof Error ? err : new Error(String(err));
      setError(error);
    } finally {
      setLoading(false);
    }
  }, [command, JSON.stringify(params), invokeOptions]);

  React.useEffect(() => {
    if (autoFetch) {
      refetch();
    }
  }, [command, JSON.stringify(params), autoFetch, refetch]);

  return { data, loading, error, refetch };
}

/**
 * React hook for event listening
 *
 * Usage:
 * const { data, isListening } = useEvent<Progress>('progress_update');
 */
export function useEvent<T = unknown>(eventName: string) {
  const [data, setData] = React.useState<T | null>(null);
  const [isListening, setIsListening] = React.useState(false);

  React.useEffect(() => {
    let unlistener: (() => Promise<void>) | null = null;

    const setupListener = async () => {
      unlistener = await onEvent<T>(eventName, (payload) => {
        setData(payload);
      });
      setIsListening(true);
    };

    setupListener().catch(console.error);

    return () => {
      if (unlistener) {
        unlistener().catch(console.error);
        setIsListening(false);
      }
    };
  }, [eventName]);

  return { data, isListening };
}

/**
 * React hook for listening to multiple events
 *
 * Usage:
 * const handlers = {
 *   'event1': (data) => console.log(data),
 *   'event2': (data) => console.log(data),
 * };
 * useEvents(handlers);
 */
export function useEvents(
  handlers: Record<string, (payload: unknown) => void>
) {
  React.useEffect(() => {
    let cleanup: (() => Promise<void>) | null = null;

    const setup = async () => {
      cleanup = await onEvents(handlers);
    };

    setup().catch(console.error);

    return () => {
      if (cleanup) {
        cleanup().catch(console.error);
      }
    };
  }, [JSON.stringify(handlers)]);
}

/**
 * Helper to create a mutation hook
 *
 * Usage:
 * const { execute, loading, error } = useMutation('write_file');
 * await execute({ path: '/tmp/file.txt', content: 'hello' });
 */
export function useMutation<K extends keyof TauriCommands>(
  command: K,
  options: InvokeOptions = {}
) {
  const [loading, setLoading] = React.useState(false);
  const [error, setError] = React.useState<Error | null>(null);
  const [data, setData] = React.useState<TauriCommands[K]['result'] | null>(null);

  const execute = React.useCallback(
    async (params?: TauriCommands[K]['params']) => {
      setLoading(true);
      setError(null);

      try {
        const result = await invoke(command, params, options);
        setData(result);
        return result;
      } catch (err) {
        const error = err instanceof Error ? err : new Error(String(err));
        setError(error);
        throw error;
      } finally {
        setLoading(false);
      }
    },
    [command, options]
  );

  return { execute, loading, error, data };
}

/**
 * Create an event emitter for client-side events
 */
export class EventEmitter<T extends Record<string, unknown>> {
  private listeners: Map<keyof T, Set<(payload: T[keyof T]) => void>> = new Map();

  on<K extends keyof T>(
    eventName: K,
    handler: (payload: T[K]) => void
  ): () => void {
    if (!this.listeners.has(eventName)) {
      this.listeners.set(eventName, new Set());
    }

    this.listeners.get(eventName)!.add(handler);

    return () => {
      this.listeners.get(eventName)?.delete(handler);
    };
  }

  emit<K extends keyof T>(eventName: K, payload: T[K]) {
    const handlers = this.listeners.get(eventName);
    if (handlers) {
      handlers.forEach((handler) => {
        try {
          handler(payload);
        } catch (error) {
          console.error(`Error in event handler for ${String(eventName)}:`, error);
        }
      });
    }
  }

  removeAllListeners() {
    this.listeners.clear();
  }
}

/**
 * Utility: Sleep function
 */
export function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

/**
 * Utility: Check if error is a Tauri error
 */
export function isTauriError(error: unknown): error is TauriError {
  return (
    typeof error === 'object' &&
    error !== null &&
    'code' in error &&
    'message' in error
  );
}

/**
 * Utility: Convert any error to a user-friendly message
 */
export function getErrorMessage(error: unknown): string {
  if (typeof error === 'string') {
    return error;
  }

  if (isTauriError(error)) {
    return error.message;
  }

  if (error instanceof Error) {
    return error.message;
  }

  return 'An unknown error occurred';
}

/**
 * Batch invoke - useful for invoking multiple commands
 *
 * Usage:
 * const results = await batchInvoke([
 *   { command: 'greet', params: { name: 'Alice' } },
 *   { command: 'greet', params: { name: 'Bob' } },
 * ]);
 */
export async function batchInvoke<K extends keyof TauriCommands>(
  requests: Array<{
    command: K;
    params?: TauriCommands[K]['params'];
  }>
): Promise<TauriCommands[K]['result'][]> {
  return Promise.all(
    requests.map(({ command, params }) => invoke(command, params))
  );
}

/**
 * Note: Import React separately in your component file:
 * import React from 'react';
 */

/**
 * Export all types for convenience
 */
export type {
  TauriCommands,
  TauriError,
  InvokeOptions,
};
