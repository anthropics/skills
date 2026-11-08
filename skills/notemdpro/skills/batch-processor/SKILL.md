---
name: batch-processor
description: "Use when processing 10+ markdown files in bulk, encountering HTTP 429 rate limits, or needing OOM-safe Base64 sanitization before LLM chunking"
---

# NoteMD Pro - Batch Processing

## Overview

This skill provides utilities for batch processing multiple markdown files with proper concurrency control, rate limiting, and error handling. It prevents API rate limits and ensures stable processing of large vaults.

## When to Use

- **Large vault migrations**: Process 100+ files
- **Bulk operations**: Translate, generate, or extract from multiple files
- **Rate limit prevention**: Avoid overwhelming LLM APIs
- **Progress tracking**: Monitor batch progress

## Key Functions (from utils.ts)

### createConcurrentProcessor

Creates a concurrent processor with staggered task execution.

```typescript
export function createConcurrentProcessor<T, R>(
  concurrency: number,
  apiCallIntervalMs: number,
  progressReporter: ProgressReporter,
): (tasks: (() => Promise<T>)[]) => Promise<R[]>;

// Features:
// - Staggered worker start (prevents burst)
// - Progress reporting
// - Cancellation support
// - Result ordering
```

### chunkArray

Splits an array into chunks of specified size.

```typescript
export function chunkArray<T>(arr: T[], size: number): T[][];

// Example:
chunkArray([1, 2, 3, 4, 5, 6, 7, 8], 3);
// Returns: [[1,2,3], [4,5,6], [7,8]]
```

### retry

Retry with exponential backoff.

```typescript
export async function retry<T>(
  fn: () => Promise<T>,
  maxRetries?: number,
  delayMs?: number,
  signal?: AbortSignal,
): Promise<T>;

// Features:
// - Exponential backoff (delay * 2^i)
// - Abort signal support
// - Error propagation
```

## Batch Processing Flow

```
batchOperation
├── Get list of files
├── Create concurrent processor
├── Create task functions
│   └── For each file
│       └── Process file
├── Execute with staggered start
├── Handle errors per file
└── Collect results
```

## Settings

### Concurrency Settings

| Setting                  | Description                     | Default |
| ------------------------ | ------------------------------- | ------- |
| `enableBatchParallelism` | Enable parallel processing      | false   |
| `batchConcurrency`       | Number of concurrent operations | 1       |
| `batchSize`              | Files per batch                 | 10      |
| `batchInterDelayMs`      | Delay between batches           | 1000    |
| `apiCallIntervalMs`      | Delay between API calls         | 0       |

### API Stability

| Setting               | Description                 |
| --------------------- | --------------------------- |
| `enableStableApiCall` | Enable stable API calls     |
| `apiCallInterval`     | Interval between calls (ms) |
| `apiCallMaxRetries`   | Max retry attempts          |

## Concurrency Strategy

### Staggered Start

Instead of starting all workers at once, workers are started with delays:

```
Worker 0: starts at 0ms
Worker 1: starts at interval * 1ms
Worker 2: starts at interval * 2ms
...
Worker N: starts at interval * Nms
```

This prevents API rate limits by distributing requests over time.

### Inter-batch Delays

For very large batches, delays between batches prevent overwhelming APIs:

```
Batch 1: [====] → delay → Batch 2: [====] → delay → Batch 3: [====]
```

## Error Handling Strategy

### Per-File Errors

Each file is processed independently. Errors don't stop the entire batch:

```typescript
try {
  await processFile(file);
  results.push({ file, success: true });
} catch (error) {
  results.push({ file, success: false, error });
}
```

### Retry Logic

For transient errors (network, rate limits), use exponential backoff:

```
Attempt 1: wait 1000ms
Attempt 2: wait 2000ms
Attempt 3: wait 4000ms
```

### 🛑 Fatal Errors & HTTP 429 (Independent Operation)

When running as an independent AI agent, you must rigorously guard against LLM API failures:

1. **HTTP 429 (Rate Limit Exceeded)**: Immeadiately pause the batch processor. Do not rely on naive retries if the bucket is exhausted. Implement a generic `AbortSignal` to gracefully halt the queue.
2. **Gateway Timeouts/502**: API providers often return HTML instead of JSON during outages. Wrap all `JSON.parse` or provider SDK calls in resilient `try/catch` blocks that log the raw text to `error_processing_filename.log` before aborting.

### Persistent Error Logging (saveErrorLog)

> [!IMPORTANT] Essential Debugging Output
> The `notemd-batch` processor utilizes `saveErrorLog` (from `fileUtils.ts`) to write detailed stack traces to `error_processing_filename.log` in the Vault root. When acting as an AI Agent, if a user reports a batch failure, you MUST proactively read this log file to secure the stack trace rather than asking the user for screenshots.

### Progress Reporting

```typescript
progressReporter.log(`Processing file ${i}/${total}: ${file.name}`);
progressReporter.updateStatus(`Processing...`, Math.floor((i / total) * 100));
progressReporter.updateActiveTasks(1); // Increment active tasks
```

## Usage Example

```typescript
import { createConcurrentProcessor, chunkArray, delay } from "./utils";

// Settings
const concurrency = 5;
const apiCallIntervalMs = 1000;
const batchSize = 10;

// Get files
const files = app.vault.getMarkdownFiles();

// Create processor
const processor = createConcurrentProcessor(
  concurrency,
  apiCallIntervalMs,
  progressReporter,
);

// Create tasks
const tasks = files.map((file) => async () => {
  await processFile(file, settings, progressReporter);
  return { file: file.name, success: true };
});

// Process in batches
const fileBatches = chunkArray(tasks, batchSize);
for (const batch of fileBatches) {
  const results = await processor(batch);

  // Handle batch results
  const errors = results.filter((r) => !r.success);
  if (errors.length > 0) {
    console.log(`Batch had ${errors.length} errors`);
  }

  // Delay between batches
  await delay(1000);
}
```

## Best Practices

1. **Start with low concurrency**: Test with 1-3 concurrent operations
2. **Monitor rate limits**: Adjust delays based on API responses
3. **Use meaningful progress messages**: Help users understand status
4. **Collect errors**: Don't fail fast; collect all errors for review
5. **Implement cancellation**: Allow users to stop long-running batches
6. **Log every N files**: Don't log every file; log every 10-50

## Common Issues

### Rate Limit (429)

- **Symptom**: API returns 429 error
- **Solution**: Increase `apiCallIntervalMs`, reduce `batchConcurrency`

### Timeout

- **Symptom**: Request times out
- **Solution**: Increase timeout settings, check network

### Memory Issues & OOM Avoidance

- **Symptom**: Heap Out of Memory (OOM) with large vaults or large files.
- **Root Cause**: `splitContent` attempts to chunk by word count, which fails completely if the Markdown file contains massive Base64 encoded images `(![[data:image/png;base64,...]])`. This causes massive strings to be cloned in memory during parallel processing.
- **Solution (Mandatory Pre-processing)**:
  1. **Base64 Sanitization**: Before passing any file to the chunker, strip or replace Base64 strings with a placeholder.
  2. Reduce `batchSize` heavily (e.g., to 2).
  3. Reduce `batchConcurrency` to 1 for extremely large vaults.

### 🧠 Token-Safe Chunking Guidelines

When building an independent implementation of `splitContent`, the AI **MUST NOT** blindly slice strings at the Nth character or word.

1. **Never Split Code Fences**: Do not split inside ` ``` ... ``` ` blocks.
2. **Never Split LaTeX**: Do not split inside `$$ ... $$` math blocks.
3. **Never Split Frontmatter**: Do not split inside the YAML `---` header.
4. **Safe Boundaries**: Always attempt to split at Markdown headers (`##`, `###`) or at least at double newlines `\n\n`.
