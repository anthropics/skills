# AI Integration in Full-Stack Apps (2025-2026)

## Vercel AI SDK v4 — The Standard

The Vercel AI SDK is the go-to library for integrating AI into TypeScript/React apps. Provider-agnostic — works with Anthropic, OpenAI, Google, Mistral, and 30+ providers via adapters.

### Core Packages
```bash
npm install ai @ai-sdk/anthropic @ai-sdk/openai @ai-sdk/react
```

### Architecture: `streamText` + `useChat`

```ts
// app/api/chat/route.ts (Next.js App Router):
import { streamText } from 'ai';
import { anthropic } from '@ai-sdk/anthropic';

export async function POST(req: Request) {
  const { messages } = await req.json();

  const result = streamText({
    model: anthropic('claude-sonnet-4-5'),
    system: 'You are a helpful assistant.',
    messages,
    maxTokens: 2048,
  });

  return result.toDataStreamResponse();
}
```

```tsx
// components/Chat.tsx:
'use client';
import { useChat } from '@ai-sdk/react';

export function Chat() {
  const { messages, input, handleInputChange, handleSubmit, isLoading, error } = useChat({
    api: '/api/chat',
    onError: (err) => console.error(err),
  });

  return (
    <div>
      <div className="messages">
        {messages.map((m) => (
          <div key={m.id} className={m.role === 'user' ? 'user' : 'assistant'}>
            {m.parts.map((part, i) => {
              if (part.type === 'text') return <p key={i}>{part.text}</p>;
              if (part.type === 'tool-invocation') return <ToolCall key={i} tool={part} />;
            })}
          </div>
        ))}
        {isLoading && <div className="typing-indicator">...</div>}
      </div>
      <form onSubmit={handleSubmit}>
        <input value={input} onChange={handleInputChange} placeholder="Ask anything..." />
        <button type="submit" disabled={isLoading}>Send</button>
      </form>
    </div>
  );
}
```

### AI SDK 4.2 — Message Parts
The `messages` array now contains typed `parts` (v4.2+), preserving the exact sequence of text, tool calls, and tool results:
```ts
type MessagePart =
  | { type: 'text'; text: string }
  | { type: 'tool-invocation'; toolInvocation: ToolInvocation }
  | { type: 'tool-result'; toolResult: ToolResult }
  | { type: 'image'; image: URL | Uint8Array }
```

---

## Tool Calling (Function Calling)

Tools let the AI call functions in your app — search a database, call an API, perform calculations.

```ts
// app/api/chat/route.ts:
import { streamText, tool } from 'ai';
import { z } from 'zod';
import { anthropic } from '@ai-sdk/anthropic';

export async function POST(req: Request) {
  const { messages } = await req.json();

  const result = streamText({
    model: anthropic('claude-sonnet-4-5'),
    messages,
    tools: {
      searchPosts: tool({
        description: 'Search blog posts by keyword',
        parameters: z.object({
          query: z.string().describe('Search query'),
          limit: z.number().min(1).max(20).default(5),
        }),
        execute: async ({ query, limit }) => {
          const posts = await db.select().from(postsTable)
            .where(sql`to_tsvector('english', title || ' ' || content) @@ plainto_tsquery(${query})`)
            .limit(limit);
          return posts;
        },
      }),
      createPost: tool({
        description: 'Create a new blog post',
        parameters: z.object({
          title: z.string(),
          content: z.string(),
        }),
        execute: async ({ title, content }) => {
          const [post] = await db.insert(postsTable).values({ title, content }).returning();
          return post;
        },
      }),
    },
    maxSteps: 5, // allow up to 5 tool-call rounds
  });

  return result.toDataStreamResponse();
}
```

### Multi-Step Tool Calling
`maxSteps` controls how many tool-call rounds the model can perform. The model calls a tool → gets result → can call another tool → final response.

### Tool Calling Gotcha
The client sends `Message[]`, but `streamText` expects `CoreMessage[]`. Don't manually convert — use the `messages` from `useChat` directly (the SDK handles conversion internally via `toDataStreamResponse`).

---

## Structured Output (generateObject / streamObject)

For when you need JSON output with type safety:

```ts
import { generateObject } from 'ai';
import { z } from 'zod';

const { object } = await generateObject({
  model: anthropic('claude-sonnet-4-5'),
  schema: z.object({
    sentiment: z.enum(['positive', 'negative', 'neutral']),
    score: z.number().min(0).max(1),
    summary: z.string(),
    topics: z.array(z.string()),
  }),
  prompt: `Analyze the sentiment of this review: "${reviewText}"`,
});

// object is fully typed as { sentiment, score, summary, topics }
```

```ts
// streamObject — for large structured outputs (stream as it generates):
import { streamObject } from 'ai';

const { partialObjectStream } = streamObject({
  model: anthropic('claude-sonnet-4-5'),
  schema: blogPostSchema,
  prompt: 'Write a blog post about React 19',
});

for await (const partial of partialObjectStream) {
  // partial is incrementally typed — use to update UI progressively
  updateUI(partial);
}
```

---

## File Upload to AI APIs

### Client → Storage → AI (Recommended for Large Files)
```tsx
// Step 1: Upload to storage directly from client:
async function uploadFile(file: File): Promise<string> {
  const { url, fields } = await fetch('/api/upload-url').then(r => r.json());
  const formData = new FormData();
  Object.entries(fields).forEach(([k, v]) => formData.append(k, v as string));
  formData.append('file', file);
  await fetch(url, { method: 'POST', body: formData });
  return `${url}/${fields.key}`;
}

// Step 2: Pass file URL to AI:
const result = streamText({
  model: anthropic('claude-opus-4-5'),
  messages: [{
    role: 'user',
    content: [
      { type: 'text', text: 'What does this document say?' },
      { type: 'file', data: fileUrl, mimeType: 'application/pdf' },
    ],
  }],
});
```

### `useChat` experimental_attachments
```tsx
const { handleSubmit } = useChat();

<form onSubmit={(e) => handleSubmit(e, {
  experimental_attachments: fileList,  // FileList from <input type="file">
})}>
```
Files are converted to data URLs on the client. Vercel Functions have a 4.5MB limit — for larger files, use presigned URLs to upload to S3/Vercel Blob first.

---

## AI-Powered Features Patterns

### Semantic Search (pgvector + embeddings)
```ts
import { embed } from 'ai';
import { openai } from '@ai-sdk/openai';

// Generate embedding for search query:
const { embedding } = await embed({
  model: openai.embedding('text-embedding-3-small'),
  value: userQuery,
});

// Vector search in PostgreSQL:
const results = await db.execute(sql`
  SELECT id, title, content,
    1 - (embedding <=> ${JSON.stringify(embedding)}::vector) AS similarity
  FROM documents
  WHERE 1 - (embedding <=> ${JSON.stringify(embedding)}::vector) > 0.7
  ORDER BY embedding <=> ${JSON.stringify(embedding)}::vector
  LIMIT 10
`);
```

### RAG (Retrieval-Augmented Generation)
```ts
async function ragQuery(userQuestion: string): Promise<string> {
  // 1. Embed question:
  const { embedding } = await embed({ model: openai.embedding('text-embedding-3-small'), value: userQuestion });

  // 2. Retrieve relevant docs:
  const docs = await vectorSearch(embedding, 5);

  // 3. Generate with context:
  const { text } = await generateText({
    model: anthropic('claude-haiku-4-5'),
    messages: [{
      role: 'user',
      content: `Context:\n${docs.map(d => d.content).join('\n\n')}\n\nQuestion: ${userQuestion}`,
    }],
  });
  return text;
}
```

### AI SDK with Vercel's experimental_output (4.1+)
Generate structured data AND call tools in the same invocation:
```ts
const result = await generateText({
  model: anthropic('claude-sonnet-4-5'),
  tools: { ... },
  experimental_output: Output.object({ schema: resultSchema }),
  prompt: '...',
});
const structuredData = result.experimental_output; // typed result
```

---

## On-Device AI (React Native)

Callstack's `@callstack/react-native-ai` runs LLMs on-device (via llama.cpp) with Vercel AI SDK compatibility:
```ts
import { createLocalLlm } from '@callstack/react-native-ai';

const model = createLocalLlm({
  model: 'llama-3.2-3b', // downloaded to device
});

const result = streamText({ model, messages });
```

Use cases: offline-first apps, privacy-sensitive apps, edge inference. Requires downloading model weights (~1-4GB). Works on iOS/Android with Metal/NNAPI acceleration.

---

## Provider Selection Guide

| Provider | Model | Best For |
|---|---|---|
| Anthropic | claude-sonnet-4-5 | Reasoning, code, long context |
| Anthropic | claude-haiku-4-5 | Fast, cheap, tool calling |
| OpenAI | gpt-4o | Multimodal, vision, general |
| OpenAI | gpt-4o-mini | Cost-efficient general use |
| OpenAI | text-embedding-3-small | Embeddings (2D to 3072D) |
| Google | gemini-1.5-pro | 1M context window |
| Mistral | mistral-large | European data residency |

All providers accessed through AI SDK adapters with identical API surface.
