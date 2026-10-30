# McpServerBase Pattern Reference

The `McpServerBase` abstract class wraps the MCP TypeScript SDK so you only write tool logic — transport, routing, error handling, and graceful shutdown are handled for you.

---

## Full implementation

```typescript
// src/McpServerBase.ts
import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import {
  CallToolRequestSchema,
  ErrorCode,
  ListToolsRequestSchema,
  McpError,
} from '@modelcontextprotocol/sdk/types.js';

// ─── Types ─────────────────────────────────────────────────────────────────

export interface ServerConfig {
  name: string;
  version: string;
}

export interface ToolResult {
  content: Array<{ type: 'text'; text: string }>;
  isError?: boolean;
}

export interface ToolDefinition {
  name: string;
  description: string;
  inputSchema: {
    type: 'object';
    properties: Record<string, {
      type: string;
      description?: string;
      enum?: string[];
      items?: { type: string };
    }>;
    required?: string[];
  };
}

type ToolHandler = (args: unknown) => Promise<ToolResult>;

// ─── ToolRegistry ──────────────────────────────────────────────────────────

class ToolRegistry {
  private tools: Map<string, { definition: ToolDefinition; handler: ToolHandler }> = new Map();

  register(name: string, description: string, inputSchema: ToolDefinition['inputSchema'], handler: ToolHandler): void {
    if (this.tools.has(name)) throw new Error(`Tool already registered: ${name}`);
    this.tools.set(name, { definition: { name, description, inputSchema }, handler });
  }

  getHandler(name: string): ToolHandler | undefined {
    return this.tools.get(name)?.handler;
  }

  getAllDefinitions(): ToolDefinition[] {
    return Array.from(this.tools.values()).map(t => t.definition);
  }
}

// ─── McpServerBase ─────────────────────────────────────────────────────────

export abstract class McpServerBase {
  protected server: Server;
  protected registry: ToolRegistry;
  protected config: ServerConfig;

  constructor(config: ServerConfig) {
    this.config = config;
    this.registry = new ToolRegistry();
    this.server = new Server(
      { name: config.name, version: config.version },
      { capabilities: { tools: {} } }
    );
    this.setupHandlers();
    this.setupErrorHandlers();
    this.registerTools(); // calls the subclass override
  }

  // Override this in your subclass. Call this.addTool() for each tool.
  protected abstract registerTools(): void;

  protected addTool(
    name: string,
    description: string,
    inputSchema: ToolDefinition['inputSchema'],
    handler: ToolHandler
  ): void {
    this.registry.register(name, description, inputSchema, handler);
  }

  // Wrap a plain data object in a success ToolResult.
  // Handlers MUST call this — never construct {content:[...]} manually.
  protected success<T extends Record<string, unknown>>(data: T): ToolResult {
    return {
      content: [{ type: 'text', text: JSON.stringify({ success: true, ...data }, null, 2) }],
    };
  }

  // Wrap an error in an error ToolResult.
  protected error(error: unknown): ToolResult {
    const message = error instanceof Error ? error.message : String(error);
    return {
      content: [{ type: 'text', text: JSON.stringify({ success: false, error: message }, null, 2) }],
      isError: true,
    };
  }

  private setupHandlers(): void {
    this.server.setRequestHandler(ListToolsRequestSchema, async () => ({
      tools: this.registry.getAllDefinitions(),
    }));

    this.server.setRequestHandler(CallToolRequestSchema, async (request) => {
      const { name, arguments: args } = request.params;
      const handler = this.registry.getHandler(name);
      if (!handler) {
        throw new McpError(ErrorCode.MethodNotFound, `Unknown tool: ${name}`);
      }
      try {
        return await handler(args);
      } catch (err) {
        if (err instanceof McpError) throw err;
        const message = err instanceof Error ? err.message : String(err);
        throw new McpError(ErrorCode.InternalError, `Tool execution failed: ${message}`);
      }
    });
  }

  private setupErrorHandlers(): void {
    this.server.onerror = (error) => {
      console.error(`[${this.config.name}] MCP Error:`, error);
    };
    process.on('SIGINT', async () => {
      await this.shutdown();
    });
  }

  async run(): Promise<void> {
    const transport = new StdioServerTransport();
    await this.server.connect(transport);
    console.error(`${this.config.name} MCP server v${this.config.version} running on stdio`);
  }

  async shutdown(): Promise<void> {
    await this.server.close();
    process.exit(0);
  }
}
```

---

## Minimal subclass — a file-reader tool

```typescript
#!/usr/bin/env node
// src/index.ts
import { McpServerBase } from './McpServerBase.js';
import { readFileSync, existsSync } from 'fs';

class FileReaderServer extends McpServerBase {
  constructor() {
    // Must call super() — sets up Server, registry, and calls registerTools().
    super({ name: 'file-reader', version: '1.0.0' });
  }

  protected registerTools(): void {
    this.addTool(
      'read_file',
      'Read the text content of a file at the given absolute path.',
      {
        type: 'object',
        properties: {
          path: { type: 'string', description: 'Absolute path to the file.' },
          encoding: {
            type: 'string',
            enum: ['utf-8', 'base64'],
            description: 'File encoding. Default: utf-8.',
          },
        },
        required: ['path'],
      },
      async (args) => {
        const { path, encoding = 'utf-8' } = args as { path: string; encoding?: 'utf-8' | 'base64' };
        if (!existsSync(path)) return this.error(`File not found: ${path}`);
        try {
          const content = readFileSync(path, encoding);
          // Pass a plain object to this.success() — never construct {content:[...]} yourself.
          return this.success({ path, encoding, content, bytes: content.length });
        } catch (err) {
          return this.error(err);
        }
      }
    );

    this.addTool(
      'file_exists',
      'Check whether a file exists at the given absolute path.',
      {
        type: 'object',
        properties: {
          path: { type: 'string', description: 'Absolute path to check.' },
        },
        required: ['path'],
      },
      async (args) => {
        const { path } = args as { path: string };
        return this.success({ path, exists: existsSync(path) });
      }
    );
  }
}

// Always end the file with this — starts the stdio transport.
new FileReaderServer().run().catch(console.error);
```

---

## Extracting testable logic

Move pure business logic out of the handler into a `core.ts` module. Test that module directly — never test through the MCP transport.

```typescript
// src/core.ts
import { readFileSync, existsSync } from 'fs';

export interface ReadResult {
  path: string;
  content: string;
  bytes: number;
}

export function readFileSafe(path: string, encoding: 'utf-8' | 'base64' = 'utf-8'): ReadResult {
  if (!existsSync(path)) throw new Error(`File not found: ${path}`);
  const content = readFileSync(path, encoding);
  return { path, content, bytes: content.length };
}
```

```typescript
// src/core.test.ts
import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { writeFileSync, mkdtempSync, rmSync } from 'fs';
import { join } from 'path';
import { tmpdir } from 'os';
import { readFileSafe } from './core.js';

describe('readFileSafe', () => {
  let tmpDir: string;

  beforeEach(() => { tmpDir = mkdtempSync(join(tmpdir(), 'file-reader-test-')); });
  afterEach(() => { rmSync(tmpDir, { recursive: true, force: true }); });

  it('reads a utf-8 file', () => {
    const file = join(tmpDir, 'hello.txt');
    writeFileSync(file, 'hello world');
    const result = readFileSafe(file);
    expect(result.content).toBe('hello world');
    expect(result.bytes).toBe(11);
  });

  it('throws when file does not exist', () => {
    expect(() => readFileSafe('/nonexistent/path.txt')).toThrow('File not found');
  });

  it('reads in base64 encoding', () => {
    const file = join(tmpDir, 'data.bin');
    writeFileSync(file, 'abc');
    const result = readFileSafe(file, 'base64');
    expect(result.content).toBe(Buffer.from('abc').toString('base64'));
  });
});
```

---

## Smoke-testing the MCP server

```sh
# Build
npm run build

# List registered tools
echo '{"jsonrpc":"2.0","id":1,"method":"tools/list","params":{}}' \
  | node build/index.js

# Call a tool
echo '{"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"read_file","arguments":{"path":"/etc/hostname"}}}' \
  | node build/index.js
```

Expected `tools/list` output:
```json
{
  "result": {
    "tools": [
      { "name": "read_file", "description": "...", "inputSchema": { ... } },
      { "name": "file_exists", "description": "...", "inputSchema": { ... } }
    ]
  }
}
```

Expected `tools/call` output:
```json
{
  "result": {
    "content": [{
      "type": "text",
      "text": "{\"success\":true,\"path\":\"/etc/hostname\",\"encoding\":\"utf-8\",\"content\":\"myhost\\n\",\"bytes\":7}"
    }]
  }
}
```

---

## Response shape

`this.success()` always produces:
```json
{ "content": [{ "type": "text", "text": "{\"success\":true, ...yourData}" }] }
```

`this.error()` always produces:
```json
{ "content": [{ "type": "text", "text": "{\"success\":false, \"error\":\"message\"}" }], "isError": true }
```

LLM agents can branch on the `success` flag without parsing stack traces.
