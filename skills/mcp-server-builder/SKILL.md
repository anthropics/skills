---
name: mcp-server-builder
description: Scaffold a production-ready MCP server in TypeScript using the McpServerBase pattern. Invoke when the user asks to create, add, or build a new MCP tool or server. Generates package.json, tsconfig.json, src/index.ts with a typed McpServerBase subclass, and src/index.test.ts with Vitest tests — all wired to stdio transport.
license: Complete terms in LICENSE.txt
---

# MCP Server Builder

A scaffolding skill. When invoked, generate all boilerplate files for a working MCP server using the `McpServerBase` pattern — a minimal abstract class that handles transport, routing, and error formatting so you only write tool logic.

> **Complements `mcp-builder`** — that skill teaches the 4-phase strategy for designing MCP servers. This skill generates the code once you know what to build.

---

## When to invoke

Invoke this skill when the user says any of:
- "create a new MCP tool / server"
- "add an MCP server for X"
- "scaffold an MCP server"
- "build an MCP tool that does X"

---

## Step 1 — Gather requirements

Ask the user (all four are required before writing any code):

1. **Tool name** — the kebab-case name for the server package (e.g., `my-tool`). This becomes the npm package name and the MCP server name.
2. **Tool description** — one sentence describing what the server does for an LLM agent.
3. **Input schema** — what parameters each tool handler accepts (field names, types, required/optional).
4. **Output shape** — what the tool returns on success (field names and types).

If the user is exploratory ("build me an MCP tool for reading files"), propose sensible defaults and confirm before generating.

---

## Step 2 — File generation order

Generate files in this sequence so each one can reference the previous:

```
<tool-name>/
├── package.json          ← 1. dependencies + build scripts
├── tsconfig.json         ← 2. TypeScript config (extends shared base)
└── src/
    ├── index.ts          ← 3. McpServerBase subclass with tool handlers
    └── index.test.ts     ← 4. Vitest unit tests (no MCP transport needed)
```

---

## Step 3 — Generate each file

### 3.1 `package.json`

```json
{
  "name": "@your-scope/<tool-name>",
  "version": "1.0.0",
  "description": "<one-line description>",
  "type": "module",
  "main": "build/index.js",
  "scripts": {
    "build": "tsc",
    "dev": "tsc --watch",
    "test": "vitest run"
  },
  "dependencies": {
    "@modelcontextprotocol/sdk": "^1.12.0"
  },
  "devDependencies": {
    "typescript": "^5.0.0",
    "vitest": "^3.0.0"
  }
}
```

> If the project uses a shared `McpServerBase` package, add it to `dependencies` and import from it instead of re-implementing the class.

---

### 3.2 `tsconfig.json`

```json
{
  "extends": "../../tsconfig.base.json",
  "compilerOptions": {
    "outDir": "./build",
    "rootDir": "./src"
  },
  "include": ["src"]
}
```

If there is no shared `tsconfig.base.json`, use this standalone config:

```json
{
  "compilerOptions": {
    "target": "ES2022",
    "module": "NodeNext",
    "moduleResolution": "NodeNext",
    "strict": true,
    "noUncheckedIndexedAccess": true,
    "outDir": "./build",
    "rootDir": "./src",
    "declaration": true,
    "skipLibCheck": true
  },
  "include": ["src"],
  "exclude": ["node_modules", "build"]
}
```

---

### 3.3 `src/index.ts` — the McpServerBase subclass

See [McpServerBase pattern reference](./reference/McpServerBase-pattern.md) for the full annotated implementation.

**Key rules:**
1. Extend `McpServerBase` — never instantiate `Server` directly.
2. Call `super({ name: '<tool-name>', version: '1.0.0' })` in the constructor.
3. Implement `protected registerTools(): void` — this is the only abstract method.
4. Inside `registerTools`, call `this.addTool(name, description, inputSchema, handler)` once per tool.
5. Handlers must return `this.success({ ...data })` or `this.error(err)` — never return a raw `{content:[...]}` object.
6. End the file with `new MyToolServer().run().catch(console.error);`.
7. All local imports must use `.js` extension (ESM): `import { helper } from './helper.js'`.

**Template:**

```typescript
import { McpServerBase } from '@your-scope/shared';

class MyToolServer extends McpServerBase {
  constructor() {
    super({ name: 'my-tool', version: '1.0.0' });
  }

  protected registerTools(): void {
    this.addTool(
      'do_thing',
      'Does the thing and returns a result.',
      {
        type: 'object',
        properties: {
          path: { type: 'string', description: 'Absolute path to the target file' },
          mode: { type: 'string', enum: ['fast', 'thorough'], description: 'Processing mode' },
        },
        required: ['path'],
      },
      async (args) => {
        const { path, mode = 'fast' } = args as { path: string; mode?: string };
        try {
          const result = await processFile(path, mode);
          return this.success({ path, mode, result });
        } catch (err) {
          return this.error(err);
        }
      }
    );
  }
}

new MyToolServer().run().catch(console.error);
```

---

### 3.4 `src/index.test.ts` — Vitest tests

**Key rule:** Test pure helper functions directly — do not test through the MCP transport. Extract logic to a separate module (e.g., `src/core.ts`) and test that module.

```typescript
import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { writeFileSync, mkdtempSync, rmSync } from 'fs';
import { join } from 'path';
import { tmpdir } from 'os';
import { processFile } from './core.js';

describe('processFile', () => {
  let tmpDir: string;

  beforeEach(() => {
    tmpDir = mkdtempSync(join(tmpdir(), 'my-tool-test-'));
  });

  afterEach(() => {
    rmSync(tmpDir, { recursive: true, force: true });
  });

  it('processes a file in fast mode', async () => {
    const file = join(tmpDir, 'sample.ts');
    writeFileSync(file, 'const x: any = 1;');
    const result = await processFile(file, 'fast');
    expect(result.violations).toHaveLength(1);
  });

  it('returns empty violations for clean file', async () => {
    const file = join(tmpDir, 'clean.ts');
    writeFileSync(file, 'const x: number = 1;');
    const result = await processFile(file, 'fast');
    expect(result.violations).toHaveLength(0);
  });

  it('uses thorough mode when specified', async () => {
    const file = join(tmpDir, 'sample.ts');
    writeFileSync(file, 'const x: any = 1;');
    const resultFast = await processFile(file, 'fast');
    const resultThorough = await processFile(file, 'thorough');
    expect(resultThorough.violations.length).toBeGreaterThanOrEqual(resultFast.violations.length);
  });
});
```

Aim for 3–5 tests per exported function: happy path, empty/no-op case, and one edge case.

---

## Step 4 — Build and test

After generating the files, instruct the user to run:

```sh
npm install
npm run build      # must compile with zero errors
npm test           # all tests must pass
```

**Smoke-test via JSON-RPC** (confirm stdio transport works):

```sh
echo '{"jsonrpc":"2.0","id":1,"method":"tools/list","params":{}}' \
  | node build/index.js
```

Expected output: a JSON object with a `tools` array containing your registered tool names.

---

## Step 5 — Common pitfalls

### Double-wrap bug
**Wrong:** Handler returns `{content:[{type:'text',text:JSON.stringify(data)}]}` and is passed to `this.success()`.  
**Right:** Handler returns `this.success({ ...plainData })`. The `success()` method wraps it — don't wrap it yourself.

```typescript
// WRONG — double-wrapped, breaks MCP clients
async (args) => this.success({ content: [{ type: 'text', text: JSON.stringify(result) }] })

// RIGHT — success() does the wrapping
async (args) => this.success({ items: result.items, count: result.items.length })
```

### Missing super() call
The `McpServerBase` constructor wires up handlers and registers tools. Without `super()`, none of that happens.

```typescript
// WRONG
constructor() { /* nothing */ }

// RIGHT
constructor() {
  super({ name: 'my-tool', version: '1.0.0' });
}
```

### ESM import extensions
With `"module": "NodeNext"`, TypeScript requires explicit `.js` extensions on local imports (the runtime resolves `.ts` → `.js` at build time).

```typescript
// WRONG — will fail at runtime
import { helper } from './helper'

// RIGHT
import { helper } from './helper.js'
```

### Exposing shell execution via tool handlers
Never call `execSync` / `spawnSync` in a tool handler with user-controlled arguments — this creates a command injection vector. If you need to run a subprocess, validate the exact executable path and arguments against an allowlist first.

### Testing through MCP transport
Unit tests that spin up the full MCP server are slow and fragile. Extract logic to pure functions in `src/core.ts` (or similar) and test those directly. The test file should never import `McpServerBase`.

---

## Reference

- [McpServerBase pattern](./reference/McpServerBase-pattern.md) — full annotated implementation with inline comments
- [MCP TypeScript SDK](https://github.com/modelcontextprotocol/typescript-sdk) — upstream SDK reference
- [MCP protocol spec](https://modelcontextprotocol.io/specification) — JSON-RPC message format
