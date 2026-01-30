---
name: mcp-app-next-ui
description: |
  Build MCP Apps with Next.js, React, Tailwind CSS, and shadcn/ui. Covers `_meta.ui.resourceUri`,
  `registerAppResource`, and `@modelcontextprotocol/ext-apps/react` for creating interactive
  UI components that communicate with MCP servers via iframe embedding.
license: Complete terms in LICENSE.txt
---

# MCP App UI Development with Next.js

## When to Use

Use this skill when:

- Building MCP Apps that render interactive UI inside Claude or other MCP hosts
- Creating React components that use `useApp`, `useHostStyles`, or `App` from `@modelcontextprotocol/ext-apps/react`
- Implementing UI resources via `registerAppResource` and `_meta.ui.resourceUri`
- Designing frontend interfaces with Next.js, Tailwind CSS, and shadcn/ui for MCP integrations
- Calling server-side MCP tools from the UI using `app.callServerTool`

---

## Concepts

### MCP Apps Overview

MCP Apps extend the Model Context Protocol to support interactive UI components. The host application (e.g., Claude Desktop) embeds the app UI in an iframe and facilitates bidirectional communication between the UI and the MCP server.

### Key Components

| Component | Purpose |
|-----------|---------|
| `App` | React component that wraps your app and handles MCP communication |
| `useApp` | Hook providing access to `callServerTool`, `sendMessage`, and app state |
| `useHostStyles` | Hook to synchronize host styling (dark mode, fonts, etc.) |
| `registerAppResource` | Server-side function to register a UI resource |
| `_meta.ui.resourceUri` | Metadata field pointing to the UI resource URI |

### Communication Flow

```
┌─────────────────┐       ┌─────────────────┐       ┌─────────────────┐
│   MCP Host      │◀─────▶│   iframe (UI)   │◀─────▶│   MCP Server    │
│  (Claude, etc.) │       │  React/Next.js  │       │  (Tools/Data)   │
└─────────────────┘       └─────────────────┘       └─────────────────┘
```

---

## Project Structure

A typical MCP App project separates server logic from UI code:

```
my-mcp-app/
├── package.json
├── tsconfig.json
├── next.config.js
├── tailwind.config.ts
├── components.json              # shadcn/ui configuration
├── server/
│   ├── index.ts                 # MCP server entry point
│   ├── tools/
│   │   └── myTool.ts            # Tool implementations
│   └── resources/
│       └── appResource.ts       # UI resource registration
├── app/                         # Next.js App Router
│   ├── layout.tsx
│   ├── page.tsx                 # Main UI entry point
│   └── globals.css
├── components/
│   ├── ui/                      # shadcn/ui components
│   └── McpAppWrapper.tsx        # App wrapper component
└── lib/
    └── mcp-client.ts            # Client-side MCP utilities
```

---

## Code Examples

### Wrapping Your App with MCP Provider

```tsx
// components/McpAppWrapper.tsx
"use client";

import { App } from "@modelcontextprotocol/ext-apps/react";
import { ReactNode } from "react";

interface McpAppWrapperProps {
  children: ReactNode;
}

export function McpAppWrapper({ children }: McpAppWrapperProps) {
  return (
    <App
      onReady={() => console.log("MCP App ready")}
      onError={(error) => console.error("MCP App error:", error)}
    >
      {children}
    </App>
  );
}
```

### Using the useApp Hook

```tsx
// components/DataFetcher.tsx
"use client";

import { useApp } from "@modelcontextprotocol/ext-apps/react";
import { Button } from "@/components/ui/button";
import { Card, CardContent, CardHeader, CardTitle } from "@/components/ui/card";
import { useState } from "react";

interface FetchResult {
  data: unknown;
  timestamp: string;
}

export function DataFetcher() {
  const app = useApp();
  const [result, setResult] = useState<FetchResult | null>(null);
  const [loading, setLoading] = useState(false);

  const handleFetch = async () => {
    setLoading(true);
    try {
      const response = await app.callServerTool("fetch-data", {
        query: "example",
        limit: 10,
      });
      setResult({
        data: response,
        timestamp: new Date().toISOString(),
      });
    } catch (error) {
      console.error("Failed to fetch data:", error);
    } finally {
      setLoading(false);
    }
  };

  return (
    <Card className="w-full max-w-md">
      <CardHeader>
        <CardTitle>Data Fetcher</CardTitle>
      </CardHeader>
      <CardContent className="space-y-4">
        <Button onClick={handleFetch} disabled={loading}>
          {loading ? "Fetching..." : "Fetch Data"}
        </Button>
        {result && (
          <pre className="bg-muted p-4 rounded-md text-sm overflow-auto">
            {JSON.stringify(result, null, 2)}
          </pre>
        )}
      </CardContent>
    </Card>
  );
}
```

### Applying Host Styles

```tsx
// components/ThemedContainer.tsx
"use client";

import { useHostStyles } from "@modelcontextprotocol/ext-apps/react";
import { cn } from "@/lib/utils";

export function ThemedContainer({ children }: { children: React.ReactNode }) {
  const hostStyles = useHostStyles();

  return (
    <div
      className={cn(
        "min-h-screen p-4 transition-colors",
        hostStyles.isDarkMode ? "dark" : ""
      )}
      style={{
        fontFamily: hostStyles.fontFamily,
        fontSize: hostStyles.fontSize,
      }}
    >
      {children}
    </div>
  );
}
```

### Registering an App Resource (Server-Side)

```typescript
// server/resources/appResource.ts
import { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";

export function registerAppResource(server: McpServer, baseUrl: string) {
  server.registerAppResource({
    uri: `${baseUrl}/app`,
    name: "My MCP App",
    description: "Interactive UI for data visualization",
    mimeType: "text/html",
  });
}
```

### Tool Response with UI Resource Reference

```typescript
// server/tools/myTool.ts
export async function myToolHandler(params: MyToolParams) {
  const result = await processData(params);

  return {
    content: [
      {
        type: "text",
        text: JSON.stringify(result),
      },
    ],
    _meta: {
      ui: {
        resourceUri: "mcp://myserver/app",
      },
    },
  };
}
```

---

## Additional Resources

The following subdirectories contain supplementary materials:

- **`scripts/`** — Helper scripts for development, building, and deployment
- **`templates/`** — Starter templates for components, pages, and configurations
- **`reference/`** — API references, schema definitions, and protocol documentation

Use these resources as starting points and adapt them to your specific requirements.
