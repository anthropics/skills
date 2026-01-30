# MCP Apps Architecture Reference

## Overview

MCP Apps extend the Model Context Protocol to support interactive UI components embedded in host applications (Claude Desktop, web clients). The architecture follows a client-server model with iframe-based isolation.

---

## Core Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                           MCP Host Application                          │
│  (Claude Desktop, Web Client, IDE Extension)                            │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌─────────────────────┐         ┌─────────────────────────────────┐   │
│  │   Host UI Layer     │         │       MCP Client                │   │
│  │                     │         │                                 │   │
│  │  ┌───────────────┐  │         │  - Tool Discovery              │   │
│  │  │   App iframe  │◀─┼─────────┼──- Resource Management         │   │
│  │  │               │  │         │  - Message Routing             │   │
│  │  │  React/Next   │  │         │  - Style Synchronization       │   │
│  │  │  Application  │  │         │                                 │   │
│  │  └───────────────┘  │         └─────────────┬───────────────────┘   │
│  │                     │                       │                        │
│  └─────────────────────┘                       │                        │
│                                                │                        │
└────────────────────────────────────────────────┼────────────────────────┘
                                                 │
                                                 │ MCP Protocol
                                                 │ (stdio/HTTP)
                                                 ▼
                                   ┌─────────────────────────────┐
                                   │       MCP Server            │
                                   │                             │
                                   │  ┌───────────────────────┐  │
                                   │  │   App Resource        │  │
                                   │  │   Registration        │  │
                                   │  └───────────────────────┘  │
                                   │                             │
                                   │  ┌───────────────────────┐  │
                                   │  │   Tools               │  │
                                   │  │   - Data fetching     │  │
                                   │  │   - Actions           │  │
                                   │  │   - Mutations         │  │
                                   │  └───────────────────────┘  │
                                   │                             │
                                   └─────────────────────────────┘
```

---

## Key Components

### 1. App Resource Registration

The server registers a UI resource that the host can render:

```typescript
import { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";

interface AppResourceOptions {
  uri: string;           // MCP URI format: mcp://{server-name}/app
  name: string;          // Human-readable name
  description: string;   // Purpose description
  mimeType: string;      // Always "text/html"
}

server.registerAppResource({
  uri: "mcp://myserver/app",
  name: "Data Visualization",
  description: "Interactive charts and data exploration",
  mimeType: "text/html",
});
```

### 2. Tool Response with UI Reference

Tools can include `_meta.ui.resourceUri` to indicate a UI should be rendered:

```typescript
interface ToolResponse {
  content: ContentBlock[];
  _meta?: {
    ui?: {
      resourceUri: string;  // Points to registered app resource
      state?: unknown;      // Optional state to pass to UI
    };
  };
}

// Example tool implementation
server.registerTool("analyze_data", {
  title: "Analyze Data",
  description: "Analyze data and show interactive visualization",
  inputSchema: z.object({
    datasetId: z.string(),
  }),
}, async ({ datasetId }) => {
  const analysis = await performAnalysis(datasetId);

  return {
    content: [{ type: "text", text: JSON.stringify(analysis) }],
    _meta: {
      ui: {
        resourceUri: "mcp://myserver/app",
        state: { datasetId, analysis },
      },
    },
  };
});
```

### 3. Client-Side Communication

The `@modelcontextprotocol/ext-apps/react` package provides hooks for communication:

```typescript
// Available from useApp() hook
interface AppContext {
  // Call a tool on the MCP server
  callServerTool: <T>(name: string, args: Record<string, unknown>) => Promise<T>;

  // Send message to host application
  sendMessage: (message: HostMessage) => void;

  // Initial state passed from tool response
  initialState: unknown;

  // Connection status
  isConnected: boolean;

  // Error state
  error: Error | null;
}
```

---

## Communication Protocol

### Message Types

```typescript
// Host → App messages
interface HostToAppMessage {
  type: "init" | "state_update" | "style_sync" | "tool_response";
  payload: unknown;
}

// App → Host messages
interface AppToHostMessage {
  type: "tool_call" | "ready" | "error" | "resize";
  payload: unknown;
}

// Tool call request
interface ToolCallRequest {
  id: string;           // Unique request ID
  name: string;         // Tool name
  arguments: unknown;   // Tool arguments
}

// Tool call response
interface ToolCallResponse {
  id: string;           // Matches request ID
  result?: unknown;     // Success result
  error?: {
    code: string;
    message: string;
  };
}
```

### Style Synchronization

The host provides styling information for consistency:

```typescript
interface HostStyles {
  isDarkMode: boolean;
  fontFamily: string;
  fontSize: string;
  primaryColor: string;
  backgroundColor: string;
  textColor: string;
  borderRadius: string;
  // Additional CSS custom properties
  customProperties: Record<string, string>;
}
```

---

## Security Model

### Iframe Sandbox

Apps run in sandboxed iframes with restricted capabilities:

```html
<iframe
  src="app-url"
  sandbox="allow-scripts allow-same-origin"
  referrerpolicy="no-referrer"
  loading="lazy"
></iframe>
```

### Content Security Policy

Recommended CSP for MCP Apps:

```
Content-Security-Policy:
  default-src 'self';
  script-src 'self' 'unsafe-inline';
  style-src 'self' 'unsafe-inline';
  connect-src 'self' ws: wss:;
  img-src 'self' data: blob:;
  frame-ancestors 'self';
```

### Origin Validation

Always validate message origins:

```typescript
window.addEventListener("message", (event) => {
  // Validate origin matches expected host
  if (!ALLOWED_ORIGINS.includes(event.origin)) {
    console.warn("Message from unauthorized origin:", event.origin);
    return;
  }

  handleHostMessage(event.data);
});
```

---

## Best Practices

### 1. State Management

- Keep UI state minimal; fetch data on demand
- Use `initialState` for critical bootstrap data only
- Implement optimistic updates for responsiveness

### 2. Error Handling

- Graceful degradation when server unavailable
- Clear error messages with recovery suggestions
- Retry logic with exponential backoff

### 3. Performance

- Lazy load heavy components
- Debounce frequent tool calls
- Use virtual scrolling for large datasets

### 4. Accessibility

- Keyboard navigation support
- Screen reader compatibility
- Sufficient color contrast (WCAG 2.1 AA)

---

## Related Documentation

- [MCP Protocol Specification](https://modelcontextprotocol.io/specification)
- [Next.js Documentation](https://nextjs.org/docs)
- [shadcn/ui Components](https://ui.shadcn.com)
