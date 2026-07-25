# TypeScript MCP Server Template

```ts
import { FastMCP } from "fastmcp";

const server = new FastMCP({ name: "my-server" });

server.tool(
  "list_items",
  "List items from upstream service",
  async (input) => {
    return {
      content: [{ type: "text", text: JSON.stringify({ status: "todo", input }) }],
    };
  }
);

server.run();
```
