/**
 * MCP Server Template for MCP Apps
 *
 * This template provides a production-ready MCP server with:
 * - App resource registration
 * - Tool definitions with proper annotations
 * - HTTP transport for remote connections
 * - Error handling and logging
 */

import { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import { z } from "zod";

// =============================================================================
// Configuration
// =============================================================================

const SERVER_NAME = "mcp-app-server";
const SERVER_VERSION = "1.0.0";
const APP_BASE_URL = process.env.APP_URL || "http://localhost:3000";

// =============================================================================
// Schema Definitions
// =============================================================================

const FetchDataInputSchema = z.object({
  query: z.string().min(1).max(500).describe("Search query"),
  limit: z.number().int().min(1).max(100).default(10).describe("Maximum results"),
  offset: z.number().int().min(0).default(0).describe("Pagination offset"),
}).strict();

const CreateItemInputSchema = z.object({
  name: z.string().min(1).max(200).describe("Item name"),
  description: z.string().max(1000).optional().describe("Item description"),
  tags: z.array(z.string()).max(10).default([]).describe("Item tags"),
}).strict();

const UpdateItemInputSchema = z.object({
  id: z.string().uuid().describe("Item ID"),
  name: z.string().min(1).max(200).optional().describe("New name"),
  description: z.string().max(1000).optional().describe("New description"),
}).strict();

// =============================================================================
// Type Definitions
// =============================================================================

type FetchDataInput = z.infer<typeof FetchDataInputSchema>;
type CreateItemInput = z.infer<typeof CreateItemInputSchema>;
type UpdateItemInput = z.infer<typeof UpdateItemInputSchema>;

interface DataItem {
  id: string;
  name: string;
  description?: string;
  tags: string[];
  createdAt: string;
  updatedAt: string;
}

interface PaginatedResponse<T> {
  data: T[];
  pagination: {
    total: number;
    limit: number;
    offset: number;
    hasMore: boolean;
  };
}

// =============================================================================
// Server Implementation
// =============================================================================

async function main() {
  const server = new McpServer({
    name: SERVER_NAME,
    version: SERVER_VERSION,
  });

  // ---------------------------------------------------------------------------
  // Register App Resource
  // ---------------------------------------------------------------------------

  server.resource(
    "app",
    "mcp://app/ui",
    async () => ({
      contents: [{
        uri: `${APP_BASE_URL}/`,
        mimeType: "text/html",
        text: "MCP App UI",
      }],
    })
  );

  // ---------------------------------------------------------------------------
  // Tool: Fetch Data
  // ---------------------------------------------------------------------------

  server.tool(
    "fetch_data",
    "Fetch and search data items with pagination support",
    FetchDataInputSchema.shape,
    async (params: FetchDataInput) => {
      try {
        // Simulate data fetching (replace with actual implementation)
        const allItems: DataItem[] = await fetchItemsFromDatabase(params.query);

        const paginatedItems = allItems.slice(
          params.offset,
          params.offset + params.limit
        );

        const response: PaginatedResponse<DataItem> = {
          data: paginatedItems,
          pagination: {
            total: allItems.length,
            limit: params.limit,
            offset: params.offset,
            hasMore: params.offset + params.limit < allItems.length,
          },
        };

        return {
          content: [
            {
              type: "text" as const,
              text: JSON.stringify(response, null, 2),
            },
          ],
          _meta: {
            ui: {
              resourceUri: "mcp://app/ui",
              state: { query: params.query, results: response },
            },
          },
        };
      } catch (error) {
        const message = error instanceof Error ? error.message : "Unknown error";
        return {
          content: [
            {
              type: "text" as const,
              text: `Error fetching data: ${message}`,
            },
          ],
          isError: true,
        };
      }
    }
  );

  // ---------------------------------------------------------------------------
  // Tool: Create Item
  // ---------------------------------------------------------------------------

  server.tool(
    "create_item",
    "Create a new data item",
    CreateItemInputSchema.shape,
    async (params: CreateItemInput) => {
      try {
        const newItem: DataItem = {
          id: crypto.randomUUID(),
          name: params.name,
          description: params.description,
          tags: params.tags,
          createdAt: new Date().toISOString(),
          updatedAt: new Date().toISOString(),
        };

        // Save to database (replace with actual implementation)
        await saveItemToDatabase(newItem);

        return {
          content: [
            {
              type: "text" as const,
              text: JSON.stringify(newItem, null, 2),
            },
          ],
          _meta: {
            ui: {
              resourceUri: "mcp://app/ui",
              state: { action: "created", item: newItem },
            },
          },
        };
      } catch (error) {
        const message = error instanceof Error ? error.message : "Unknown error";
        return {
          content: [
            {
              type: "text" as const,
              text: `Error creating item: ${message}`,
            },
          ],
          isError: true,
        };
      }
    }
  );

  // ---------------------------------------------------------------------------
  // Tool: Update Item
  // ---------------------------------------------------------------------------

  server.tool(
    "update_item",
    "Update an existing data item",
    UpdateItemInputSchema.shape,
    async (params: UpdateItemInput) => {
      try {
        const existingItem = await getItemFromDatabase(params.id);
        if (!existingItem) {
          return {
            content: [
              {
                type: "text" as const,
                text: `Item not found: ${params.id}`,
              },
            ],
            isError: true,
          };
        }

        const updatedItem: DataItem = {
          ...existingItem,
          name: params.name ?? existingItem.name,
          description: params.description ?? existingItem.description,
          updatedAt: new Date().toISOString(),
        };

        await updateItemInDatabase(updatedItem);

        return {
          content: [
            {
              type: "text" as const,
              text: JSON.stringify(updatedItem, null, 2),
            },
          ],
        };
      } catch (error) {
        const message = error instanceof Error ? error.message : "Unknown error";
        return {
          content: [
            {
              type: "text" as const,
              text: `Error updating item: ${message}`,
            },
          ],
          isError: true,
        };
      }
    }
  );

  // ---------------------------------------------------------------------------
  // Start Server
  // ---------------------------------------------------------------------------

  const transport = new StdioServerTransport();
  await server.connect(transport);

  console.error(`[${SERVER_NAME}] Server started`);
}

// =============================================================================
// Database Stubs (Replace with actual implementation)
// =============================================================================

async function fetchItemsFromDatabase(query: string): Promise<DataItem[]> {
  // TODO: Implement actual database query
  return [];
}

async function saveItemToDatabase(item: DataItem): Promise<void> {
  // TODO: Implement actual database save
}

async function getItemFromDatabase(id: string): Promise<DataItem | null> {
  // TODO: Implement actual database fetch
  return null;
}

async function updateItemInDatabase(item: DataItem): Promise<void> {
  // TODO: Implement actual database update
}

// =============================================================================
// Entry Point
// =============================================================================

main().catch((error) => {
  console.error("Fatal error:", error);
  process.exit(1);
});
