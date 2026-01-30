#!/bin/bash
# MCP App Project Setup Script
# Creates a new Next.js project configured for MCP App development

set -e

PROJECT_NAME="${1:-mcp-app}"
echo "Creating MCP App project: $PROJECT_NAME"

# Create Next.js project with TypeScript and Tailwind
npx create-next-app@latest "$PROJECT_NAME" \
  --typescript \
  --tailwind \
  --eslint \
  --app \
  --src-dir \
  --import-alias "@/*" \
  --use-npm

cd "$PROJECT_NAME"

# Install MCP dependencies
npm install @modelcontextprotocol/sdk @modelcontextprotocol/ext-apps

# Install shadcn/ui dependencies
npm install class-variance-authority clsx tailwind-merge lucide-react
npm install -D @types/node

# Initialize shadcn/ui
npx shadcn@latest init -y

# Add essential components
npx shadcn@latest add button card input label toast dialog

# Create MCP-specific directories
mkdir -p src/components/mcp
mkdir -p src/hooks
mkdir -p src/lib/mcp
mkdir -p server/tools
mkdir -p server/resources

# Create MCP wrapper component
cat > src/components/mcp/McpProvider.tsx << 'EOF'
"use client";

import { App } from "@modelcontextprotocol/ext-apps/react";
import { ReactNode, useCallback } from "react";

interface McpProviderProps {
  children: ReactNode;
}

export function McpProvider({ children }: McpProviderProps) {
  const handleReady = useCallback(() => {
    console.log("[MCP] App connected and ready");
  }, []);

  const handleError = useCallback((error: Error) => {
    console.error("[MCP] Connection error:", error);
  }, []);

  return (
    <App onReady={handleReady} onError={handleError}>
      {children}
    </App>
  );
}
EOF

# Create useServerTool hook
cat > src/hooks/useServerTool.ts << 'EOF'
"use client";

import { useApp } from "@modelcontextprotocol/ext-apps/react";
import { useState, useCallback } from "react";

interface UseServerToolOptions<T> {
  onSuccess?: (data: T) => void;
  onError?: (error: Error) => void;
}

export function useServerTool<TInput, TOutput>(
  toolName: string,
  options: UseServerToolOptions<TOutput> = {}
) {
  const app = useApp();
  const [data, setData] = useState<TOutput | null>(null);
  const [error, setError] = useState<Error | null>(null);
  const [loading, setLoading] = useState(false);

  const execute = useCallback(
    async (input: TInput): Promise<TOutput | null> => {
      setLoading(true);
      setError(null);

      try {
        const result = await app.callServerTool(toolName, input as Record<string, unknown>);
        setData(result as TOutput);
        options.onSuccess?.(result as TOutput);
        return result as TOutput;
      } catch (err) {
        const error = err instanceof Error ? err : new Error(String(err));
        setError(error);
        options.onError?.(error);
        return null;
      } finally {
        setLoading(false);
      }
    },
    [app, toolName, options]
  );

  const reset = useCallback(() => {
    setData(null);
    setError(null);
  }, []);

  return { execute, data, error, loading, reset };
}
EOF

echo ""
echo "✅ MCP App project created successfully!"
echo ""
echo "Next steps:"
echo "  cd $PROJECT_NAME"
echo "  npm run dev"
echo ""
echo "Project structure:"
echo "  src/components/mcp/  - MCP-specific components"
echo "  src/hooks/           - Custom React hooks"
echo "  src/lib/mcp/         - MCP utilities"
echo "  server/              - MCP server code"
EOF
