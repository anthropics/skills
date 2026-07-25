# OpenAPI Extraction Guide

## Goal

Turn stable API operations into stable MCP tools with clear names and reliable schemas.

## Extraction Rules

1. Prefer `operationId` as tool name.
2. Fallback naming: `<method>_<path>` sanitized to snake_case.
3. Pull `summary` for tool description; fallback to `description`.
4. Merge path/query parameters into `inputSchema.properties`.
5. Merge `application/json` request-body object properties when available.
6. Preserve required fields from both parameters and request body.

## Naming Guidance

Good names:

- `list_customers`
- `create_invoice`
- `archive_project`

Avoid:

- `tool1`
- `run`
- `get__v1__customer___id`

## Schema Guidance

- `inputSchema.type` must be `object`.
- Every `required` key must exist in `properties`.
- Include concise descriptions on high-risk fields (IDs, dates, money, destructive flags).
