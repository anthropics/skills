---
name: endpoints
description: Interact with the Endpoints API to manage document endpoints, scan files, and retrieve extracted data. Use when users want to list endpoints, inspect endpoint contents, scan documents, create/delete endpoints, download files, or check usage stats. Requires ENDPOINTS_API_URL and ENDPOINTS_API_KEY environment variables.
---

# Endpoints API Skill

Interact with the Endpoints document management API. This skill enables listing, inspecting, creating, and managing document endpoints with AI-extracted metadata.

## Prerequisites

Ensure these environment variables are set:
- `ENDPOINTS_API_URL` - Base URL (e.g., `https://endpoints.work`)
- `ENDPOINTS_API_KEY` - API key with `ep_` prefix (generate from dashboard)

## Quick Reference

### List All Endpoints (Overview)
```bash
curl -s -H "Authorization: Bearer $ENDPOINTS_API_KEY" \
  "$ENDPOINTS_API_URL/api/endpoints/tree" | jq
```

### Inspect Endpoint
```bash
curl -s -H "Authorization: Bearer $ENDPOINTS_API_KEY" \
  "$ENDPOINTS_API_URL/api/endpoints/category/slug" | jq
```

### Scan Text Content
```bash
curl -s -X POST -H "Authorization: Bearer $ENDPOINTS_API_KEY" \
  -F "texts=Your text content here" \
  -F "prompt=job tracker" \
  "$ENDPOINTS_API_URL/api/scan" | jq
```

### Scan File
```bash
curl -s -X POST -H "Authorization: Bearer $ENDPOINTS_API_KEY" \
  -F "files=@/path/to/file.pdf" \
  -F "prompt=invoice tracker" \
  "$ENDPOINTS_API_URL/api/scan" | jq
```

### Create Empty Endpoint
```bash
curl -s -X POST -H "Authorization: Bearer $ENDPOINTS_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"path": "/category/slug", "items": []}' \
  "$ENDPOINTS_API_URL/api/endpoints" | jq
```

### Delete Endpoint
```bash
curl -s -X DELETE -H "Authorization: Bearer $ENDPOINTS_API_KEY" \
  "$ENDPOINTS_API_URL/api/endpoints/category/slug" | jq
```

### Delete Individual Item
```bash
curl -s -X DELETE -H "Authorization: Bearer $ENDPOINTS_API_KEY" \
  "$ENDPOINTS_API_URL/api/items/abc12345" | jq
```

### Get File URL
```bash
curl -s -H "Authorization: Bearer $ENDPOINTS_API_KEY" \
  "$ENDPOINTS_API_URL/api/files/userid/category/slug/filename.pdf?format=json" | jq
```

### Check Usage Stats
```bash
curl -s -H "Authorization: Bearer $ENDPOINTS_API_KEY" \
  "$ENDPOINTS_API_URL/api/billing/stats" | jq
```

## Helper Script

Use `scripts/endpoints.sh` for simplified commands:

```bash
# List all endpoints
scripts/endpoints.sh overview

# Inspect specific endpoint
scripts/endpoints.sh inspect /job-tracker/january

# Scan text
scripts/endpoints.sh scan-text "Meeting with John about Q1 goals" "meeting tracker"

# Scan file
scripts/endpoints.sh scan-file /path/to/document.pdf "invoice tracker"

# Delete endpoint
scripts/endpoints.sh delete /category/slug

# Delete individual item
scripts/endpoints.sh delete-item abc12345

# Check stats
scripts/endpoints.sh stats
```

Run `scripts/endpoints.sh --help` for full usage details.

## Workflow Guidance

### When to Use Each Command

1. **overview** - Start here to see all endpoints organized by category
2. **inspect** - View specific endpoint data and all extracted metadata items
3. **scan** - Add new documents or text; AI extracts structured data
4. **create** - Programmatically create endpoint with pre-structured data
5. **delete** - Remove endpoint and all associated files
6. **delete-item** - Remove a single item from an endpoint by its ID

### Response Structure

Endpoints use the Living JSON pattern:
- `metadata.oldMetadata` - Historical items (rotated from previous scans)
- `metadata.newMetadata` - Recent items (from latest scan)
- Items are keyed by unique 8-character IDs (e.g., `abc12345`)

### Error Handling

| Status | Meaning |
|--------|---------|
| 401 | Invalid or missing API key |
| 404 | Endpoint or item not found |
| 409 | Endpoint already exists (use scan to add items) |
| 429 | Rate/usage limit exceeded |

## See Also

- [API Reference](references/api-reference.md) - Complete endpoint documentation
