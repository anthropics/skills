# Endpoints API Reference

Complete API documentation for the Endpoints document management platform.

## Base URL

```
Production: https://endpoints.work/api
Development: http://localhost:3000/api
```

## Authentication

All endpoints require Bearer token authentication:

```
Authorization: Bearer ep_your_api_key_here
```

Generate API keys from the dashboard at `/api-keys`.

## Core Endpoints

### GET /api/endpoints/tree

List all endpoints organized by category.

**Response:**
```json
{
  "categories": [
    {
      "name": "job-tracker",
      "endpoints": [
        { "id": 1, "path": "/job-tracker/january", "slug": "january" },
        { "id": 2, "path": "/job-tracker/february", "slug": "february" }
      ]
    }
  ]
}
```

### GET /api/endpoints/{category}/{slug}

Get endpoint details with all metadata items.

**Response:**
```json
{
  "endpoint": {
    "id": 1,
    "path": "/job-tracker/january",
    "category": "job-tracker",
    "slug": "january"
  },
  "metadata": {
    "oldMetadata": {
      "abc12345": { "summary": "...", "entities": [...] }
    },
    "newMetadata": {
      "def67890": { "summary": "...", "entities": [...] }
    }
  },
  "totalItems": 2
}
```

### POST /api/endpoints

Create a new endpoint.

**Request:**
```json
{
  "path": "/category/slug",
  "items": []
}
```

**Response:**
```json
{
  "success": true,
  "endpoint": { "id": 1, "path": "/category/slug", ... }
}
```

### DELETE /api/endpoints/{category}/{slug}

Delete an endpoint and all associated files.

**Response:**
```json
{
  "success": true,
  "message": "Endpoint deleted"
}
```

## Scanning

### POST /api/scan

Scan files or text with AI extraction.

**Request:** `multipart/form-data`

| Field | Type | Description |
|-------|------|-------------|
| `files` | File[] | Files to scan (PDF, images, docs) |
| `texts` | String[] | Text content to scan |
| `prompt` | String | Category hint (e.g., "job tracker") |

**Response:**
```json
{
  "endpoint": {
    "path": "/job-tracker/january-2026",
    "category": "job-tracker",
    "slug": "january-2026"
  },
  "entriesAdded": 3,
  "metadata": {
    "newMetadata": {
      "abc12345": {
        "summary": "Software Engineer position at Acme Corp",
        "entities": [
          { "name": "Acme Corp", "type": "company" },
          { "name": "Software Engineer", "type": "role" }
        ],
        "filePath": "https://...",
        "fileType": "application/pdf"
      }
    }
  }
}
```

## Items

### DELETE /api/items/{itemId}

Delete a single item from an endpoint by its 8-character ID.

**Response:**
```json
{
  "success": true,
  "message": "Item deleted"
}
```

## Files

### GET /api/files/{key}

Get a presigned URL for a file.

**Query Parameters:**
- `format=json` - Return JSON with URL (default returns redirect)
- `expiresIn=3600` - URL expiration in seconds (default: 3600)

**Response:**
```json
{
  "url": "https://s3.amazonaws.com/...",
  "expiresIn": 3600
}
```

## Billing

### GET /api/billing/stats

Get usage statistics for current billing period.

**Response:**
```json
{
  "tier": "pro_managed",
  "parsesUsed": 45,
  "parsesLimit": 300,
  "storageUsed": 1073741824,
  "storageLimit": 107374182400,
  "billingPeriodStart": "2026-01-01T00:00:00Z",
  "billingPeriodEnd": "2026-02-01T00:00:00Z"
}
```

## Error Responses

| Status | Response |
|--------|----------|
| 401 | `{ "error": "Unauthorized" }` |
| 404 | `{ "error": "Endpoint not found" }` |
| 409 | `{ "error": "Endpoint already exists" }` |
| 429 | `{ "error": "Monthly parse limit exceeded" }` |
| 500 | `{ "error": "Internal server error" }` |

## Living JSON Structure

Endpoints use the Living JSON pattern for tracking document history:

```
metadata: {
  oldMetadata: { ... }  // Historical items (rotated from previous scans)
  newMetadata: { ... }  // Recent items (from latest scan)
}
```

Each item has:
- **8-character ID** - Unique identifier (e.g., `abc12345`)
- **summary** - AI-generated description
- **entities** - Extracted entities (people, companies, dates, etc.)
- **filePath** - S3 URL if file was uploaded
- **fileType** - MIME type
- **originalText** - Source text (if text scan)

## Subscription Tiers

### BYOK Tiers (Bring Your Own Key)
| Tier | Parses | Storage | Price |
|------|--------|---------|-------|
| Starter BYOK | Unlimited | 25GB | $5/mo |
| Pro BYOK | Unlimited | 100GB | $9/mo |
| Business BYOK | Unlimited | 500GB | $35/mo |

### Managed Tiers
| Tier | Parses | Storage | Price |
|------|--------|---------|-------|
| Free | 25/mo | 10GB | $0 |
| Starter | 100/mo | 25GB | $19/mo |
| Pro | 300/mo | 100GB | $69/mo |
| Business | 1000/mo | 500GB | $249/mo |
