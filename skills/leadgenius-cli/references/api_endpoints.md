# API Endpoints Reference

Complete request/response schemas for every LeadGenius Pro Automation API endpoint.

**Base URL:** `https://api.leadgenius.app`
**Authentication:** `X-API-Key: lgp_xxx` header on every request.
**Admin Bypass:** Optional `X-Admin-Key` header to bypass rate limits (see [Admin Key](#admin-key---rate-limit-bypass) below).

---

## Authentication

Every request requires the `X-API-Key` header with a valid AgentApiKey (`lgp_` prefix). This key authenticates the caller and resolves the owner, company, and permissions context.

### Admin Key — Rate Limit Bypass

An optional `X-Admin-Key` header can be sent alongside `X-API-Key` to bypass all rate limits. Both keys are required together — the admin key does not replace the API key.

| Header | Purpose | Required |
|--------|---------|----------|
| `X-API-Key` | AgentApiKey — authenticates caller, resolves owner/company | Always |
| `X-Admin-Key` | Admin secret — bypasses rate limits when valid | Optional |

When the admin key is valid, the response includes `X-RateLimit-Bypass: admin` instead of the normal rate limit headers.

**curl example:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  -H "X-Admin-Key: $LGP_ADMIN_KEY" \
  https://api.leadgenius.app/api/automation/leads?client_id=YOUR_CLIENT | jq
```

**CLI equivalent:**

```bash
LGP_ADMIN_KEY=your_admin_key python lgp.py leads list --client YOUR_CLIENT
```

**Response headers (with admin key):**

```
X-RateLimit-Bypass: admin
```

**Response headers (without admin key — normal rate limiting):**

```
X-RateLimit-Limit: 60
X-RateLimit-Remaining: 59
X-RateLimit-Reset: 1711000000
```

---

### `GET /api/automation/auth/test`

Verify that your API key is valid and see the associated identity (owner, company, key ID).

**Query Parameters:** None.

**Response:**

```json
{
  "success": true,
  "data": {
    "authenticated": true,
    "owner": "f4a844a8-00c1-7087-b434-f6d681e1f269",
    "companyId": "company-api-test2-030526",
    "apiKeyId": "apikey-api-test2-1772645628",
    "message": "API key is valid"
  },
  "requestId": "req-abc123"
}
```

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  https://api.leadgenius.app/api/automation/auth/test | jq
```

**CLI equivalent:**

```bash
python lgp.py auth test
```

---

## Leads

### `GET /api/automation/leads`

List EnrichLeads by `client_id`, sorted by `createdAt` descending. Supports field selection and pagination.

**Query Parameters:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `client_id` | string | Yes | — | Client to list leads for. Use `__orphaned__` to find leads with missing client_id. |
| `fields` | string | No | default set | Comma-separated field names to return |
| `limit` | integer | No | 50 | Max records per page (capped at 50). Use `nextToken` to paginate. |
| `nextToken` | string | No | — | Pagination token from previous response |

**Default fields returned:** `id`, `firstName`, `lastName`, `fullName`, `email`, `linkedinUrl`, `companyName`, `title`, `status`, `client_id`, `company_id`, `createdAt`, `updatedAt`.

**Custom field selection:** Pass `fields=email,companyName,aiLeadScore` to return only those fields (`id` is always included).

**Response:**

```json
{
  "success": true,
  "data": {
    "items": [
      {
        "id": "lead-001",
        "firstName": "Jane",
        "lastName": "Doe",
        "email": "jane@example.com",
        "companyName": "Acme Corp",
        "title": "VP Sales",
        "status": "active",
        "client_id": "client-123",
        "createdAt": "2026-03-01T10:00:00.000Z"
      }
    ],
    "count": 1,
    "nextToken": null
  }
}
```

**Pagination:** When `nextToken` is present in the response, pass it as a query parameter to fetch the next page. When `nextToken` is `null`, there are no more pages.

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/leads?client_id=YOUR_CLIENT_ID&limit=10" | jq
```

```bash
# With field selection
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/leads?client_id=YOUR_CLIENT_ID&fields=email,companyName,aiLeadScore" | jq
```

**CLI equivalent:**

```bash
python lgp.py leads list --client YOUR_CLIENT_ID --limit 10
```

---

### `GET /api/automation/leads/{id}`

Return a single EnrichLead with all fields (100+ fields including enrichment, AI, scoring, engagement data).

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | EnrichLead record ID |

**Response:**

```json
{
  "success": true,
  "data": {
    "id": "lead-001",
    "firstName": "Jane",
    "lastName": "Doe",
    "fullName": "Jane Doe",
    "email": "jane@example.com",
    "linkedinUrl": "https://linkedin.com/in/janedoe",
    "companyName": "Acme Corp",
    "title": "VP Sales",
    "aiLeadScore": "85",
    "aiQualification": "Highly Qualified",
    "engagementScore": 42,
    "client_id": "client-123",
    "company_id": "company-456",
    "owner": "owner-sub-789",
    "status": "active",
    "createdAt": "2026-03-01T10:00:00.000Z",
    "updatedAt": "2026-03-15T14:30:00.000Z"
  }
}
```

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/leads/LEAD_ID" | jq
```

**CLI equivalent:**

```bash
python lgp.py leads get LEAD_ID
```

---

### `POST /api/automation/leads/import`

Import one or more EnrichLeads. Supports single lead or batch (up to 500).

**Request Body — Single lead:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `client_id` | string | Yes | — | Client to import into (must belong to your company) |
| `firstName` | string | No | — | First name |
| `lastName` | string | No | — | Last name |
| `email` | string | No | — | Email address |
| `companyName` | string | No | — | Company name |
| `title` | string | No | — | Job title |
| `linkedinUrl` | string | No | — | LinkedIn profile URL |

Any additional EnrichLead fields can be included. Unknown fields are silently stripped. `owner` and `company_id` are auto-set from your API key.

**Request Body — Batch:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `leads` | array | Yes | — | Array of lead objects (max 500). Each object uses the same fields as single-lead import. |

**Key behaviors:**
- Cross-client duplicate detection by `email` / `linkedinUrl` (warning only, not blocking)
- Max batch size: 500 leads

**Response:**

```json
{
  "success": true,
  "data": {
    "created": 2,
    "failed": 0,
    "createdIds": ["id-1", "id-2"],
    "errors": [],
    "warnings": []
  },
  "message": "Imported 2 of 2 leads"
}
```

**curl:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"client_id":"YOUR_CLIENT","firstName":"Jane","lastName":"Doe","email":"jane@example.com","companyName":"Acme"}' \
  https://api.leadgenius.app/api/automation/leads/import | jq
```

**CLI equivalent:**

```bash
# Import from JSON file
python lgp.py leads import --file leads.json

# Import inline
python lgp.py leads import --data '{"client_id":"YOUR_CLIENT","firstName":"Jane","email":"jane@example.com"}'
```

---

### `GET /api/automation/leads/search`

Search leads by email, name, companyUrl, or linkedinUrl. Uses GSI indexes for efficient lookups.

**Query Parameters (at least one search field required):**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `email` | string | No | — | Exact email match (uses `email-index` GSI) |
| `firstName` | string | No | — | Exact first name match (uses `firstName-lastName-index` GSI) |
| `lastName` | string | No | — | Used with `firstName` (uses `firstName-lastName-index` GSI) |
| `companyUrl` | string | No | — | Exact company URL match (uses `company_id` GSI + filter) |
| `linkedinUrl` | string | No | — | Exact LinkedIn URL match (uses `company_id` GSI + filter) |
| `client_id` | string | No | — | Narrow results to a specific client |
| `limit` | integer | No | 50 | Max records (capped at 500) |
| `nextToken` | string | No | — | Pagination token |

**Response:**

```json
{
  "success": true,
  "data": {
    "items": [
      {
        "id": "lead-001",
        "firstName": "Jane",
        "lastName": "Doe",
        "email": "jane@example.com",
        "companyName": "Acme Corp"
      }
    ],
    "count": 1,
    "nextToken": null
  }
}
```

**Pagination:** Same as List Leads — pass `nextToken` from the response to get the next page.

**curl:**

```bash
# Search by email
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/leads/search?email=jane@example.com" | jq

# Search by name
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/leads/search?firstName=Jane&lastName=Doe" | jq
```

**CLI equivalent:**

```bash
python lgp.py leads search --email jane@example.com
python lgp.py leads search --first-name Jane --last-name Doe
```

---

### `POST /api/automation/leads/deduplicate`

Scan leads for a client and find duplicate groups by match fields.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `client_id` | string | Yes | — | Client to scan for duplicates |
| `matchFields` | array | Yes | — | Fields to match on (see valid values below) |
| `dryRun` | boolean | No | `true` | When `true`, report duplicates without making changes |

**Valid match fields:**

| Match Field | Confidence | Description |
|-------------|------------|-------------|
| `email` | high | Exact email match (case-insensitive) |
| `linkedinUrl` | medium | Exact LinkedIn URL match |
| `fullName+companyName` | low | Combined name + company match |

**Response:**

```json
{
  "success": true,
  "data": {
    "matches": [
      {
        "matchField": "email",
        "confidence": "high",
        "matchValue": "jane@example.com",
        "leadIds": ["id-1", "id-2"]
      }
    ],
    "totalLeadsScanned": 150,
    "totalDuplicateGroups": 3,
    "dryRun": true
  }
}
```

**curl:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"client_id":"YOUR_CLIENT","matchFields":["email"],"dryRun":true}' \
  https://api.leadgenius.app/api/automation/leads/deduplicate | jq
```

**CLI equivalent:**

```bash
python lgp.py leads dedup --client YOUR_CLIENT --match email,linkedinUrl
```

---

### `POST /api/automation/leads/deduplicate/resolve`

Merge data from duplicate leads into a "keep" lead. Empty fields on the keep lead are filled from merge leads. Merge leads are marked with `status: 'duplicate'`.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `keepLeadId` | string | Yes | — | Lead ID to keep (receives merged data) |
| `mergeLeadIds` | array | Yes | — | Array of lead IDs to merge from (marked as duplicate) |

**Key behaviors:**
- Only empty fields on the keep lead are filled from merge leads
- System fields (`id`, `owner`, `company_id`, `client_id`, `createdAt`, `updatedAt`) are never merged
- First merge lead's value wins if multiple merge leads have a value for the same empty field
- All merge leads get `status: 'duplicate'`
- Conflicts (both leads have a value) are reported but the keep lead's value wins

**Response:**

```json
{
  "success": true,
  "data": {
    "keepLeadId": "lead-to-keep",
    "mergedFields": ["phoneNumber", "industry", "headline"],
    "conflicts": [
      {
        "field": "title",
        "keepValue": "VP Sales",
        "mergeValue": "Director of Sales",
        "mergeLeadId": "duplicate-1"
      }
    ],
    "mergeLeadsMarked": 2
  }
}
```

**curl:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"keepLeadId":"KEEP_ID","mergeLeadIds":["DUP_1","DUP_2"]}' \
  https://api.leadgenius.app/api/automation/leads/deduplicate/resolve | jq
```

**CLI equivalent:**

```bash
python lgp.py leads dedup-resolve --keep KEEP_ID --merge DUP_1,DUP_2
```

---

### `POST /api/automation/leads/transfer`

Transfer leads between clients within the same company. Includes duplicate detection against the target client.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `fromClientId` | string | Yes | — | Source client ID |
| `toClientId` | string | Yes | — | Target client ID |
| `leadIds` | array | No | — | Specific lead IDs to transfer (use this or `transferAll`) |
| `transferAll` | boolean | No | `false` | Transfer all leads from source client |
| `dryRun` | boolean | No | `false` | When `true`, simulate without making changes |

**Key behaviors:**
- Both clients must belong to your company
- Source and target must be different
- Duplicate detection by `email` and `linkedinUrl` against target client
- Duplicates are skipped (not overwritten)
- Only `client_id` is updated on transferred leads

**Response:**

```json
{
  "success": true,
  "data": {
    "transferred": 5,
    "skippedDuplicates": 1,
    "errors": [],
    "dryRun": false,
    "details": {
      "transferred": [{"leadId": "lead-1", "previousClientId": "source-client"}],
      "skippedDuplicates": [{"leadId": "lead-2", "duplicateId": "existing-lead", "matchField": "email"}]
    }
  }
}
```

**curl:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"fromClientId":"SOURCE_CLIENT","toClientId":"TARGET_CLIENT","transferAll":true,"dryRun":true}' \
  https://api.leadgenius.app/api/automation/leads/transfer | jq
```

**CLI equivalent:**

```bash
python lgp.py leads transfer --from SOURCE_CLIENT --to TARGET_CLIENT --all --dry-run
```

---

### `GET /api/automation/leads/{id}/activities`

Return the engagement history for a lead.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | EnrichLead record ID |

**Response:**

```json
{
  "success": true,
  "data": {
    "leadId": "lead-id",
    "totalActivities": 5,
    "engagementScore": 42,
    "lastEngagementAt": "2026-03-01T10:00:00.000Z",
    "activities": [
      {
        "type": "email_opened",
        "timestamp": "2026-03-01T10:00:00.000Z",
        "notes": "Opened Q1 campaign email",
        "metadata": {"campaignId": "camp-1"}
      }
    ]
  }
}
```

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/leads/LEAD_ID/activities" | jq
```

**CLI equivalent:**

```bash
python lgp.py leads activities LEAD_ID
```

---

### `POST /api/automation/leads/{id}/activities`

Log one or more engagement activities on a lead. Appends to `engagementHistory`, updates `lastEngagementAt`, and recalculates `engagementScore`.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | EnrichLead record ID |

**Request Body — Single activity:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `type` | string | Yes | — | Activity type (see valid types below) |
| `timestamp` | string | No | now | ISO 8601 date string |
| `notes` | string | No | — | Free-text notes |
| `metadata` | object | No | — | Arbitrary JSON data |

**Request Body — Batch:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `activities` | array | Yes | — | Array of activity objects (same fields as single activity) |

**Valid activity types:** `linkedin_connection_sent`, `linkedin_connection_accepted`, `linkedin_message_sent`, `linkedin_message_received`, `linkedin_profile_viewed`, `email_sent`, `email_opened`, `email_clicked`, `email_answered`, `email_bounced`, `call_completed`, `call_no_answer`, `meeting_scheduled`, `meeting_completed`, `form_submitted`, `website_visited`, `content_downloaded`, `demo_requested`, `proposal_sent`, `contract_signed`, `custom`.

**Engagement score weights:** Activities are scored with time decay. Recent activities (< 30 days) get full weight, older ones get 50%. Score is capped at 100.

| Activity | Points |
|----------|--------|
| `contract_signed`, `meeting_completed` | 30 |
| `meeting_scheduled`, `demo_requested` | 25 |
| `email_answered`, `proposal_sent`, `form_submitted` | 20 |
| `linkedin_message_received`, `call_completed` | 15 |
| `linkedin_connection_accepted`, `content_downloaded` | 10 |
| `email_clicked` | 8 |
| `email_opened` | 5 |
| `custom` | 5 |
| `linkedin_message_sent`, `email_sent`, `website_visited` | 2–3 |
| `linkedin_connection_sent`, `linkedin_profile_viewed`, `call_no_answer` | 1–2 |
| `email_bounced` | -5 |

**Response:**

```json
{
  "success": true,
  "data": {
    "leadId": "lead-id",
    "activitiesAdded": 3,
    "totalActivities": 8,
    "engagementScore": 55,
    "lastEngagementAt": "2026-03-01T10:05:00.000Z"
  },
  "message": "3 activity(ies) logged"
}
```

**curl:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"type":"email_opened","notes":"Opened Q1 email"}' \
  https://api.leadgenius.app/api/automation/leads/LEAD_ID/activities | jq
```

**CLI equivalent:**

```bash
python lgp.py leads activity LEAD_ID --type email_opened --notes "Opened Q1 email"
```

---

### `POST /api/automation/leads/validate-ownership`

Scan all EnrichLeads for your company and report ownership issues.

**Request Body:** Empty `{}` or omit body.

**Checks performed:**
- Orphaned leads: `client_id` references a non-existent Client record
- Mismatched company: Client's `company_id` doesn't match lead's `company_id`
- Null owner: Lead has empty or null `owner` field

**Response:**

```json
{
  "success": true,
  "data": {
    "status": "healthy",
    "totalLeadsScanned": 200,
    "orphanedRecords": 0,
    "mismatchedCompany": 0,
    "nullOwner": 0,
    "totalIssues": 0,
    "details": []
  }
}
```

**curl:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  https://api.leadgenius.app/api/automation/leads/validate-ownership | jq
```

**CLI equivalent:**

```bash
python lgp.py leads validate-ownership
```


## Tasks

Background processing jobs (enrichment, copyright, scoring) run asynchronously via Trigger.dev. Use these endpoints to trigger jobs and monitor their progress.

### `GET /api/automation/tasks`

List background jobs for your company with optional status and type filters.

**Query Parameters:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `status` | string | No | — | Filter by status: `running`, `completed`, `failed` |
| `type` | string | No | — | Filter by type: `enrichment`, `copyright`, `scoring` |
| `limit` | integer | No | 50 | Max records (capped at 500) |
| `nextToken` | string | No | — | Pagination token from previous response |

**Response:**

```json
{
  "success": true,
  "data": {
    "items": [
      {
        "jobId": "uuid-123",
        "userId": "user-sub-456",
        "company_id": "company-789",
        "type": "enrichment",
        "status": "running",
        "totalTasks": 3,
        "completedTasks": 1,
        "failedTasks": 0,
        "finishedAt": null,
        "createdAt": "2026-03-01T10:00:00.000Z",
        "updatedAt": "2026-03-01T10:01:00.000Z"
      }
    ],
    "count": 1,
    "nextToken": null
  }
}
```

**Pagination:** When `nextToken` is present in the response, pass it as a query parameter to fetch the next page. When `nextToken` is `null`, there are no more pages.

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/tasks?status=running" | jq
```

```bash
# Filter by type
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/tasks?status=running&type=enrichment" | jq
```

**CLI equivalent:**

```bash
python lgp.py tasks list
python lgp.py tasks list --status running --type enrichment
```

---

### `GET /api/automation/tasks/{jobId}`

Get a single job's status and progress.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `jobId` | string | Yes | The job UUID |

**Response:**

```json
{
  "success": true,
  "data": {
    "jobId": "uuid-123",
    "userId": "user-sub-456",
    "company_id": "company-789",
    "type": "enrichment",
    "status": "completed",
    "totalTasks": 3,
    "completedTasks": 3,
    "failedTasks": 0,
    "finishedAt": "2026-03-01T10:05:00.000Z",
    "createdAt": "2026-03-01T10:00:00.000Z",
    "updatedAt": "2026-03-01T10:05:00.000Z"
  }
}
```

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/tasks/JOB_ID" | jq
```

**CLI equivalent:**

```bash
python lgp.py tasks status JOB_ID
```

---

### `POST /api/automation/tasks/enrich`

Trigger enrichment services for a single lead. Uses UrlSettings configuration to determine which services are available. Jobs run asynchronously — use `GET /api/automation/tasks/{jobId}` to monitor progress.

**Prerequisites:**
- **UrlSettings** must be configured for your company with service URLs. Create/update via `POST /api/automation/tables/UrlSettings`.
- Each service needs a URL configured in UrlSettings (e.g., the `enrichment1` field).
- Optional API keys per service (e.g., `enrichment1_Apikey`).

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `leadId` | string | Yes | — | EnrichLead record ID to enrich |
| `services` | array | No | all configured | Array of service keys to trigger. If omitted, triggers all configured services. |

**Available enrichment service identifiers:**

| Service Key | Description |
|-------------|-------------|
| `companyUrl` | Discover and verify the company website URL |
| `emailFinder` | Find and verify the lead's email address |
| `enrichment1` | Custom enrichment service 1 (configured in UrlSettings) |
| `enrichment2` | Custom enrichment service 2 (configured in UrlSettings) |
| `enrichment3` | Custom enrichment service 3 (configured in UrlSettings) |
| `enrichment4` | Custom enrichment service 4 (configured in UrlSettings) |
| `enrichment5` | Custom enrichment service 5 (configured in UrlSettings) |
| `enrichment6` | Custom enrichment service 6 (configured in UrlSettings) |
| `enrichment7` | Custom enrichment service 7 (configured in UrlSettings) |
| `enrichment8` | Custom enrichment service 8 (configured in UrlSettings) |
| `enrichment9` | Custom enrichment service 9 (configured in UrlSettings) |
| `enrichment10` | Custom enrichment service 10 (configured in UrlSettings) |

**Response:**

```json
{
  "success": true,
  "data": {
    "jobId": "uuid-456",
    "batchTag": "automation-enrich-1709...",
    "triggered": ["companyUrl", "enrichment1"],
    "skipped": ["enrichment2"],
    "leadId": "enrich-lead-id",
    "runIds": ["run_xxx", "run_yyy"]
  },
  "message": "Triggered 2 enrichment services, skipped 1"
}
```

**curl:**

```bash
# Trigger all configured services
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"leadId":"LEAD_ID"}' \
  https://api.leadgenius.app/api/automation/tasks/enrich | jq
```

```bash
# Trigger specific services
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"leadId":"LEAD_ID","services":["companyUrl","emailFinder","enrichment1"]}' \
  https://api.leadgenius.app/api/automation/tasks/enrich | jq
```

**CLI equivalent:**

```bash
python lgp.py tasks enrich --lead LEAD_ID
python lgp.py tasks enrich --lead LEAD_ID --services companyUrl,emailFinder
```

---

### `POST /api/automation/tasks/copyright`

Trigger copyright (AI content generation) processes for a single lead. Uses AgentSettings configuration. Each process maps to an AI agent that generates content for the lead. Jobs run asynchronously — use `GET /api/automation/tasks/{jobId}` to monitor progress.

**Prerequisites:**
- **AgentSettings** must be configured for your company. Create/update via `POST /api/automation/tables/AgentSettings`.
- Each process needs an agent ID configured (e.g., `enrichment1AgentId` field in AgentSettings).
- A `projectId` must be set in AgentSettings for the AI platform.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `leadId` | string | Yes | — | EnrichLead record ID to process |
| `processes` | array | No | all configured | Array of process keys to trigger. If omitted, triggers all configured processes. |

**Available copyright process identifiers:**

Each process key maps to an AI agent configured in AgentSettings. The agent ID is stored in the corresponding `<key>AgentId` field (e.g., `enrichment1` → `enrichment1AgentId`).

| Process Key | AgentSettings Field | Description |
|-------------|---------------------|-------------|
| `enrichment1` | `enrichment1AgentId` | AI content generation process 1 |
| `enrichment2` | `enrichment2AgentId` | AI content generation process 2 |
| `enrichment3` | `enrichment3AgentId` | AI content generation process 3 |
| `enrichment4` | `enrichment4AgentId` | AI content generation process 4 |
| `enrichment5` | `enrichment5AgentId` | AI content generation process 5 |
| `enrichment6` | `enrichment6AgentId` | AI content generation process 6 |
| `enrichment7` | `enrichment7AgentId` | AI content generation process 7 |
| `enrichment8` | `enrichment8AgentId` | AI content generation process 8 |
| `enrichment9` | `enrichment9AgentId` | AI content generation process 9 |
| `enrichment10` | `enrichment10AgentId` | AI content generation process 10 |

**Response:**

```json
{
  "success": true,
  "data": {
    "jobId": "uuid-789",
    "batchTag": "automation-copyright-1709...",
    "triggered": ["enrichment1"],
    "skipped": ["enrichment2"],
    "leadId": "enrich-lead-id",
    "runIds": ["run_xxx"]
  },
  "message": "Triggered 1 copyright processes, skipped 1"
}
```

**curl:**

```bash
# Trigger all configured processes
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"leadId":"LEAD_ID"}' \
  https://api.leadgenius.app/api/automation/tasks/copyright | jq
```

```bash
# Trigger specific processes
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"leadId":"LEAD_ID","processes":["enrichment1","enrichment2"]}' \
  https://api.leadgenius.app/api/automation/tasks/copyright | jq
```

**CLI equivalent:**

```bash
python lgp.py tasks copyright --lead LEAD_ID
```

---

### `POST /api/automation/tasks/score`

Trigger SDR AI scoring for one or more leads. Supports single-lead and batch (up to 100 leads) variants. Uses SdrAiSettings configuration. Jobs run asynchronously — use `GET /api/automation/tasks/{jobId}` to monitor progress.

**Prerequisites:**
- **SdrAiSettings** must be configured for your company. Create/update via `POST /api/automation/tables/SdrAiSettings`.
- Each scoring field needs an agent ID configured (e.g., `aiLeadScoreAgentId` field in SdrAiSettings).
- A `projectId` must be set in SdrAiSettings for the AI platform.

**Request Body — Single lead:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `leadId` | string | One of `leadId`/`leadIds` | — | Single EnrichLead record ID |
| `fields` | array | No | all configured | Array of scoring field keys to trigger |

**Request Body — Batch (up to 100 leads):**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `leadIds` | array | One of `leadId`/`leadIds` | — | Array of EnrichLead record IDs (max 100) |
| `fields` | array | No | all configured | Array of scoring field keys to trigger |

**Available scoring field identifiers:**

| Field Key | Description |
|-----------|-------------|
| `aiLeadScore` | Numeric lead quality score (0–100) |
| `aiQualification` | Text qualification assessment (e.g., "Highly Qualified", "Not Qualified") |
| `aiNextAction` | Recommended next sales action for the lead |
| `aiColdEmail` | AI-generated cold email draft tailored to the lead |
| `aiInterest` | Assessed interest level based on lead data |
| `aiLinkedinConnect` | AI-generated LinkedIn connection request message |
| `aiCompetitorAnalysis` | Competitive landscape analysis for the lead's company |
| `aiEngagementLevel` | Predicted engagement level based on lead profile |
| `aiPurchaseWindow` | Estimated purchase timeline or buying window |
| `aiDecisionMakerRole` | Assessment of the lead's decision-making authority |
| `aiSentiment` | Sentiment analysis based on available lead data |
| `aiSocialEngagement` | Social media engagement analysis |
| `aiNurturingStage` | Recommended nurturing stage placement |
| `aiBudgetEstimation` | Estimated budget range for the lead's company |
| `aiRiskScore` | Risk assessment score for the opportunity |
| `aiProductFitScore` | Product-market fit score for the lead |

**Response:**

```json
{
  "success": true,
  "data": {
    "jobId": "uuid-012",
    "batchTag": "automation-score-1709...",
    "triggered": ["aiLeadScore", "aiQualification"],
    "skipped": ["aiColdEmail"],
    "leadIds": ["lead-1", "lead-2"],
    "runIds": ["run_xxx", "run_yyy"]
  },
  "message": "Triggered 2 scoring fields for 2 leads (4 total tasks), skipped 1 unconfigured fields"
}
```

**curl:**

```bash
# Score a single lead with all configured fields
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"leadId":"LEAD_ID"}' \
  https://api.leadgenius.app/api/automation/tasks/score | jq
```

```bash
# Score a single lead with specific fields
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"leadId":"LEAD_ID","fields":["aiLeadScore","aiQualification"]}' \
  https://api.leadgenius.app/api/automation/tasks/score | jq
```

```bash
# Batch score multiple leads (max 100)
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"leadIds":["LEAD_1","LEAD_2","LEAD_3"],"fields":["aiLeadScore","aiQualification"]}' \
  https://api.leadgenius.app/api/automation/tasks/score | jq
```

**CLI equivalent:**

```bash
python lgp.py tasks score --lead LEAD_ID
python lgp.py tasks score --lead LEAD_ID --fields aiLeadScore,aiQualification
```


---

## Territory Companies

### `GET /api/automation/companies`

List TerritoryCompany records by `client_id` with optional filtering and sorting.

**Query Parameters:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `client_id` | string | Yes | — | Client to list companies for |
| `sortBy` | string | No | — | Sort field: `totalLeads`, `qualifiedLeads`, `averageLeadScore`, `lastActivityDate`, `companyName` |
| `industry` | string | No | — | Filter by industry |
| `country` | string | No | — | Filter by country |
| `minLeads` | integer | No | — | Minimum total leads |
| `maxLeads` | integer | No | — | Maximum total leads |
| `minScore` | number | No | — | Minimum average lead score |
| `maxScore` | number | No | — | Maximum average lead score |
| `limit` | integer | No | 50 | Max records (capped at 500) |
| `nextToken` | string | No | — | Pagination token |

**Response:**

```json
{
  "success": true,
  "data": {
    "items": [
      {
        "id": "tc-001",
        "companyName": "Acme Corp",
        "totalLeads": 25,
        "qualifiedLeads": 10,
        "averageLeadScore": 72,
        "industry": "SaaS",
        "country": "US",
        "client_id": "client-123"
      }
    ],
    "count": 1,
    "nextToken": null
  }
}
```

**Pagination:** When `nextToken` is present in the response, pass it as a query parameter to fetch the next page. When `nextToken` is `null`, there are no more pages.

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies?client_id=YOUR_CLIENT&sortBy=totalLeads" | jq
```

**CLI equivalent:**

```bash
python lgp.py companies list --client YOUR_CLIENT
python lgp.py companies list --client YOUR_CLIENT --sort totalLeads
```

---

### `GET /api/automation/companies/{id}`

Return a complete TerritoryCompany record with all metrics, content analysis fields, and a `leadsSummary` (count + IDs of associated EnrichLeads).

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | TerritoryCompany record ID |

**Response:**

```json
{
  "success": true,
  "data": {
    "id": "tc-001",
    "companyName": "Acme Corp",
    "totalLeads": 25,
    "qualifiedLeads": 10,
    "averageLeadScore": 72,
    "industry": "SaaS",
    "country": "US",
    "contentTopics": ["AI", "Automation"],
    "contentKeywords": ["machine learning", "workflow"],
    "painPoints": ["manual processes", "data silos"],
    "valuePropositions": ["efficiency", "integration"],
    "competitorMentions": ["CompetitorX"],
    "engagementInsights": "High email open rate",
    "contentRecommendations": "Focus on ROI case studies",
    "leadsSummary": {
      "count": 25,
      "leadIds": ["lead-1", "lead-2"]
    }
  }
}
```

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies/COMPANY_ID" | jq
```

**CLI equivalent:**

```bash
python lgp.py companies get COMPANY_ID
```

---

### `GET /api/automation/companies/{id}/leads`

Return all EnrichLeads associated with a TerritoryCompany (matched by `companyName` and `client_id`).

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | TerritoryCompany record ID |

**Query Parameters:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `limit` | integer | No | 50 | Max records (capped at 500) |
| `nextToken` | string | No | — | Pagination token |

**Response:**

```json
{
  "success": true,
  "data": {
    "items": [
      {
        "id": "lead-001",
        "firstName": "Jane",
        "lastName": "Doe",
        "fullName": "Jane Doe",
        "email": "jane@acme.com",
        "linkedinUrl": "https://linkedin.com/in/janedoe",
        "headline": "VP Sales at Acme",
        "title": "VP Sales",
        "companyName": "Acme Corp",
        "companyUrl": "https://acme.com",
        "companyDomain": "acme.com",
        "industry": "SaaS",
        "country": "US",
        "state": "CA",
        "city": "San Francisco",
        "status": "active",
        "aiScoreValue": "85",
        "aiQualification": "Highly Qualified",
        "client_id": "client-123",
        "company_id": "company-456",
        "createdAt": "2026-03-01T10:00:00.000Z",
        "updatedAt": "2026-03-15T14:30:00.000Z"
      }
    ],
    "count": 1,
    "nextToken": null
  }
}
```

**Pagination:** When `nextToken` is present in the response, pass it as a query parameter to fetch the next page. When `nextToken` is `null`, there are no more pages.

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies/COMPANY_ID/leads?limit=50" | jq
```

**CLI equivalent:**

```bash
python lgp.py companies leads COMPANY_ID --limit 50
```

---

### `POST /api/automation/companies/aggregate`

Trigger company data aggregation from EnrichLeads into TerritoryCompany records.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `client_id` | string | Yes | — | Client to aggregate for |
| `companyName` | string | No | — | Aggregate a single company only |
| `forceRefresh` | boolean | No | `false` | Delete and re-create existing records |
| `maxLeads` | integer | No | — | Max leads to process |

**Response:**

```json
{
  "success": true,
  "data": {
    "companiesCreated": 15,
    "companiesUpdated": 3,
    "totalLeadsProcessed": 200,
    "errors": []
  }
}
```

**curl:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"client_id":"YOUR_CLIENT"}' \
  https://api.leadgenius.app/api/automation/companies/aggregate | jq
```

```bash
# Aggregate a single company with force refresh
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"client_id":"YOUR_CLIENT","companyName":"Acme Corp","forceRefresh":true}' \
  https://api.leadgenius.app/api/automation/companies/aggregate | jq
```

**CLI equivalent:**

No direct CLI command — use the API endpoint via curl. After aggregation completes, view results with:

```bash
python lgp.py companies list --client YOUR_CLIENT
```

---

### `GET /api/automation/companies/events`

List CompanyEvent records by `client_id`, sorted by `eventDate` descending.

**Query Parameters:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `client_id` | string | Yes | — | Client to list events for |
| `eventType` | string | No | — | Filter: `new_lead`, `lead_qualified`, `score_increased`, `new_company`, `custom` |
| `territoryCompanyId` | string | No | — | Filter by specific company |
| `dateFrom` | string | No | — | ISO date string lower bound |
| `dateTo` | string | No | — | ISO date string upper bound |
| `limit` | integer | No | 50 | Max records (capped at 500) |
| `nextToken` | string | No | — | Pagination token |

**Response:**

```json
{
  "success": true,
  "data": {
    "items": [
      {
        "id": "event-001",
        "territoryCompanyId": "tc-001",
        "eventType": "new_lead",
        "eventTitle": "New lead added",
        "eventDescription": "Jane Doe added to Acme Corp",
        "eventDate": "2026-03-01T10:00:00.000Z",
        "client_id": "client-123"
      }
    ],
    "count": 1,
    "nextToken": null
  }
}
```

**Pagination:** When `nextToken` is present in the response, pass it as a query parameter to fetch the next page. When `nextToken` is `null`, there are no more pages.

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies/events?client_id=YOUR_CLIENT&eventType=new_lead" | jq
```

---

### `POST /api/automation/companies/events`

Create a manual CompanyEvent.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `territoryCompanyId` | string | Yes | — | TerritoryCompany record ID |
| `eventType` | string | Yes | — | One of: `new_lead`, `lead_qualified`, `score_increased`, `new_company`, `custom` |
| `eventTitle` | string | Yes | — | Short event title |
| `eventDescription` | string | No | — | Longer description |
| `eventData` | object | No | — | Arbitrary JSON data |
| `leadId` | string | No | — | Associated lead ID |
| `client_id` | string | No | — | Override client (defaults to TerritoryCompany's client) |

**Response:**

```json
{
  "success": true,
  "data": {
    "id": "event-002",
    "territoryCompanyId": "tc-001",
    "eventType": "custom",
    "eventTitle": "Partnership announced",
    "eventDescription": "Acme announced partnership with Beta Inc",
    "eventData": {"source": "press_release"},
    "client_id": "client-123"
  }
}
```

**curl:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"territoryCompanyId":"TC_ID","eventType":"custom","eventTitle":"Partnership announced","eventDescription":"Acme announced partnership with Beta Inc"}' \
  https://api.leadgenius.app/api/automation/companies/events | jq
```

---

### `DELETE /api/automation/companies/events`

Batch delete CompanyEvent records.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `eventIds` | array | Yes | — | Array of event IDs to delete |

**Response:**

```json
{
  "success": true,
  "data": {
    "deleted": 2
  }
}
```

**curl:**

```bash
curl -s -X DELETE -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"eventIds":["event-1","event-2"]}' \
  https://api.leadgenius.app/api/automation/companies/events | jq
```

---

### `POST /api/automation/companies/events/generate`

Auto-generate CompanyEvent records from recent EnrichLeads activity.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `client_id` | string | Yes | — | Client to generate events for |
| `since` | string | No | — | Only process leads created after this ISO date |
| `maxLeads` | integer | No | — | Max leads to process |

**Response:**

```json
{
  "success": true,
  "data": {
    "eventsCreated": 25,
    "eventsByType": {
      "new_lead": 15,
      "lead_qualified": 10
    },
    "errors": []
  }
}
```

**curl:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"client_id":"YOUR_CLIENT","since":"2025-01-01T00:00:00Z"}' \
  https://api.leadgenius.app/api/automation/companies/events/generate | jq
```

---

### `GET /api/automation/companies/events/radar`

Return a radar dashboard summary with recent events, counts by type, top active companies, and timeline.

**Query Parameters:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `client_id` | string | Yes | — | Client to get radar for |

**Response:**

```json
{
  "success": true,
  "data": {
    "recentEvents": [
      {
        "id": "event-001",
        "eventType": "new_lead",
        "eventTitle": "New lead added",
        "eventDate": "2026-03-01T10:00:00.000Z"
      }
    ],
    "eventCountsByType": {
      "new_lead": 50,
      "lead_qualified": 20
    },
    "topActiveCompanies": [
      {
        "companyName": "Acme Corp",
        "eventCount": 15
      }
    ],
    "timeline": [
      {
        "date": "2026-03-01",
        "count": 5
      }
    ]
  }
}
```

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies/events/radar?client_id=YOUR_CLIENT" | jq
```

---

### `POST /api/automation/companies/{id}/content-analysis`

Re-run content analysis aggregation for a TerritoryCompany. Fetches all associated EnrichLeads, extracts content insights, and updates the company record.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | TerritoryCompany record ID |

**Request Body:** Empty `{}` or omit body.

**Updated fields:** `contentTopics`, `contentKeywords`, `leadTitles`, `leadHeadlines`, `targetAudiences`, `painPoints`, `valuePropositions`, `competitorMentions`, `engagementInsights`, `contentRecommendations`, `lastContentAnalysisDate`.

**Response:**

```json
{
  "success": true,
  "data": {
    "id": "tc-001",
    "companyName": "Acme Corp",
    "contentTopics": ["AI", "Automation"],
    "contentKeywords": ["machine learning", "workflow"],
    "painPoints": ["manual processes", "data silos"],
    "valuePropositions": ["efficiency", "integration"],
    "competitorMentions": ["CompetitorX"],
    "engagementInsights": "High email open rate",
    "contentRecommendations": "Focus on ROI case studies",
    "lastContentAnalysisDate": "2026-03-15T14:30:00.000Z"
  }
}
```

**curl:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  https://api.leadgenius.app/api/automation/companies/COMPANY_ID/content-analysis | jq
```

**CLI equivalent:**

```bash
python lgp.py companies content-analysis COMPANY_ID
```


---

## Webhook Events

### `GET /api/automation/webhook-events`

List WebhookLog records for your company, sorted by `createdAt` descending.

**Query Parameters:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `platform` | string | No | — | Filter by platform (e.g., `woodpecker`, `lemlist`) |
| `eventType` | string | No | — | Filter by event type |
| `matchStatus` | string | No | — | Filter by match status |
| `processingStatus` | string | No | — | Filter: `success` or `failure` |
| `clientId` | string | No | — | Filter by webhook ID / client |
| `dateFrom` | string | No | — | ISO date lower bound |
| `dateTo` | string | No | — | ISO date upper bound |
| `limit` | integer | No | 50 | Max records (capped at 500) |
| `nextToken` | string | No | — | Pagination token |

**Response:**

```json
{
  "success": true,
  "data": {
    "items": [
      {
        "id": "wh-001",
        "webhookId": "hook-123",
        "webhookType": "inbound",
        "platform": "woodpecker",
        "eventType": "email_opened",
        "matchStatus": "matched",
        "matchedLeadId": "lead-001",
        "matchConfidence": "high",
        "normalizedData": {"email": "jane@example.com"},
        "requestMethod": "POST",
        "responseStatus": 200,
        "isSuccess": true,
        "processingTime": 150,
        "createdAt": "2026-03-01T10:00:00.000Z"
      }
    ],
    "count": 1,
    "nextToken": null
  }
}
```

**Pagination:** When `nextToken` is present in the response, pass it as a query parameter to fetch the next page. When `nextToken` is `null`, there are no more pages.

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/webhook-events?platform=woodpecker&limit=20" | jq
```

**CLI equivalent:**

```bash
python lgp.py webhooks list
python lgp.py webhooks list --platform woodpecker --limit 20
```

---

### `GET /api/automation/webhook-events/{id}`

Return a complete WebhookLog record including raw payload, normalized data, and processing details.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | WebhookLog record ID |

**Response:**

```json
{
  "success": true,
  "data": {
    "id": "wh-001",
    "webhookId": "hook-123",
    "webhookType": "inbound",
    "platform": "woodpecker",
    "eventType": "email_opened",
    "matchStatus": "matched",
    "matchedLeadId": "lead-001",
    "matchConfidence": "high",
    "normalizedData": {"email": "jane@example.com", "firstName": "Jane"},
    "requestMethod": "POST",
    "requestBody": "{\"prospect\":{\"email\":\"jane@example.com\"}}",
    "responseStatus": 200,
    "isSuccess": true,
    "errorMessage": null,
    "leadsCreated": 0,
    "eventHash": "abc123",
    "processingTime": 150,
    "createdAt": "2026-03-01T10:00:00.000Z"
  }
}
```

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/webhook-events/EVENT_ID" | jq
```

**CLI equivalent:**

```bash
python lgp.py webhooks get EVENT_ID
```

---

### `PUT /api/automation/webhook-events/{id}`

Update specific fields on a WebhookLog record. Immutable fields (`owner`, `company_id`) cannot be modified.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | WebhookLog record ID |

**Request Body (all fields optional):**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `matchStatus` | string | No | — | Update match status |
| `matchedLeadId` | string | No | — | Link to a matched lead |
| `processingStatus` | string | No | — | `success` or `failure` (mapped to `isSuccess`) |
| `client_id` | string | No | — | Reassign to a different client |

**Response:**

```json
{
  "success": true,
  "data": {
    "id": "wh-001",
    "matchStatus": "matched",
    "matchedLeadId": "lead-123",
    "isSuccess": true
  }
}
```

**curl:**

```bash
curl -s -X PUT -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"matchStatus":"matched","matchedLeadId":"lead-123"}' \
  https://api.leadgenius.app/api/automation/webhook-events/EVENT_ID | jq
```

---

### `DELETE /api/automation/webhook-events`

Batch delete WebhookLog records by ID.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `eventIds` | array | Yes | — | Array of WebhookLog IDs to delete |

**Response:**

```json
{
  "success": true,
  "data": {
    "deleted": 2,
    "failed": 1,
    "results": [
      {"id": "event-1", "success": true},
      {"id": "event-2", "success": true},
      {"id": "event-3", "success": false, "error": "Not found"}
    ]
  }
}
```

**curl:**

```bash
curl -s -X DELETE -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"eventIds":["event-1","event-2"]}' \
  https://api.leadgenius.app/api/automation/webhook-events | jq
```

---

### `POST /api/automation/webhook-events/{id}/reprocess`

Re-run lead matching and engagement update logic for a specific webhook event. Useful when new leads have been imported since the original webhook was received.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | WebhookLog record ID |

**Request Body:** Empty `{}` or omit body.

**Matching priority:**
1. Email match (high confidence) — uses `email-index` GSI
2. LinkedIn URL match (medium confidence) — uses `company_id` GSI with filter
3. First name + last name match (low confidence) — uses `firstName-lastName-index` GSI

**Key behaviors:**
- Updates `matchStatus`, `matchedLeadId`, and `matchConfidence` on the WebhookLog
- If a lead is matched, appends the webhook event to the lead's `engagementHistory` and recalculates `engagementScore`
- Matching uses the `normalizedData` JSON field from the webhook event

**Response:**

```json
{
  "success": true,
  "data": {
    "id": "wh-001",
    "matchStatus": "matched",
    "matchedLeadId": "lead-123",
    "matchConfidence": "high",
    "matchMethod": "email",
    "reprocessedAt": "2026-03-05T12:00:00.000Z",
    "platform": "woodpecker",
    "eventType": "email_opened"
  },
  "message": "Matched lead via email (high confidence)"
}
```

**curl:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  https://api.leadgenius.app/api/automation/webhook-events/EVENT_ID/reprocess | jq
```

**CLI equivalent:**

```bash
python lgp.py webhooks reprocess EVENT_ID
```


---

## Users

### `GET /api/automation/users`

List CompanyUser records in your company.

**Query Parameters:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `group` | string | No | — | Filter by group: `admin`, `manager`, `user`, `viewer` |
| `limit` | integer | No | 50 | Max records (capped at 500) |
| `nextToken` | string | No | — | Pagination token |

**Response:**

```json
{
  "success": true,
  "data": {
    "items": [
      {
        "id": "cu-001",
        "user_id": "cognito-sub-123",
        "company_id": "company-456",
        "email": "jane@example.com",
        "role": "admin",
        "group": "admin",
        "menuAccess": ["dashboard", "enrich-leads", "sdr-ai"],
        "permissions": {"canExport": true},
        "clientAccessMode": "all",
        "allowedClientIds": [],
        "status": "active",
        "invitedBy": "owner-sub-789",
        "invitedAt": "2026-01-15T10:00:00.000Z",
        "acceptedAt": "2026-01-15T10:05:00.000Z",
        "createdAt": "2026-01-15T10:00:00.000Z"
      }
    ],
    "count": 1,
    "nextToken": null
  }
}
```

**Pagination:** When `nextToken` is present in the response, pass it as a query parameter to fetch the next page. When `nextToken` is `null`, there are no more pages.

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/users?group=admin" | jq
```

**CLI equivalent:**

```bash
python lgp.py users list
python lgp.py users list --group admin
```

---

### `GET /api/automation/users/{id}`

Get a single CompanyUser's details.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | CompanyUser record ID |

**Response:**

```json
{
  "success": true,
  "data": {
    "id": "cu-001",
    "user_id": "cognito-sub-123",
    "company_id": "company-456",
    "email": "jane@example.com",
    "role": "admin",
    "group": "admin",
    "menuAccess": ["dashboard", "enrich-leads"],
    "permissions": {},
    "clientAccessMode": "all",
    "status": "active",
    "createdAt": "2026-01-15T10:00:00.000Z"
  }
}
```

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/users/USER_ID" | jq
```

**CLI equivalent:**

```bash
python lgp.py users get USER_ID
```

---

### `POST /api/automation/users`

Create/invite a new CompanyUser record.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `email` | string | Yes | — | User email |
| `role` | string | No | `member` | `owner`, `admin`, `member`, `viewer` |
| `group` | string | No | `user` | `admin`, `manager`, `user`, `viewer` |
| `user_id` | string | No | auto-generated | Cognito sub (if known) |
| `menuAccess` | array | No | — | Array of menu keys |
| `permissions` | object | No | — | Permissions object |
| `clientAccessMode` | string | No | — | `all`, `own`, `specific` |
| `allowedClientIds` | array | No | — | Array of client IDs (for `specific` mode) |

**Response:**

```json
{
  "success": true,
  "data": {
    "id": "cu-002",
    "email": "newuser@example.com",
    "role": "member",
    "group": "user",
    "company_id": "company-456",
    "status": "pending",
    "createdAt": "2026-03-01T10:00:00.000Z"
  }
}
```

**curl:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"email":"newuser@example.com","role":"member","group":"user"}' \
  https://api.leadgenius.app/api/automation/users | jq
```

**CLI equivalent:**

```bash
python lgp.py users create --email newuser@example.com --role member --group user
```

---

### `PUT /api/automation/users/{id}`

Update a CompanyUser's group, role, status, menu access, or permissions.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | CompanyUser record ID |

**Request Body (all fields optional):**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `group` | string | No | — | `admin`, `manager`, `user`, `viewer` |
| `role` | string | No | — | `owner`, `admin`, `member`, `viewer` |
| `status` | string | No | — | `pending`, `active`, `inactive`, `disabled` |
| `menuAccess` | array | No | — | Array of menu keys |
| `permissions` | object | No | — | Permissions object |
| `clientAccessMode` | string | No | — | `all`, `own`, `specific` |
| `allowedClientIds` | array | No | — | Client IDs for `specific` mode |

**Response:**

```json
{
  "success": true,
  "data": {
    "id": "cu-001",
    "role": "admin",
    "group": "manager",
    "status": "active",
    "menuAccess": ["dashboard", "enrich-leads", "sdr-ai"]
  }
}
```

**curl:**

```bash
curl -s -X PUT -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"role":"admin","group":"manager"}' \
  https://api.leadgenius.app/api/automation/users/USER_ID | jq
```

**CLI equivalent:**

```bash
python lgp.py users update USER_ID --role admin --group manager
```

---

### `DELETE /api/automation/users/{id}`

Remove a CompanyUser from the company. Cannot delete your own account.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | CompanyUser record ID |

**Response:**

```json
{
  "success": true,
  "data": {
    "id": "cu-002",
    "deleted": true
  }
}
```

**curl:**

```bash
curl -s -X DELETE -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/users/USER_ID" | jq
```

**CLI equivalent:**

```bash
python lgp.py users delete USER_ID
```

---

### `GET /api/automation/users/menu-config`

Returns the master list of available menu keys, categories, and default menus per group.

**Query Parameters:** None.

**Response:**

```json
{
  "success": true,
  "data": {
    "menus": [
      {"key": "dashboard", "label": "Dashboard", "category": "main"},
      {"key": "enrich-leads", "label": "Enrich Leads", "category": "leads"},
      {"key": "source-leads", "label": "Source Leads", "category": "leads"},
      {"key": "sdr-ai", "label": "SDR AI", "category": "ai"}
    ],
    "groupDefaults": {
      "admin": ["dashboard", "source-leads", "enrich-leads", "sdr-ai"],
      "manager": ["dashboard", "enrich-leads", "sdr-ai"],
      "user": ["dashboard", "enrich-leads"],
      "viewer": ["dashboard"]
    }
  }
}
```

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/users/menu-config" | jq
```

---

### `GET /api/automation/users/cognito`

Look up or list Cognito users.

**Query Parameters:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `email` | string | No | — | Get a specific user by email |
| `limit` | integer | No | 20 | Max users to list (max 60) |

**Response (single user by email):**

```json
{
  "success": true,
  "data": {
    "username": "user@example.com",
    "sub": "f4a844a8-00c1-7087-b434-f6d681e1f269",
    "status": "CONFIRMED",
    "email": "user@example.com",
    "enabled": true,
    "createdAt": "2026-01-15T10:00:00.000Z"
  }
}
```

**curl:**

```bash
# Get specific user
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/users/cognito?email=user@example.com" | jq

# List users
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/users/cognito?limit=10" | jq
```

**CLI equivalent:**

```bash
python lgp.py cognito get --email user@example.com
python lgp.py cognito list --limit 10
```

---

### `POST /api/automation/users/cognito`

Create a Cognito user with a permanent password (no force-change on first login).

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `email` | string | Yes | — | User email |
| `password` | string | Yes | — | Min 8 characters |
| `name` | string | No | — | Display name |

**Response:**

```json
{
  "success": true,
  "data": {
    "username": "newuser@example.com",
    "sub": "f4a844a8-00c1-7087-b434-f6d681e1f269",
    "status": "CONFIRMED",
    "email": "newuser@example.com"
  }
}
```

**Error Codes:**

| Condition | Error | Description |
|-----------|-------|-------------|
| Email already registered | `UsernameExistsException` | A Cognito user with this email already exists |
| Weak password | `InvalidPasswordException` | Password does not meet complexity requirements (min 8 chars) |

**curl:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"email":"newuser@example.com","password":"SecurePass123!","name":"Jane Doe"}' \
  https://api.leadgenius.app/api/automation/users/cognito | jq
```

**CLI equivalent:**

```bash
python lgp.py cognito create --email newuser@example.com --password "SecurePass123!"
```

---

### `PUT /api/automation/users/cognito`

Enable, disable, reset password, or set custom attributes on a Cognito user.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `email` | string | Yes | — | User email |
| `action` | string | Yes | — | `enable`, `disable`, `set-password`, `set-attributes` |
| `password` | string | For `set-password` | — | New password |
| `attributes` | object | For `set-attributes` | — | Object of attribute name → value |

**Response:**

```json
{
  "success": true,
  "data": {
    "email": "user@example.com",
    "action": "set-attributes",
    "result": "success"
  }
}
```

**curl:**

```bash
# Enable a user
curl -s -X PUT -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"email":"user@example.com","action":"enable"}' \
  https://api.leadgenius.app/api/automation/users/cognito | jq

# Set custom attributes
curl -s -X PUT -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"email":"user@example.com","action":"set-attributes","attributes":{"custom:allowed_views":"role:companyAdmin|*"}}' \
  https://api.leadgenius.app/api/automation/users/cognito | jq
```

**CLI equivalent:**

```bash
python lgp.py cognito enable --email user@example.com
python lgp.py cognito disable --email user@example.com
```

---

### `POST /api/automation/users/provision`

One-shot endpoint that creates a complete user setup: Cognito user → Company (new or existing) → CompanyUser → API key.

**Request Body — New company:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `email` | string | Yes | — | User email |
| `password` | string | Yes | — | Min 8 characters |
| `name` | string | No | — | Display name |
| `companyName` | string | No | Derived from email domain | New company name |
| `role` | string | No | `owner` | User role |
| `group` | string | No | `admin` | User group |
| `menuAccess` | array | No | — | Array of menu keys |
| `permissions` | object | No | — | Permissions object |
| `clientAccessMode` | string | No | — | `all`, `own`, `specific` |
| `allowedClientIds` | array | No | — | Client IDs for `specific` mode |
| `createApiKey` | boolean | No | `true` | Generate API key |
| `apiKeyName` | string | No | Auto-generated | API key display name |

**Request Body — Join existing company:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `email` | string | Yes | — | User email |
| `password` | string | Yes | — | Min 8 characters |
| `company_id` | string | Yes | — | Existing company ID to join |
| `role` | string | No | `member` | User role |
| `group` | string | No | `user` | User group |
| `createApiKey` | boolean | No | `false` | Generate API key |

**Response:**

```json
{
  "success": true,
  "data": {
    "cognito": {
      "sub": "f4a844a8-00c1-7087-b434-f6d681e1f269",
      "username": "newuser@example.com",
      "status": "CONFIRMED"
    },
    "company": {
      "id": "company-xxx",
      "name": "Acme Corp",
      "action": "created"
    },
    "companyUser": {
      "id": "user-xxx",
      "email": "newuser@example.com",
      "role": "owner"
    },
    "apiKey": {
      "id": "apikey-xxx",
      "name": "Jane's API Key",
      "keyPrefix": "lgp_6bd162",
      "plainTextKey": "lgp_xxxxxxxx..."
    },
    "companyId": "company-xxx"
  },
  "message": "User fully provisioned (new company)"
}
```

The `plainTextKey` is only returned once — store it securely.

**Error Codes:**

| Condition | Error | Description | Recovery |
|-----------|-------|-------------|----------|
| Email already registered | `UsernameExistsException` | A Cognito user with this email already exists | Use `GET /api/automation/users/cognito?email=...` to check first, or use `company_id` to join existing |
| Weak password | `InvalidPasswordException` | Password does not meet complexity requirements | Use min 8 characters with mixed case, numbers, and symbols |
| Company not found | `NOT_FOUND` | The `company_id` provided does not exist | Verify the company ID or create a new company instead |

**curl:**

```bash
# Provision with new company
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"email":"newuser@example.com","password":"SecurePass123!","name":"Jane Doe","companyName":"Acme Corp","createApiKey":true}' \
  https://api.leadgenius.app/api/automation/users/provision | jq

# Provision joining existing company
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"email":"newuser@example.com","password":"SecurePass123!","company_id":"COMPANY_ID","role":"member","group":"user"}' \
  https://api.leadgenius.app/api/automation/users/provision | jq
```

**CLI equivalent:**

```bash
python lgp.py users provision --email newuser@example.com --password "SecurePass123!" --company-name "Acme Corp"
```


---

## Organizations

### `GET /api/automation/companies/manage`

List companies owned by the authenticated user.

**Query Parameters:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `limit` | integer | No | 50 | Max records (max 500) |

**Response:**

```json
{
  "success": true,
  "data": {
    "items": [
      {
        "id": "company-001",
        "name": "Acme Corp",
        "owner": "owner-sub-789",
        "createdAt": "2026-01-01T10:00:00.000Z"
      }
    ],
    "count": 1
  }
}
```

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies/manage" | jq
```

**CLI equivalent:**

```bash
python lgp.py org list
```

---

### `GET /api/automation/companies/manage?id={id}`

Get a single company by ID.

**Query Parameters:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `id` | string | Yes | — | Company record ID |

**Response:**

```json
{
  "success": true,
  "data": {
    "id": "company-001",
    "name": "Acme Corp",
    "owner": "owner-sub-789",
    "createdAt": "2026-01-01T10:00:00.000Z"
  }
}
```

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies/manage?id=COMPANY_ID" | jq
```

**CLI equivalent:**

```bash
python lgp.py org get COMPANY_ID
```

---

### `POST /api/automation/companies/manage`

Create a new company. The authenticated user becomes the owner.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `name` | string | Yes | — | Company display name |

**Response:**

```json
{
  "success": true,
  "data": {
    "id": "company-002",
    "name": "Acme Corp",
    "owner": "owner-sub-789",
    "createdAt": "2026-03-01T10:00:00.000Z"
  }
}
```

**curl:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"name":"Acme Corp"}' \
  https://api.leadgenius.app/api/automation/companies/manage | jq
```

**CLI equivalent:**

```bash
python lgp.py org create --name "Acme Corp"
```

---

### `PUT /api/automation/companies/manage` — Rename

Rename an existing company.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `id` | string | Yes | — | Company record ID |
| `name` | string | Yes | — | New company name |

**Response:**

```json
{
  "success": true,
  "data": {
    "id": "company-001",
    "name": "New Company Name"
  }
}
```

**curl:**

```bash
curl -s -X PUT -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"id":"COMPANY_ID","name":"New Company Name"}' \
  https://api.leadgenius.app/api/automation/companies/manage | jq
```

**CLI equivalent:**

```bash
python lgp.py org rename COMPANY_ID --name "New Name"
```

---

### `DELETE /api/automation/companies/manage?id={id}`

Delete a company. Only the company owner can delete it. Does not cascade-delete users or data.

**Query Parameters:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `id` | string | Yes | — | Company record ID |

**Response:**

```json
{
  "success": true,
  "data": {
    "id": "company-001",
    "deleted": true
  }
}
```

**curl:**

```bash
curl -s -X DELETE -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies/manage?id=COMPANY_ID" | jq
```

**CLI equivalent:**

```bash
python lgp.py org delete COMPANY_ID
```

---

### `GET /api/automation/companies/manage?id={id}&users=true`

List all CompanyUser records in a specific company.

**Query Parameters:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `id` | string | Yes | — | Company record ID |
| `users` | boolean | Yes | `true` | Must be `true` to list users |

**Response:**

```json
{
  "success": true,
  "data": {
    "company": {
      "id": "company-001",
      "name": "Acme Corp"
    },
    "users": [
      {
        "id": "cu-001",
        "email": "admin@acme.com",
        "role": "owner",
        "group": "admin",
        "status": "active"
      },
      {
        "id": "cu-002",
        "email": "member@acme.com",
        "role": "member",
        "group": "user",
        "status": "active"
      }
    ]
  }
}
```

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies/manage?id=COMPANY_ID&users=true" | jq
```

**CLI equivalent:**

```bash
python lgp.py org users COMPANY_ID
```

---

### `PUT /api/automation/companies/manage` — Add User

Add a user to a company.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `action` | string | Yes | — | Must be `add-user` |
| `company_id` | string | Yes | — | Target company ID |
| `email` | string | Yes | — | User email |
| `user_id` | string | No | auto-generated | Cognito sub (if known) |
| `role` | string | No | `member` | `owner`, `admin`, `member`, `viewer` |
| `group` | string | No | `user` | `admin`, `manager`, `user`, `viewer` |
| `menuAccess` | array | No | — | Array of menu keys |
| `permissions` | object | No | — | Permissions object |
| `clientAccessMode` | string | No | — | `all`, `own`, `specific` |
| `allowedClientIds` | array | No | — | Client IDs for `specific` mode |

**Response:**

```json
{
  "success": true,
  "data": {
    "id": "cu-003",
    "email": "newuser@example.com",
    "role": "member",
    "group": "user",
    "company_id": "company-001",
    "status": "pending"
  }
}
```

**curl:**

```bash
curl -s -X PUT -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"action":"add-user","company_id":"COMPANY_ID","email":"newuser@example.com","role":"member","group":"user"}' \
  https://api.leadgenius.app/api/automation/companies/manage | jq
```

**CLI equivalent:**

```bash
python lgp.py org add-user COMPANY_ID --email newuser@example.com --role member --group user
```

---

### `PUT /api/automation/companies/manage` — Update User

Update a user's role, group, or status within a company.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `action` | string | Yes | — | Must be `update-user` |
| `id` | string | Yes | — | CompanyUser record ID |
| `role` | string | No | — | `owner`, `admin`, `member`, `viewer` |
| `group` | string | No | — | `admin`, `manager`, `user`, `viewer` |
| `status` | string | No | — | `active`, `inactive`, `pending` |
| `email` | string | No | — | Update email |
| `menuAccess` | array | No | — | Update menu access |
| `permissions` | object | No | — | Update permissions |

**Response:**

```json
{
  "success": true,
  "data": {
    "id": "cu-003",
    "role": "admin",
    "group": "manager",
    "status": "active"
  }
}
```

**curl:**

```bash
curl -s -X PUT -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"action":"update-user","id":"COMPANY_USER_ID","role":"admin","group":"manager"}' \
  https://api.leadgenius.app/api/automation/companies/manage | jq
```

**CLI equivalent:**

```bash
python lgp.py org update-user COMPANY_USER_ID --role admin --group manager
```

---

### `PUT /api/automation/companies/manage` — Remove User

Remove a user from a company.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `action` | string | Yes | — | Must be `remove-user` |
| `id` | string | Yes | — | CompanyUser record ID |

**Response:**

```json
{
  "success": true,
  "data": {
    "id": "cu-003",
    "removed": true
  }
}
```

**curl:**

```bash
curl -s -X PUT -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"action":"remove-user","id":"COMPANY_USER_ID"}' \
  https://api.leadgenius.app/api/automation/companies/manage | jq
```

**CLI equivalent:**

```bash
python lgp.py org remove-user COMPANY_USER_ID
```


---

## Tables (Generic CRUD with ICP Focus)

Generic CRUD operations for any supported DynamoDB table. The Tables API is the primary interface for managing configuration records (UrlSettings, AgentSettings, SdrAiSettings, Client, EmailPlatformSettings) and business data models (ICP, ABMCampaign, etc.). This section uses ICP (Ideal Customer Profile) as the primary example since it is central to FSD pipeline automation.

### `GET /api/automation/tables/{tableName}`

List records from any supported table, filtered by your `company_id`. Supports pagination.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `tableName` | string | Yes | Exact model name (case-sensitive). See supported tables below. |

**Query Parameters:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `limit` | integer | No | 100 | Max records per page (capped at 1000) |
| `nextToken` | string | No | — | Pagination token from previous response |

**Supported Tables:**

| Category | Tables |
|----------|--------|
| Multi-Tenant Company | `Company`, `CompanyUser`, `CompanyInvitation` |
| Core Data & Leads | `Jobs`, `B2BLeads`, `EnrichLeads`, `SourceLeads`, `TerritoryCompany`, `CompanyEvent`, `LinkedInJobs` |
| Campaign & Targeting | `ICP`, `ABMCampaign`, `TargetAccount` |
| Outreach & Workflow | `OutreachSequence`, `SequenceEnrollment`, `Workflow`, `WorkflowExecution` |
| Webhook & Integration | `Integration`, `Webhook`, `WebhookLog`, `WebhookSettings`, `InboundWebhook`, `WebhookEvent` |
| AI & Agent Config | `Agent`, `AgentSettings`, `SdrAiSettings`, `CopyrightSettings`, `SdrSettings` |
| Service & Platform Config | `EnrichmentService`, `EmailPlatformSettings`, `OutreachCampaign`, `OutreachTemplate`, `BaserowSyncConfig`, `BaserowSyncHistory`, `BaserowConfig`, `UnipileSettings`, `UnipileAccount`, `UnipileMessage`, `UnipileChat`, `UnipileLog`, `UnipileCampaign`, `UnipileIntegration` |
| System & Settings | `AgentApiKey`, `UrlSettings`, `Client`, `SearchHistory`, `Maintenance`, `SidebarConfig`, `SharedView` |

**Response:**

```json
{
  "success": true,
  "data": {
    "items": [
      {
        "id": "record-id",
        "name": "Enterprise SaaS ICP",
        "client_id": "client-123",
        "company_id": "company-456",
        "owner": "owner-sub-789",
        "createdAt": "2026-03-01T10:00:00.000Z",
        "updatedAt": "2026-03-15T14:30:00.000Z"
      }
    ],
    "count": 1,
    "nextToken": null
  }
}
```

**Pagination:** When `nextToken` is present in the response, pass it as a query parameter to fetch the next page. When `nextToken` is `null`, there are no more pages.

**curl:**

```bash
# List all ICP records
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/tables/ICP" | jq
```

```bash
# List ICP records with pagination
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/tables/ICP?limit=10" | jq
```

```bash
# List other table types
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/tables/Client?limit=50" | jq

curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/tables/UrlSettings?limit=10" | jq
```

**CLI equivalent:**

```bash
python lgp.py tables list ICP
python lgp.py tables list Client
python lgp.py tables list UrlSettings --limit 10
```

---

### `POST /api/automation/tables/{tableName}`

Create a new record in any supported table. `owner` and `company_id` are auto-set from your API key.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `tableName` | string | Yes | Exact model name (case-sensitive) |

**Request Body:** Any valid fields for the target model. See ICP field schema below for ICP-specific fields.

**Key behaviors:**
- `owner` is auto-set to your API key's owner
- `company_id` is auto-set to your API key's company
- If you provide `owner` or `company_id` that don't match your key, the request is rejected with `IMMUTABLE_FIELD`
- Unknown fields are passed through to GraphQL (may cause errors if not in schema)

**ICP Field Schema:**

The ICP (Ideal Customer Profile) model has four field groups:

**Targeting Criteria Fields:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `name` | string | No | ICP display name |
| `description` | string | No | ICP description |
| `industries` | JSON array | No | Target industries (e.g., `["SaaS", "FinTech", "Healthcare"]`) |
| `companySizes` | JSON array | No | Company size ranges (e.g., `["1-10", "11-50", "51-200", "201-500"]`) |
| `geographies` | JSON array | No | Target countries/regions (e.g., `["United States", "United Kingdom", "Germany"]`) |
| `jobTitles` | JSON array | No | Target job titles (e.g., `["VP Sales", "Head of Marketing", "CTO"]`) |
| `seniority` | JSON array | No | Seniority levels (e.g., `["Director", "VP", "C-Suite"]`) |
| `departments` | JSON array | No | Target departments (e.g., `["Sales", "Marketing", "Engineering"]`) |
| `functions` | JSON array | No | Target functions (e.g., `["Business Development", "Product Management"]`) |
| `keywords` | JSON array | No | Search keywords (e.g., `["AI", "machine learning", "automation"]`) |
| `technologies` | JSON array | No | Target technologies (e.g., `["Salesforce", "HubSpot", "AWS"]`) |

**Apify Configuration Fields (required for lead generation):**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `apifyActorId` | string | Yes (for generation) | Apify actor ID for lead scraping (e.g., `"apify/linkedin-sales-navigator"`) |
| `apifyInput` | JSON string | No | Apify actor input configuration (search parameters as JSON string) |
| `apifySettings` | JSON string | No | Additional Apify settings (e.g., proxy, timeout) |
| `maxLeads` | integer | No (default 100) | Maximum leads per generation run |
| `leadSources` | JSON array | No | Lead source identifiers |

**Qualification Fields:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `qualificationCriteria` | JSON string | No | Qualification rules as JSON string |
| `scoringWeights` | JSON string | No | Scoring weights per criterion as JSON string |

**Metadata Fields (mostly auto-managed):**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `isActive` | boolean | No (default `true`) | Whether the ICP is active |
| `lastUsedDate` | datetime | No (auto-updated) | Last time this ICP was used for generation |
| `totalLeadsGenerated` | integer | No (auto-updated) | Cumulative leads generated from this ICP |
| `client_id` | string | Yes | Client partition for data isolation |
| `company_id` | string | Auto-set | Company isolation (set from API key) |
| `owner` | string | Auto-set | Owner identity (set from API key) |

**Example — Create ICP with full targeting criteria:**

```json
{
  "client_id": "client-123",
  "name": "Enterprise SaaS Decision Makers",
  "description": "VP+ level contacts at mid-to-large SaaS companies in North America",
  "industries": ["SaaS", "Cloud Computing", "Enterprise Software"],
  "companySizes": ["51-200", "201-500", "501-1000", "1001-5000"],
  "geographies": ["United States", "Canada"],
  "jobTitles": ["VP Sales", "VP Marketing", "Head of Growth", "CTO", "CMO"],
  "seniority": ["VP", "C-Suite", "Director"],
  "departments": ["Sales", "Marketing", "Engineering"],
  "functions": ["Business Development", "Product Management", "Revenue Operations"],
  "keywords": ["B2B SaaS", "product-led growth", "enterprise sales"],
  "technologies": ["Salesforce", "HubSpot", "Outreach", "Gong"],
  "apifyActorId": "apify/linkedin-sales-navigator",
  "apifyInput": "{\"searchUrl\":\"https://www.linkedin.com/sales/search/people?query=...\",\"maxResults\":200}",
  "apifySettings": "{\"proxyConfiguration\":{\"useApifyProxy\":true}}",
  "maxLeads": 200,
  "leadSources": ["LinkedIn Sales Navigator"],
  "qualificationCriteria": "{\"minCompanySize\":50,\"requiredIndustries\":[\"SaaS\",\"Cloud Computing\"]}",
  "scoringWeights": "{\"industryMatch\":0.3,\"seniorityMatch\":0.25,\"companySize\":0.2,\"technologyFit\":0.25}",
  "isActive": true
}
```

**Response:**

```json
{
  "success": true,
  "data": {
    "record": {
      "id": "icp-generated-id",
      "name": "Enterprise SaaS Decision Makers",
      "client_id": "client-123",
      "owner": "your-owner",
      "company_id": "your-company",
      "isActive": true,
      "totalLeadsGenerated": 0,
      "createdAt": "2026-03-01T10:00:00.000Z",
      "updatedAt": "2026-03-01T10:00:00.000Z"
    }
  },
  "message": "ICP record created"
}
```

**curl:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT",
    "name": "Enterprise SaaS Decision Makers",
    "industries": ["SaaS", "Cloud Computing"],
    "companySizes": ["51-200", "201-500"],
    "geographies": ["United States"],
    "jobTitles": ["VP Sales", "CTO"],
    "seniority": ["VP", "C-Suite"],
    "apifyActorId": "apify/linkedin-sales-navigator",
    "apifyInput": "{\"searchUrl\":\"https://linkedin.com/sales/search/...\"}",
    "maxLeads": 200,
    "isActive": true
  }' \
  https://api.leadgenius.app/api/automation/tables/ICP | jq
```

**CLI equivalent:**

```bash
python lgp.py tables create ICP --data '{
  "client_id": "YOUR_CLIENT",
  "name": "Enterprise SaaS Decision Makers",
  "industries": ["SaaS", "Cloud Computing"],
  "companySizes": ["51-200", "201-500"],
  "geographies": ["United States"],
  "jobTitles": ["VP Sales", "CTO"],
  "seniority": ["VP", "C-Suite"],
  "apifyActorId": "apify/linkedin-sales-navigator",
  "apifyInput": "{\"searchUrl\":\"https://linkedin.com/sales/search/...\"}",
  "maxLeads": 200,
  "isActive": true
}'
```

---

### `GET /api/automation/tables/{tableName}/{id}`

Return a single record by ID. Verifies `company_id` match — you can only access records belonging to your company.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `tableName` | string | Yes | Exact model name (case-sensitive) |
| `id` | string | Yes | Record ID |

**Response:**

```json
{
  "success": true,
  "data": {
    "id": "icp-123",
    "name": "Enterprise SaaS Decision Makers",
    "industries": ["SaaS", "Cloud Computing", "Enterprise Software"],
    "companySizes": ["51-200", "201-500", "501-1000"],
    "geographies": ["United States", "Canada"],
    "jobTitles": ["VP Sales", "VP Marketing", "CTO"],
    "seniority": ["VP", "C-Suite", "Director"],
    "departments": ["Sales", "Marketing"],
    "functions": ["Business Development"],
    "keywords": ["B2B SaaS"],
    "technologies": ["Salesforce", "HubSpot"],
    "apifyActorId": "apify/linkedin-sales-navigator",
    "apifyInput": "{\"searchUrl\":\"...\"}",
    "maxLeads": 200,
    "isActive": true,
    "totalLeadsGenerated": 450,
    "lastUsedDate": "2026-03-10T08:00:00.000Z",
    "client_id": "client-123",
    "company_id": "company-456",
    "owner": "owner-sub-789",
    "createdAt": "2026-03-01T10:00:00.000Z",
    "updatedAt": "2026-03-10T08:00:00.000Z"
  }
}
```

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/tables/ICP/ICP_ID" | jq
```

**CLI equivalent:**

```bash
python lgp.py tables get ICP ICP_ID
```

---

### `PUT /api/automation/tables/{tableName}/{id}`

Update a record. Verifies `company_id` match. Rejects changes to immutable fields (`owner`, `company_id`).

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `tableName` | string | Yes | Exact model name (case-sensitive) |
| `id` | string | Yes | Record ID |

**Request Body:** Any valid fields for the target model. Only provided fields are updated.

**Error Codes:**
- `IMMUTABLE_FIELD` (400) — Attempted to modify `owner` or `company_id`
- `NOT_FOUND` (404) — Record does not exist or belongs to a different company

**Example — Update ICP targeting criteria:**

```json
{
  "industries": ["SaaS", "Cloud Computing", "AI/ML"],
  "companySizes": ["201-500", "501-1000", "1001-5000"],
  "jobTitles": ["VP Sales", "VP Marketing", "CTO", "VP Engineering"],
  "keywords": ["B2B SaaS", "product-led growth", "AI-powered"]
}
```

**Example — Deactivate an ICP:**

```json
{
  "isActive": false
}
```

**Response:**

```json
{
  "success": true,
  "data": {
    "record": {
      "id": "icp-123",
      "name": "Enterprise SaaS Decision Makers",
      "isActive": false,
      "updatedAt": "2026-03-15T14:30:00.000Z"
    }
  },
  "message": "ICP record updated"
}
```

**curl:**

```bash
# Update targeting criteria
curl -s -X PUT -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"industries":["SaaS","Cloud Computing","AI/ML"],"companySizes":["201-500","501-1000"]}' \
  https://api.leadgenius.app/api/automation/tables/ICP/ICP_ID | jq
```

```bash
# Deactivate an ICP
curl -s -X PUT -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"isActive":false}' \
  https://api.leadgenius.app/api/automation/tables/ICP/ICP_ID | jq
```

**CLI equivalent:**

```bash
# Update targeting criteria
python lgp.py tables update ICP ICP_ID --data '{"industries":["SaaS","Cloud Computing","AI/ML"]}'

# Deactivate an ICP
python lgp.py tables update ICP ICP_ID --data '{"isActive":false}'
```

---

### `DELETE /api/automation/tables/{tableName}/{id}`

Delete a record. Verifies `company_id` match before deletion.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `tableName` | string | Yes | Exact model name (case-sensitive) |
| `id` | string | Yes | Record ID |

**Response:**

```json
{
  "success": true,
  "data": {
    "deleted": true,
    "id": "icp-123"
  },
  "message": "ICP record deleted"
}
```

**curl:**

```bash
curl -s -X DELETE -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/tables/ICP/ICP_ID" | jq
```

**CLI equivalent:**

```bash
python lgp.py tables delete ICP ICP_ID
```


---

## Email Platforms

List configured email platforms and send leads to them for outreach campaigns.

### `GET /api/automation/email-platforms`

Return configured email platforms with connection status for your company.

**Query Parameters:** None.

**Response:**

```json
{
  "success": true,
  "data": [
    {
      "id": "platform-1",
      "name": "My Woodpecker",
      "platform": "woodpecker",
      "isActive": true,
      "connectionStatus": "connected",
      "client_id": "client-123",
      "createdAt": "2026-03-01T10:00:00.000Z",
      "updatedAt": "2026-03-15T14:30:00.000Z"
    }
  ]
}
```

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/email-platforms" | jq
```

**CLI equivalent:**

```bash
python lgp.py email-platforms list
```

---

### `POST /api/automation/email-platforms/send`

Send leads to a configured email platform for a campaign. Leads without a valid email are skipped.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `leadIds` | array | Yes | — | Array of EnrichLead IDs (max 200) |
| `platform` | string | Yes | — | Platform name (e.g., `woodpecker`, `lemlist`). Matches by `platform` type or display `name` (case-insensitive). |
| `campaignId` | string | Yes | — | Campaign identifier on the email platform |

**Key behaviors:**
- Platform must be active (`isActive: true`)
- Prefers `emailFinder` field over `email` for verified addresses
- Leads without any email are skipped with `missing_email` reason
- Leads from other companies are rejected

**Response:**

```json
{
  "success": true,
  "data": {
    "platform": "woodpecker",
    "platformName": "My Woodpecker",
    "campaignId": "campaign-123",
    "sent": 2,
    "skipped": [
      {"leadId": "lead-3", "reason": "missing_email"}
    ],
    "errors": [],
    "deliveryDetails": [
      {"leadId": "lead-1", "email": "jane@example.com", "status": "queued"},
      {"leadId": "lead-2", "email": "john@example.com", "status": "queued"}
    ]
  },
  "message": "Processed 3 leads: 2 queued, 1 skipped, 0 errors"
}
```

**curl:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"leadIds":["lead-1","lead-2","lead-3"],"platform":"woodpecker","campaignId":"campaign-123"}' \
  https://api.leadgenius.app/api/automation/email-platforms/send | jq
```

**CLI equivalent:**

```bash
python lgp.py email-platforms send --platform woodpecker --campaign campaign-123 --leads lead-1,lead-2,lead-3
```


---

## FSD Pipeline

Full-Stack Demand generation pipeline — create campaigns, run lead generation pipelines, and monitor stage-by-stage progress. The FSD pipeline orchestrates the entire demand generation flow: lead generation (via Apify) → enrichment → scoring → qualification → email delivery.

### `GET /api/automation/fsd/campaigns`

List all FsdCampaign records for your company with status and progress metrics.

**Query Parameters:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `limit` | integer | No | 50 | Max records per page (capped at 500) |
| `nextToken` | string | No | — | Pagination token from previous response |

**Response fields per campaign:** `id`, `name`, `client_id`, `icpId`, `apifyActorId`, `apifyInput`, `frequency`, `targetLeadCount`, `isActive`, `nextRunAt`, `enrichAfterGeneration`, `scoreAfterEnrichment`, `sendToEmailPlatform`, `qualificationThreshold`, `emailCampaignId`, `totalRuns`, `totalLeadsGenerated`, `totalLeadsEnriched`, `totalLeadsScored`, `totalLeadsSent`, `lastRunAt`, `createdAt`.

**Response:**

```json
{
  "success": true,
  "data": {
    "items": [
      {
        "id": "campaign-001",
        "name": "Q1 Outreach Campaign",
        "client_id": "client-123",
        "icpId": "icp-456",
        "frequency": "weekly",
        "targetLeadCount": 200,
        "isActive": true,
        "enrichAfterGeneration": true,
        "scoreAfterEnrichment": true,
        "sendToEmailPlatform": "woodpecker",
        "qualificationThreshold": 60,
        "emailCampaignId": "camp-wp-001",
        "totalRuns": 4,
        "totalLeadsGenerated": 780,
        "totalLeadsEnriched": 750,
        "totalLeadsScored": 750,
        "totalLeadsSent": 320,
        "lastRunAt": "2026-03-10T08:00:00.000Z",
        "nextRunAt": "2026-03-17T08:00:00.000Z",
        "createdAt": "2026-02-15T10:00:00.000Z"
      }
    ],
    "count": 1,
    "nextToken": null
  }
}
```

**Pagination:** When `nextToken` is present in the response, pass it as a query parameter to fetch the next page. When `nextToken` is `null`, there are no more pages.

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/campaigns" | jq
```

**CLI equivalent:**

```bash
python lgp.py fsd campaigns
```

---

### `GET /api/automation/fsd/campaigns/{id}`

Return a single FsdCampaign by ID with all fields and cumulative metrics.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | FsdCampaign record ID |

**Response:**

```json
{
  "success": true,
  "data": {
    "id": "campaign-001",
    "name": "Q1 Outreach Campaign",
    "client_id": "client-123",
    "icpId": "icp-456",
    "apifyActorId": "apify/linkedin-sales-navigator",
    "apifyInput": {"searchUrl": "https://linkedin.com/sales/search/..."},
    "frequency": "weekly",
    "targetLeadCount": 200,
    "isActive": true,
    "enrichAfterGeneration": true,
    "scoreAfterEnrichment": true,
    "sendToEmailPlatform": "woodpecker",
    "qualificationThreshold": 60,
    "emailCampaignId": "camp-wp-001",
    "totalRuns": 4,
    "totalLeadsGenerated": 780,
    "totalLeadsEnriched": 750,
    "totalLeadsScored": 750,
    "totalLeadsSent": 320,
    "lastRunAt": "2026-03-10T08:00:00.000Z",
    "nextRunAt": "2026-03-17T08:00:00.000Z",
    "createdAt": "2026-02-15T10:00:00.000Z",
    "updatedAt": "2026-03-10T08:05:00.000Z"
  }
}
```

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/campaigns/CAMPAIGN_ID" | jq
```

**CLI equivalent:**

```bash
python lgp.py fsd campaign CAMPAIGN_ID
```

---

### `POST /api/automation/fsd/campaigns`

Create a new FSD campaign with lead generation configuration. A campaign defines recurring or one-time pipeline runs with automation flags.

**FSD Campaign Fields:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `client_id` | string | Yes | — | Target client (must belong to your company) |
| `name` | string | No | — | Campaign display name |
| `icpId` | string | No | — | ICP record ID — the API resolves `apifyActorId` and `apifyInput` from the ICP automatically |
| `apifyActorId` | string | No | — | Direct Apify actor ID (alternative to `icpId`) |
| `apifyInput` | JSON | No | — | Apify actor input config (JSON object or string) |
| `frequency` | string | No | `once` | Run frequency: `once`, `daily`, `weekly`, `monthly` |
| `targetLeadCount` | integer | No | 100 | Target number of leads per pipeline run |
| `enrichAfterGeneration` | boolean | No | `false` | When `true`, automatically trigger enrichment after lead generation completes |
| `scoreAfterEnrichment` | boolean | No | `false` | When `true`, automatically trigger SDR AI scoring after enrichment completes |
| `sendToEmailPlatform` | string | No | — | Platform name to send qualified leads to (e.g., `woodpecker`, `lemlist`) |
| `qualificationThreshold` | integer | No | — | Minimum score (0–100) a lead must reach to be sent to the email platform |
| `emailCampaignId` | string | No | — | Campaign ID on the email platform for lead delivery |

**Automation Flags Logic:**
- `enrichAfterGeneration: true` → pipeline automatically moves to enrichment stage after generation completes
- `scoreAfterEnrichment: true` → pipeline automatically moves to scoring stage after enrichment completes
- `sendToEmailPlatform` set + `qualificationThreshold` defined → pipeline filters scored leads by threshold and sends qualifying leads to the email platform
- If automation flags are not set, the pipeline stops after generation and you must trigger subsequent stages manually

**Example — Create campaign with ICP and full automation:**

```json
{
  "client_id": "client-123",
  "name": "Q1 Enterprise Outreach",
  "icpId": "icp-456",
  "frequency": "weekly",
  "targetLeadCount": 200,
  "enrichAfterGeneration": true,
  "scoreAfterEnrichment": true,
  "sendToEmailPlatform": "woodpecker",
  "qualificationThreshold": 60,
  "emailCampaignId": "camp-wp-001"
}
```

**Example — Create campaign with direct Apify config (no ICP):**

```json
{
  "client_id": "client-123",
  "name": "Direct LinkedIn Scrape",
  "apifyActorId": "apify/linkedin-sales-navigator",
  "apifyInput": {"searchUrl": "https://www.linkedin.com/sales/search/people?query=..."},
  "frequency": "once",
  "targetLeadCount": 100,
  "enrichAfterGeneration": true
}
```

**Response:**

```json
{
  "success": true,
  "data": {
    "record": {
      "id": "campaign-new-id",
      "name": "Q1 Enterprise Outreach",
      "client_id": "client-123",
      "icpId": "icp-456",
      "frequency": "weekly",
      "targetLeadCount": 200,
      "isActive": true,
      "enrichAfterGeneration": true,
      "scoreAfterEnrichment": true,
      "sendToEmailPlatform": "woodpecker",
      "qualificationThreshold": 60,
      "emailCampaignId": "camp-wp-001",
      "totalRuns": 0,
      "totalLeadsGenerated": 0,
      "createdAt": "2026-03-01T10:00:00.000Z"
    }
  },
  "message": "FSD campaign created"
}
```

**curl:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT",
    "name": "Q1 Enterprise Outreach",
    "icpId": "ICP_ID",
    "frequency": "weekly",
    "targetLeadCount": 200,
    "enrichAfterGeneration": true,
    "scoreAfterEnrichment": true,
    "sendToEmailPlatform": "woodpecker",
    "qualificationThreshold": 60,
    "emailCampaignId": "camp-wp-001"
  }' \
  https://api.leadgenius.app/api/automation/fsd/campaigns | jq
```

**CLI equivalent:**

```bash
python lgp.py fsd create-campaign --client YOUR_CLIENT --name "Q1 Enterprise Outreach" --icp ICP_ID --frequency weekly --target 200
```

---

### `PUT /api/automation/fsd/campaigns/{id}`

Update campaign settings. Only allowed fields can be modified.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | FsdCampaign record ID |

**Allowed update fields:** `name`, `targetLeadCount`, `frequency`, `isActive`, `enrichAfterGeneration`, `scoreAfterEnrichment`, `sendToEmailPlatform`, `qualificationThreshold`, `emailCampaignId`, `apifyActorId`, `apifyInput`, `icpId`, `nextRunAt`.

**Request Body (all fields optional):**

```json
{
  "name": "Updated Campaign Name",
  "targetLeadCount": 300,
  "frequency": "daily",
  "isActive": true,
  "enrichAfterGeneration": true,
  "scoreAfterEnrichment": true,
  "qualificationThreshold": 70
}
```

**Response:**

```json
{
  "success": true,
  "data": {
    "record": {
      "id": "campaign-001",
      "name": "Updated Campaign Name",
      "targetLeadCount": 300,
      "frequency": "daily",
      "updatedAt": "2026-03-15T14:30:00.000Z"
    }
  },
  "message": "FSD campaign updated"
}
```

**curl:**

```bash
curl -s -X PUT -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"name":"Updated Name","targetLeadCount":300,"frequency":"daily"}' \
  https://api.leadgenius.app/api/automation/fsd/campaigns/CAMPAIGN_ID | jq
```

**CLI equivalent:**

```bash
python lgp.py fsd update-campaign CAMPAIGN_ID --name "Updated Name" --target 300
```

---

### `DELETE /api/automation/fsd/campaigns/{id}`

Soft-delete a campaign by setting `isActive` to `false`. The record is not physically deleted — it can be reactivated via `PUT` with `{"isActive": true}`.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | FsdCampaign record ID |

**Response:**

```json
{
  "success": true,
  "data": {
    "id": "campaign-001",
    "isActive": false
  },
  "message": "FSD campaign deactivated"
}
```

**curl:**

```bash
curl -s -X DELETE -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/campaigns/CAMPAIGN_ID" | jq
```

**CLI equivalent:**

```bash
python lgp.py fsd deactivate-campaign CAMPAIGN_ID
```

---

### `POST /api/automation/fsd/run`

Start a new FSD pipeline run. Creates an FsdPipelineRun record and initiates lead generation. The pipeline progresses through stages automatically based on automation flags.

**ICP-to-Generation Flow:**
When `icpId` is provided, the API automatically resolves `apifyActorId` and `apifyInput` from the ICP record. This is the recommended approach — define your Apify config once on the ICP, then reference it by ID in pipeline runs.

**ICP Validation Rules:**
- The ICP record must exist → error `ICP_NOT_FOUND` (404) if not found
- The ICP must have `apifyActorId` set → error `ICP_NO_APIFY` (400) if missing
- The ICP must belong to the same company as the API key → error `ICP_LOOKUP_FAILED` (500) on resolution failure

**Alternative Direct Apify Flow:**
Instead of using an ICP, you can provide `apifyActorId` and `apifyInput` directly in the request body. This is useful for one-off runs or testing without creating an ICP record.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `client_id` | string | Yes | — | Target client for generated leads |
| `icpId` | string | One of `icpId` / `apifyActorId` | — | ICP record ID — API resolves Apify config from ICP |
| `apifyActorId` | string | One of `icpId` / `apifyActorId` | — | Direct Apify actor ID (alternative to `icpId`) |
| `apifyInput` | JSON | With `apifyActorId` | — | Apify actor input configuration |
| `targetLeadCount` | integer | No | 100 | Target number of leads to generate |
| `enrichAfterGeneration` | boolean | No | `false` | Auto-enrich after generation completes |
| `scoreAfterEnrichment` | boolean | No | `false` | Auto-score after enrichment completes |
| `sendToEmailPlatform` | string | No | — | Platform name to send qualified leads |
| `qualificationThreshold` | integer | No | 50 | Min score (0–100) for qualification filtering |
| `campaignId` | string | No | — | Link run to an FsdCampaign record |

**Pipeline Stage Progression:**

```
generating → enriching → scoring → qualifying → sending → completed
                                                              ↘ failed
```

| Stage | Description | Metric Field |
|-------|-------------|--------------|
| `generating` | Apify actor is scraping leads | `leadsGenerated` |
| `enriching` | Enrichment services running on generated leads | `leadsEnriched` |
| `scoring` | SDR AI scoring leads | `leadsScored` |
| `qualifying` | Filtering leads by `qualificationThreshold` | `leadsQualified` |
| `sending` | Sending qualified leads to email platform | `leadsSent` |
| `completed` | Pipeline finished successfully | — |
| `failed` | Pipeline encountered an error (see `errorMessage`, `stageErrors`) | — |

**SearchHistory Integration:**
Each generation run creates a SearchHistory record tracking:
- `icpId` and `icpName` — which ICP was used
- `client_id` — target client
- `apifyActorId` — which actor ran
- `totalLeadsFound` — leads found by Apify
- `totalLeadsSaved` — leads saved to the client
- `status` — generation status (`running`, `completed`, `failed`)

**Example — Run with ICP (recommended):**

```json
{
  "client_id": "client-123",
  "icpId": "icp-456",
  "targetLeadCount": 100,
  "enrichAfterGeneration": true,
  "scoreAfterEnrichment": true,
  "sendToEmailPlatform": "woodpecker",
  "qualificationThreshold": 60
}
```

**Example — Run with direct Apify config (no ICP):**

```json
{
  "client_id": "client-123",
  "apifyActorId": "apify/linkedin-sales-navigator",
  "apifyInput": {"searchUrl": "https://www.linkedin.com/sales/search/people?query=..."},
  "targetLeadCount": 50
}
```

**Response:**

```json
{
  "success": true,
  "data": {
    "pipelineId": "pipeline-uuid-001",
    "stage": "generating",
    "targetLeadCount": 100,
    "flags": {
      "enrichAfterGeneration": true,
      "scoreAfterEnrichment": true,
      "sendToEmailPlatform": "woodpecker",
      "qualificationThreshold": 60
    }
  },
  "message": "FSD pipeline run created — lead generation initiated"
}
```

**Error Codes:**
- `ICP_NOT_FOUND` (404) — ICP record with the given `icpId` does not exist
- `ICP_NO_APIFY` (400) — ICP record exists but `apifyActorId` is not configured
- `ICP_LOOKUP_FAILED` (500) — Failed to resolve the ICP record (internal error)
- `MISSING_CLIENT_ID` (400) — `client_id` not provided
- `CLIENT_WRONG_COMPANY` (400) — Client does not belong to your company

**curl:**

```bash
# Run with ICP
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"client_id":"YOUR_CLIENT","icpId":"ICP_ID","targetLeadCount":100,"enrichAfterGeneration":true,"scoreAfterEnrichment":true}' \
  https://api.leadgenius.app/api/automation/fsd/run | jq
```

```bash
# Run with direct Apify config (no ICP)
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"client_id":"YOUR_CLIENT","apifyActorId":"apify/linkedin-scraper","apifyInput":{"searchUrl":"https://..."},"targetLeadCount":50}' \
  https://api.leadgenius.app/api/automation/fsd/run | jq
```

**CLI equivalent:**

```bash
# Run with ICP
python lgp.py fsd run --client YOUR_CLIENT --icp ICP_ID --target 100

# Run with direct Apify config
python lgp.py fsd run --client YOUR_CLIENT --actor apify/linkedin-scraper --input '{"searchUrl":"https://..."}' --target 50
```

---

### `GET /api/automation/fsd/run/{pipelineId}`

Return the status and progress of an FSD pipeline run, including per-stage counts, error info, and timing.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `pipelineId` | string | Yes | FsdPipelineRun record ID |

**Response fields:** `id`, `campaignId`, `client_id`, `stage`, `leadsGenerated`, `leadsEnriched`, `leadsScored`, `leadsQualified`, `leadsSent`, `targetLeadCount`, `enrichAfterGeneration`, `scoreAfterEnrichment`, `sendToEmailPlatform`, `qualificationThreshold`, `errorMessage`, `stageErrors`, `startedAt`, `finishedAt`, `createdAt`, `updatedAt`.

**Response — In progress:**

```json
{
  "success": true,
  "data": {
    "id": "pipeline-uuid-001",
    "campaignId": "campaign-001",
    "client_id": "client-123",
    "stage": "enriching",
    "leadsGenerated": 50,
    "leadsEnriched": 20,
    "leadsScored": 0,
    "leadsQualified": 0,
    "leadsSent": 0,
    "targetLeadCount": 50,
    "enrichAfterGeneration": true,
    "scoreAfterEnrichment": true,
    "sendToEmailPlatform": "woodpecker",
    "qualificationThreshold": 60,
    "errorMessage": null,
    "stageErrors": null,
    "startedAt": "2026-03-05T10:00:00.000Z",
    "finishedAt": null,
    "createdAt": "2026-03-05T10:00:00.000Z",
    "updatedAt": "2026-03-05T10:15:00.000Z"
  }
}
```

**Response — Completed:**

```json
{
  "success": true,
  "data": {
    "id": "pipeline-uuid-001",
    "campaignId": "campaign-001",
    "client_id": "client-123",
    "stage": "completed",
    "leadsGenerated": 50,
    "leadsEnriched": 48,
    "leadsScored": 48,
    "leadsQualified": 30,
    "leadsSent": 30,
    "targetLeadCount": 50,
    "enrichAfterGeneration": true,
    "scoreAfterEnrichment": true,
    "sendToEmailPlatform": "woodpecker",
    "qualificationThreshold": 60,
    "errorMessage": null,
    "stageErrors": null,
    "startedAt": "2026-03-05T10:00:00.000Z",
    "finishedAt": "2026-03-05T11:30:00.000Z"
  }
}
```

**Response — Failed:**

```json
{
  "success": true,
  "data": {
    "id": "pipeline-uuid-002",
    "stage": "failed",
    "leadsGenerated": 50,
    "leadsEnriched": 10,
    "leadsScored": 0,
    "errorMessage": "Enrichment service timeout after 3 retries",
    "stageErrors": {"enriching": "Service enrichment1 returned 503"},
    "startedAt": "2026-03-05T10:00:00.000Z",
    "finishedAt": "2026-03-05T10:45:00.000Z"
  }
}
```

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/run/PIPELINE_ID" | jq
```

**CLI equivalent:**

```bash
python lgp.py fsd status PIPELINE_ID
```


---

## Lead Generation

Multi-provider lead generation endpoints. Trigger lead scraping from ICP profiles or direct provider configuration, monitor run status, view history, and manage recurring FSD schedules.

All endpoints use `withAutomationAuth` middleware (`X-API-Key` header). Data is scoped to the caller's `company_id` and `owner`.

Supported providers: `apify`, `vayne`, `generic`.

---

### `POST /api/automation/lead-generation`

Trigger a lead generation run. Supports two modes: ICP-based (resolve provider config from an ICP record) or direct (provide provider and config inline). Only one mode per request.

**Request Body — ICP-based:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `icpId` | string | Yes | — | ICP record ID to use for provider configuration |
| `clientId` | string | Yes | — | Client ID for lead data isolation |
| `maxLeads` | integer | No | ICP default | Override max leads per run |
| `saveToSourceLeads` | boolean | No | `true` | Save scraped leads to SourceLeads table |
| `saveToEnrichLeads` | boolean | No | `false` | Save scraped leads to EnrichLeads table |

**Request Body — Direct provider:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `provider` | string | Yes | — | Provider name: `apify`, `vayne`, or `generic` |
| `providerConfig` | object | Yes | — | Provider-specific configuration (see below) |
| `clientId` | string | Yes | — | Client ID for lead data isolation |

**Vayne `providerConfig`:**

```json
{
  "salesNavigatorUrl": "https://www.linkedin.com/sales/search/people?query=...",
  "maxLeads": 100
}
```

**Generic `providerConfig`:**

```json
{
  "endpointUrl": "https://api.example.com/scrape",
  "method": "POST",
  "headers": { "Authorization": "Bearer xxx" },
  "bodyTemplate": { "query": "{{keywords}}", "limit": "{{maxLeads}}" },
  "responseMapping": { "firstName": "first_name", "email": "contact_email" }
}
```

**Validation rules:**
- Cannot provide both `icpId` and `provider`/`providerConfig` → 400 `PROVIDER_CONFIG_CONFLICT`
- Must provide either ICP-based or direct fields → 400 `VALIDATION_ERROR`
- Unrecognized `provider` value → 400 `PROVIDER_UNKNOWN`
- Invalid `salesNavigatorUrl` for Vayne → 400 `INVALID_SALES_NAV_URL`
- Non-existent `icpId` → 404 `ICP_NOT_FOUND`
- Insufficient credits → 402 `CREDIT_EXCEEDED`

**Response (201):**

```json
{
  "success": true,
  "runId": "trigger-run-id",
  "searchHistoryId": "sh-uuid",
  "status": "initiated",
  "requestId": "req-uuid"
}
```

**curl — ICP-based:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"icpId":"ICP_ID","clientId":"CLIENT_ID","maxLeads":200}' \
  https://api.leadgenius.app/api/automation/lead-generation | jq
```

**curl — Direct Vayne:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"provider":"vayne","providerConfig":{"salesNavigatorUrl":"https://www.linkedin.com/sales/search/people?query=...","maxLeads":100},"clientId":"CLIENT_ID"}' \
  https://api.leadgenius.app/api/automation/lead-generation | jq
```

**CLI equivalent:**

```bash
# ICP-based
python lgp.py generate from-icp --icp ICP_ID --client CLIENT_ID --max-leads 200

# Direct Vayne
python lgp.py generate direct --provider vayne --client CLIENT_ID --sales-nav-url "https://www.linkedin.com/sales/search/people?query=..."
```

---

### `GET /api/automation/lead-generation/{runId}`

Get the current status of a lead generation run. Consolidates data from both the Trigger.dev run and the SearchHistory record.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `runId` | string | Yes | Trigger.dev run ID returned from the trigger endpoint |

**Response (200):**

```json
{
  "success": true,
  "runId": "trigger-run-id",
  "status": "RUNNING",
  "progress": 45,
  "totalLeadsFound": 67,
  "totalLeadsSaved": 45,
  "totalLeadsFailed": 2,
  "providerType": "apify",
  "error": null,
  "searchHistoryId": "sh-uuid",
  "requestId": "req-uuid"
}
```

**Status values:** `RUNNING`, `COMPLETED`, `FAILED`

**Errors:** 404 `RUN_NOT_FOUND` when `runId` does not match any SearchHistory record.

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/lead-generation/RUN_ID" | jq
```

**CLI equivalent:**

```bash
python lgp.py generate status RUN_ID
```

---

### `GET /api/automation/lead-generation/history`

List past lead generation runs for the caller's company. Results are sorted by `createdAt` descending.

**Query Parameters:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `clientId` | string | No | — | Filter by client ID |
| `icpId` | string | No | — | Filter by ICP ID |
| `status` | string | No | — | Filter by status: `initiated`, `running`, `completed`, `failed` |
| `limit` | integer | No | 20 | Max records to return |
| `nextToken` | string | No | — | Pagination token from previous response |

**Response (200):**

```json
{
  "success": true,
  "items": [
    {
      "id": "sh-uuid",
      "searchId": "search-xxx",
      "searchName": "Lead generation - client-1",
      "status": "completed",
      "providerType": "apify",
      "totalLeadsFound": 150,
      "totalLeadsSaved": 148,
      "icpId": "icp-uuid",
      "clientId": "client-uuid",
      "createdAt": "2025-01-15T10:00:00Z"
    }
  ],
  "count": 1,
  "nextToken": null,
  "requestId": "req-uuid"
}
```

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/lead-generation/history?clientId=CLIENT_ID&limit=10" | jq
```

**CLI equivalent:**

```bash
python lgp.py generate history --client CLIENT_ID --limit 10
```

---

### `POST /api/automation/lead-generation/schedules`

Create an FSD (Full-Stack Demand) schedule for recurring lead generation from an ICP.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `icpId` | string | Yes | — | ICP record ID |
| `clientId` | string | Yes | — | Client ID for lead isolation |
| `frequency` | string | Yes | — | Cron expression or preset: `daily`, `weekly`, `biweekly`, `monthly` |
| `maxLeadsPerRun` | integer | No | 100 | Max leads per scheduled run |
| `saveToSourceLeads` | boolean | No | `true` | Save to SourceLeads table |
| `saveToEnrichLeads` | boolean | No | `false` | Save to EnrichLeads table |

**Frequency presets:**

| Preset | Cron Expression | Schedule |
|--------|----------------|----------|
| `daily` | `0 8 * * *` | 8 AM UTC daily |
| `weekly` | `0 8 * * 1` | 8 AM UTC Monday |
| `biweekly` | `0 8 1,15 * *` | 8 AM UTC 1st and 15th |
| `monthly` | `0 8 1 * *` | 8 AM UTC 1st of month |

Custom cron expressions are also accepted.

**Response (201):**

```json
{
  "success": true,
  "scheduleId": "sched-uuid",
  "nextRunAt": "2025-01-22T08:00:00Z",
  "frequency": "weekly",
  "requestId": "req-uuid"
}
```

**curl:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"icpId":"ICP_ID","clientId":"CLIENT_ID","frequency":"weekly","maxLeadsPerRun":100}' \
  https://api.leadgenius.app/api/automation/lead-generation/schedules | jq
```

**CLI equivalent:**

```bash
python lgp.py generate schedule create --icp ICP_ID --client CLIENT_ID --frequency weekly --max-leads 100
```

---

### `GET /api/automation/lead-generation/schedules`

List all FSD schedules for the caller's company.

**Query Parameters:** None.

**Response (200):**

```json
{
  "success": true,
  "items": [
    {
      "id": "sched-uuid",
      "icpId": "icp-uuid",
      "icpName": "Enterprise SaaS",
      "clientId": "client-uuid",
      "clientName": "Q1 Campaign",
      "frequency": "0 8 * * 1",
      "frequencyPreset": "weekly",
      "enabled": true,
      "status": "active",
      "nextRunAt": "2025-01-22T08:00:00Z",
      "lastRunAt": "2025-01-15T08:00:00Z",
      "lastRunStatus": "completed",
      "totalRuns": 3,
      "totalLeadsGenerated": 450,
      "maxLeadsPerRun": 100,
      "createdAt": "2025-01-01T10:00:00Z"
    }
  ],
  "count": 1,
  "requestId": "req-uuid"
}
```

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  https://api.leadgenius.app/api/automation/lead-generation/schedules | jq
```

**CLI equivalent:**

```bash
python lgp.py generate schedule list
```

---

### `PATCH /api/automation/lead-generation/schedules/{scheduleId}`

Update an FSD schedule. Use to pause/resume or change frequency and run configuration.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `scheduleId` | string | Yes | Schedule record ID |

**Request Body:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `enabled` | boolean | No | `false` to pause, `true` to resume |
| `frequency` | string | No | New cron expression or preset |
| `maxLeadsPerRun` | integer | No | New max leads per run |

**Response (200):**

```json
{
  "success": true,
  "scheduleId": "sched-uuid",
  "enabled": false,
  "status": "paused",
  "nextRunAt": null,
  "requestId": "req-uuid"
}
```

**Errors:** 404 `SCHEDULE_NOT_FOUND` when `scheduleId` does not exist.

**curl — pause:**

```bash
curl -s -X PATCH -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"enabled":false}' \
  https://api.leadgenius.app/api/automation/lead-generation/schedules/SCHEDULE_ID | jq
```

**curl — resume:**

```bash
curl -s -X PATCH -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"enabled":true}' \
  https://api.leadgenius.app/api/automation/lead-generation/schedules/SCHEDULE_ID | jq
```

**CLI equivalent:**

```bash
python lgp.py generate schedule pause SCHEDULE_ID
python lgp.py generate schedule resume SCHEDULE_ID
```

---

### `DELETE /api/automation/lead-generation/schedules/{scheduleId}`

Delete an FSD schedule and cancel any pending runs.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `scheduleId` | string | Yes | Schedule record ID |

**Response (200):**

```json
{
  "success": true,
  "message": "Schedule deleted",
  "scheduleId": "sched-uuid",
  "requestId": "req-uuid"
}
```

**Errors:** 404 `SCHEDULE_NOT_FOUND` when `scheduleId` does not exist.

**curl:**

```bash
curl -s -X DELETE -H "X-API-Key: $LGP_API_KEY" \
  https://api.leadgenius.app/api/automation/lead-generation/schedules/SCHEDULE_ID | jq
```

**CLI equivalent:**

```bash
python lgp.py generate schedule delete SCHEDULE_ID
```

---

## Job Ad Lead Triggering

Bridges the LinkedIn Job Scraper pipeline to the Lead Generation pipeline. When a scrape run completes and new job ads are saved, unique company names are extracted and lead searches are triggered for each company. The scraper integration is fire-and-forget — trigger failures never affect the scraper's success status.

These endpoints use Cognito JWT authentication (browser session), not `X-API-Key`.

---

### `POST /api/trigger/linkedin-jobs/lead-search`

Manually trigger lead searches from a completed scrape run's results. Extracts unique companies from the scraped LinkedIn jobs and triggers the `job-ad-lead-trigger-task` Trigger.dev task.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `jobId` | string | Yes | — | Scrape run ID to pull LinkedIn jobs from |
| `max_leads_per_company` | integer | No | 25 | Override max leads per company search |
| `max_companies_per_run` | integer | No | 10 | Override max companies to trigger per run |
| `actorId` | string | No | — | Override Apify actor ID for lead generation |

**Flow:**
1. Authenticate user via Cognito session
2. Resolve `company_id` from user's company membership
3. Fetch LinkedInJobs for the scrape run (time-window filtering around job record creation)
4. Apply multi-tenant filtering by `company_id`
5. Extract unique companies using `extractUniqueCompanies()`
6. Trigger `job-ad-lead-trigger-task` with payload
7. Return trigger run ID and company count

**Response (200):**

```json
{
  "success": true,
  "triggerRunId": "trigger-run-id",
  "companiesFound": 15,
  "jobId": "scrape-job-id",
  "message": "Lead search triggered for 15 companies from scrape run scrape-job-id"
}
```

**Error Responses:**

| Status | Condition |
|--------|-----------|
| 400 | Missing or empty `jobId` |
| 401 | Authentication required (no valid Cognito session) |
| 404 | No LinkedIn jobs found for the scrape run |
| 500 | Failed to query LinkedIn jobs or trigger task |

**curl:**

```bash
curl -s -X POST \
  -H "Cookie: <cognito-session-cookies>" \
  -H "Content-Type: application/json" \
  -d '{"jobId":"SCRAPE_JOB_ID","max_leads_per_company":50,"max_companies_per_run":20}' \
  https://api.leadgenius.app/api/trigger/linkedin-jobs/lead-search | jq
```

---

### `GET /api/trigger/linkedin-jobs/lead-search`

List `JobAdLeadTriggerLog` entries with pagination. Query by `client_id` (required) or narrow by `source_job_id`.

**Query Parameters:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `client_id` | string | Yes | — | Filter logs by client workspace |
| `source_job_id` | string | No | — | Filter by specific scrape run ID |
| `limit` | integer | No | 50 | Page size |
| `nextToken` | string | No | — | Pagination cursor from previous response |

**Response (200):**

```json
{
  "success": true,
  "items": [
    {
      "id": "log-uuid",
      "source_job_id": "scrape-job-id",
      "company_name": "Acme Corp",
      "company_linkedin_url": "https://linkedin.com/company/acme",
      "lead_generation_run_id": "trigger-run-id",
      "status": "completed",
      "leads_found": 12,
      "error_message": null,
      "duration_seconds": 180,
      "client_id": "client-uuid",
      "company_id": "company-uuid",
      "owner": "user-sub",
      "createdAt": "2026-03-01T10:00:00Z"
    }
  ],
  "nextToken": null,
  "totalCount": 1
}
```

**Log status values:** `pending`, `running`, `completed`, `failed`, `timeout`

**Error Responses:**

| Status | Condition |
|--------|-----------|
| 400 | Missing `client_id` parameter |
| 401 | Authentication required |

**curl:**

```bash
# By client_id
curl -s -H "Cookie: <cognito-session-cookies>" \
  "https://api.leadgenius.app/api/trigger/linkedin-jobs/lead-search?client_id=CLIENT_ID&limit=20" | jq

# By source_job_id
curl -s -H "Cookie: <cognito-session-cookies>" \
  "https://api.leadgenius.app/api/trigger/linkedin-jobs/lead-search?client_id=CLIENT_ID&source_job_id=SCRAPE_JOB_ID" | jq
```

---

### `GET /api/trigger/linkedin-jobs/lead-search/config`

Fetch the `JobAdLeadTriggerConfig` for a specific client workspace.

**Query Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `client_id` | string | Yes | Client workspace to fetch config for |

**Response (200):**

```json
{
  "success": true,
  "config": {
    "id": "config-uuid",
    "client_id": "client-uuid",
    "company_id": "company-uuid",
    "owner": "user-sub",
    "enabled": true,
    "actorId": "apify/linkedin-sales-navigator",
    "max_leads_per_company": 25,
    "max_companies_per_run": 10,
    "keyword_filters": "[\"hiring\",\"growth\"]",
    "createdAt": "2026-01-15T10:00:00Z",
    "updatedAt": "2026-03-01T10:00:00Z"
  }
}
```

Returns `{ "success": true, "config": null }` when no config exists for the client.

**curl:**

```bash
curl -s -H "Cookie: <cognito-session-cookies>" \
  "https://api.leadgenius.app/api/trigger/linkedin-jobs/lead-search/config?client_id=CLIENT_ID" | jq
```

---

### `PUT /api/trigger/linkedin-jobs/lead-search/config`

Create or update the `JobAdLeadTriggerConfig` for a client workspace. If a config already exists for the `client_id` (and matches the caller's company), it is updated. Otherwise a new config is created.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `client_id` | string | Yes | — | Client workspace ID |
| `enabled` | boolean | No | `false` (create) | Enable/disable automatic triggering |
| `actorId` | string | No | — | Apify actor ID for lead generation |
| `max_leads_per_company` | integer | No | 25 | Max leads per company search |
| `max_companies_per_run` | integer | No | 10 | Max companies to trigger per scrape run |
| `keyword_filters` | string | No | — | JSON array of keyword strings for filtering job titles/descriptions |

**Response (200):**

```json
{
  "success": true,
  "config": {
    "id": "config-uuid",
    "client_id": "client-uuid",
    "company_id": "company-uuid",
    "owner": "user-sub",
    "enabled": true,
    "actorId": "apify/linkedin-sales-navigator",
    "max_leads_per_company": 50,
    "max_companies_per_run": 20,
    "keyword_filters": "[\"hiring\",\"growth\"]",
    "createdAt": "2026-01-15T10:00:00Z",
    "updatedAt": "2026-03-01T12:00:00Z"
  }
}
```

**curl:**

```bash
curl -s -X PUT \
  -H "Cookie: <cognito-session-cookies>" \
  -H "Content-Type: application/json" \
  -d '{"client_id":"CLIENT_ID","enabled":true,"max_leads_per_company":50,"max_companies_per_run":20,"keyword_filters":"[\"hiring\",\"growth\"]"}' \
  https://api.leadgenius.app/api/trigger/linkedin-jobs/lead-search/config | jq
```

---

### DynamoDB Models

**JobAdLeadTriggerConfig** — Per-client trigger settings

| Field | Type | Description |
|-------|------|-------------|
| `id` | string | Primary key (UUID) |
| `client_id` | string | Client workspace ID |
| `company_id` | string | Company ID for multi-tenant isolation |
| `owner` | string | User who created/updated |
| `enabled` | boolean | Whether automatic triggering is active (default: false) |
| `actorId` | string | Apify actor ID for lead generation |
| `max_leads_per_company` | integer | Max leads per company (default: 25) |
| `max_companies_per_run` | integer | Max companies per run (default: 10) |
| `keyword_filters` | string | JSON array of keyword strings |

GSI: `client_id` → `jobadleadtriggerconfig-client_id-index`

**JobAdLeadTriggerLog** — Audit trail per company search

| Field | Type | Description |
|-------|------|-------------|
| `id` | string | Primary key (UUID) |
| `source_job_id` | string | Scrape run jobId that triggered this search |
| `company_name` | string | Company targeted for lead search |
| `company_linkedin_url` | string | Company LinkedIn URL if available |
| `lead_generation_run_id` | string | Trigger.dev run ID of the lead generation task |
| `status` | string | `pending`, `running`, `completed`, `failed`, `timeout` |
| `leads_found` | integer | Number of leads generated (default: 0) |
| `error_message` | string | Error details if failed |
| `duration_seconds` | integer | Time taken for the search |
| `client_id` | string | Client workspace ID |
| `company_id` | string | Company ID for multi-tenant isolation |
| `owner` | string | User who owns this record |

GSIs: `client_id+createdAt` → `jobadleadtriggerlog-client_id-createdAt-index`, `source_job_id` → `jobadleadtriggerlog-source_job_id-index`

---


## Lead Notifications (Unipile)

Event-driven notification system that alerts users when lead lifecycle events occur. Notifications are dispatched through Unipile-connected channels (email, Slack, LinkedIn, WhatsApp). All notification calls from lead processing pipelines are fire-and-forget — errors never disrupt lead processing.

These endpoints use Cognito JWT authentication (browser session).

### Key Behaviors

- **60-second batch window**: Leads arriving within 60s for the same company/event type are aggregated into a single notification
- **5-minute dedup window**: Duplicate notifications (same config + lead + event type) within 5 minutes are skipped
- **Fire-and-forget**: All notification calls from pipelines are non-blocking; errors are caught silently

### Event Types

| Event Type | Trigger Point |
|------------|---------------|
| `new_source_lead` | After `saveLeadsToDatabase` in `lead-scraping-complete-updated.ts` |
| `new_enrich_lead` | After `saveLeadsToDatabase` when `saveToEnrichLeads` is true |
| `enrichment_completed` | After successful verification in `enrichmentWorker.ts` |
| `ai_qualification_changed` | After database update in `company-analysis-task.ts` |
| `ai_score_changed` | After database update in `company-analysis-task.ts` / `website-qualification-task.ts` |
| `lead_status_changed` | After status field update |

### Channel Routing

| Channel Types | Dispatch Method |
|---------------|-----------------|
| `MAIL`, `GOOGLE_OAUTH`, `OUTLOOK` | `UnipileClient.sendEmail` |
| `LINKEDIN`, `WHATSAPP`, `SLACK`, `MOBILE` | `UnipileClient.sendMessage` |

---

### `GET /api/lead-notifications/config`

List all `LeadNotificationConfig` records for the authenticated user's company.

**Query Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `accounts` | string | No | Set to `"true"` to return connected Unipile accounts instead of configs |

**Response — Config list (200):**

```json
{
  "configs": [
    {
      "id": "config-uuid",
      "company_id": "company-uuid",
      "owner": "user-sub",
      "name": "New Lead Alert",
      "enabled": true,
      "eventTypes": "[\"new_source_lead\",\"new_enrich_lead\"]",
      "unipileAccountId": "unipile-account-id",
      "channelType": "MAIL",
      "messageTemplate": "New lead: {{lead_name}} at {{lead_company}}",
      "recipientEmail": "alerts@company.com",
      "lastTriggeredAt": "2026-03-01T10:00:00Z",
      "createdAt": "2026-01-15T10:00:00Z"
    }
  ]
}
```

**Response — Unipile accounts (200):**

```json
{
  "accounts": [
    {
      "id": "unipile-account-id",
      "name": "Work Email",
      "type": "GOOGLE_OAUTH"
    }
  ]
}
```

**curl:**

```bash
# List configs
curl -s -H "Cookie: <cognito-session-cookies>" \
  https://api.leadgenius.app/api/lead-notifications/config | jq

# List Unipile accounts
curl -s -H "Cookie: <cognito-session-cookies>" \
  "https://api.leadgenius.app/api/lead-notifications/config?accounts=true" | jq
```

---

### `POST /api/lead-notifications/config`

Create a new notification config. Validates the Unipile account ID via `UnipileClient.getAccount`.

**Request Body:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `name` | string | Yes | — | Human-readable rule name |
| `eventTypes` | array | Yes | — | Array of event type strings (see Event Types above) |
| `unipileAccountId` | string | Yes | — | Unipile account ID for dispatch |
| `channelType` | string | Yes | — | Channel type (see Channel Routing above) |
| `messageTemplate` | string | Yes | — | Message template with `{{placeholder}}` tokens (max 2000 chars) |
| `enabled` | boolean | No | `true` | Whether the config is active |
| `recipientEmail` | string | No | — | Override recipient email (for email channels) |
| `recipientChatId` | string | No | — | Override chat ID (for message channels) |

**Template Placeholders:**

| Placeholder | Description |
|-------------|-------------|
| `{{lead_name}}` | First lead name, or "Name and N others" for batches |
| `{{lead_email}}` | First lead email |
| `{{lead_company}}` | First lead company name |
| `{{lead_title}}` | First lead job title |
| `{{client_id}}` | Client ID |
| `{{event_type}}` | Human-readable event type |
| `{{previous_value}}` | Previous field value (for change events) or "N/A" |
| `{{new_value}}` | New field value (for change events) |
| `{{timestamp}}` | ISO timestamp |
| `{{lead_count}}` | Number of leads in batch |

**Response (201):**

```json
{
  "config": {
    "id": "new-config-uuid",
    "company_id": "company-uuid",
    "owner": "user-sub",
    "name": "New Lead Alert",
    "enabled": true,
    "eventTypes": "[\"new_source_lead\"]",
    "unipileAccountId": "unipile-account-id",
    "channelType": "MAIL",
    "messageTemplate": "New lead: {{lead_name}} at {{lead_company}}",
    "createdAt": "2026-03-24T10:00:00Z"
  }
}
```

**Error Responses:**

| Status | Condition |
|--------|-----------|
| 400 | Missing required fields (`name`, `eventTypes`, `unipileAccountId`, `channelType`, `messageTemplate`) |
| 400 | `messageTemplate` exceeds 2000 characters |
| 400 | Invalid Unipile account ID (account not found) |
| 401 | Authentication required |
| 403 | No company found for user |

**curl:**

```bash
curl -s -X POST \
  -H "Cookie: <cognito-session-cookies>" \
  -H "Content-Type: application/json" \
  -d '{
    "name": "New Lead Alert",
    "eventTypes": ["new_source_lead", "new_enrich_lead"],
    "unipileAccountId": "UNIPILE_ACCOUNT_ID",
    "channelType": "MAIL",
    "messageTemplate": "New lead: {{lead_name}} at {{lead_company}} ({{lead_email}})",
    "recipientEmail": "alerts@company.com"
  }' \
  https://api.leadgenius.app/api/lead-notifications/config | jq
```

---

### `PUT /api/lead-notifications/config`

Update an existing notification config. Validates ownership (config's `company_id` must match caller's company). If `unipileAccountId` is changed, validates the new account.

**Request Body:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | Config ID to update |
| `name` | string | No | Updated rule name |
| `enabled` | boolean | No | Enable/disable toggle |
| `eventTypes` | array | No | Updated event types |
| `unipileAccountId` | string | No | Updated Unipile account ID |
| `channelType` | string | No | Updated channel type |
| `messageTemplate` | string | No | Updated message template |
| `recipientEmail` | string | No | Updated recipient email |
| `recipientChatId` | string | No | Updated chat ID |

**Response (200):**

```json
{
  "config": { /* updated config object */ }
}
```

**Error Responses:**

| Status | Condition |
|--------|-----------|
| 400 | Missing `id` field |
| 400 | Invalid new Unipile account ID |
| 401 | Authentication required |
| 403 | Config belongs to another company |
| 404 | Config not found |

**curl:**

```bash
curl -s -X PUT \
  -H "Cookie: <cognito-session-cookies>" \
  -H "Content-Type: application/json" \
  -d '{"id":"CONFIG_ID","enabled":false}' \
  https://api.leadgenius.app/api/lead-notifications/config | jq
```

---

### `DELETE /api/lead-notifications/config`

Delete a notification config. Validates ownership before deletion.

**Parameters:** `id` via query parameter or request body.

**Response (200):**

```json
{
  "success": true,
  "id": "deleted-config-uuid"
}
```

**Error Responses:**

| Status | Condition |
|--------|-----------|
| 400 | Missing `id` |
| 401 | Authentication required |
| 403 | Config belongs to another company |
| 404 | Config not found |

**curl:**

```bash
curl -s -X DELETE \
  -H "Cookie: <cognito-session-cookies>" \
  "https://api.leadgenius.app/api/lead-notifications/config?id=CONFIG_ID" | jq
```

---

### `GET /api/lead-notifications/logs`

List recent `LeadNotificationLog` entries for the authenticated user's company, sorted by `createdAt` descending.

**Query Parameters:** None (scoped by authenticated user's company).

**Response (200):**

```json
{
  "logs": [
    {
      "id": "log-uuid",
      "configId": "config-uuid",
      "company_id": "company-uuid",
      "owner": "user-sub",
      "eventType": "new_source_lead",
      "leadIds": "[\"lead-1\",\"lead-2\"]",
      "channelType": "MAIL",
      "status": "sent",
      "unipileMessageId": "msg-uuid",
      "errorMessage": null,
      "leadCount": 2,
      "renderedMessage": "New lead: Jane Doe and 1 others at Acme Corp",
      "createdAt": "2026-03-01T10:00:00Z"
    }
  ]
}
```

**Log status values:** `sent`, `failed`, `duplicate_skipped`, `batched`

**curl:**

```bash
curl -s -H "Cookie: <cognito-session-cookies>" \
  https://api.leadgenius.app/api/lead-notifications/logs | jq
```

---

### DynamoDB Models

**LeadNotificationConfig** — Per-company notification rules

| Field | Type | Description |
|-------|------|-------------|
| `id` | string | Primary key (UUID) |
| `company_id` | string | Company ID (required) |
| `owner` | string | User who created (required) |
| `name` | string | Human-readable rule name |
| `enabled` | boolean | Whether active (default: true) |
| `eventTypes` | string | JSON array of event type strings |
| `unipileAccountId` | string | Unipile account for dispatch |
| `channelType` | string | Channel type for routing |
| `messageTemplate` | string | Template with `{{placeholder}}` tokens |
| `recipientEmail` | string | Override recipient (email channels) |
| `recipientChatId` | string | Override chat ID (message channels) |
| `lastTriggeredAt` | datetime | Last notification dispatch time |

GSIs: `company_id+createdAt` → `leadnotifconfig-company_id-createdAt-index`, `owner+createdAt` → `leadnotifconfig-owner-createdAt-index`

**LeadNotificationLog** — Dispatch audit trail

| Field | Type | Description |
|-------|------|-------------|
| `id` | string | Primary key (UUID) |
| `configId` | string | Reference to config ID |
| `company_id` | string | Company ID |
| `owner` | string | User who owns this record |
| `eventType` | string | Event that triggered notification |
| `leadIds` | string | JSON array of lead IDs |
| `channelType` | string | Channel used for dispatch |
| `status` | string | `sent`, `failed`, `duplicate_skipped`, `batched` |
| `unipileMessageId` | string | Unipile response message ID (on success) |
| `errorMessage` | string | Error details (on failure) |
| `leadCount` | integer | Number of leads in notification |
| `renderedMessage` | string | Final rendered message (for audit) |

GSIs: `company_id+createdAt` → `leadnotiflog-company_id-createdAt-index`, `configId+createdAt` → `leadnotiflog-configId-createdAt-index`

---


## Error Codes

All Automation API errors return a consistent JSON envelope with `success: false`, a human-readable `error` message, an optional `details` field, and a machine-readable `code`. Use the `code` field for programmatic error handling.

**Error response format:**

```json
{
  "success": false,
  "error": "Human-readable error message",
  "details": "Additional context or validation errors",
  "code": "MACHINE_READABLE_ERROR_CODE",
  "requestId": "uuid-v4"
}
```

---

### `UNAUTHORIZED`

**HTTP Status:** 401

Missing or invalid API key. The `X-API-Key` header is absent, malformed, or references a revoked/non-existent key.

**Example response:**

```json
{
  "success": false,
  "error": "Missing or invalid API key",
  "code": "UNAUTHORIZED",
  "requestId": "req-abc123"
}
```

**Recovery:** Verify the `X-API-Key` header is present and starts with `lgp_`. Confirm the key has not been revoked. Generate a new key via `POST /api/automation/users/provision` if needed.

---

### `RATE_LIMITED`

**HTTP Status:** 429

Too many requests. The API key has exceeded its rate limit for the current window (60/min, 1 000/hr, or 10 000/day).

**Example response:**

```json
{
  "success": false,
  "error": "Rate limit exceeded (minute window)",
  "details": "You have exceeded the 60 requests per minute limit.",
  "code": "RATE_LIMITED",
  "requestId": "req-abc124"
}
```

**Response headers:**

```
Retry-After: 45
X-RateLimit-Limit: 60
X-RateLimit-Remaining: 0
X-RateLimit-Reset: 1711000045
```

**Recovery:** Wait for the `Retry-After` seconds and retry. Reduce request frequency or implement exponential back-off. Alternatively, use the `X-Admin-Key` header to bypass rate limits entirely (see [Admin Key](#admin-key---rate-limit-bypass)).

---

### `MISSING_CLIENT_ID`

**HTTP Status:** 400

A required `client_id` parameter was not provided. Most list and mutation endpoints require a `client_id` to scope data.

**Example response:**

```json
{
  "success": false,
  "error": "client_id is required",
  "code": "MISSING_CLIENT_ID",
  "requestId": "req-abc125"
}
```

**Recovery:** Include the `client_id` query parameter or request body field. List available clients via `GET /api/automation/tables/Client` to find valid IDs.

---

### `CLIENT_WRONG_COMPANY`

**HTTP Status:** 400 / 403

The specified `client_id` belongs to a different company than the one associated with your API key.

**Example response:**

```json
{
  "success": false,
  "error": "Client does not belong to your company",
  "code": "CLIENT_WRONG_COMPANY",
  "requestId": "req-abc126"
}
```

**Recovery:** Verify the `client_id` belongs to your company. List your company's clients via `GET /api/automation/tables/Client` and use a valid ID.

---

### `NOT_FOUND`

**HTTP Status:** 404

The requested resource does not exist or belongs to another company (the API returns 404 instead of 403 for cross-company access to avoid leaking resource existence).

**Example response:**

```json
{
  "success": false,
  "error": "Resource not found",
  "code": "NOT_FOUND",
  "requestId": "req-abc127"
}
```

**Recovery:** Confirm the resource ID is correct. Use the appropriate list endpoint to verify the resource exists within your company.

---

### `VALIDATION_ERROR`

**HTTP Status:** 400

The request body failed schema validation. One or more fields have invalid types, missing required values, or out-of-range values.

**Example response:**

```json
{
  "success": false,
  "error": "Validation failed",
  "details": "\"leadId\" is required; \"services\" must be an array",
  "code": "VALIDATION_ERROR",
  "requestId": "req-abc128"
}
```

**Recovery:** Check the `details` field for specific validation failures. Correct the request body to match the endpoint's schema and retry.

---

### `INVALID_BODY`

**HTTP Status:** 400

The request body is not valid JSON. The server could not parse the payload.

**Example response:**

```json
{
  "success": false,
  "error": "Invalid JSON in request body",
  "code": "INVALID_BODY",
  "requestId": "req-abc129"
}
```

**Recovery:** Ensure the request body is well-formed JSON. Verify the `Content-Type: application/json` header is set. Check for trailing commas, unquoted keys, or encoding issues.

---

### `IMMUTABLE_FIELD`

**HTTP Status:** 400

The request attempted to modify a read-only field. The `owner` and `company_id` fields are auto-set from the API key and cannot be changed via update operations.

**Example response:**

```json
{
  "success": false,
  "error": "Cannot modify immutable field",
  "details": "Fields 'owner', 'company_id' cannot be updated",
  "code": "IMMUTABLE_FIELD",
  "requestId": "req-abc130"
}
```

**Recovery:** Remove `owner` and `company_id` from the request body. These fields are automatically managed by the API based on your API key identity.

---

### `ICP_NOT_FOUND`

**HTTP Status:** 404

The ICP record referenced by `icpId` does not exist or belongs to another company. Returned by FSD pipeline endpoints when the specified ICP cannot be resolved.

**Example response:**

```json
{
  "success": false,
  "error": "ICP record not found",
  "details": "No ICP with id 'icp-xyz' found for your company",
  "code": "ICP_NOT_FOUND",
  "requestId": "req-abc131"
}
```

**Recovery:** Verify the `icpId` is correct. List available ICPs via `GET /api/automation/tables/ICP` to find valid IDs. Ensure the ICP belongs to your company.

---

### `ICP_NO_APIFY`

**HTTP Status:** 400

The ICP record exists but is missing the required `apifyActorId` field. An ICP must have Apify configuration to be used for lead generation via the FSD pipeline.

**Example response:**

```json
{
  "success": false,
  "error": "ICP missing Apify configuration",
  "details": "ICP 'icp-xyz' does not have apifyActorId configured",
  "code": "ICP_NO_APIFY",
  "requestId": "req-abc132"
}
```

**Recovery:** Update the ICP record to include `apifyActorId` (and optionally `apifyInput`, `apifySettings`) via `PUT /api/automation/tables/ICP/{id}`. Alternatively, use the direct Apify flow by providing `apifyActorId` and `apifyInput` directly in the FSD run request body.

---

### `ICP_LOOKUP_FAILED`

**HTTP Status:** 500

An internal error occurred while resolving the ICP record. The ICP may exist but the lookup operation failed due to a transient database or service error.

**Example response:**

```json
{
  "success": false,
  "error": "Failed to resolve ICP record",
  "details": "DynamoDB read failed for ICP 'icp-xyz'",
  "code": "ICP_LOOKUP_FAILED",
  "requestId": "req-abc133"
}
```

**Recovery:** Retry the request after a short delay. If the error persists, verify the ICP record exists via `GET /api/automation/tables/ICP/{id}`. Contact support if the issue continues.

---

### `PROVIDER_UNKNOWN`

**HTTP Status:** 400

The specified `provider` value is not a recognized provider name. Supported providers are `apify`, `vayne`, and `generic`.

**Example response:**

```json
{
  "success": false,
  "error": "Unknown provider: 'foo'",
  "details": "Supported providers: apify, vayne, generic",
  "code": "PROVIDER_UNKNOWN",
  "requestId": "req-abc134"
}
```

**Recovery:** Use one of the supported provider names: `apify`, `vayne`, or `generic`.

---

### `PROVIDER_CONFIG_CONFLICT`

**HTTP Status:** 400

Both `icpId` and `provider`/`providerConfig` were provided in the same request. Only one mode is allowed per request.

**Example response:**

```json
{
  "success": false,
  "error": "Cannot provide both icpId and provider/providerConfig",
  "details": "Use either ICP-based or direct provider configuration, not both",
  "code": "PROVIDER_CONFIG_CONFLICT",
  "requestId": "req-abc135"
}
```

**Recovery:** Remove either `icpId` or the `provider`/`providerConfig` fields from the request.

---

### `INVALID_SALES_NAV_URL`

**HTTP Status:** 400

The `salesNavigatorUrl` provided for a URL-based provider (e.g., Vayne) does not match the expected LinkedIn Sales Navigator URL format.

**Example response:**

```json
{
  "success": false,
  "error": "Invalid Sales Navigator URL",
  "details": "salesNavigatorUrl must start with https://www.linkedin.com/sales/",
  "code": "INVALID_SALES_NAV_URL",
  "requestId": "req-abc136"
}
```

**Recovery:** Provide a URL that starts with `https://www.linkedin.com/sales/`.

---

### `SCHEDULE_NOT_FOUND`

**HTTP Status:** 404

The specified schedule ID does not exist or does not belong to the caller's company.

**Example response:**

```json
{
  "success": false,
  "error": "Schedule not found",
  "details": "No schedule found with ID 'sched-xyz'",
  "code": "SCHEDULE_NOT_FOUND",
  "requestId": "req-abc137"
}
```

**Recovery:** Verify the schedule ID via `GET /api/automation/lead-generation/schedules`.

---

### `CREDIT_EXCEEDED`

**HTTP Status:** 402

Insufficient credits to start a lead generation run. The credit check is enforced before the provider run starts.

**Example response:**

```json
{
  "success": false,
  "error": "Insufficient credits",
  "details": "Required: 200, Available: 50",
  "code": "CREDIT_EXCEEDED",
  "requestId": "req-abc138"
}
```

**Recovery:** Purchase additional credits via the EpsimoAI credit system or reduce the `maxLeads` parameter.

---

### `RUN_NOT_FOUND`

**HTTP Status:** 404

The specified run ID does not match any SearchHistory record.

**Example response:**

```json
{
  "success": false,
  "error": "Run not found",
  "details": "No lead generation run found with ID 'run-xyz'",
  "code": "RUN_NOT_FOUND",
  "requestId": "req-abc139"
}
```

**Recovery:** Verify the run ID from the trigger response or check `GET /api/automation/lead-generation/history`.

---

## EpsimoAI User & Credit Management

All routes use `epsimoApiClient.ts` (`src/utils/epsimoApiClient.ts`) which centralizes HTTP calls to `https://backend.epsimoai.io`. The client throws `EpsimoApiError` with `statusCode`, `errorCode`, and `message` for all upstream failures. Error mapping: 401/403 → `EPSIMO_AUTH_FAILED`, 5xx/network → `EPSIMO_UNAVAILABLE`.

**Token convention:** `X-Epsimo-Token` header (preferred) or `epsimoToken` query parameter (GET fallback). Header takes precedence. Extracted by `extractEpsimoToken(request)`.

**Auth order:** All automation epsimo routes validate: (1) `X-API-Key` via `withAutomationAuth` → `AUTH_MISSING`/`AUTH_INVALID`, (2) EpsimoAI token → `MISSING_EPSIMO_TOKEN`, (3) upstream call → endpoint-specific errors.

**Workflow:** Activate → Info → Credits → Purchase → Verify

### Plan Derivation Logic

`derivePlan(threadMax, stripeClientId?)` evaluates in order:

| Condition | Plan |
|-----------|------|
| threadMax >= 120,000 | enterprise |
| threadMax >= 50,000 OR stripeClientId is truthy | premium |
| threadMax >= 10,000 | pro |
| default | free |

**Important:** `/users/info` calls `derivePlan(threadMax, stripeClientId)` (full). `/threads` calls `derivePlan(threadMax)` without `stripeClientId` (thread-info API doesn't return it). This means plan may differ between endpoints for users with `stripeClientId` and low `threadMax`.

---

### `POST /api/automation/epsimo/users/activate`

Activate an EpsimoAI user via email/password login or Cognito token exchange. Only epsimo endpoint that does not require an EpsimoAI token.

**Logic:**
- If `cognitoIdToken` present → calls `POST /auth/exchange`, returns `{ epsimoToken, userId: null, email: null }`
- If `email` + `password` present → calls `POST /auth/login`, returns `{ epsimoToken, userId, email }`
- If neither → 400 with missing field names
- Invalid JSON body → 400 `VALIDATION_ERROR`

**Request Body (login mode):**

```json
{ "email": "user@example.com", "password": "secret" }
```

**Request Body (exchange mode):**

```json
{ "cognitoIdToken": "<cognito-id-token>" }
```

**Response (login mode):**

```json
{
  "success": true,
  "data": {
    "epsimoToken": "eyJ...",
    "userId": "usr_123",
    "email": "user@example.com"
  },
  "requestId": "req-abc"
}
```

**Response (exchange mode):**

```json
{
  "success": true,
  "data": {
    "epsimoToken": "eyJ...",
    "userId": null,
    "email": null
  },
  "requestId": "req-abc"
}
```

**Errors:** 400 `VALIDATION_ERROR` (missing fields or invalid JSON), 401 `EPSIMO_AUTH_FAILED` (upstream 401/403), 502 `EPSIMO_UNAVAILABLE` (upstream 5xx/network).

**curl:**

```bash
# Login mode
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"email":"user@example.com","password":"secret"}' \
  https://api.leadgenius.app/api/automation/epsimo/users/activate | jq

# Exchange mode
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"cognitoIdToken":"eyJ..."}' \
  https://api.leadgenius.app/api/automation/epsimo/users/activate | jq
```

**CLI equivalent:**

```bash
python lgp.py epsimo activate --email user@example.com --password secret
python lgp.py epsimo activate --cognito-token eyJ...
```

---

### `GET /api/automation/epsimo/users/info`

Retrieve EpsimoAI user profile and derived plan information.

**Headers:** `X-API-Key`, `X-Epsimo-Token`

**Logic:**
- Calls `GET /user/info` on EpsimoAI backend
- Derives plan via `derivePlan(thread_max, stripe_client_id)` — includes stripeClientId
- Maps upstream `EPSIMO_AUTH_FAILED` → `EPSIMO_TOKEN_INVALID` (401)
- All other upstream errors → `EPSIMO_UNAVAILABLE` (502)

**Response:**

```json
{
  "success": true,
  "data": {
    "userId": "usr_123",
    "email": "user@example.com",
    "projectId": "proj_456",
    "threadCounter": 5000,
    "threadMax": 50000,
    "stripeClientId": "cus_xxx",
    "plan": "premium"
  },
  "requestId": "req-abc"
}
```

**Field mapping:** `user_id` → `userId`, `project_id` → `projectId`, `thread_counter` → `threadCounter`, `thread_max` → `threadMax`, `stripe_client_id` → `stripeClientId` (defaults to `null`), `plan` derived.

**Errors:** 400 `MISSING_EPSIMO_TOKEN`, 401 `EPSIMO_TOKEN_INVALID` (upstream auth failure), 502 `EPSIMO_UNAVAILABLE`.

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  -H "X-Epsimo-Token: $EPSIMO_TOKEN" \
  https://api.leadgenius.app/api/automation/epsimo/users/info | jq
```

**CLI equivalent:**

```bash
python lgp.py epsimo info --token $EPSIMO_TOKEN
```

---

### `GET /api/automation/epsimo/credits/balance`

Check EpsimoAI credit balance (remaining AI threads).

**Headers:** `X-API-Key`, `X-Epsimo-Token`

**Logic:**
- Calls `GET /auth/thread-info` on EpsimoAI backend
- Computes `credits = Math.max(0, thread_max - thread_counter)` — never negative
- Adds `lastUpdated` as current ISO 8601 timestamp
- All `EpsimoApiError` → 502 `EPSIMO_UNAVAILABLE` (no token-invalid distinction)

**Response:**

```json
{
  "success": true,
  "data": {
    "credits": 45000,
    "threadCounter": 5000,
    "threadMax": 50000,
    "lastUpdated": "2026-03-05T12:00:00.000Z"
  },
  "requestId": "req-abc"
}
```

**Errors:** 400 `MISSING_EPSIMO_TOKEN`, 502 `EPSIMO_UNAVAILABLE` (any upstream error including invalid token).

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  -H "X-Epsimo-Token: $EPSIMO_TOKEN" \
  https://api.leadgenius.app/api/automation/epsimo/credits/balance | jq
```

**CLI equivalent:**

```bash
python lgp.py epsimo credits --token $EPSIMO_TOKEN
```

---

### `POST /api/automation/epsimo/credits/purchase`

Purchase additional EpsimoAI credits.

**Headers:** `X-API-Key`, `X-Epsimo-Token`

**Logic:**
- Validates `amount`: must be present, `Number.isInteger(amount)`, and `> 0`
- Invalid values: `null`, `0`, `-1`, `1.5`, `"10"` (string) → all fail validation
- Calls `POST /credits/purchase` on EpsimoAI backend
- If upstream `statusCode === 402` OR `errorCode === 'EPSIMO_PURCHASE_FAILED'` → 402
- All other upstream errors → 502 `EPSIMO_UNAVAILABLE`

**Request Body:**

```json
{ "amount": 10000 }
```

**Response:**

```json
{
  "success": true,
  "data": {
    "previousBalance": 5000,
    "purchasedAmount": 10000,
    "newBalance": 15000,
    "transactionId": "txn_789"
  },
  "requestId": "req-abc"
}
```

**Errors:** 400 `MISSING_EPSIMO_TOKEN`, 400 `VALIDATION_ERROR` (invalid amount or JSON), 402 `EPSIMO_PURCHASE_FAILED`, 502 `EPSIMO_UNAVAILABLE`.

**curl:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "X-Epsimo-Token: $EPSIMO_TOKEN" \
  -H "Content-Type: application/json" \
  -d '{"amount":10000}' \
  https://api.leadgenius.app/api/automation/epsimo/credits/purchase | jq
```

**CLI equivalent:**

```bash
python lgp.py epsimo purchase --token $EPSIMO_TOKEN --amount 10000
```

---

### `GET /api/automation/epsimo/threads`

Get detailed thread usage information including usage percentage and plan.

**Headers:** `X-API-Key`, `X-Epsimo-Token`

**Logic:**
- Calls `GET /auth/thread-info` on EpsimoAI backend
- `remainingThreads = Math.max(0, thread_max - thread_counter)`
- `usagePercentage`: if `thread_max === 0` → `0`, else `Math.round((thread_counter / thread_max) * 100 * 100) / 100`
- `plan = derivePlan(thread_max)` — **without stripeClientId** (thread-info doesn't return it)
- All `EpsimoApiError` → 502 `EPSIMO_UNAVAILABLE`

**Response:**

```json
{
  "success": true,
  "data": {
    "threadCounter": 5000,
    "threadMax": 50000,
    "remainingThreads": 45000,
    "usagePercentage": 10.00,
    "plan": "premium"
  },
  "requestId": "req-abc"
}
```

**Important:** `plan` may differ from `/users/info` for users with `stripeClientId` and low `threadMax` (< 50,000).

**Errors:** 400 `MISSING_EPSIMO_TOKEN`, 502 `EPSIMO_UNAVAILABLE`.

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  -H "X-Epsimo-Token: $EPSIMO_TOKEN" \
  https://api.leadgenius.app/api/automation/epsimo/threads | jq
```

**CLI equivalent:**

```bash
python lgp.py epsimo threads --token $EPSIMO_TOKEN
```

---

### UI Route: `POST /api/credits/purchase`

Cookie-based route for frontend `CreditService.purchaseCredits()`. Does NOT use `withAutomationAuth` or standard JSON envelope.

**Auth:** `epsimo_token` cookie (via `getCookie('epsimo_token', { req: request })`)

**Logic:**
- Missing cookie → 401 `{ "error": "EpsimoAI token not found" }`
- Invalid JSON → 400 `{ "error": "Invalid JSON body" }`
- Invalid amount → 400 `{ "error": "Amount must be a positive integer" }`
- Calls `epsimoPurchaseCredits(token, amount)` from shared client
- On `EpsimoApiError`: returns `err.statusCode` (or 502 if >= 500) with `{ "error": message }`

**Request Body:**

```json
{ "amount": 10000 }
```

**Response (flat, no envelope):**

```json
{
  "success": true,
  "previousBalance": 5000,
  "purchasedAmount": 10000,
  "newBalance": 15000
}
```

---

### EpsimoAI Error Codes

| Code | HTTP Status | Description | Used by |
|------|-------------|-------------|---------|
| `EPSIMO_AUTH_FAILED` | 401 | EpsimoAI login credentials invalid (upstream 401/403) | activate |
| `EPSIMO_TOKEN_INVALID` | 401 | EpsimoAI token expired or invalid | info only |
| `EPSIMO_UNAVAILABLE` | 502 | EpsimoAI backend unreachable, 5xx, or other error | all endpoints |
| `EPSIMO_PURCHASE_FAILED` | 402 | Credit purchase rejected (upstream 402) | purchase |
| `MISSING_EPSIMO_TOKEN` | 400 | Required EpsimoAI token not provided | info, balance, purchase, threads |
| `VALIDATION_ERROR` | 400 | Missing/invalid request fields or invalid JSON | activate, purchase |

### Source Files

| File | Purpose |
|------|---------|
| `src/utils/epsimoApiClient.ts` | Shared API client, error class, plan derivation, token extraction |
| `src/app/api/automation/epsimo/users/activate/route.ts` | Activate endpoint |
| `src/app/api/automation/epsimo/users/info/route.ts` | User info endpoint |
| `src/app/api/automation/epsimo/credits/balance/route.ts` | Credit balance endpoint |
| `src/app/api/automation/epsimo/credits/purchase/route.ts` | Credit purchase (automation) endpoint |
| `src/app/api/automation/epsimo/threads/route.ts` | Thread usage endpoint |
| `src/app/api/credits/purchase/route.ts` | Credit purchase (UI/cookie) endpoint |


---

## Account-Based Lead Analysis

Company-level analytics derived from existing EnrichLead records. Groups leads by company (case-insensitive `companyName`, merged by `companyDomain`), computes aggregate metrics, and supports CSV/JSON export. All endpoints use `withAutomationAuth` middleware.

### `GET /api/automation/account-analysis/companies`

List company groups with sorting and filtering.

**Query Parameters:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `client_id` | string | Yes | — | Client to analyze |
| `sort_by` | string | No | `count` | Sort field: `count`, `avg_score`, `total_score` |
| `order` | string | No | `desc` | Sort direction: `asc`, `desc` |
| `limit` | integer | No | all | Return top N companies |
| `min_leads` | integer | No | — | Exclude companies with fewer leads |

**Response:**

```json
{
  "success": true,
  "data": {
    "companies": [
      {
        "companyName": "acme corp",
        "companyDomain": "acme.com",
        "leadCount": 15,
        "avgScore": 72.50,
        "totalScore": 1087
      }
    ],
    "totalCompanies": 25,
    "totalLeads": 350
  },
  "requestId": "req-abc123"
}
```

**Error Responses:**

| Status | Error | Condition |
|--------|-------|-----------|
| 400 | `client_id is required` | Missing `client_id` query param |
| 401 | `Authentication failed - verify your API key is valid` | Invalid or missing API key |
| 429 | `Rate limit exceeded` | Too many requests (includes `Retry-After` header) |
| 502 | `Upstream API error` | Internal leads API returned 5xx |
| 504 | `Request timed out while fetching lead data` | 30-second timeout exceeded |

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/account-analysis/companies?client_id=YOUR_CLIENT&sort_by=avg_score&order=desc&min_leads=3" | jq
```

**CLI equivalent:**

```bash
python lgp.py account-analysis list --client YOUR_CLIENT --sort avg_score --order desc --min-leads 3
```

---

### `GET /api/automation/account-analysis/companies/{companyName}`

Detailed metrics for a single company. The `companyName` path segment is URL-decoded and matched case-insensitively against grouped company names.

**Path Parameters:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `companyName` | string | Yes | URL-encoded company name |

**Query Parameters:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `client_id` | string | Yes | — | Client to analyze |

**Response:**

```json
{
  "success": true,
  "data": {
    "companyName": "acme corp",
    "companyDomain": "acme.com",
    "leadCount": 15,
    "scoreStats": {
      "average": 72.50,
      "median": 75.00,
      "max": 95,
      "min": 30
    },
    "statusDistribution": {
      "New": 33.3,
      "Contacted": 26.7,
      "Qualified": 20.0,
      "Unqualified": 13.3,
      "Disqualified": 6.7
    },
    "engagementVelocity": 8,
    "championLead": {
      "id": "lead-001",
      "fullName": "Jane Doe",
      "email": "jane@acme.com",
      "title": "VP Sales",
      "aiScoreValue": 95
    }
  },
  "requestId": "req-abc123"
}
```

**Score Stats fields:**
- `average`: Arithmetic mean of valid scores, rounded to 2 decimal places (null if no valid scores)
- `median`: Middle value of sorted valid scores (null if no valid scores)
- `max` / `min`: Highest / lowest valid score (null if no valid scores)

**Status Distribution:** Percentage per status category, 1 decimal place, sums to exactly 100.0. Leads with null/empty status are categorized as "Unknown".

**Engagement Velocity:** Count of leads with `createdAt` or `updatedAt` within the last 30 days.

**Champion Lead:** Highest-scored lead in the group. Tiebreak by most recent `updatedAt`. Null if no leads have valid scores.

**Error Responses:**

| Status | Error | Condition |
|--------|-------|-----------|
| 400 | `client_id is required` | Missing `client_id` query param |
| 404 | `Company not found` | No matching company group |
| 401 | `Authentication failed` | Invalid API key |
| 429 | `Rate limit exceeded` | Rate limited (includes `Retry-After` header) |

**curl:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/account-analysis/companies/Acme%20Corp?client_id=YOUR_CLIENT" | jq
```

**CLI equivalent:**

```bash
python lgp.py account-analysis analyze --client YOUR_CLIENT --company "Acme Corp"
```

---

### `GET /api/automation/account-analysis/analyze`

Bulk analysis across all companies (or a single company). Returns full `CompanyMetrics` for each company plus a summary object.

**Query Parameters:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `client_id` | string | Yes | — | Client to analyze |
| `company` | string | No | — | Specific company name (case-insensitive) |
| `limit` | integer | No | all | Return top N companies |

**Response:**

```json
{
  "success": true,
  "data": {
    "companies": [
      {
        "companyName": "acme corp",
        "companyDomain": "acme.com",
        "leadCount": 15,
        "scoreStats": {
          "average": 72.50,
          "median": 75.00,
          "max": 95,
          "min": 30
        },
        "statusDistribution": {
          "New": 33.3,
          "Contacted": 26.7,
          "Qualified": 20.0,
          "Unqualified": 13.3,
          "Disqualified": 6.7
        },
        "engagementVelocity": 8,
        "championLead": {
          "id": "lead-001",
          "fullName": "Jane Doe",
          "email": "jane@acme.com",
          "title": "VP Sales",
          "aiScoreValue": 95
        }
      }
    ],
    "summary": {
      "totalCompanies": 25,
      "totalLeads": 350,
      "overallAvgScore": 65.30,
      "topCompany": "acme corp"
    }
  },
  "requestId": "req-abc123"
}
```

**Summary fields:**
- `totalCompanies`: Number of company groups
- `totalLeads`: Sum of all lead counts across all companies
- `overallAvgScore`: Weighted average of all valid lead scores
- `topCompany`: Company name with the highest average score

Companies are sorted by lead count descending. The `limit` parameter truncates after sorting.

**Error Responses:**

| Status | Error | Condition |
|--------|-------|-----------|
| 400 | `client_id is required` | Missing `client_id` query param |
| 404 | `Company not found` | `company` param specified but no match |
| 401 | `Authentication failed` | Invalid API key |
| 429 | `Rate limit exceeded` | Rate limited |

**curl:**

```bash
# All companies
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/account-analysis/analyze?client_id=YOUR_CLIENT&limit=10" | jq

# Single company
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/account-analysis/analyze?client_id=YOUR_CLIENT&company=Acme%20Corp" | jq
```

**CLI equivalent:**

```bash
python lgp.py account-analysis analyze --client YOUR_CLIENT --limit 10
python lgp.py account-analysis analyze --client YOUR_CLIENT --company "Acme Corp"
```

---

### `GET /api/automation/account-analysis/export`

Export analysis results as CSV or JSON.

**Query Parameters:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `client_id` | string | Yes | — | Client to analyze |
| `format` | string | Yes | — | Export format: `csv` or `json` |

**CSV Response:**

Content-Type: `text/csv`
Content-Disposition: `attachment; filename="company_analysis.csv"`

CSV columns (14 total):

| Column | Source |
|--------|--------|
| Company Name | `companyName` |
| Domain | `companyDomain` |
| Lead Count | `leadCount` |
| Avg Score | `scoreStats.average` |
| Median Score | `scoreStats.median` |
| Max Score | `scoreStats.max` |
| Min Score | `scoreStats.min` |
| Pct New | `statusDistribution["New"]` |
| Pct Contacted | `statusDistribution["Contacted"]` |
| Pct Qualified | `statusDistribution["Qualified"]` |
| Velocity | `engagementVelocity` |
| Champion Name | `championLead.fullName` |
| Champion Email | `championLead.email` |
| Champion Score | `championLead.aiScoreValue` |

**JSON Response:**

```json
{
  "success": true,
  "data": [
    {
      "companyName": "acme corp",
      "companyDomain": "acme.com",
      "leadCount": 15,
      "scoreStats": { "average": 72.50, "median": 75.00, "max": 95, "min": 30 },
      "statusDistribution": { "New": 33.3, "Contacted": 26.7, "Qualified": 20.0 },
      "engagementVelocity": 8,
      "championLead": { "id": "lead-001", "fullName": "Jane Doe", "email": "jane@acme.com", "title": "VP Sales", "aiScoreValue": 95 }
    }
  ],
  "requestId": "req-abc123"
}
```

**Error Responses:**

| Status | Error | Condition |
|--------|-------|-----------|
| 400 | `client_id is required` | Missing `client_id` query param |
| 400 | `format is required and must be "csv" or "json"` | Missing or invalid `format` param |
| 401 | `Authentication failed` | Invalid API key |
| 429 | `Rate limit exceeded` | Rate limited |

**curl:**

```bash
# CSV export
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/account-analysis/export?client_id=YOUR_CLIENT&format=csv" \
  -o company_analysis.csv

# JSON export
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/account-analysis/export?client_id=YOUR_CLIENT&format=json" | jq
```

**CLI equivalent:**

```bash
python lgp.py account-analysis export --client YOUR_CLIENT --format csv --output ./company_analysis.csv
python lgp.py account-analysis export --client YOUR_CLIENT --format json
```
