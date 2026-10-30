# LeadGenius Pro — CLI Reference (`lgp`)

The `lgp` CLI is a thin HTTP client wrapping the Automation API. All business logic stays server-side; the CLI is a convenient wrapper for constructing and sending requests.

---

## Installation & Setup

No separate installation is required. The CLI runs via `npx tsx`:

```bash
npx tsx src/scripts/lgp.ts <command> [options]
```

### Environment Variables

| Variable | Description | Default |
|----------|-------------|---------|
| `LGP_API_KEY` | API key with `lgp_` prefix | — (required) |
| `LGP_ADMIN_KEY` | Admin key to bypass rate limits | — (optional) |
| `LGP_URL` | Base URL of the LeadGenius API | `http://localhost:3000` |

**Recommended setup:**

```bash
export LGP_API_KEY="lgp_your_key_here"
export LGP_ADMIN_KEY="your_admin_key_here"
export LGP_URL="https://api.leadgenius.app"
```

---

## Global Options

These options apply to every command and override environment variables when provided.

| Option | Type | Required | Default | Description |
|--------|------|----------|---------|-------------|
| `--api-key <key>` | string | No | `LGP_API_KEY` env var | API key for authentication (overrides environment variable) |
| `--admin-key <key>` | string | No | `LGP_ADMIN_KEY` env var | Admin key to bypass rate limits (overrides environment variable) |
| `--url <url>` | string | No | `LGP_URL` env var or `http://localhost:3000` | Base URL of the LeadGenius API |
| `--format <fmt>` | string | No | `json` | Output format: `json` or `table` |

When `--admin-key` (or `LGP_ADMIN_KEY`) is set, the CLI sends an `X-Admin-Key` header alongside `X-API-Key`. This bypasses all rate limits. The API key is still required for authentication — the admin key only removes rate limiting.

---

## Output Formats

| Format | Description |
|--------|-------------|
| `json` | Full JSON response body (default). Useful for piping to `jq` or programmatic consumption. |
| `table` | Tabular output with selected columns. Columns vary by command — see below. |

### Table Columns by List Command

| Command | Table Columns |
|---------|---------------|
| `leads list` | `id`, `firstName`, `lastName`, `email`, `companyName`, `status`, `createdAt` |
| `tasks list` | `jobId`, `type`, `status`, `leadId`, `createdAt` |
| `companies list` | `id`, `companyName`, `totalLeads`, `qualifiedLeads`, `averageLeadScore` |
| `webhooks list` | `id`, `platform`, `eventType`, `matched`, `createdAt` |

---

## auth

Test API key validity and connectivity.

### `auth test`

Test that the configured API key is valid and the server is reachable.

**Syntax:**

```bash
lgp auth test
```

**Flags:** None (uses global options only).

**Example:**

```bash
npx tsx src/scripts/lgp.ts auth test --api-key lgp_abc123def456
```

**Expected output (json):**

```json
{ "success": true, "message": "Authenticated", "company_id": "comp_abc123" }
```

---

## leads

Manage leads: list, get, import, search, deduplicate, transfer, and track engagement.

### `leads list`

List leads for a specific client with optional pagination and field selection.

**Syntax:**

```bash
lgp leads list --client <id> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--client <id>` | string | Yes | — | Client ID to list leads for |
| `--limit <n>` | integer | No | `50` | Maximum number of records to return |
| `--next-token <token>` | string | No | — | Pagination token from a previous response |
| `--fields <f1,f2,...>` | string | No | all fields | Comma-separated list of fields to include in the response |

**Example:**

```bash
npx tsx src/scripts/lgp.ts leads list \
  --client cl_9f3a2b7e \
  --limit 20 \
  --fields firstName,lastName,email,companyName,aiLeadScore
```

### `leads get`

Retrieve full details for a single lead by ID.

**Syntax:**

```bash
lgp leads get <id>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<id>` | string (positional) | Yes | — | Lead ID to retrieve |

**Example:**

```bash
npx tsx src/scripts/lgp.ts leads get lead_5c8d1e2f-a3b4-4567-89ef-0123456789ab
```

### `leads import`

Import one or more leads into a client. Provide data via a JSON file or inline JSON string.

**Syntax:**

```bash
lgp leads import --file <path.json>
lgp leads import --data '<json-string>'
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--file <path>` | string | One of `--file` or `--data` | — | Path to a JSON file containing lead(s) to import |
| `--data <json>` | string | One of `--file` or `--data` | — | Inline JSON string with lead data. Must include `client_id`. |

**Example — inline single lead:**

```bash
npx tsx src/scripts/lgp.ts leads import --data '{
  "client_id": "cl_9f3a2b7e",
  "firstName": "Jane",
  "lastName": "Doe",
  "email": "jane.doe@acmecorp.com",
  "companyName": "Acme Corp",
  "linkedinUrl": "https://linkedin.com/in/janedoe",
  "title": "VP of Sales"
}'
```

**Example — file import:**

```bash
npx tsx src/scripts/lgp.ts leads import --file ./leads-batch.json
```

### `leads search`

Search for leads by email, name, company URL, or LinkedIn URL.

**Syntax:**

```bash
lgp leads search [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--email <email>` | string | No | — | Search by email address |
| `--first-name <name>` | string | No | — | Search by first name |
| `--last-name <name>` | string | No | — | Search by last name (use with `--first-name`) |
| `--company-url <url>` | string | No | — | Search by company URL |
| `--linkedin-url <url>` | string | No | — | Search by LinkedIn profile URL |
| `--client <id>` | string | No | — | Narrow search to a specific client |
| `--limit <n>` | integer | No | `50` | Maximum results to return |

**Example:**

```bash
npx tsx src/scripts/lgp.ts leads search \
  --email jane.doe@acmecorp.com \
  --client cl_9f3a2b7e
```

### `leads dedup`

Find duplicate leads within a client based on specified match fields.

**Syntax:**

```bash
lgp leads dedup --client <id> --match <fields>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--client <id>` | string | Yes | — | Client ID to scan for duplicates |
| `--match <fields>` | string | Yes | — | Comma-separated match fields: `email`, `linkedinUrl`, `fullName+companyName` |

**Example:**

```bash
npx tsx src/scripts/lgp.ts leads dedup \
  --client cl_9f3a2b7e \
  --match email,linkedinUrl
```

### `leads dedup-resolve`

Merge duplicate leads by keeping one lead and merging data from others into it.

**Syntax:**

```bash
lgp leads dedup-resolve --keep <leadId> --merge <id1,id2,...>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--keep <leadId>` | string | Yes | — | Lead ID to keep as the primary record |
| `--merge <ids>` | string | Yes | — | Comma-separated lead IDs to merge into the kept lead |

**Example:**

```bash
npx tsx src/scripts/lgp.ts leads dedup-resolve \
  --keep lead_5c8d1e2f-a3b4-4567-89ef-0123456789ab \
  --merge lead_aaaa1111-bbbb-2222-cccc-333344445555,lead_dddd6666-eeee-7777-ffff-888899990000
```

### `leads transfer`

Transfer leads between clients within the same company.

**Syntax:**

```bash
lgp leads transfer --from <clientId> --to <clientId> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--from <clientId>` | string | Yes | — | Source client ID |
| `--to <clientId>` | string | Yes | — | Target client ID |
| `--leads <id1,id2,...>` | string | No | — | Comma-separated lead IDs to transfer (omit for `--all`) |
| `--all` | boolean | No | `false` | Transfer all leads from source to target |
| `--dry-run` | boolean | No | `false` | Simulate the transfer without making changes |

**Example — dry run:**

```bash
npx tsx src/scripts/lgp.ts leads transfer \
  --from cl_9f3a2b7e \
  --to cl_4d5e6f7a \
  --all \
  --dry-run
```

### `leads validate-ownership`

Scan for leads with ownership issues (orphaned records, mismatched company assignments).

**Syntax:**

```bash
lgp leads validate-ownership
```

**Flags:** None (uses global options only).

**Example:**

```bash
npx tsx src/scripts/lgp.ts leads validate-ownership
```

### `leads activity`

Log an engagement activity on a lead.

**Syntax:**

```bash
lgp leads activity <leadId> --type <activityType> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<leadId>` | string (positional) | Yes | — | Lead ID to log activity for |
| `--type <activityType>` | string | Yes | — | Activity type (see list below) |
| `--notes <text>` | string | No | — | Free-text notes about the activity |
| `--metadata <json>` | string | No | — | JSON string with additional metadata |

**Activity types:** `linkedin_connection_sent`, `linkedin_connection_accepted`, `linkedin_message_sent`, `linkedin_message_received`, `linkedin_profile_viewed`, `email_sent`, `email_opened`, `email_clicked`, `email_answered`, `email_bounced`, `call_completed`, `call_no_answer`, `meeting_scheduled`, `meeting_completed`, `form_submitted`, `website_visited`, `content_downloaded`, `demo_requested`, `proposal_sent`, `contract_signed`, `custom`

**Example:**

```bash
npx tsx src/scripts/lgp.ts leads activity lead_5c8d1e2f-a3b4-4567-89ef-0123456789ab \
  --type email_sent \
  --notes "Initial outreach email" \
  --metadata '{"campaignId":"camp_001","subject":"Quick question about your pipeline"}'
```

### `leads activities`

Retrieve the engagement history for a lead.

**Syntax:**

```bash
lgp leads activities <leadId>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<leadId>` | string (positional) | Yes | — | Lead ID to retrieve engagement history for |

**Example:**

```bash
npx tsx src/scripts/lgp.ts leads activities lead_5c8d1e2f-a3b4-4567-89ef-0123456789ab
```

### `leads update-batch`

Batch update a single field on leads from a CSV file. The CSV must contain an `id` column and the target field column.

**Syntax:**

```bash
lgp leads update-batch --client-id <id> --field <field> --csv <path>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--client-id <id>` | string | Yes | — | Client ID that owns the leads |
| `--field <field>` | string | Yes | — | Field name to update on each lead |
| `--csv <path>` | string | Yes | — | Path to CSV file with `id` and target field columns |

**Behavior:**
- Reads the CSV file and validates it contains `id` and the specified `--field` column
- Processes rows in batches of 25, sending `PUT /api/automation/leads` with `{leads: [{id, [field]: value}, ...]}`
- Reports success/failure counts after completion

**Example:**

```bash
npx tsx src/scripts/lgp.ts leads update-batch \
  --client-id cl_9f3a2b7e \
  --field companyName \
  --csv ./leads-update.csv
```

### `leads prune-blanks`

Scan a client partition and remove leads where firstName, lastName, and companyName are all empty, null, or whitespace.

**Syntax:**

```bash
lgp leads prune-blanks --client-id <id> [--dry-run]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--client-id <id>` | string | Yes | — | Client ID to scan for blank leads |
| `--dry-run` | boolean | No | `false` | Report blank lead count without deleting |

**Behavior:**
- Paginates through all leads via `GET /api/automation/leads?client_id=<id>&limit=1000`
- Identifies blank leads: firstName, lastName, and companyName are all empty/null/whitespace
- In dry-run mode: reports count of blank leads found
- In normal mode: deletes blank leads in batches of 25 via `DELETE /api/automation/leads` with `{ids: [...]}`
- Reports total scanned, blank found, and deleted counts

**Example — dry run:**

```bash
npx tsx src/scripts/lgp.ts leads prune-blanks --client-id cl_9f3a2b7e --dry-run
```

**Example — delete blank leads:**

```bash
npx tsx src/scripts/lgp.ts leads prune-blanks --client-id cl_9f3a2b7e
```

---

## tasks

Manage background processing jobs: enrichment, copyright (AI content), and scoring.

### `tasks list`

List background jobs with optional status and type filters.

**Syntax:**

```bash
lgp tasks list [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--status <status>` | string | No | — | Filter by status: `running`, `completed`, `failed` |
| `--type <type>` | string | No | — | Filter by type: `enrichment`, `copyright`, `scoring` |
| `--limit <n>` | integer | No | `50` | Maximum number of jobs to return |

**Example:**

```bash
npx tsx src/scripts/lgp.ts tasks list --status running --type enrichment --limit 10
```

### `tasks status`

Get the current status and details of a specific job.

**Syntax:**

```bash
lgp tasks status <jobId>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<jobId>` | string (positional) | Yes | — | Job ID to check status for |

**Example:**

```bash
npx tsx src/scripts/lgp.ts tasks status job_7a8b9c0d-1234-5678-abcd-ef0123456789
```

### `tasks enrich`

Trigger enrichment for a lead using configured external data services. Requires UrlSettings to be configured.

**Syntax:**

```bash
lgp tasks enrich --lead <leadId> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--lead <leadId>` | string | Yes | — | Lead ID to enrich |
| `--services <s1,s2,...>` | string | No | all services | Comma-separated enrichment service identifiers to run |

**Enrichment service identifiers:** `companyUrl`, `emailFinder`, `enrichment1` through `enrichment10`

**Example:**

```bash
npx tsx src/scripts/lgp.ts tasks enrich \
  --lead lead_5c8d1e2f-a3b4-4567-89ef-0123456789ab \
  --services companyUrl,emailFinder,enrichment1
```

### `tasks copyright`

Trigger AI content generation (copyright) for a lead. Requires AgentSettings to be configured.

**Syntax:**

```bash
lgp tasks copyright --lead <leadId> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--lead <leadId>` | string | Yes | — | Lead ID to generate content for |
| `--processes <p1,p2,...>` | string | No | all processes | Comma-separated copyright process identifiers to run |

**Copyright process identifiers:** `enrichment1` through `enrichment10` — each maps to an AI agent configured in AgentSettings.

**Example:**

```bash
npx tsx src/scripts/lgp.ts tasks copyright \
  --lead lead_5c8d1e2f-a3b4-4567-89ef-0123456789ab \
  --processes enrichment1,enrichment2
```

### `tasks score`

Trigger SDR AI scoring for a lead. Requires SdrAiSettings to be configured.

**Syntax:**

```bash
lgp tasks score --lead <leadId> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--lead <leadId>` | string | Yes | — | Lead ID to score |
| `--fields <f1,f2,...>` | string | No | all fields | Comma-separated scoring field identifiers to compute |

**Scoring field identifiers:** `aiLeadScore`, `aiQualification`, `aiNextAction`, `aiColdEmail`, `aiInterest`, `aiLinkedinConnect`, `aiCompetitorAnalysis`, `aiEngagementLevel`, `aiPurchaseWindow`, `aiDecisionMakerRole`, `aiSentiment`, `aiSocialEngagement`, `aiNurturingStage`, `aiBudgetEstimation`, `aiRiskScore`, `aiProductFitScore`

**Example:**

```bash
npx tsx src/scripts/lgp.ts tasks score \
  --lead lead_5c8d1e2f-a3b4-4567-89ef-0123456789ab \
  --fields aiLeadScore,aiQualification,aiNextAction
```

---

## companies

Browse territory companies aggregated from lead data.

### `companies list`

List territory companies for a client with optional sorting.

**Syntax:**

```bash
lgp companies list --client <id> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--client <id>` | string | Yes | — | Client ID to list companies for |
| `--sort <field>` | string | No | — | Sort field: `totalLeads`, `qualifiedLeads`, `averageLeadScore`, `lastActivityDate`, `companyName` |
| `--limit <n>` | integer | No | `50` | Maximum number of companies to return |

**Example:**

```bash
npx tsx src/scripts/lgp.ts companies list \
  --client cl_9f3a2b7e \
  --sort averageLeadScore \
  --limit 25
```

### `companies get`

Get detailed information for a territory company including leads summary.

**Syntax:**

```bash
lgp companies get <id>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<id>` | string (positional) | Yes | — | Territory company ID |

**Example:**

```bash
npx tsx src/scripts/lgp.ts companies get tc_1a2b3c4d-5678-9abc-def0-123456789abc
```

### `companies leads`

List leads belonging to a specific territory company.

**Syntax:**

```bash
lgp companies leads <id> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<id>` | string (positional) | Yes | — | Territory company ID |
| `--limit <n>` | integer | No | `50` | Maximum number of leads to return |

**Example:**

```bash
npx tsx src/scripts/lgp.ts companies leads tc_1a2b3c4d-5678-9abc-def0-123456789abc \
  --limit 50
```

### `companies content-analysis`

Re-run content analysis for a territory company.

**Syntax:**

```bash
lgp companies content-analysis <id>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<id>` | string (positional) | Yes | — | Territory company ID to analyze |

**Example:**

```bash
npx tsx src/scripts/lgp.ts companies content-analysis tc_1a2b3c4d-5678-9abc-def0-123456789abc
```

---

## webhooks

Manage inbound webhook events from email platforms (e.g., Woodpecker).

### `webhooks list`

List webhook events with optional platform and event type filters.

**Syntax:**

```bash
lgp webhooks list [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--platform <name>` | string | No | — | Filter by platform name (e.g., `woodpecker`) |
| `--event-type <type>` | string | No | — | Filter by event type (e.g., `email_opened`, `email_clicked`) |
| `--limit <n>` | integer | No | `50` | Maximum number of events to return |

**Example:**

```bash
npx tsx src/scripts/lgp.ts webhooks list \
  --platform woodpecker \
  --event-type email_opened \
  --limit 30
```

### `webhooks get`

Get full details for a specific webhook event.

**Syntax:**

```bash
lgp webhooks get <id>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<id>` | string (positional) | Yes | — | Webhook event ID |

**Example:**

```bash
npx tsx src/scripts/lgp.ts webhooks get wh_evt_aabb1122-ccdd-3344-eeff-556677889900
```

### `webhooks reprocess`

Re-run lead matching for a webhook event. Useful for events that initially failed to match a lead.

**Syntax:**

```bash
lgp webhooks reprocess <id>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<id>` | string (positional) | Yes | — | Webhook event ID to reprocess |

**Example:**

```bash
npx tsx src/scripts/lgp.ts webhooks reprocess wh_evt_aabb1122-ccdd-3344-eeff-556677889900
```


---

## tables

Generic CRUD operations for any DynamoDB table. Commonly used for `ICP`, `Client`, `UrlSettings`, `AgentSettings`, `SdrAiSettings`, and `EmailPlatformSettings` records.

### `tables list`

List records from any table with optional pagination.

**Syntax:**

```bash
lgp tables list <tableName> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<tableName>` | string (positional) | Yes | — | DynamoDB table name (e.g., `ICP`, `Client`, `UrlSettings`) |
| `--limit <n>` | integer | No | `50` | Maximum number of records to return |

**Example — list all ICP records:**

```bash
npx tsx src/scripts/lgp.ts tables list ICP
```

**Example — list clients:**

```bash
npx tsx src/scripts/lgp.ts tables list Client --limit 10
```

### `tables create`

Create a new record in any table.

**Syntax:**

```bash
lgp tables create <tableName> --data '<json-string>'
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<tableName>` | string (positional) | Yes | — | DynamoDB table name |
| `--data <json>` | string | Yes | — | JSON string containing the record fields |

**Example — create an ICP with targeting criteria and Apify config:**

```bash
npx tsx src/scripts/lgp.ts tables create ICP --data '{
  "name": "Enterprise SaaS Decision Makers",
  "client_id": "cl_9f3a2b7e",
  "industries": ["SaaS", "Cloud Computing", "Enterprise Software"],
  "companySizes": ["51-200", "201-500", "501-1000"],
  "geographies": ["United States", "United Kingdom", "Germany"],
  "jobTitles": ["VP of Sales", "Head of Revenue", "CRO"],
  "seniority": ["Director", "VP", "C-Suite"],
  "departments": ["Sales", "Revenue Operations"],
  "keywords": ["B2B SaaS", "revenue growth", "pipeline"],
  "technologies": ["Salesforce", "HubSpot", "Outreach"],
  "apifyActorId": "apify/linkedin-sales-navigator",
  "apifyInput": "{\"searchUrl\":\"https://www.linkedin.com/sales/search/people?query=...\"}",
  "maxLeads": 200,
  "isActive": true
}'
```

**Example — create a Client:**

```bash
npx tsx src/scripts/lgp.ts tables create Client --data '{
  "name": "Q1 Campaign",
  "description": "Leads for Q1 outbound campaign"
}'
```

### `tables get`

Retrieve a single record by ID from any table.

**Syntax:**

```bash
lgp tables get <tableName> <id>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<tableName>` | string (positional) | Yes | — | DynamoDB table name |
| `<id>` | string (positional) | Yes | — | Record ID to retrieve |

**Example — get an ICP record:**

```bash
npx tsx src/scripts/lgp.ts tables get ICP icp_a1b2c3d4-5678-9abc-def0-123456789abc
```

### `tables update`

Update fields on an existing record. Only the fields provided in `--data` are modified.

**Syntax:**

```bash
lgp tables update <tableName> <id> --data '<json-string>'
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<tableName>` | string (positional) | Yes | — | DynamoDB table name |
| `<id>` | string (positional) | Yes | — | Record ID to update |
| `--data <json>` | string | Yes | — | JSON string with fields to update |

**Example — update ICP targeting criteria:**

```bash
npx tsx src/scripts/lgp.ts tables update ICP icp_a1b2c3d4-5678-9abc-def0-123456789abc --data '{
  "jobTitles": ["VP of Sales", "Head of Revenue", "CRO", "Director of Sales"],
  "companySizes": ["201-500", "501-1000", "1001-5000"]
}'
```

**Example — deactivate an ICP:**

```bash
npx tsx src/scripts/lgp.ts tables update ICP icp_a1b2c3d4-5678-9abc-def0-123456789abc --data '{
  "isActive": false
}'
```

### `tables delete`

Delete a record from any table.

**Syntax:**

```bash
lgp tables delete <tableName> <id>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<tableName>` | string (positional) | Yes | — | DynamoDB table name |
| `<id>` | string (positional) | Yes | — | Record ID to delete |

**Example — delete an ICP:**

```bash
npx tsx src/scripts/lgp.ts tables delete ICP icp_a1b2c3d4-5678-9abc-def0-123456789abc
```

---

## email-platforms

Manage email platform integrations for outbound delivery.

### `email-platforms list`

List all configured email platforms for the company.

**Syntax:**

```bash
lgp email-platforms list
```

**Flags:** None (uses global options only).

**Example:**

```bash
npx tsx src/scripts/lgp.ts email-platforms list
```

### `email-platforms send`

Send qualified leads to an email platform campaign.

**Syntax:**

```bash
lgp email-platforms send --platform <name> --campaign <id> --leads <id1,id2,...>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--platform <name>` | string | Yes | — | Email platform name (e.g., `woodpecker`) |
| `--campaign <id>` | string | Yes | — | Campaign ID on the email platform |
| `--leads <ids>` | string | Yes | — | Comma-separated lead IDs to send |

**Example:**

```bash
npx tsx src/scripts/lgp.ts email-platforms send \
  --platform woodpecker \
  --campaign camp_12345 \
  --leads lead_5c8d1e2f-a3b4-4567-89ef-0123456789ab,lead_aaaa1111-bbbb-2222-cccc-333344445555
```

---

## users

Manage company users: list, create, update, delete, and provision.

### `users list`

List users in the company with optional group filter.

**Syntax:**

```bash
lgp users list [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--group <group>` | string | No | — | Filter by group: `admin`, `manager`, `user`, `viewer` |
| `--limit <n>` | integer | No | `50` | Maximum number of users to return |

**Example:**

```bash
npx tsx src/scripts/lgp.ts users list --group admin --limit 20
```

### `users get`

Get full details for a specific user.

**Syntax:**

```bash
lgp users get <id>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<id>` | string (positional) | Yes | — | User ID to retrieve |

**Example:**

```bash
npx tsx src/scripts/lgp.ts users get usr_1a2b3c4d-5678-9abc-def0-123456789abc
```

### `users create`

Create or invite a new user into the company.

**Syntax:**

```bash
lgp users create --email <email> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--email <email>` | string | Yes | — | User's email address |
| `--role <role>` | string | No | `member` | Role: `owner`, `admin`, `member`, `viewer` |
| `--group <group>` | string | No | `user` | Group: `admin`, `manager`, `user`, `viewer` |

**Example:**

```bash
npx tsx src/scripts/lgp.ts users create \
  --email newuser@acmecorp.com \
  --role member \
  --group user
```

### `users update`

Update an existing user's role, group, or status.

**Syntax:**

```bash
lgp users update <id> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<id>` | string (positional) | Yes | — | User ID to update |
| `--role <role>` | string | No | — | New role: `owner`, `admin`, `member`, `viewer` |
| `--group <group>` | string | No | — | New group: `admin`, `manager`, `user`, `viewer` |
| `--status <status>` | string | No | — | New status: `pending`, `active`, `inactive`, `disabled` |

**Example:**

```bash
npx tsx src/scripts/lgp.ts users update usr_1a2b3c4d-5678-9abc-def0-123456789abc \
  --role admin \
  --group admin
```

### `users delete`

Remove a user from the company.

**Syntax:**

```bash
lgp users delete <id>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<id>` | string (positional) | Yes | — | User ID to remove |

**Example:**

```bash
npx tsx src/scripts/lgp.ts users delete usr_1a2b3c4d-5678-9abc-def0-123456789abc
```

### `users provision`

Full user provisioning: creates a Cognito user, company (or joins existing), CompanyUser record, and API key in a single operation.

**Syntax:**

```bash
lgp users provision --email <email> --password <password> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--email <email>` | string | Yes | — | User's email address |
| `--password <password>` | string | Yes | — | Initial password (must meet Cognito policy) |
| `--name <name>` | string | No | — | User's display name |
| `--company-name <name>` | string | No | — | Create a new company with this name |
| `--company-id <id>` | string | No | — | Join an existing company by ID (alternative to `--company-name`) |
| `--role <role>` | string | No | `member` | Role: `owner`, `admin`, `member`, `viewer` |
| `--group <group>` | string | No | `user` | Group: `admin`, `manager`, `user`, `viewer` |

**Example — provision with new company:**

```bash
npx tsx src/scripts/lgp.ts users provision \
  --email admin@newcorp.com \
  --password "SecurePass123!" \
  --name "Admin User" \
  --company-name "New Corp" \
  --role owner \
  --group admin
```

**Example — provision into existing company:**

```bash
npx tsx src/scripts/lgp.ts users provision \
  --email teammate@newcorp.com \
  --password "SecurePass456!" \
  --name "Team Member" \
  --company-id comp_abc123 \
  --role member \
  --group user
```

---

## cognito

Manage AWS Cognito user accounts directly (low-level user pool operations).

### `cognito list`

List Cognito users in the user pool.

**Syntax:**

```bash
lgp cognito list [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--limit <n>` | integer | No | `50` | Maximum number of users to return |

**Example:**

```bash
npx tsx src/scripts/lgp.ts cognito list --limit 20
```

### `cognito get`

Get a Cognito user by email address.

**Syntax:**

```bash
lgp cognito get --email <email>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--email <email>` | string | Yes | — | Email address of the Cognito user to retrieve |

**Example:**

```bash
npx tsx src/scripts/lgp.ts cognito get --email admin@newcorp.com
```

### `cognito create`

Create a new Cognito user in the user pool.

**Syntax:**

```bash
lgp cognito create --email <email> --password <password> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--email <email>` | string | Yes | — | Email address for the new user |
| `--password <password>` | string | Yes | — | Initial password (must meet Cognito password policy) |
| `--name <name>` | string | No | — | User's display name |

**Example:**

```bash
npx tsx src/scripts/lgp.ts cognito create \
  --email newuser@acmecorp.com \
  --password "SecurePass789!" \
  --name "New User"
```

### `cognito enable`

Enable a disabled Cognito user account.

**Syntax:**

```bash
lgp cognito enable --email <email>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--email <email>` | string | Yes | — | Email address of the Cognito user to enable |

**Example:**

```bash
npx tsx src/scripts/lgp.ts cognito enable --email user@acmecorp.com
```

### `cognito disable`

Disable a Cognito user account (prevents login without deleting the account).

**Syntax:**

```bash
lgp cognito disable --email <email>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--email <email>` | string | Yes | — | Email address of the Cognito user to disable |

**Example:**

```bash
npx tsx src/scripts/lgp.ts cognito disable --email user@acmecorp.com
```

---

## org

Manage companies (organizations): create, rename, delete, and manage user membership.

### `org list`

List companies accessible to the authenticated user.

**Syntax:**

```bash
lgp org list [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--limit <n>` | integer | No | `50` | Maximum number of companies to return |

**Example:**

```bash
npx tsx src/scripts/lgp.ts org list --limit 10
```

### `org get`

Get detailed information for a specific company.

**Syntax:**

```bash
lgp org get <id>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<id>` | string (positional) | Yes | — | Company ID to retrieve |

**Example:**

```bash
npx tsx src/scripts/lgp.ts org get comp_abc123
```

### `org create`

Create a new company.

**Syntax:**

```bash
lgp org create --name <name>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--name <name>` | string | Yes | — | Company name |

**Example:**

```bash
npx tsx src/scripts/lgp.ts org create --name "Acme Corp"
```

### `org rename`

Rename an existing company.

**Syntax:**

```bash
lgp org rename <id> --name <newName>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<id>` | string (positional) | Yes | — | Company ID to rename |
| `--name <newName>` | string | Yes | — | New company name |

**Example:**

```bash
npx tsx src/scripts/lgp.ts org rename comp_abc123 --name "Acme Corporation"
```

### `org delete`

Delete a company. Only the company owner can perform this action.

**Syntax:**

```bash
lgp org delete <id>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<id>` | string (positional) | Yes | — | Company ID to delete |

**Example:**

```bash
npx tsx src/scripts/lgp.ts org delete comp_abc123
```

### `org users`

List users belonging to a specific company.

**Syntax:**

```bash
lgp org users <companyId> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<companyId>` | string (positional) | Yes | — | Company ID to list users for |
| `--limit <n>` | integer | No | `50` | Maximum number of users to return |

**Example:**

```bash
npx tsx src/scripts/lgp.ts org users comp_abc123 --limit 20
```

### `org add-user`

Add a user to a company with a specified role and group.

**Syntax:**

```bash
lgp org add-user <companyId> --email <email> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<companyId>` | string (positional) | Yes | — | Company ID to add the user to |
| `--email <email>` | string | Yes | — | Email address of the user to add |
| `--user-id <cognitoSub>` | string | No | — | Cognito user sub (resolved from email if omitted) |
| `--role <role>` | string | No | `member` | Role: `owner`, `admin`, `member`, `viewer` |
| `--group <group>` | string | No | `user` | Group: `admin`, `manager`, `user`, `viewer` |

**Example:**

```bash
npx tsx src/scripts/lgp.ts org add-user comp_abc123 \
  --email colleague@acmecorp.com \
  --role member \
  --group user
```

### `org update-user`

Update a user's role, group, or status within a company.

**Syntax:**

```bash
lgp org update-user <userId> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<userId>` | string (positional) | Yes | — | User ID to update |
| `--role <role>` | string | No | — | New role: `owner`, `admin`, `member`, `viewer` |
| `--group <group>` | string | No | — | New group: `admin`, `manager`, `user`, `viewer` |
| `--status <status>` | string | No | — | New status: `active`, `inactive`, `pending` |

**Example:**

```bash
npx tsx src/scripts/lgp.ts org update-user usr_1a2b3c4d-5678-9abc-def0-123456789abc \
  --role admin \
  --group admin \
  --status active
```

### `org remove-user`

Remove a user from a company.

**Syntax:**

```bash
lgp org remove-user <userId>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<userId>` | string (positional) | Yes | — | User ID to remove from the company |

**Example:**

```bash
npx tsx src/scripts/lgp.ts org remove-user usr_1a2b3c4d-5678-9abc-def0-123456789abc
```

---

## fsd

Manage FSD (Full-Stack Demand) pipeline campaigns: create, run, monitor, and manage automated lead generation pipelines.

### `fsd campaigns`

List all FSD campaigns.

**Syntax:**

```bash
lgp fsd campaigns
```

**Flags:** None (uses global options only).

**Example:**

```bash
npx tsx src/scripts/lgp.ts fsd campaigns
```

### `fsd campaign`

Get detailed information for a specific FSD campaign.

**Syntax:**

```bash
lgp fsd campaign <id>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<id>` | string (positional) | Yes | — | Campaign ID to retrieve |

**Example:**

```bash
npx tsx src/scripts/lgp.ts fsd campaign fsd_camp_a1b2c3d4
```

### `fsd create-campaign`

Create a new FSD campaign linking an ICP or direct Apify configuration.

**Syntax:**

```bash
lgp fsd create-campaign --client <clientId> --name <name> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--client <clientId>` | string | Yes | — | Client ID for lead data isolation |
| `--name <name>` | string | Yes | — | Campaign display name |
| `--icp <icpId>` | string | No | — | ICP record ID — resolves Apify config automatically |
| `--actor <apifyActorId>` | string | No | — | Direct Apify actor ID (alternative to `--icp`) |
| `--input <json>` | string | No | — | Apify input JSON (used with `--actor`) |
| `--frequency <freq>` | string | No | `once` | Run frequency: `once`, `daily`, `weekly`, `monthly` |
| `--target <n>` | integer | No | `100` | Target lead count per run |
| `--enrich <bool>` | boolean | No | `false` | Auto-enrich leads after generation |
| `--score <bool>` | boolean | No | `false` | Auto-score leads after enrichment |
| `--send-to <platform>` | string | No | — | Email platform name for delivery |
| `--threshold <n>` | integer | No | — | Qualification score threshold (0–100) |
| `--email-campaign <id>` | string | No | — | Campaign ID on the email platform |

**Example — create with ICP and full automation:**

```bash
npx tsx src/scripts/lgp.ts fsd create-campaign \
  --client cl_9f3a2b7e \
  --name "Q1 Enterprise Outreach" \
  --icp icp_a1b2c3d4-5678-9abc-def0-123456789abc \
  --frequency weekly \
  --target 200 \
  --enrich true \
  --score true \
  --send-to woodpecker \
  --threshold 60 \
  --email-campaign camp-wp-001
```

### `fsd update-campaign`

Update settings on an existing FSD campaign.

**Syntax:**

```bash
lgp fsd update-campaign <id> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<id>` | string (positional) | Yes | — | Campaign ID to update |
| `--name <name>` | string | No | — | New campaign name |
| `--target <n>` | integer | No | — | Target lead count per run |
| `--frequency <freq>` | string | No | — | Run frequency: `once`, `daily`, `weekly`, `monthly` |
| `--active <bool>` | boolean | No | — | Set campaign active status |
| `--enrich <bool>` | boolean | No | — | Enable/disable auto-enrichment after generation |
| `--score <bool>` | boolean | No | — | Enable/disable auto-scoring after enrichment |

**Example:**

```bash
npx tsx src/scripts/lgp.ts fsd update-campaign fsd_camp_a1b2c3d4 \
  --target 300 \
  --frequency weekly \
  --enrich true \
  --score true
```

### `fsd deactivate-campaign`

Soft-delete a campaign by setting `isActive` to false.

**Syntax:**

```bash
lgp fsd deactivate-campaign <id>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<id>` | string (positional) | Yes | — | Campaign ID to deactivate |

**Example:**

```bash
npx tsx src/scripts/lgp.ts fsd deactivate-campaign fsd_camp_a1b2c3d4
```

### `fsd run`

Start an FSD pipeline run. Provide either `--icp` to use an ICP record's Apify config, or `--actor`/`--input` for direct Apify execution.

**Syntax:**

```bash
lgp fsd run --client <clientId> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--client <clientId>` | string | Yes | — | Client ID for lead data isolation |
| `--icp <icpId>` | string | No | — | ICP record ID — resolves `apifyActorId` and `apifyInput` from the ICP automatically |
| `--actor <apifyActorId>` | string | No | — | Direct Apify actor ID (alternative to `--icp`) |
| `--input <json>` | string | No | — | Apify input JSON (used with `--actor`) |
| `--target <n>` | integer | No | `100` | Target number of leads to generate |
| `--enrich` | boolean | No | `false` | Auto-enrich leads after generation |
| `--score` | boolean | No | `false` | Auto-score leads after enrichment |

**Example — ICP-driven run:**

```bash
npx tsx src/scripts/lgp.ts fsd run \
  --client cl_9f3a2b7e \
  --icp icp_a1b2c3d4-5678-9abc-def0-123456789abc \
  --target 200 \
  --enrich \
  --score
```

**Example — direct Apify run (without ICP):**

```bash
npx tsx src/scripts/lgp.ts fsd run \
  --client cl_9f3a2b7e \
  --actor apify/linkedin-sales-navigator \
  --input '{"searchUrl":"https://www.linkedin.com/sales/search/people?query=..."}' \
  --target 150
```

### `fsd status`

Get the current status and per-stage metrics of an FSD pipeline run.

**Syntax:**

```bash
lgp fsd status <pipelineId>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<pipelineId>` | string (positional) | Yes | — | Pipeline run ID to check |

**Example:**

```bash
npx tsx src/scripts/lgp.ts fsd status pipeline_x1y2z3w4
```

---

## maintenance

Manage maintenance items: bug reports and enhancement requests. These commands use the standard API key authentication (not admin key).

### `maintenance bugs list`

List all bug reports.

**Syntax:**

```bash
lgp maintenance bugs list
```

**Flags:** None (uses global options only). Supports `--format json|table`.

**Example:**

```bash
npx tsx src/scripts/lgp.ts maintenance bugs list
npx tsx src/scripts/lgp.ts maintenance bugs list --format table
```

### `maintenance bugs report`

Report a new bug.

**Syntax:**

```bash
lgp maintenance bugs report --desc <description> [--email <email>]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--desc <description>` | string | Yes | — | Description of the bug |
| `--email <email>` | string | No | — | Reporter email address |

**Example:**

```bash
npx tsx src/scripts/lgp.ts maintenance bugs report \
  --desc "Enrichment fails on LinkedIn URLs with special characters" \
  --email developer@acmecorp.com
```

### `maintenance enhancements list`

List all enhancement requests.

**Syntax:**

```bash
lgp maintenance enhancements list
```

**Flags:** None (uses global options only). Supports `--format json|table`.

**Example:**

```bash
npx tsx src/scripts/lgp.ts maintenance enhancements list
npx tsx src/scripts/lgp.ts maintenance enhancements list --format table
```

### `maintenance enhancements request`

Submit a new enhancement request.

**Syntax:**

```bash
lgp maintenance enhancements request --desc <description> [--email <email>]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--desc <description>` | string | Yes | — | Description of the enhancement |
| `--email <email>` | string | No | — | Requester email address |

**Example:**

```bash
npx tsx src/scripts/lgp.ts maintenance enhancements request \
  --desc "Add support for Google Maps leads" \
  --email developer@acmecorp.com
```

---

## pipeline

View pipeline analytics with optional date range filtering.

### `pipeline`

Show pipeline analytics for a date range.

**Syntax:**

```bash
lgp pipeline [--start <date>] [--end <date>]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--start <date>` | string | No | 30 days ago | Start date (ISO format, e.g., `2026-01-01`) |
| `--end <date>` | string | No | today | End date (ISO format, e.g., `2026-02-01`) |

**Behavior:**
- Calls `GET /api/analytics/pipeline` with `startDate` and `endDate` query params
- Defaults to the last 30 days when dates are omitted
- Supports `--format json|table`

**Example:**

```bash
npx tsx src/scripts/lgp.ts pipeline --start 2026-01-01 --end 2026-02-01
npx tsx src/scripts/lgp.ts pipeline --format table
```

---

## campaigns

Manage marketing campaigns: list and create.

### `campaigns list`

List all campaigns.

**Syntax:**

```bash
lgp campaigns list
```

**Flags:** None (uses global options only). Supports `--format json|table`.

**Example:**

```bash
npx tsx src/scripts/lgp.ts campaigns list
npx tsx src/scripts/lgp.ts campaigns list --format table
```

### `campaigns create`

Create a new campaign.

**Syntax:**

```bash
lgp campaigns create --name <name> [--type <type>]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--name <name>` | string | Yes | — | Campaign name |
| `--type <type>` | string | No | `abm` | Campaign type (e.g., `abm`, `outbound`) |

**Behavior:**
- Calls `POST /api/campaigns` with `{name, campaignType: type || 'abm', status: 'active'}`

**Example:**

```bash
npx tsx src/scripts/lgp.ts campaigns create --name "Q3 Enterprise Outreach"
npx tsx src/scripts/lgp.ts campaigns create --name "Q3 Outbound" --type outbound
```

---

## clients

Manage clients: list and create. Clients provide data isolation for leads.

### `clients list`

List all clients with their details.

**Syntax:**

```bash
lgp clients list
```

**Flags:** None (uses global options only). Supports `--format json|table`.

**Table columns (--format table):** `id`, `client_id`, `clientName`

**Example:**

```bash
npx tsx src/scripts/lgp.ts clients list
npx tsx src/scripts/lgp.ts clients list --format table
```

### `clients create`

Create a new client.

**Syntax:**

```bash
lgp clients create --name <name> [--url <url>]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--name <name>` | string | Yes | — | Client display name |
| `--url <url>` | string | No | — | Company website URL |

**Behavior:**
- Calls `POST /api/automation/tables/Client` with `{clientName, companyURL?}`

**Example:**

```bash
npx tsx src/scripts/lgp.ts clients create --name "Acme Corp"
npx tsx src/scripts/lgp.ts clients create --name "Beta Inc" --url "https://beta.io"
```

---

## EpsimoAI Commands

Manage EpsimoAI user activation, profile, credits, and thread usage. All commands pass `X-Epsimo-Token` as an extra header alongside `X-API-Key` (the `apiRequest` function was extended to accept optional `extraHeaders`).

### `epsimo activate`

Activate an EpsimoAI user via email/password or Cognito token exchange.

**Syntax:**

```bash
lgp epsimo activate --email <email> --password <password>
lgp epsimo activate --cognito-token <token>
```

**Flags:**

| Flag | Type | Required | Description |
|------|------|----------|-------------|
| `--email` | string | Yes (login mode) | EpsimoAI email |
| `--password` | string | Yes (login mode) | EpsimoAI password |
| `--cognito-token` | string | Yes (exchange mode) | Cognito ID token |

**Behavior:**
- If `--cognito-token` provided → sends `{ cognitoIdToken }` to activate endpoint
- If `--email` + `--password` provided → sends `{ email, password }`
- If neither → exits with error
- On success, prints the EpsimoAI token with a save warning

**Example:**

```bash
npx tsx src/scripts/lgp.ts epsimo activate --email user@example.com --password secret
npx tsx src/scripts/lgp.ts epsimo activate --cognito-token eyJ...
```

### `epsimo info`

Get EpsimoAI user profile and plan information.

**Syntax:**

```bash
lgp epsimo info --token <epsimoToken>
```

**Flags:**

| Flag | Type | Required | Description |
|------|------|----------|-------------|
| `--token` | string | Yes | EpsimoAI JWT token |

**Table columns (--format table):** `userId`, `email`, `projectId`, `threadCounter`, `threadMax`, `plan`

**Example:**

```bash
npx tsx src/scripts/lgp.ts epsimo info --token eyJ...
npx tsx src/scripts/lgp.ts epsimo info --token eyJ... --format table
```

### `epsimo credits`

Check EpsimoAI credit balance.

**Syntax:**

```bash
lgp epsimo credits --token <epsimoToken>
```

**Flags:**

| Flag | Type | Required | Description |
|------|------|----------|-------------|
| `--token` | string | Yes | EpsimoAI JWT token |

**Table columns (--format table):** `credits`, `threadCounter`, `threadMax`, `lastUpdated`

**Example:**

```bash
npx tsx src/scripts/lgp.ts epsimo credits --token eyJ...
```

### `epsimo purchase`

Purchase additional EpsimoAI credits.

**Syntax:**

```bash
lgp epsimo purchase --token <epsimoToken> --amount <n>
```

**Flags:**

| Flag | Type | Required | Description |
|------|------|----------|-------------|
| `--token` | string | Yes | EpsimoAI JWT token |
| `--amount` | integer | Yes | Number of credits to purchase (positive) |

**Behavior:** Parses `--amount` with `parseInt`, validates > 0 before sending. Sends `{ amount }` body with `X-Epsimo-Token` header.

**Table columns (--format table):** `previousBalance`, `purchasedAmount`, `newBalance`, `transactionId`

**Example:**

```bash
npx tsx src/scripts/lgp.ts epsimo purchase --token eyJ... --amount 10000
```

### `epsimo threads`

Get detailed thread usage information.

**Syntax:**

```bash
lgp epsimo threads --token <epsimoToken>
```

**Flags:**

| Flag | Type | Required | Description |
|------|------|----------|-------------|
| `--token` | string | Yes | EpsimoAI JWT token |

**Table columns (--format table):** `threadCounter`, `threadMax`, `remainingThreads`, `usagePercentage`, `plan`

**Note:** `plan` is derived from `threadMax` only (without `stripeClientId`), so may differ from `epsimo info` for users with a Stripe subscription and low thread max.

**Example:**

```bash
npx tsx src/scripts/lgp.ts epsimo threads --token eyJ...
npx tsx src/scripts/lgp.ts epsimo threads --token eyJ... --format table
```


---

## generate

Trigger, monitor, and schedule multi-provider lead generation. Supports ICP-based runs (resolve provider config from an ICP record) and direct provider runs (specify provider and config inline).

### `generate from-icp`

Trigger lead generation from an ICP profile. The ICP's `providerType` determines which provider is used (defaults to `apify`).

**Syntax:**

```bash
lgp generate from-icp --icp <icpId> --client <clientId> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--icp <icpId>` | string | Yes | — | ICP record ID |
| `--client <clientId>` | string | Yes | — | Client ID for lead data isolation |
| `--max-leads <n>` | integer | No | ICP default | Override max leads per run |
| `--save-to-source` | boolean | No | `true` | Save leads to SourceLeads table |
| `--save-to-enrich` | boolean | No | `false` | Save leads to EnrichLeads table |
| `--provider <name>` | string | No | ICP default | Override provider: `apify`, `vayne`, `generic` |

**Example:**

```bash
npx tsx src/scripts/lgp.ts generate from-icp \
  --icp icp_a1b2c3d4-5678-9abc-def0-123456789abc \
  --client cl_9f3a2b7e \
  --max-leads 200 \
  --save-to-enrich
```

**Expected output (json):**

```json
{
  "success": true,
  "runId": "trigger-run-id",
  "searchHistoryId": "sh-uuid",
  "status": "initiated"
}
```

### `generate direct`

Trigger lead generation by specifying a provider and configuration directly (without an ICP).

**Syntax:**

```bash
lgp generate direct --provider <name> --config <json> --client <clientId> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--provider <name>` | string | Yes | — | Provider name: `apify`, `vayne`, `generic` |
| `--config <json>` | string | Yes | — | JSON string with provider-specific configuration |
| `--client <clientId>` | string | Yes | — | Client ID for lead data isolation |
| `--sales-nav-url <url>` | string | No | — | LinkedIn Sales Navigator URL (shorthand for Vayne; injected into `providerConfig.salesNavigatorUrl`) |

**Example — Vayne with Sales Navigator URL:**

```bash
npx tsx src/scripts/lgp.ts generate direct \
  --provider vayne \
  --config '{"maxLeads":100}' \
  --client cl_9f3a2b7e \
  --sales-nav-url "https://www.linkedin.com/sales/search/people?query=..."
```

**Example — Generic HTTP provider:**

```bash
npx tsx src/scripts/lgp.ts generate direct \
  --provider generic \
  --config '{"endpointUrl":"https://api.example.com/scrape","method":"POST","bodyTemplate":{"query":"SaaS","limit":50},"responseMapping":{"firstName":"first_name","email":"contact_email"}}' \
  --client cl_9f3a2b7e
```

### `generate status`

Check the status of a lead generation run.

**Syntax:**

```bash
lgp generate status <runId>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<runId>` | string (positional) | Yes | — | Run ID from the trigger response |

**Example:**

```bash
npx tsx src/scripts/lgp.ts generate status run_abc123def456
```

**Expected output (json):**

```json
{
  "success": true,
  "runId": "run_abc123def456",
  "status": "RUNNING",
  "progress": 45,
  "totalLeadsFound": 67,
  "totalLeadsSaved": 45,
  "totalLeadsFailed": 2,
  "providerType": "apify",
  "searchHistoryId": "sh-uuid"
}
```

**Table columns (--format table):** `runId`, `status`, `progress`, `totalLeadsFound`, `totalLeadsSaved`, `providerType`

### `generate history`

List past lead generation runs with optional filters.

**Syntax:**

```bash
lgp generate history [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--client <clientId>` | string | No | — | Filter by client ID |
| `--icp <icpId>` | string | No | — | Filter by ICP ID |
| `--status <status>` | string | No | — | Filter by status: `initiated`, `running`, `completed`, `failed` |
| `--limit <n>` | integer | No | 20 | Maximum records to return |

**Example:**

```bash
npx tsx src/scripts/lgp.ts generate history --client cl_9f3a2b7e --status completed --limit 10
```

**Table columns (--format table):** `id`, `searchName`, `status`, `providerType`, `totalLeadsFound`, `totalLeadsSaved`, `createdAt`

### `generate schedule create`

Create an FSD schedule for recurring lead generation.

**Syntax:**

```bash
lgp generate schedule create --icp <icpId> --client <clientId> --frequency <freq> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--icp <icpId>` | string | Yes | — | ICP record ID |
| `--client <clientId>` | string | Yes | — | Client ID for lead isolation |
| `--frequency <freq>` | string | Yes | — | Preset (`daily`, `weekly`, `biweekly`, `monthly`) or cron expression |
| `--max-leads <n>` | integer | No | 100 | Max leads per scheduled run |

**Example:**

```bash
npx tsx src/scripts/lgp.ts generate schedule create \
  --icp icp_a1b2c3d4-5678-9abc-def0-123456789abc \
  --client cl_9f3a2b7e \
  --frequency weekly \
  --max-leads 150
```

**Expected output (json):**

```json
{
  "success": true,
  "scheduleId": "sched-uuid",
  "nextRunAt": "2025-01-22T08:00:00Z",
  "frequency": "weekly"
}
```

### `generate schedule list`

List all FSD schedules for the company.

**Syntax:**

```bash
lgp generate schedule list
```

**Flags:** None (uses global options only).

**Example:**

```bash
npx tsx src/scripts/lgp.ts generate schedule list --format table
```

**Table columns (--format table):** `id`, `icpName`, `clientName`, `frequencyPreset`, `enabled`, `status`, `nextRunAt`, `totalRuns`

### `generate schedule pause`

Pause an active FSD schedule without deleting it.

**Syntax:**

```bash
lgp generate schedule pause <scheduleId>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<scheduleId>` | string (positional) | Yes | — | Schedule ID to pause |

**Example:**

```bash
npx tsx src/scripts/lgp.ts generate schedule pause sched-uuid
```

### `generate schedule resume`

Resume a paused FSD schedule.

**Syntax:**

```bash
lgp generate schedule resume <scheduleId>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<scheduleId>` | string (positional) | Yes | — | Schedule ID to resume |

**Example:**

```bash
npx tsx src/scripts/lgp.ts generate schedule resume sched-uuid
```

### `generate schedule delete`

Delete an FSD schedule and cancel any pending runs.

**Syntax:**

```bash
lgp generate schedule delete <scheduleId>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `<scheduleId>` | string (positional) | Yes | — | Schedule ID to delete |

**Example:**

```bash
npx tsx src/scripts/lgp.ts generate schedule delete sched-uuid
```

---

## admin

Manage platform administration: companies, members, users, views, clients, backups, and organisation trees. All admin commands require the `LGP_ADMIN_KEY` environment variable or `--admin-key` flag. The CLI sends `X-Admin-Key` header on every admin request for authentication.

### Environment Variables

| Variable | Description | Required |
|----------|-------------|----------|
| `LGP_ADMIN_KEY` | Admin secret key for `X-Admin-Key` header | Yes (for all admin commands) |

If `LGP_ADMIN_KEY` is not set and `--admin-key` is not provided, the CLI exits with an error message instructing the user to set the variable.

---

### `admin org-tree`

Display the organisation tree for a company showing members, roles, client access, and views. Shorthand for `admin companies org-tree`.

**Syntax:**

```bash
lgp admin org-tree --company <id> [--detailed] [--json]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--company <id>` | string | Yes | — | Company ID to display org tree for |
| `--detailed` | boolean | No | `false` | Show full view lists, client names, menuAccess, and permissions for each member |
| `--json` | boolean | No | `false` | Output raw JSON from the org-tree API instead of ASCII tree |

**Behavior:**
- Calls `GET /api/admin/companies/<id>/org-tree` using `adminApiRequest`
- Sorts members by role priority: owner > admin > member > viewer
- Renders ASCII tree with Unicode box-drawing characters (├──, └──, │)
- Basic mode shows `email [role, group]`, `Client Access: <mode>`, `Views: <count>`
- Detailed mode additionally shows menu access and permissions for each member

**Example (default):**

```bash
npx tsx src/scripts/lgp.ts admin org-tree --company company-abc123
```

**Expected output (default):**

```
Acme Corp
├── owner@acme.com [owner, admin]
│   ├── Client Access: all
│   └── Views: 6 views
├── user1@acme.com [member, user]
│   ├── Client Access: specific (2 clients)
│   └── Views: 3 views
└── user2@acme.com [viewer, viewer]
    ├── Client Access: all
    └── Views: 1 view
```

**Example (detailed):**

```bash
npx tsx src/scripts/lgp.ts admin org-tree --company company-abc123 --detailed
```

**Expected output (detailed):**

```
Acme Corp
├── owner@acme.com [owner, admin]
│   ├── Client Access: all
│   ├── Views: full, prod2, focus, marketing, sales, analyst
│   ├── Menu Access: (none)
│   └── Permissions: (none)
└── user1@acme.com [member, user]
    ├── Client Access: specific
    │   ├── Q1 Campaign (client-abc)
    │   └── Q2 Outbound (client-def)
    ├── Views: prod2, focus
    ├── Menu Access: dashboard, leads
    └── Permissions: canExport=true, canDelete=false
```

---

### `admin companies list`

List all companies with owner details, member counts, and client counts.

**Syntax:**

```bash
lgp admin companies list [--json]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--json` | boolean | No | `false` | Output raw JSON instead of formatted table |

**Table columns:** `ID`, `Name`, `Owner Email`, `Members`, `Clients`, `Created`

**Example:**

```bash
lgp admin companies list
```

**Expected output (table):**

```
ID                                    Name           Owner Email          Members  Clients  Created
------------------------------------  -------------  -------------------  -------  -------  ----------
company-abc123                        Acme Corp      owner@acme.com       5        3        2026-01-15
company-def456                        Beta Inc       admin@beta.io        2        1        2026-02-01
```

---

### `admin companies show`

Show detailed information for a specific company including members and data counts.

**Syntax:**

```bash
lgp admin companies show --id <companyId> [--json]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--id <companyId>` | string | Yes | — | Company ID to show details for |
| `--json` | boolean | No | `false` | Output raw JSON instead of formatted table |

**Example:**

```bash
lgp admin companies show --id company-abc123
```

---

### `admin companies members list`

List all members of a specific company.

**Syntax:**

```bash
lgp admin companies members list --company <id> [--json]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--company <id>` | string | Yes | — | Company ID to list members for |
| `--json` | boolean | No | `false` | Output raw JSON instead of formatted table |

**Example:**

```bash
lgp admin companies members list --company company-abc123
```

---

### `admin companies members add`

Add a new member to a company.

**Syntax:**

```bash
lgp admin companies members add --company <id> --email <email> --role <role> [--json]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--company <id>` | string | Yes | — | Company ID to add the member to |
| `--email <email>` | string | Yes | — | Email address of the user to add |
| `--role <role>` | string | Yes | — | Role: `owner`, `admin`, `member`, `viewer` |
| `--json` | boolean | No | `false` | Output raw JSON instead of formatted output |

**Example:**

```bash
lgp admin companies members add --company company-abc123 --email newuser@acme.com --role member
```

---

### `admin companies members update`

Update a company member's role, client access, and organisation rights.

**Syntax:**

```bash
lgp admin companies members update --company <id> --user <userId> [options] [--json]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--company <id>` | string | Yes | — | Company ID |
| `--user <userId>` | string | Yes | — | User ID of the member to update |
| `--role <role>` | string | No | — | New role: `owner`, `admin`, `member`, `viewer` |
| `--access-mode <mode>` | string | No | — | Client access mode: `all`, `own`, `specific` |
| `--client-ids <ids>` | string | No | — | Comma-separated client IDs (required when access-mode is `specific`) |
| `--group <group>` | string | No | — | Organisation group: `admin`, `manager`, `user`, `viewer` |
| `--menu-access <json>` | string | No | — | JSON array of menu keys (e.g., `'["dashboard","leads"]'`) |
| `--json` | boolean | No | `false` | Output raw JSON instead of formatted output |

**Example:**

```bash
lgp admin companies members update --company company-abc123 --user usr-456 \
  --role admin --access-mode specific --client-ids "client-1,client-2" --group manager
```

---

### `admin companies members remove`

Remove a member from a company. Cannot remove the company owner.

**Syntax:**

```bash
lgp admin companies members remove --company <id> --user <userId> [--json]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--company <id>` | string | Yes | — | Company ID |
| `--user <userId>` | string | Yes | — | User ID of the member to remove |
| `--json` | boolean | No | `false` | Output raw JSON instead of formatted output |

**Example:**

```bash
lgp admin companies members remove --company company-abc123 --user usr-456
```

---

### `admin companies clients list`

List all clients belonging to a specific company.

**Syntax:**

```bash
lgp admin companies clients list --company <id> [--json]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--company <id>` | string | Yes | — | Company ID to list clients for |
| `--json` | boolean | No | `false` | Output raw JSON instead of formatted table |

**Example:**

```bash
lgp admin companies clients list --company company-abc123
```

---

### `admin companies org-tree`

Display the organisation tree for a company showing members, roles, client access, and views.

**Syntax:**

```bash
lgp admin companies org-tree --company <id> [--detailed] [--json]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--company <id>` | string | Yes | — | Company ID to display org tree for |
| `--detailed` | boolean | No | `false` | Show full view lists, client names, menuAccess, and permissions for each member |
| `--json` | boolean | No | `false` | Output raw JSON from the org-tree API instead of ASCII tree |

**Example (default):**

```bash
lgp admin companies org-tree --company company-abc123
```

**Expected output (default):**

```
Acme Corp
├── owner@acme.com [owner, admin]
│   ├── Client Access: all
│   └── Views: 6 views
├── user1@acme.com [member, user]
│   ├── Client Access: specific (2 clients)
│   └── Views: 3 views
└── user2@acme.com [viewer, viewer]
    ├── Client Access: all
    └── Views: 1 view
```

**Example (detailed):**

```bash
lgp admin companies org-tree --company company-abc123 --detailed
```

**Expected output (detailed):**

```
Acme Corp
├── owner@acme.com [owner, admin]
│   ├── Client Access: all
│   ├── Views: full, prod2, focus, marketing, sales, analyst
│   ├── Menu Access: (none)
│   └── Permissions: (none)
├── user1@acme.com [member, user]
│   ├── Client Access: specific
│   │   ├── Q1 Campaign (client-abc)
│   │   └── Q2 Outbound (client-def)
│   ├── Views: prod2, focus
│   ├── Menu Access: dashboard, leads
│   └── Permissions: canExport=true, canDelete=false
└── user2@acme.com [viewer, viewer]
    ├── Client Access: all
    ├── Views: prod2
    ├── Menu Access: (none)
    └── Permissions: (none)
```

---

### `admin users list`

List all Cognito users with roles and view assignments. Supports search filtering.

**Syntax:**

```bash
lgp admin users list [--search <term>] [--json]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--search <term>` | string | No | — | Filter users by email substring (case-insensitive) |
| `--json` | boolean | No | `false` | Output raw JSON instead of formatted table |

**Table columns:** `Username`, `Email`, `Role`, `Views`, `Status`, `Master Admin`

**Example:**

```bash
lgp admin users list --search acme
```

---

### `admin users set-role`

Set a user's role in Cognito.

**Syntax:**

```bash
lgp admin users set-role --username <username> --role <role> [--json]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--username <username>` | string | Yes | — | Cognito username |
| `--role <role>` | string | Yes | — | Role ID: `admin`, `companyAdmin`, `marketing`, `sales`, `analyst`, `viewer`, `custom` |
| `--json` | boolean | No | `false` | Output raw JSON instead of formatted output |

**Example:**

```bash
lgp admin users set-role --username user-abc123 --role marketing
```

---

### `admin users set-views`

Set a user's allowed views in Cognito.

**Syntax:**

```bash
lgp admin users set-views --username <username> --views <views> [--json]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--username <username>` | string | Yes | — | Cognito username |
| `--views <views>` | string | Yes | — | Comma-separated view IDs (e.g., `full,prod2,focus`) |
| `--json` | boolean | No | `false` | Output raw JSON instead of formatted output |

**Example:**

```bash
lgp admin users set-views --username user-abc123 --views full,prod2,focus
```

---

### `admin views list`

List all available view configurations and role definitions.

**Syntax:**

```bash
lgp admin views list [--json]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--json` | boolean | No | `false` | Output raw JSON instead of formatted tables |

**Example:**

```bash
lgp admin views list
```

---

### `admin clients list`

List all clients across all companies with company name resolution.

**Syntax:**

```bash
lgp admin clients list [--json]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--json` | boolean | No | `false` | Output raw JSON instead of formatted table |

**Example:**

```bash
lgp admin clients list
```


---

### `admin backup tables`

List all DynamoDB tables, optionally filtered by name prefix. Useful for discovering Amplify-managed tables before creating backups.

**Syntax:**

```bash
lgp admin backup tables [--prefix PREFIX] [--json]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--prefix <PREFIX>` | string | No | — | Filter table names by prefix string |
| `--json` | boolean | No | `false` | Output raw JSON instead of formatted table |

**Example:**

```bash
lgp admin backup tables
lgp admin backup tables --prefix Company
lgp admin backup tables --json
```

**Expected output (table):**

```
Table Name
------------------------------------
Company-abc123def
CompanyUser-abc123def
Client-abc123def
EnrichLeads-abc123def
SourceLeads-abc123def
...
Found 25 tables
```

**Expected output (json):**

```json
{
  "tables": ["Company-abc123def", "CompanyUser-abc123def", "Client-abc123def"],
  "count": 3
}
```

---

### `admin backup create`

Create an on-demand backup for a single table or all discovered tables.

**Syntax:**

```bash
lgp admin backup create --table <TABLE> [--json]
lgp admin backup create --all [--json]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--table <TABLE>` | string | One of `--table` or `--all` | — | DynamoDB table name to back up |
| `--all` | boolean | One of `--table` or `--all` | `false` | Back up all discovered tables |
| `--json` | boolean | No | `false` | Output raw JSON instead of formatted output |

**Backup naming convention:** `<tableName>-<YYYYMMDD>-<HHmmss>` (UTC)

**Example — single table:**

```bash
lgp admin backup create --table Company-abc123def
```

**Expected output (single table):**

```json
{
  "backup": {
    "backupArn": "arn:aws:dynamodb:us-east-1:123456789012:table/Company-abc123def/backup/01234567890123-abcdef",
    "tableName": "Company-abc123def",
    "backupName": "Company-abc123def-20260315-143022",
    "backupStatus": "CREATING",
    "createdAt": "2026-03-15T14:30:22.000Z"
  }
}
```

**Example — all tables:**

```bash
lgp admin backup create --all
```

**Expected output (all tables, table format):**

```
Creating backups for 25 tables...
✓ Company-abc123          Company-abc123-20260315-143022
✓ CompanyUser-abc123      CompanyUser-abc123-20260315-143023
✗ SomeTable-xyz           Table not found
...
Summary: 24 succeeded, 1 failed
```

---

### `admin backup list`

List existing backups with optional table name and status filters.

**Syntax:**

```bash
lgp admin backup list [--table TABLE] [--status STATUS] [--json]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--table <TABLE>` | string | No | — | Filter backups by table name |
| `--status <STATUS>` | string | No | — | Filter by status: `AVAILABLE`, `CREATING`, `DELETED` |
| `--json` | boolean | No | `false` | Output raw JSON instead of formatted table |

**Example:**

```bash
lgp admin backup list
lgp admin backup list --table Company-abc123def --status AVAILABLE
lgp admin backup list --json
```

**Expected output (table):**

```
ARN (truncated)          Table              Status     Size       Created
-----------------------  -----------------  ---------  ---------  ----------
...abc123/backup-001     Company-abc123     AVAILABLE  1.0 MB     2026-03-15
...abc123/backup-002     CompanyUser-abc    AVAILABLE  512.0 KB   2026-03-15
```

---

### `admin backup describe`

Get detailed information about a specific backup by ARN.

**Syntax:**

```bash
lgp admin backup describe --arn <ARN> [--json]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--arn <ARN>` | string | Yes | — | Full backup ARN |
| `--json` | boolean | No | `false` | Output raw JSON instead of key-value pairs |

**Example:**

```bash
lgp admin backup describe --arn arn:aws:dynamodb:us-east-1:123456789012:table/Company-abc123/backup/01234567890123-abcdef
```

**Expected output (json):**

```json
{
  "backup": {
    "backupArn": "arn:aws:dynamodb:us-east-1:...",
    "tableName": "Company-abc123",
    "tableId": "abc123-def456",
    "backupStatus": "AVAILABLE",
    "backupType": "USER",
    "backupSizeBytes": 1048576,
    "itemCount": 5000,
    "createdAt": "2026-03-15T14:30:22.000Z",
    "expiryDate": null
  }
}
```

---

### `admin backup delete`

Delete a specific backup by ARN.

**Syntax:**

```bash
lgp admin backup delete --arn <ARN> [--json]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--arn <ARN>` | string | Yes | — | Full backup ARN to delete |
| `--json` | boolean | No | `false` | Output raw JSON instead of formatted confirmation |

**Example:**

```bash
lgp admin backup delete --arn arn:aws:dynamodb:us-east-1:123456789012:table/Company-abc123/backup/01234567890123-abcdef
```

**Expected output (json):**

```json
{
  "deleted": {
    "backupArn": "arn:aws:dynamodb:us-east-1:...",
    "tableName": "Company-abc123"
  }
}
```

**Error cases:**
- Backup not found → 404
- Backup still in CREATING status → 400 "Cannot delete a backup that is still being created"

---

### `admin backup restore`

Restore a table from a backup to a new target table name.

**Syntax:**

```bash
lgp admin backup restore --arn <ARN> --target-table <NAME> [--json]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--arn <ARN>` | string | Yes | — | Full backup ARN to restore from |
| `--target-table <NAME>` | string | Yes | — | Name for the restored table (must not already exist) |
| `--json` | boolean | No | `false` | Output raw JSON instead of formatted output |

**Example:**

```bash
lgp admin backup restore \
  --arn arn:aws:dynamodb:us-east-1:123456789012:table/Company-abc123/backup/01234567890123-abcdef \
  --target-table Company-abc123-restored-20260315
```

**Expected output (json):**

```json
{
  "restored": {
    "targetTableName": "Company-abc123-restored-20260315",
    "tableArn": "arn:aws:dynamodb:us-east-1:...",
    "tableStatus": "CREATING",
    "sourceBackupArn": "arn:aws:dynamodb:us-east-1:..."
  }
}
```

**Error cases:**
- Backup not found → 404
- Target table already exists → 409

---

### `admin backup pitr-status`

Check Point-in-Time Recovery (PITR) status for one or all tables.

**Syntax:**

```bash
lgp admin backup pitr-status [--table TABLE] [--json]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--table <TABLE>` | string | No | — | Specific table to check; if omitted, checks all tables |
| `--json` | boolean | No | `false` | Output raw JSON instead of formatted table |

**Example:**

```bash
lgp admin backup pitr-status
lgp admin backup pitr-status --table Company-abc123def
lgp admin backup pitr-status --json
```

**Expected output (table):**

```
Table Name               PITR     Earliest Restore     Latest Restore
-----------------------  -------  -------------------  -------------------
Company-abc123           Enabled  2026-03-10 00:00     2026-03-15 14:30
CompanyUser-abc123       Disabled -                    -
```

---

### `admin backup pitr-enable`

Enable Point-in-Time Recovery on a specific table.

**Syntax:**

```bash
lgp admin backup pitr-enable --table <TABLE>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--table <TABLE>` | string | Yes | — | DynamoDB table name to enable PITR on |

**Example:**

```bash
lgp admin backup pitr-enable --table Company-abc123def
```

**Expected output:**

```json
{
  "tableName": "Company-abc123def",
  "pitrEnabled": true,
  "message": "PITR enabled successfully"
}
```

---

### `admin backup pitr-disable`

Disable Point-in-Time Recovery on a specific table.

**Syntax:**

```bash
lgp admin backup pitr-disable --table <TABLE>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--table <TABLE>` | string | Yes | — | DynamoDB table name to disable PITR on |

**Example:**

```bash
lgp admin backup pitr-disable --table Company-abc123def
```

**Expected output:**

```json
{
  "tableName": "Company-abc123def",
  "pitrEnabled": false,
  "message": "PITR disabled successfully"
}
```


---

## account-analysis

Company-level lead analytics: group leads by company, compute aggregate metrics, and export results. All subcommands default to `--format table` (unlike the global `json` default).

### `account-analysis list`

List company groups with sorting and filtering.

**Syntax:**

```bash
lgp account-analysis list --client <ID> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--client <ID>` | string | Yes | — | Client ID to analyze |
| `--sort <field>` | string | No | `count` | Sort field: `count`, `avg_score`, `total_score` |
| `--order <dir>` | string | No | `desc` | Sort direction: `asc`, `desc` |
| `--limit <n>` | integer | No | all | Return top N companies |
| `--min-leads <n>` | integer | No | — | Exclude companies with fewer leads |
| `--format <fmt>` | string | No | `table` | Output format: `json` or `table` |
| `--no-cache` | boolean | No | `false` | Bypass local cache |
| `--refresh` | boolean | No | `false` | Invalidate cache and fetch fresh data |

**Table columns:** Company Name, Domain, Lead Count, Avg Score, Total Score

**Example:**

```bash
npx tsx src/scripts/lgp.ts account-analysis list \
  --client cl_9f3a2b7e \
  --sort avg_score \
  --order desc \
  --min-leads 3
```

---

### `account-analysis analyze`

Detailed metrics for all companies or a single company.

**Syntax:**

```bash
lgp account-analysis analyze --client <ID> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--client <ID>` | string | Yes | — | Client ID to analyze |
| `--company <name>` | string | No | — | Specific company name (case-insensitive) |
| `--limit <n>` | integer | No | all | Return top N companies |
| `--format <fmt>` | string | No | `table` | Output format: `json` or `table` |
| `--no-cache` | boolean | No | `false` | Bypass local cache |
| `--refresh` | boolean | No | `false` | Invalidate cache and fetch fresh data |

**Without `--company`:** Table with columns: Company, Leads, Avg Score, Median, Max, Min, Velocity, Champion

**With `--company`:** Detailed key-value format with score stats, status distribution percentages, engagement velocity, and champion lead details.

**Example — all companies:**

```bash
npx tsx src/scripts/lgp.ts account-analysis analyze --client cl_9f3a2b7e
```

**Example — single company:**

```bash
npx tsx src/scripts/lgp.ts account-analysis analyze \
  --client cl_9f3a2b7e \
  --company "Acme Corp"
```

---

### `account-analysis export`

Export analysis results to CSV or JSON file (or stdout).

**Syntax:**

```bash
lgp account-analysis export --client <ID> --format <csv|json> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--client <ID>` | string | Yes | — | Client ID to analyze |
| `--format <fmt>` | string | Yes | — | Export format: `csv` or `json` |
| `--output <path>` | string | No | stdout | File path to write output to |
| `--no-cache` | boolean | No | `false` | Bypass local cache |
| `--refresh` | boolean | No | `false` | Invalidate cache and fetch fresh data |

**Example — export CSV to file:**

```bash
npx tsx src/scripts/lgp.ts account-analysis export \
  --client cl_9f3a2b7e \
  --format csv \
  --output ./company-analysis.csv
```

**Example — export JSON to stdout:**

```bash
npx tsx src/scripts/lgp.ts account-analysis export \
  --client cl_9f3a2b7e \
  --format json
```

---

### `account-analysis cache-clear`

Clear the local ABLA cache for a specific client or all clients.

**Syntax:**

```bash
lgp account-analysis cache-clear [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--client <ID>` | string | No | — | Clear cache for a specific client (omit to clear all) |

**Example:**

```bash
npx tsx src/scripts/lgp.ts account-analysis cache-clear --client cl_9f3a2b7e
```

**Cache details:**
- Location: `~/.leadgenius/abla-cache.json`
- TTL: 15 minutes
- Use `--no-cache` on any subcommand to bypass cache for a single request
- Use `--refresh` to invalidate and re-fetch

---

## shares

Manage shared CRM/SDR view links: list, create, extend expiration, revoke, and reactivate.

### `shares list`

List shared links with optional status and client filters.

**Syntax:**

```bash
lgp shares list [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--status <status>` | string | No | `all` | Filter: `active`, `revoked`, `expired`, `all` |
| `--client <id>` | string | No | — | Filter by client ID |
| `--limit <n>` | integer | No | `50` | Maximum results |

**Example:**

```bash
npx tsx src/scripts/lgp.ts shares list --status active
npx tsx src/scripts/lgp.ts shares list --status expired --format table
```

### `shares get`

Get details for a specific shared link.

**Syntax:**

```bash
lgp shares get <id>
```

**Example:**

```bash
npx tsx src/scripts/lgp.ts shares get sv_abc123
```

### `shares create`

Create a new shared link.

**Syntax:**

```bash
lgp shares create [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--client <id>` | string | No | — | Client ID to scope the shared view |
| `--view-type <type>` | string | No | `sdr` | View type: `sdr` or `crm` |
| `--allow-edit` | boolean | No | `false` | Allow recipients to edit lead status/notes |
| `--days <n>` | integer | No | `7` | Expiration in days (1-365) |

**Example:**

```bash
npx tsx src/scripts/lgp.ts shares create --view-type crm --days 30 --allow-edit
npx tsx src/scripts/lgp.ts shares create --client cl_9f3a2b7e --days 14
```

### `shares extend`

Extend the expiration of an existing shared link.

**Syntax:**

```bash
lgp shares extend <id> --days <n>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--days <n>` | integer | Yes | — | Additional days to add (1-365) |

**Example:**

```bash
npx tsx src/scripts/lgp.ts shares extend sv_abc123 --days 30
```

### `shares set-expiry`

Set an explicit expiration date on a shared link.

**Syntax:**

```bash
lgp shares set-expiry <id> --date <iso>
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--date <iso>` | string | Yes | — | New expiration date (ISO 8601 format) |

**Example:**

```bash
npx tsx src/scripts/lgp.ts shares set-expiry sv_abc123 --date 2026-06-30T00:00:00.000Z
```

### `shares revoke`

Revoke (disable) a shared link. The link URL will stop working immediately.

**Syntax:**

```bash
lgp shares revoke <id>
```

**Example:**

```bash
npx tsx src/scripts/lgp.ts shares revoke sv_abc123
```

### `shares reactivate`

Re-enable a previously revoked shared link. Optionally extend its expiration.

**Syntax:**

```bash
lgp shares reactivate <id> [options]
```

**Flags:**

| Flag | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| `--days <n>` | integer | No | — | Also extend expiration by N days |

**Example:**

```bash
npx tsx src/scripts/lgp.ts shares reactivate sv_abc123 --days 14
```
