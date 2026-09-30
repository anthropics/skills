# LeadGenius Pro — CLI & Automation API

A comprehensive skill for operating the LeadGenius Pro Automation API and the `lgp` CLI tool. Covers the full lifecycle of B2B lead management — from ICP definition and automated lead generation through enrichment, scoring, qualification, and email delivery via the FSD (Full-Stack Demand) pipeline.

## Table of Contents

- [Overview](#overview)
- [Installation & Setup](#installation--setup)
- [Authentication](#authentication)
- [API Endpoint Groups](#api-endpoint-groups)
  - [Auth](#auth)
  - [Leads](#leads)
  - [Tasks (Background Processing)](#tasks-background-processing)
  - [Territory Companies](#territory-companies)
  - [Webhook Events](#webhook-events)
  - [Users](#users)
  - [Organizations](#organizations)
  - [Cognito (User Pool)](#cognito-user-pool)
  - [Tables (Generic CRUD)](#tables-generic-crud)
  - [Email Platforms](#email-platforms)
  - [FSD Pipeline](#fsd-pipeline)
  - [EpsimoAI](#epsimoai)
- [CLI Command Reference](#cli-command-reference)
- [Business Workflows](#business-workflows)
- [Business Use Cases](#business-use-cases)
- [Error Handling](#error-handling)
- [Prerequisites Checklist](#prerequisites-checklist)
- [Reference Files](#reference-files)

---

## Overview

LeadGenius Pro is a B2B lead management and enrichment platform. The Automation API exposes the full platform functionality via REST endpoints, and the `lgp` CLI wraps those endpoints for terminal-based workflows.

The platform pipeline:

```
Source Leads → Import → Enrich → Score → Qualify → Deliver to Email Platform
```

The FSD (Full-Stack Demand) pipeline automates this end-to-end:

```
ICP Definition → Apify Lead Generation → Enrichment → SDR AI Scoring → Qualification → Email Delivery
```

**Base URL:** `https://api.leadgenius.app`

All API endpoints live under `/api/automation/`.

---

## Installation & Setup

The CLI runs via `npx tsx` (TypeScript execution) — no separate installation required:

```bash
npx tsx src/scripts/lgp.ts <command> [options]
```

### Environment Variables

| Variable | Description | Default |
|----------|-------------|---------|
| `LGP_API_KEY` | API key with `lgp_` prefix | — (required) |
| `LGP_ADMIN_KEY` | Admin key for admin commands | — (required for `admin` commands) |
| `LGP_URL` | Base URL of the LeadGenius API | `http://localhost:3000` |

```bash
export LGP_API_KEY="lgp_your_key_here"
export LGP_ADMIN_KEY="your_admin_key_here"
export LGP_URL="https://api.leadgenius.app"
```

### Global CLI Options

| Option | Default | Description |
|--------|---------|-------------|
| `--api-key <key>` | `LGP_API_KEY` env | Override API key |
| `--admin-key <key>` | `LGP_ADMIN_KEY` env | Override admin key |
| `--url <url>` | `LGP_URL` env | Override base URL |
| `--format <fmt>` | `json` | Output: `json` or `table` |

---

## Authentication

Every request requires an `X-API-Key` header:

```
X-API-Key: lgp_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
```

- Keys are prefixed with `lgp_` and tied to a specific company
- The key determines `company_id`, `owner` identity, and rate limits
- Keys are created via `POST /api/automation/users/provision` — the plain-text key is returned only once
- Test your key: `GET /api/automation/auth/test`

### Rate Limits

| Window | Limit |
|--------|-------|
| Per minute | 60 requests |
| Per hour | 1,000 requests |
| Per day | 10,000 requests |

---

## API Endpoint Groups

### Auth

| Method | Endpoint | Description |
|--------|----------|-------------|
| `GET` | `/api/automation/auth/test` | Verify API key validity, returns owner/company/keyId |

```bash
lgp auth test
```

---

### Leads

Full lead lifecycle: list, get, import, search, deduplicate, transfer, and engagement tracking.

| Method | Endpoint | Description |
|--------|----------|-------------|
| `GET` | `/api/automation/leads` | List leads by `client_id` with field selection and pagination |
| `GET` | `/api/automation/leads/{id}` | Get single lead (100+ fields) |
| `POST` | `/api/automation/leads/import` | Import leads (single or batch up to 500) |
| `GET` | `/api/automation/leads/search` | Search by email, name, companyUrl, linkedinUrl |
| `POST` | `/api/automation/leads/deduplicate` | Find duplicate groups by match fields |
| `POST` | `/api/automation/leads/deduplicate/resolve` | Merge duplicates into a keep lead |
| `POST` | `/api/automation/leads/transfer` | Transfer leads between clients with dedup detection |
| `GET` | `/api/automation/leads/{id}/activities` | Get engagement history |
| `POST` | `/api/automation/leads/{id}/activities` | Log engagement activities (single or batch) |
| `POST` | `/api/automation/leads/validate-ownership` | Scan for orphaned/mismatched leads |

**Key behaviors:**
- `owner` and `company_id` are auto-set from API key on import
- Cross-client duplicate detection by email/linkedinUrl (warning only)
- Batch import max: 500 leads
- Field selection: pass `fields=email,companyName,aiLeadScore` to return only those fields
- Pagination via `nextToken`

**Deduplication match fields:**

| Field | Confidence |
|-------|------------|
| `email` | high |
| `linkedinUrl` | medium |
| `fullName+companyName` | low |

**Engagement activity types:** `linkedin_connection_sent`, `linkedin_connection_accepted`, `linkedin_message_sent`, `linkedin_message_received`, `linkedin_profile_viewed`, `email_sent`, `email_opened`, `email_clicked`, `email_answered`, `email_bounced`, `call_completed`, `call_no_answer`, `meeting_scheduled`, `meeting_completed`, `form_submitted`, `website_visited`, `content_downloaded`, `demo_requested`, `proposal_sent`, `contract_signed`, `custom`

**Engagement score weights (time-decayed, capped at 100):**

| Activity | Points |
|----------|--------|
| `contract_signed`, `meeting_completed` | 30 |
| `meeting_scheduled`, `demo_requested` | 25 |
| `email_answered`, `proposal_sent`, `form_submitted` | 20 |
| `linkedin_message_received`, `call_completed` | 15 |
| `linkedin_connection_accepted`, `content_downloaded` | 10 |
| `email_clicked` | 8 |
| `email_opened`, `custom` | 5 |
| `linkedin_message_sent`, `email_sent`, `website_visited` | 2–3 |
| `linkedin_connection_sent`, `linkedin_profile_viewed`, `call_no_answer` | 1–2 |
| `email_bounced` | -5 |

Activities < 30 days old get full weight; older activities get 50%.


---

### Tasks (Background Processing)

Enrichment, copyright (AI content), and scoring jobs run asynchronously via Trigger.dev.

| Method | Endpoint | Description |
|--------|----------|-------------|
| `GET` | `/api/automation/tasks` | List jobs (filter by status/type) |
| `GET` | `/api/automation/tasks/{jobId}` | Get job status and progress |
| `POST` | `/api/automation/tasks/enrich` | Trigger enrichment for a lead |
| `POST` | `/api/automation/tasks/copyright` | Trigger AI content generation for a lead |
| `POST` | `/api/automation/tasks/score` | Trigger SDR AI scoring (single or batch up to 100) |

**Enrichment services:** `companyUrl`, `emailFinder`, `enrichment1`–`enrichment10` (configured in UrlSettings)

**Copyright processes:** `enrichment1`–`enrichment10` (each maps to an AI agent in AgentSettings)

**Scoring fields:** `aiLeadScore`, `aiQualification`, `aiNextAction`, `aiColdEmail`, `aiInterest`, `aiLinkedinConnect`, `aiCompetitorAnalysis`, `aiEngagementLevel`, `aiPurchaseWindow`, `aiDecisionMakerRole`, `aiSentiment`, `aiSocialEngagement`, `aiNurturingStage`, `aiBudgetEstimation`, `aiRiskScore`, `aiProductFitScore`

---

### Territory Companies

Company-level intelligence aggregated from lead data.

| Method | Endpoint | Description |
|--------|----------|-------------|
| `GET` | `/api/automation/companies` | List territory companies (sort, filter by industry/country/score) |
| `GET` | `/api/automation/companies/{id}` | Get company detail with content analysis and leads summary |
| `GET` | `/api/automation/companies/{id}/leads` | List leads for a company |
| `POST` | `/api/automation/companies/aggregate` | Aggregate leads into TerritoryCompany records |
| `POST` | `/api/automation/companies/{id}/content-analysis` | Re-run content analysis |
| `GET` | `/api/automation/companies/events` | List company events |
| `POST` | `/api/automation/companies/events` | Create manual event |
| `DELETE` | `/api/automation/companies/events` | Batch delete events |
| `POST` | `/api/automation/companies/events/generate` | Auto-generate events from lead activity |
| `GET` | `/api/automation/companies/events/radar` | Radar dashboard summary |

**Content analysis fields:** `contentTopics`, `contentKeywords`, `leadTitles`, `leadHeadlines`, `targetAudiences`, `painPoints`, `valuePropositions`, `competitorMentions`, `engagementInsights`, `contentRecommendations`

**Event types:** `new_lead`, `lead_qualified`, `score_increased`, `new_company`, `custom`

---

### Webhook Events

Inbound webhook event management from email platforms (Woodpecker, Lemlist, etc.).

| Method | Endpoint | Description |
|--------|----------|-------------|
| `GET` | `/api/automation/webhook-events` | List events (filter by platform/type/status/date) |
| `GET` | `/api/automation/webhook-events/{id}` | Get event detail with raw payload |
| `PUT` | `/api/automation/webhook-events/{id}` | Update event fields |
| `DELETE` | `/api/automation/webhook-events` | Batch delete events |
| `POST` | `/api/automation/webhook-events/{id}/reprocess` | Re-run lead matching |

**Lead matching priority on reprocess:**

| Priority | Method | Confidence | GSI |
|----------|--------|------------|-----|
| 1 | Email | high | `email-index` |
| 2 | LinkedIn URL | medium | `company_id` GSI + filter |
| 3 | First + Last name | low | `firstName-lastName-index` |

---

### Users

Company user management with role-based access control.

| Method | Endpoint | Description |
|--------|----------|-------------|
| `GET` | `/api/automation/users` | List company users (filter by group) |
| `GET` | `/api/automation/users/{id}` | Get user detail |
| `POST` | `/api/automation/users` | Create/invite user |
| `PUT` | `/api/automation/users/{id}` | Update role/group/status/permissions |
| `DELETE` | `/api/automation/users/{id}` | Remove user |
| `GET` | `/api/automation/users/menu-config` | Get menu keys and group defaults |
| `POST` | `/api/automation/users/provision` | One-shot: Cognito + Company + CompanyUser + API key |

**Roles:** `owner`, `admin`, `member`, `viewer`
**Groups:** `admin`, `manager`, `user`, `viewer`
**Client access modes:** `all`, `own`, `specific`

**Provisioning** creates everything in one call — Cognito user, company (new or join existing), CompanyUser record, and API key. The `plainTextKey` is returned only once.

---

### Organizations

Company (organization) management.

| Method | Endpoint | Description |
|--------|----------|-------------|
| `GET` | `/api/automation/companies/manage` | List companies |
| `GET` | `/api/automation/companies/manage?id={id}` | Get company |
| `POST` | `/api/automation/companies/manage` | Create company |
| `PUT` | `/api/automation/companies/manage` | Rename / add-user / update-user / remove-user |
| `DELETE` | `/api/automation/companies/manage?id={id}` | Delete company |
| `GET` | `/api/automation/companies/manage?id={id}&users=true` | List company users |

---

### Cognito (User Pool)

Low-level AWS Cognito user pool operations.

| Method | Endpoint | Description |
|--------|----------|-------------|
| `GET` | `/api/automation/users/cognito` | Look up user by email or list users |
| `POST` | `/api/automation/users/cognito` | Create Cognito user with permanent password |
| `PUT` | `/api/automation/users/cognito` | Enable/disable/set-password/set-attributes |

---

### Tables (Generic CRUD)

Generic CRUD for any supported DynamoDB table. Primary interface for configuration records and business data models.

| Method | Endpoint | Description |
|--------|----------|-------------|
| `GET` | `/api/automation/tables/{tableName}` | List records (paginated) |
| `POST` | `/api/automation/tables/{tableName}` | Create record |
| `GET` | `/api/automation/tables/{tableName}/{id}` | Get record by ID |
| `PUT` | `/api/automation/tables/{tableName}/{id}` | Update record |
| `DELETE` | `/api/automation/tables/{tableName}/{id}` | Delete record |

**Supported tables:**

| Category | Tables |
|----------|--------|
| Multi-Tenant | `Company`, `CompanyUser`, `CompanyInvitation` |
| Core Data | `Jobs`, `B2BLeads`, `EnrichLeads`, `SourceLeads`, `TerritoryCompany`, `CompanyEvent`, `LinkedInJobs` |
| Campaign & Targeting | `ICP`, `ABMCampaign`, `TargetAccount` |
| Outreach & Workflow | `OutreachSequence`, `SequenceEnrollment`, `Workflow`, `WorkflowExecution` |
| Webhook & Integration | `Integration`, `Webhook`, `WebhookLog`, `WebhookSettings`, `InboundWebhook`, `WebhookEvent` |
| AI & Agent Config | `Agent`, `AgentSettings`, `SdrAiSettings`, `CopyrightSettings`, `SdrSettings` |
| Service Config | `EnrichmentService`, `EmailPlatformSettings`, `OutreachCampaign`, `OutreachTemplate`, `BaserowSyncConfig`, `BaserowSyncHistory`, `BaserowConfig`, `UnipileSettings`, `UnipileAccount`, `UnipileMessage`, `UnipileChat`, `UnipileLog`, `UnipileCampaign`, `UnipileIntegration` |
| System | `AgentApiKey`, `UrlSettings`, `Client`, `SearchHistory`, `Maintenance`, `SidebarConfig`, `SharedView` |

**ICP field groups:**
- Targeting: `name`, `description`, `industries`, `companySizes`, `geographies`, `jobTitles`, `seniority`, `departments`, `functions`, `keywords`, `technologies`
- Apify config: `apifyActorId` (required for generation), `apifyInput`, `apifySettings`, `maxLeads`, `leadSources`
- Qualification: `qualificationCriteria`, `scoringWeights`
- Metadata: `isActive`, `lastUsedDate`, `totalLeadsGenerated`, `client_id`


---

### Email Platforms

Email platform integration for outbound lead delivery.

| Method | Endpoint | Description |
|--------|----------|-------------|
| `GET` | `/api/automation/email-platforms` | List configured platforms with connection status |
| `POST` | `/api/automation/email-platforms/send` | Send leads to a platform campaign (max 200) |

**Send behavior:**
- Platform must be active (`isActive: true`)
- Prefers `emailFinder` field over `email` for verified addresses
- Leads without email are skipped with `missing_email` reason

---

### FSD Pipeline

Full-Stack Demand generation — create campaigns, run lead generation pipelines, and monitor stage-by-stage progress.

| Method | Endpoint | Description |
|--------|----------|-------------|
| `GET` | `/api/automation/fsd/campaigns` | List campaigns with metrics |
| `GET` | `/api/automation/fsd/campaigns/{id}` | Get campaign detail |
| `POST` | `/api/automation/fsd/campaigns` | Create campaign |
| `PUT` | `/api/automation/fsd/campaigns/{id}` | Update campaign settings |
| `DELETE` | `/api/automation/fsd/campaigns/{id}` | Soft-delete (deactivate) campaign |
| `POST` | `/api/automation/fsd/run` | Start pipeline run |
| `GET` | `/api/automation/fsd/run/{pipelineId}` | Get pipeline status and metrics |

**Pipeline stage progression:**

```
generating → enriching → scoring → qualifying → sending → completed
                                                            ↘ failed
```

| Stage | Description | Metric |
|-------|-------------|--------|
| `generating` | Apify actor scraping leads | `leadsGenerated` |
| `enriching` | Enrichment services running | `leadsEnriched` |
| `scoring` | SDR AI scoring leads | `leadsScored` |
| `qualifying` | Filtering by threshold | `leadsQualified` |
| `sending` | Delivering to email platform | `leadsSent` |
| `completed` | Pipeline finished | — |
| `failed` | Error occurred | `errorMessage`, `stageErrors` |

**Automation flags:**
- `enrichAfterGeneration: true` → auto-enrich after generation
- `scoreAfterEnrichment: true` → auto-score after enrichment
- `sendToEmailPlatform` + `qualificationThreshold` → auto-filter and deliver

**ICP-to-Generation flow:** When `icpId` is provided, the API resolves `apifyActorId` and `apifyInput` from the ICP record automatically. Alternative: provide `apifyActorId` and `apifyInput` directly.

**Campaign fields:** `name`, `client_id`, `icpId`, `apifyActorId`, `apifyInput`, `frequency` (`once`/`daily`/`weekly`/`monthly`), `targetLeadCount`, `enrichAfterGeneration`, `scoreAfterEnrichment`, `sendToEmailPlatform`, `qualificationThreshold`, `emailCampaignId`, `isActive`

---

### EpsimoAI

EpsimoAI user activation, profile, credit management, and thread usage.

| Method | Endpoint | Description |
|--------|----------|-------------|
| `POST` | `/api/automation/epsimo/users/activate` | Login or Cognito token exchange |
| `GET` | `/api/automation/epsimo/users/info` | User profile with derived plan |
| `GET` | `/api/automation/epsimo/credits/balance` | Credit balance (remaining threads) |
| `POST` | `/api/automation/epsimo/credits/purchase` | Purchase credits |
| `GET` | `/api/automation/epsimo/threads` | Thread usage with percentage and plan |

**Token convention:** `X-Epsimo-Token` header (preferred) or `epsimoToken` query parameter. The activate endpoint is the only one that doesn't require a token.

**Auth order:** All epsimo routes validate: (1) `X-API-Key` → `AUTH_MISSING`/`AUTH_INVALID`, (2) EpsimoAI token → `MISSING_EPSIMO_TOKEN`, (3) upstream call.

**Plan derivation logic (`derivePlan`):**

| Condition | Plan |
|-----------|------|
| threadMax >= 120,000 | enterprise |
| threadMax >= 50,000 OR stripeClientId is truthy | premium |
| threadMax >= 10,000 | pro |
| default | free |

Note: `/users/info` uses `derivePlan(threadMax, stripeClientId)` (full), while `/threads` uses `derivePlan(threadMax)` only — plan may differ between endpoints for users with `stripeClientId` and low `threadMax`.

**Credit balance:** `credits = Math.max(0, thread_max - thread_counter)` — never negative.

**Usage percentage:** `Math.round((thread_counter / thread_max) * 100 * 100) / 100` (0 if threadMax is 0).

**Purchase validation:** `amount` must be present, `Number.isInteger(amount)`, and `> 0`. Strings, floats, zero, and negatives all fail.

**UI route:** `POST /api/credits/purchase` — cookie-based (`epsimo_token` cookie), flat response (no standard envelope), used by frontend `CreditService.purchaseCredits()`.

---

## CLI Command Reference

All commands use the syntax: `npx tsx src/scripts/lgp.ts <group> <command> [options]`

### auth

| Command | Description |
|---------|-------------|
| `auth test` | Verify API key validity |

### leads

| Command | Description |
|---------|-------------|
| `leads list --client <id>` | List leads (supports `--limit`, `--fields`, `--next-token`) |
| `leads get <id>` | Get lead detail |
| `leads import --file <path>` or `--data '<json>'` | Import leads |
| `leads search` | Search by `--email`, `--first-name`, `--last-name`, `--company-url`, `--linkedin-url` |
| `leads dedup --client <id> --match <fields>` | Find duplicates |
| `leads dedup-resolve --keep <id> --merge <ids>` | Merge duplicates |
| `leads transfer --from <id> --to <id>` | Transfer leads (`--all`, `--dry-run`) |
| `leads validate-ownership` | Scan for ownership issues |
| `leads activity <leadId> --type <type>` | Log engagement (`--notes`, `--metadata`) |
| `leads activities <leadId>` | Get engagement history |
| `leads update-batch --client-id <id> --field <f> --csv <path>` | Batch update leads from CSV |
| `leads prune-blanks --client-id <id>` | Remove blank leads (`--dry-run`) |

### tasks

| Command | Description |
|---------|-------------|
| `tasks list` | List jobs (`--status`, `--type`, `--limit`) |
| `tasks status <jobId>` | Get job status |
| `tasks enrich --lead <id>` | Trigger enrichment (`--services`) |
| `tasks copyright --lead <id>` | Trigger AI content (`--processes`) |
| `tasks score --lead <id>` | Trigger scoring (`--fields`) |

### companies

| Command | Description |
|---------|-------------|
| `companies list --client <id>` | List territory companies (`--sort`, `--limit`) |
| `companies get <id>` | Get company detail |
| `companies leads <id>` | List company leads |
| `companies content-analysis <id>` | Re-run content analysis |

### webhooks

| Command | Description |
|---------|-------------|
| `webhooks list` | List events (`--platform`, `--event-type`, `--limit`) |
| `webhooks get <id>` | Get event detail |
| `webhooks reprocess <id>` | Re-run lead matching |

### tables

| Command | Description |
|---------|-------------|
| `tables list <tableName>` | List records (`--limit`) |
| `tables create <tableName> --data '<json>'` | Create record |
| `tables get <tableName> <id>` | Get record |
| `tables update <tableName> <id> --data '<json>'` | Update record |
| `tables delete <tableName> <id>` | Delete record |

### email-platforms

| Command | Description |
|---------|-------------|
| `email-platforms list` | List configured platforms |
| `email-platforms send` | Send leads (`--platform`, `--campaign`, `--leads`) |

### users

| Command | Description |
|---------|-------------|
| `users list` | List users (`--group`, `--limit`) |
| `users get <id>` | Get user detail |
| `users create --email <email>` | Create user (`--role`, `--group`) |
| `users update <id>` | Update user (`--role`, `--group`, `--status`) |
| `users delete <id>` | Remove user |
| `users provision --email <email> --password <pwd>` | Full provisioning (`--company-name` or `--company-id`) |

### cognito

| Command | Description |
|---------|-------------|
| `cognito list` | List Cognito users |
| `cognito get --email <email>` | Get user by email |
| `cognito create --email <email> --password <pwd>` | Create user |
| `cognito enable --email <email>` | Enable user |
| `cognito disable --email <email>` | Disable user |

### org

| Command | Description |
|---------|-------------|
| `org list` | List companies |
| `org get <id>` | Get company |
| `org create --name <name>` | Create company |
| `org rename <id> --name <name>` | Rename company |
| `org delete <id>` | Delete company |
| `org users <companyId>` | List company users |
| `org add-user <companyId> --email <email>` | Add user (`--role`, `--group`) |
| `org update-user <userId>` | Update user (`--role`, `--group`, `--status`) |
| `org remove-user <userId>` | Remove user |

### fsd

| Command | Description |
|---------|-------------|
| `fsd campaigns` | List campaigns |
| `fsd campaign <id>` | Get campaign detail |
| `fsd create-campaign --client <id> --name <name>` | Create campaign (`--icp`, `--frequency`, `--target`) |
| `fsd update-campaign <id>` | Update campaign (`--name`, `--target`, `--frequency`) |
| `fsd deactivate-campaign <id>` | Soft-delete campaign |
| `fsd run --client <id>` | Start pipeline (`--icp` or `--actor`/`--input`, `--target`) |
| `fsd status <pipelineId>` | Get pipeline status |

### epsimo

| Command | Description |
|---------|-------------|
| `epsimo activate --email <email> --password <pwd>` | Login mode |
| `epsimo activate --cognito-token <token>` | Exchange mode |
| `epsimo info --token <token>` | User profile and plan |
| `epsimo credits --token <token>` | Credit balance |
| `epsimo purchase --token <token> --amount <n>` | Purchase credits |
| `epsimo threads --token <token>` | Thread usage and percentage |

### admin (requires `LGP_ADMIN_KEY`)

| Command | Description |
|---------|-------------|
| `admin backup tables [--prefix <p>]` | List DynamoDB tables |
| `admin backup create --table <name>` or `--all` | Create on-demand backup |
| `admin backup list [--table <n>] [--status <s>]` | List existing backups |
| `admin backup describe --arn <arn>` | Describe a backup |
| `admin backup delete --arn <arn>` | Delete a backup |
| `admin backup restore --arn <arn> --target-table <n>` | Restore from backup |
| `admin backup pitr-status [--table <n>]` | Check PITR status |
| `admin backup pitr-enable --table <name>` | Enable PITR |
| `admin backup pitr-disable --table <name>` | Disable PITR |
| `admin org-tree --company <id>` | Display org tree (`--detailed`, `--json`) |
| `admin companies list` | List all companies |
| `admin companies show --id <id>` | Show company detail |
| `admin users list [--search <term>]` | List Cognito users |
| `admin views list` | List view configurations |
| `admin clients list` | List all clients across companies |

### maintenance

| Command | Description |
|---------|-------------|
| `maintenance bugs list` | List bug reports |
| `maintenance bugs report --desc <text>` | Report a bug (`--email`) |
| `maintenance enhancements list` | List enhancement requests |
| `maintenance enhancements request --desc <text>` | Request enhancement (`--email`) |

### pipeline

| Command | Description |
|---------|-------------|
| `pipeline [--start <date>] [--end <date>]` | Show pipeline analytics (defaults to last 30 days) |

### campaigns

| Command | Description |
|---------|-------------|
| `campaigns list` | List all campaigns |
| `campaigns create --name <name> [--type <type>]` | Create campaign (default type: `abm`) |

### clients

| Command | Description |
|---------|-------------|
| `clients list` | List all clients |
| `clients create --name <name> [--url <url>]` | Create a new client |

### generate

| Command | Description |
|---------|-------------|
| `generate from-icp --icp <id> --client <id>` | Generate leads from ICP (`--max-leads`, `--provider`) |
| `generate direct --provider <name> --config <json> --client <id>` | Direct provider generation |
| `generate status <runId>` | Check generation run status |
| `generate history` | List past runs (`--client`, `--icp`, `--status`, `--limit`) |
| `generate schedule create --icp <id> --client <id> --frequency <f>` | Create schedule (`--max-leads`) |
| `generate schedule list` | List all schedules |
| `generate schedule pause <scheduleId>` | Pause a schedule |
| `generate schedule resume <scheduleId>` | Resume a schedule |
| `generate schedule delete <scheduleId>` | Delete a schedule |

### shares

| Command | Description |
|---------|-------------|
| `shares list` | List shared links (`--status`, `--client`) |
| `shares get <id>` | Get shared link detail |
| `shares create` | Create shared link (`--view-type`, `--days`, `--allow-edit`) |
| `shares extend <id> --days <n>` | Extend expiration |
| `shares set-expiry <id> --date <iso>` | Set explicit expiration |
| `shares revoke <id>` | Revoke shared link |
| `shares reactivate <id>` | Re-enable revoked link (`--days`) |

### account-analysis

| Command | Description |
|---------|-------------|
| `account-analysis list --client <id>` | List company groups (`--sort`, `--min-leads`) |
| `account-analysis analyze --client <id>` | Detailed metrics (`--company`) |
| `account-analysis export --client <id> --format <fmt>` | Export to CSV/JSON (`--output`) |
| `account-analysis cache-clear` | Clear local cache (`--client`) |


---

## Business Workflows

Detailed step-by-step operational workflows for multi-step processes. Full details in [references/workflows.md](references/workflows.md).

### 1. Lead Deduplication

Find and merge duplicate leads within a client. Steps: dry-run scan → review groups → resolve (merge) → verify.

**Match fields:** `email` (high), `linkedinUrl` (medium), `fullName+companyName` (low).

**Merge rules:** Only empty fields on the keep lead are filled. System fields never merged. First merge lead's value wins for ties. Keep lead's value always preserved on conflicts.

### 2. Lead Transfer

Transfer leads between clients with duplicate detection. Steps: dry-run → review skipped duplicates → execute → verify.

**Rules:** Both clients must belong to your company. Duplicates in target are skipped (not overwritten). Only `client_id` is updated.

### 3. Webhook Reprocessing

Re-match unmatched webhook events to leads after new imports. Steps: list unmatched → reprocess each → verify matches → clean up.

**Matching:** Uses `normalizedData` from the webhook. Tries email → LinkedIn URL → name in priority order. Updates `engagementHistory` and recalculates `engagementScore` on match.

### 4. Territory Analysis

Build company-level intelligence from lead data. Steps: aggregate → list companies → view detail → content analysis → generate events → radar dashboard.

**Aggregation:** Creates TerritoryCompany records from unique `companyName` values within a client, with metrics like `totalLeads`, `qualifiedLeads`, `averageLeadScore`.

### 5. Engagement Tracking

Log activities on leads and understand score calculation. Steps: log activity → batch log → retrieve history → verify score.

**Score:** Weighted by activity type with time decay (< 30 days = full, > 30 days = 50%). Capped at 100.

### 6. Data Health Check

Validate lead ownership and data integrity. Steps: run validation → review issues → fix orphaned records → verify client-company relationships → re-validate.

**Checks:** Orphaned leads (invalid `client_id`), mismatched company, null owner.

### 7. ICP-First Campaign Setup

Define ICP → validate Apify config → create FSD campaign → run pipeline → monitor → verify leads.

**ICP validation:** Must have `apifyActorId` set. Pipeline resolves Apify config from ICP automatically.

### 8. Multi-ICP Campaign Strategy

Create multiple ICPs for different segments → separate campaigns per ICP → run pipelines → compare results → deactivate underperformers.

### 9. Iterative ICP Refinement

Run initial generation → review scores → record baseline → update ICP criteria → run refined generation → compare before/after.

### 10. Full Automation Setup

Configure all prerequisites (UrlSettings, AgentSettings, SdrAiSettings, EmailPlatformSettings) → create ICP → create campaign with all automation flags → run and verify end-to-end.

### 11. Campaign Monitoring Dashboard

List active campaigns → check pipeline status → review per-stage metrics → diagnose failures → rerun failed pipelines → deactivate problematic campaigns.

### 12. Qualification and Delivery

Review scored leads → understand threshold → verify email platform config → check delivery metrics → verify via webhook events → manual send fallback.

---

## Business Use Cases

End-to-end business scenario guides. Full details in [references/use_cases.md](references/use_cases.md).

### 1. New Customer Onboarding

Complete environment setup: provision user → create client → configure UrlSettings → configure AgentSettings → configure SdrAiSettings → create ICP → run first FSD pipeline → monitor.

**Outcome:** Cognito user, company, client, all config records, active ICP, and a completed pipeline run with generated/enriched/scored leads.

### 2. ICP-Driven Campaign Launch

Define ICP with targeting + Apify config → create FSD campaign → run pipeline → monitor stages → review leads → verify email delivery.

**Outcome:** ICP record, FSD campaign, completed pipeline, leads delivered to email platform, webhook events tracking engagement.

### 3. Lead Qualification Pipeline

Import raw leads → enrich → copyright (AI content) → score → filter by threshold → send to email platform.

**Outcome:** Each lead progresses through import → enrichment → AI content → scoring → qualification → delivery. Full pipeline from raw data to outreach-ready leads.

---

## Error Handling

All errors return a consistent JSON envelope:

```json
{
  "success": false,
  "error": "Human-readable message",
  "details": "Additional context",
  "code": "MACHINE_READABLE_CODE",
  "requestId": "uuid-v4"
}
```

| Code | HTTP | Description |
|------|------|-------------|
| `UNAUTHORIZED` | 401 | Missing or invalid API key |
| `RATE_LIMITED` | 429 | Rate limit exceeded (60/min, 1000/hr, 10000/day) |
| `MISSING_CLIENT_ID` | 400 | Required `client_id` not provided |
| `CLIENT_WRONG_COMPANY` | 400/403 | Client belongs to a different company |
| `NOT_FOUND` | 404 | Resource doesn't exist or belongs to another company |
| `VALIDATION_ERROR` | 400 | Invalid field types, missing required values |
| `INVALID_BODY` | 400 | Request body is not valid JSON |
| `IMMUTABLE_FIELD` | 400 | Attempted to modify `owner` or `company_id` |
| `ICP_NOT_FOUND` | 404 | ICP record not found |
| `ICP_NO_APIFY` | 400 | ICP missing `apifyActorId` |
| `ICP_LOOKUP_FAILED` | 500 | Internal error resolving ICP |

**EpsimoAI-specific errors:**

| Code | HTTP | Description |
|------|------|-------------|
| `EPSIMO_AUTH_FAILED` | 401 | Login credentials invalid |
| `EPSIMO_TOKEN_INVALID` | 401 | Token expired or invalid (info endpoint only) |
| `EPSIMO_UNAVAILABLE` | 502 | Backend unreachable or 5xx |
| `EPSIMO_PURCHASE_FAILED` | 402 | Credit purchase rejected |
| `MISSING_EPSIMO_TOKEN` | 400 | Required EpsimoAI token not provided |

---

## Prerequisites Checklist

Before running enrichment, copyright, scoring, or FSD pipelines, these configuration records must exist (create via Tables API):

### UrlSettings (enrichment)

| Field | Description |
|-------|-------------|
| `companyUrl` | Company URL lookup service endpoint |
| `companyUrl_Apikey` | API key for company URL service |
| `emailFinder` | Email finder service endpoint |
| `emailFinder_Apikey` | API key for email finder |
| `enrichment1`–`enrichment10` | Enrichment service endpoints |
| `enrichment1_Apikey`–`enrichment10_Apikey` | Corresponding API keys |

### AgentSettings (copyright / AI content)

| Field | Description |
|-------|-------------|
| `projectId` | EpsimoAI project ID |
| `enrichment1AgentId`–`enrichment10AgentId` | Agent IDs per copyright process |

### SdrAiSettings (scoring)

| Field | Description |
|-------|-------------|
| `projectId` | EpsimoAI project ID |
| `aiLeadScoreAgentId` | Lead scoring agent |
| `aiQualificationAgentId` | Qualification assessment agent |
| `aiNextActionAgentId` | Next-action recommendation agent |
| `aiColdEmailAgentId` | Cold email generation agent |
| `aiInterestAgentId` | Interest analysis agent |
| `aiLinkedinConnectAgentId` | LinkedIn connect message agent |
| `aiCompetitorAnalysisAgentId` | Competitor analysis agent |
| `aiEngagementLevelAgentId` | Engagement level agent |
| `aiPurchaseWindowAgentId` | Purchase window estimation agent |
| `aiDecisionMakerRoleAgentId` | Decision-maker role agent |
| `aiSentimentAgentId` | Sentiment analysis agent |
| `aiSocialEngagementAgentId` | Social engagement agent |
| `aiNurturingStageAgentId` | Nurturing stage agent |
| `aiBudgetEstimationAgentId` | Budget estimation agent |
| `aiRiskScoreAgentId` | Risk scoring agent |
| `aiProductFitScoreAgentId` | Product-fit scoring agent |

### ICP (lead generation)

| Field | Description |
|-------|-------------|
| `apifyActorId` | Apify actor ID (required) |
| `apifyInput` | Actor input config (JSON string) |
| `maxLeads` | Max leads per run (default 100) |
| `client_id` | Client partition |

### EmailPlatformSettings (delivery)

| Field | Description |
|-------|-------------|
| `platform` | Platform name (e.g., `woodpecker`) |
| `apiKey` | Platform API key |
| `campaignId` | Default campaign ID |

---

## Reference Files

| File | Description |
|------|-------------|
| [SKILL.md](SKILL.md) | Skill metadata, prerequisites checklist, and quick-reference maps |
| [references/api_endpoints.md](references/api_endpoints.md) | Complete request/response schemas for every API endpoint |
| [references/cli_reference.md](references/cli_reference.md) | Full CLI command reference with syntax, flags, and examples |
| [references/workflows.md](references/workflows.md) | Step-by-step operational workflows (12 workflows) |
| [references/use_cases.md](references/use_cases.md) | End-to-end business scenario guides (3+ use cases) |

---

## License

Proprietary — LeadGenius Pro. All rights reserved.
