# Workflow Reference

Step-by-step operational workflows for common multi-step processes in LeadGenius Pro.

---

## 1. Lead Deduplication Workflow

Find and merge duplicate leads within a client using configurable match fields.

### When to Use

- After a bulk import that may have introduced duplicates
- Periodic data hygiene on a client's lead set
- Before transferring leads to another client (clean source first)

### Steps

**Step 1 — Run a dry-run deduplication scan**

Identify duplicate groups without making changes. Choose one or more match fields based on desired confidence level.

| Match Field | Confidence | Description |
|-------------|------------|-------------|
| `email` | high | Exact email match (case-insensitive) |
| `linkedinUrl` | medium | Exact LinkedIn URL match |
| `fullName+companyName` | low | Combined name + company match |

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT_ID",
    "matchFields": ["email", "linkedinUrl", "fullName+companyName"],
    "dryRun": true
  }' \
  https://api.leadgenius.app/api/automation/leads/deduplicate | jq
```

**CLI:**

```bash
python lgp.py leads dedup --client YOUR_CLIENT_ID --match email,linkedinUrl,fullName+companyName
```

**Expected response:** A list of `matches`, each containing `matchField`, `confidence`, `matchValue`, and `leadIds` (the group of duplicates). Also returns `totalLeadsScanned` and `totalDuplicateGroups`.

**Step 2 — Review duplicate groups**

Examine each duplicate group returned in Step 1. For each group:

1. Note the `matchField` and `confidence` level.
2. Retrieve full details for each lead in the group to decide which to keep.

**API (for each lead in a group):**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/leads/LEAD_ID" | jq
```

**CLI:**

```bash
python lgp.py leads get LEAD_ID
```

Compare fields across leads in the group. Pick the lead with the most complete data as the "keep" lead.

**Step 3 — Resolve (merge) duplicates**

Merge data from duplicate leads into the chosen "keep" lead. Empty fields on the keep lead are filled from merge leads. Merge leads are marked `status: 'duplicate'`.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "keepLeadId": "KEEP_LEAD_ID",
    "mergeLeadIds": ["DUPLICATE_1", "DUPLICATE_2"]
  }' \
  https://api.leadgenius.app/api/automation/leads/deduplicate/resolve | jq
```

**CLI:**

```bash
python lgp.py leads dedup-resolve --keep KEEP_LEAD_ID --merge DUPLICATE_1,DUPLICATE_2
```

**Expected response:** Returns `mergedFields` (fields that were filled in), `conflicts` (fields where both keep and merge leads had values — keep lead's value wins), and `mergeLeadsMarked` count.

**Step 4 — Verify the merge result**

Retrieve the keep lead to confirm merged fields are populated correctly.

```bash
python lgp.py leads get KEEP_LEAD_ID
```

### Merge Rules

- Only empty fields on the keep lead are filled from merge leads.
- System fields (`id`, `owner`, `company_id`, `client_id`, `createdAt`, `updatedAt`) are never merged.
- If multiple merge leads have a value for the same empty field, the first merge lead's value wins.
- Conflicts (both keep and merge have a value) are reported but the keep lead's value is preserved.

### Common Failure Points and Recovery

| Failure | Cause | Recovery |
|---------|-------|----------|
| `NOT_FOUND` on resolve | One of the lead IDs is invalid or belongs to a different company | Verify lead IDs with `leads get` before resolving |
| No duplicate groups found | Match fields too strict, or data is already clean | Try broader match fields (e.g., add `fullName+companyName`) |
| Unexpected conflicts | Both leads have different values for the same field | Review conflicts in the response; manually update the keep lead if the merge lead's value is preferred |
| Large number of groups | Broad match fields on a large dataset | Process groups in batches; start with `email` (high confidence) first, then lower confidence fields |

---

## 2. Lead Transfer Workflow

Transfer leads between clients within the same company, with built-in duplicate detection against the target client.

### When to Use

- Reorganizing leads across campaigns or market segments
- Consolidating leads from a staging client into a production client
- Splitting a client's leads into multiple clients for team assignment

### Steps

**Step 1 — Dry-run the transfer**

Simulate the transfer to see how many leads will move and how many will be skipped as duplicates in the target client.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "fromClientId": "SOURCE_CLIENT_ID",
    "toClientId": "TARGET_CLIENT_ID",
    "leadIds": ["lead-1", "lead-2", "lead-3"],
    "dryRun": true
  }' \
  https://api.leadgenius.app/api/automation/leads/transfer | jq
```

**CLI:**

```bash
python lgp.py leads transfer --from SOURCE_CLIENT_ID --to TARGET_CLIENT_ID --all --dry-run
```

**Expected response:** Returns `transferred` count, `skippedDuplicates` count, and `details` with per-lead breakdown including which duplicates were detected and by which match field.

**Step 2 — Review dry-run results**

Check the response for:
- `transferred`: Number of leads that will move.
- `skippedDuplicates`: Leads already present in the target client (matched by email or linkedinUrl). Review the `details.skippedDuplicates` array to see which leads and match fields triggered the skip.

If too many duplicates are skipped, consider deduplicating the target client first (see Workflow 1).

**Step 3 — Execute the transfer**

Run the transfer for real by setting `dryRun: false` (or omitting it).

**API — Transfer specific leads:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "fromClientId": "SOURCE_CLIENT_ID",
    "toClientId": "TARGET_CLIENT_ID",
    "leadIds": ["lead-1", "lead-2", "lead-3"],
    "dryRun": false
  }' \
  https://api.leadgenius.app/api/automation/leads/transfer | jq
```

**API — Transfer all leads:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "fromClientId": "SOURCE_CLIENT_ID",
    "toClientId": "TARGET_CLIENT_ID",
    "transferAll": true,
    "dryRun": false
  }' \
  https://api.leadgenius.app/api/automation/leads/transfer | jq
```

**CLI:**

```bash
# Transfer all leads
python lgp.py leads transfer --from SOURCE_CLIENT_ID --to TARGET_CLIENT_ID --all

# Transfer specific leads (use API with leadIds array)
```

**Step 4 — Verify the transfer**

List leads in the target client to confirm they arrived.

```bash
python lgp.py leads list --client TARGET_CLIENT_ID --limit 10
```

Optionally, list the source client to confirm leads were moved out.

```bash
python lgp.py leads list --client SOURCE_CLIENT_ID --limit 10
```

### Transfer Rules

- Both source and target clients must belong to your company.
- Source and target must be different clients.
- Duplicate detection runs against the target client by email and linkedinUrl.
- Duplicates are skipped (not overwritten) — the target client's existing lead is preserved.
- Only the `client_id` field is updated on transferred leads; all other data is preserved.

### Common Failure Points and Recovery

| Failure | Cause | Recovery |
|---------|-------|----------|
| `CLIENT_WRONG_COMPANY` | Source or target client belongs to a different company | Verify both client IDs belong to your company with `leads list --client CLIENT_ID` |
| Source equals target | Same client ID for both `fromClientId` and `toClientId` | Use different client IDs |
| All leads skipped as duplicates | Target client already has all the same leads | Deduplicate the target client first, or verify you're using the correct client IDs |
| `NOT_FOUND` | Invalid client ID | List your clients to find valid IDs |
| Partial transfer errors | Individual lead update failures | Check the `errors` array in the response; retry failed leads individually |

---

## 3. Webhook Reprocessing Workflow

Re-match unmatched webhook events to leads. Useful when new leads have been imported since the original webhook was received.

### When to Use

- After importing new leads that should match previously unmatched webhook events
- When webhook events arrived before their corresponding leads were created
- Periodic cleanup of unmatched webhook events to improve engagement tracking

### Steps

**Step 1 — List unmatched webhook events**

Filter webhook events by match status to find events that didn't match any lead.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/webhook-events?matchStatus=unmatched&limit=50" | jq
```

**CLI:**

```bash
python lgp.py webhooks list --platform woodpecker --limit 50
```

Review the results. Each event includes `normalizedData` with contact information (email, name, LinkedIn URL) that will be used for matching.

**Step 2 — Reprocess individual events**

For each unmatched event, trigger reprocessing. The system re-runs lead matching using the following priority:

| Priority | Match Method | Confidence | GSI Used |
|----------|-------------|------------|----------|
| 1 | Email | high | `email-index` |
| 2 | LinkedIn URL | medium | `company_id` GSI + filter |
| 3 | First name + Last name | low | `firstName-lastName-index` |

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  https://api.leadgenius.app/api/automation/webhook-events/EVENT_ID/reprocess | jq
```

**CLI:**

```bash
python lgp.py webhooks reprocess EVENT_ID
```

**Expected response:** Returns updated `matchStatus`, `matchedLeadId`, `matchConfidence`, and `matchMethod`. If a lead is matched, the webhook event is appended to the lead's `engagementHistory` and `engagementScore` is recalculated.

**Step 3 — Batch reprocess multiple events**

To reprocess multiple unmatched events, iterate over the event IDs from Step 1.

**Bash loop example:**

```bash
for EVENT_ID in event-1 event-2 event-3; do
  curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
    https://api.leadgenius.app/api/automation/webhook-events/$EVENT_ID/reprocess | jq
done
```

**CLI loop:**

```bash
for EVENT_ID in event-1 event-2 event-3; do
  python lgp.py webhooks reprocess $EVENT_ID
done
```

**Step 4 — Verify match results**

After reprocessing, list webhook events again to check how many are now matched.

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/webhook-events?matchStatus=matched&limit=50" | jq
```

For matched events, verify the engagement was recorded on the lead:

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/leads/MATCHED_LEAD_ID/activities" | jq
```

**CLI:**

```bash
python lgp.py webhooks list --limit 50
```

**Step 5 — Clean up permanently unmatched events (optional)**

If events remain unmatched after reprocessing and are no longer needed, delete them.

**API:**

```bash
curl -s -X DELETE -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"eventIds": ["event-1", "event-2"]}' \
  https://api.leadgenius.app/api/automation/webhook-events | jq
```

### Matching Behavior

- Matching uses the `normalizedData` JSON field from the webhook event, which contains extracted contact information (email, name, LinkedIn URL).
- The system tries each match method in priority order and stops at the first match.
- If a lead is matched, the webhook event type (e.g., `email_opened`) is appended to the lead's `engagementHistory` and `engagementScore` is recalculated.
- The WebhookLog record is updated with `matchStatus`, `matchedLeadId`, and `matchConfidence`.

### Common Failure Points and Recovery

| Failure | Cause | Recovery |
|---------|-------|----------|
| Event still unmatched after reprocess | No lead in the system matches the event's contact data | Import the missing lead first, then reprocess again |
| `NOT_FOUND` on reprocess | Invalid event ID | List events to get valid IDs |
| Low-confidence match (name only) | Email and LinkedIn URL not available in the webhook data | Verify the match manually by comparing the matched lead with the event's `normalizedData` |
| Engagement score not updated | Lead was matched but activity logging failed | Check the lead's activities endpoint; manually log the activity if missing |
| Duplicate engagement entries | Event was reprocessed multiple times | Check the lead's activity history; the system should deduplicate by `eventHash`, but verify |


---

## 4. Territory Analysis Workflow

Build and maintain company-level intelligence from lead data. Aggregate leads into TerritoryCompany records, run content analysis, generate events, and view the radar dashboard.

### When to Use

- After importing or enriching a batch of leads to build company-level insights
- Periodically refreshing territory intelligence for sales planning
- Before territory review meetings to surface recent company activity
- When onboarding a new client and building initial territory maps

### Steps

**Step 1 — Aggregate companies from lead data**

Trigger aggregation to create or update TerritoryCompany records from EnrichLeads. Each unique `companyName` within a client becomes a TerritoryCompany with metrics like `totalLeads`, `qualifiedLeads`, and `averageLeadScore`.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT_ID",
    "forceRefresh": false,
    "maxLeads": 1000
  }' \
  https://api.leadgenius.app/api/automation/companies/aggregate | jq
```

To aggregate a single company only:

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT_ID",
    "companyName": "Acme Corp",
    "forceRefresh": true
  }' \
  https://api.leadgenius.app/api/automation/companies/aggregate | jq
```

**Expected response:** Returns `companiesCreated`, `companiesUpdated`, `totalLeadsProcessed`, and any `errors`.

Use `forceRefresh: true` to delete and re-create existing TerritoryCompany records (useful when lead data has changed significantly).

**Step 2 — List territory companies**

Browse the aggregated companies with optional filtering and sorting.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies?client_id=YOUR_CLIENT_ID&sortBy=totalLeads&limit=50" | jq
```

**CLI:**

```bash
python lgp.py companies list --client YOUR_CLIENT_ID
python lgp.py companies list --client YOUR_CLIENT_ID --sort totalLeads
```

Available `sortBy` values: `totalLeads`, `qualifiedLeads`, `averageLeadScore`, `lastActivityDate`, `companyName`.

Optional filters: `industry`, `country`, `minLeads`, `maxLeads`, `minScore`, `maxScore`.

**Step 3 — View company detail and associated leads**

Get a complete TerritoryCompany record including content analysis fields and a summary of associated leads.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies/COMPANY_ID" | jq
```

**CLI:**

```bash
python lgp.py companies get COMPANY_ID
```

To retrieve the full lead records associated with a company:

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies/COMPANY_ID/leads?limit=50" | jq
```

**Step 4 — Run content analysis**

Re-run content analysis on a TerritoryCompany to extract insights from its associated leads. This updates fields like `contentTopics`, `contentKeywords`, `painPoints`, `valuePropositions`, `competitorMentions`, `engagementInsights`, and `contentRecommendations`.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  https://api.leadgenius.app/api/automation/companies/COMPANY_ID/content-analysis | jq
```

**Expected response:** The updated TerritoryCompany record with all content analysis fields populated and `lastContentAnalysisDate` set.

**Step 5 — Generate events from lead activity**

Auto-generate CompanyEvent records from recent lead activity. Events are created for new leads, qualified leads, score increases, and new companies.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT_ID",
    "since": "2025-01-01T00:00:00Z",
    "maxLeads": 500
  }' \
  https://api.leadgenius.app/api/automation/companies/events/generate | jq
```

**Expected response:** Returns `eventsCreated` and `eventsByType` breakdown (e.g., `{"new_lead": 15, "lead_qualified": 10}`).

You can also create manual events for custom intelligence:

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "territoryCompanyId": "COMPANY_ID",
    "eventType": "custom",
    "eventTitle": "Partnership announced",
    "eventDescription": "Acme announced partnership with Beta Inc",
    "eventData": {"source": "press_release"}
  }' \
  https://api.leadgenius.app/api/automation/companies/events | jq
```

**Step 6 — View the radar dashboard**

Get a summary view of recent events, event counts by type, top active companies, and a timeline.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies/events/radar?client_id=YOUR_CLIENT_ID" | jq
```

**Expected response:** Returns `recentEvents`, `eventCountsByType`, `topActiveCompanies`, and `timeline`.

**Step 7 — Filter and review events (optional)**

List events with filters to focus on specific activity.

**API:**

```bash
# Filter by event type
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies/events?client_id=YOUR_CLIENT_ID&eventType=lead_qualified" | jq

# Filter by company
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies/events?client_id=YOUR_CLIENT_ID&territoryCompanyId=COMPANY_ID" | jq

# Filter by date range
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies/events?client_id=YOUR_CLIENT_ID&dateFrom=2025-06-01T00:00:00Z&dateTo=2025-06-30T23:59:59Z" | jq
```

Valid `eventType` values: `new_lead`, `lead_qualified`, `score_increased`, `new_company`, `custom`.

### Common Failure Points and Recovery

| Failure | Cause | Recovery |
|---------|-------|----------|
| `MISSING_CLIENT_ID` on aggregate | No `client_id` in request body | Include `client_id` in the request body |
| Zero companies created | No leads exist for the client, or all companies already aggregated | Check lead count with `leads list --client CLIENT_ID`; use `forceRefresh: true` to re-aggregate |
| Content analysis returns empty fields | Company has very few leads or leads lack enrichment data | Enrich leads first (see Tasks API), then re-run content analysis |
| Event generation returns zero events | No recent lead activity since the `since` date | Adjust the `since` parameter to an earlier date, or omit it to process all leads |
| `NOT_FOUND` on company detail | Invalid TerritoryCompany ID | List companies first to get valid IDs |

---

## 5. Engagement Tracking Workflow

Log engagement activities on leads, retrieve engagement history, and understand how the engagement score is calculated.

### When to Use

- Tracking outreach activities (emails, calls, LinkedIn messages) on leads
- Building engagement history for lead scoring and prioritization
- Auditing engagement data before running SDR AI scoring
- Monitoring campaign effectiveness through activity patterns

### Steps

**Step 1 — Log a single activity on a lead**

Record an engagement activity with a type, optional notes, and optional metadata.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "type": "email_opened",
    "notes": "Opened Q1 campaign email",
    "metadata": {"campaignId": "camp-1"}
  }' \
  https://api.leadgenius.app/api/automation/leads/LEAD_ID/activities | jq
```

**CLI:**

```bash
python lgp.py leads activity LEAD_ID --type email_opened --notes "Opened Q1 campaign email"
```

**Expected response:** Returns `activitiesAdded`, `totalActivities`, updated `engagementScore`, and `lastEngagementAt`.

**Step 2 — Log multiple activities in batch**

Record several activities at once, each with its own timestamp.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "activities": [
      {"type": "email_sent", "timestamp": "2026-03-01T09:00:00.000Z"},
      {"type": "email_opened", "timestamp": "2026-03-01T10:00:00.000Z"},
      {"type": "email_clicked", "timestamp": "2026-03-01T10:05:00.000Z"},
      {"type": "meeting_scheduled", "timestamp": "2026-03-02T14:00:00.000Z", "notes": "Demo call booked"}
    ]
  }' \
  https://api.leadgenius.app/api/automation/leads/LEAD_ID/activities | jq
```

**Step 3 — Retrieve engagement history**

Get the full activity history and current engagement score for a lead.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/leads/LEAD_ID/activities" | jq
```

**Expected response:** Returns `leadId`, `totalActivities`, `engagementScore`, `lastEngagementAt`, and an `activities` array with each activity's `type`, `timestamp`, `notes`, and `metadata`.

**Step 4 — Understand the engagement score**

The engagement score is automatically recalculated each time activities are logged. It uses weighted activity types with time decay.

**Activity type weights:**

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

**Time decay:** Activities less than 30 days old receive full weight. Activities older than 30 days receive 50% weight.

**Score cap:** The engagement score is capped at 100.

**Valid activity types:** `linkedin_connection_sent`, `linkedin_connection_accepted`, `linkedin_message_sent`, `linkedin_message_received`, `linkedin_profile_viewed`, `email_sent`, `email_opened`, `email_clicked`, `email_answered`, `email_bounced`, `call_completed`, `call_no_answer`, `meeting_scheduled`, `meeting_completed`, `form_submitted`, `website_visited`, `content_downloaded`, `demo_requested`, `proposal_sent`, `contract_signed`, `custom`.

**Step 5 — Verify engagement on the lead record**

Retrieve the full lead to confirm engagement fields are updated.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/leads/LEAD_ID" | jq '.data | {engagementScore, lastEngagementAt, engagementHistory}'
```

**CLI:**

```bash
python lgp.py leads get LEAD_ID
```

Check that `engagementScore`, `lastEngagementAt`, and `engagementHistory` reflect the logged activities.

### Common Failure Points and Recovery

| Failure | Cause | Recovery |
|---------|-------|----------|
| `NOT_FOUND` on activity log | Invalid lead ID | Verify the lead ID with `leads get LEAD_ID` |
| Invalid activity `type` | Unrecognized activity type string | Use one of the valid activity types listed above |
| Score not increasing | Activities are older than 30 days (50% weight) or low-point types | Log higher-weight activities or more recent ones |
| Score stuck at 100 | Cap reached | Score is capped at 100; additional activities won't increase it further |
| Duplicate activities | Same activity logged multiple times | Review the activities list; the system does not deduplicate manual activity logs |
| `engagementHistory` empty after logging | Activity was logged but lead record not refreshed | Re-fetch the lead; if still empty, check the activity endpoint directly |

---

## 6. Data Health Check Workflow

Validate lead ownership, detect orphaned records, and verify client-company relationships across your data.

### When to Use

- After bulk imports or transfers to verify data integrity
- Periodic data hygiene audits
- Before running enrichment or scoring pipelines to ensure clean input data
- When leads appear to be missing or inaccessible

### Steps

**Step 1 — Run ownership validation**

Scan all EnrichLeads for your company and report ownership issues. The validation checks for orphaned leads, company mismatches, and null owners.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  https://api.leadgenius.app/api/automation/leads/validate-ownership | jq
```

**CLI:**

```bash
python lgp.py leads validate-ownership
```

**Expected response:**

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

**Checks performed:**

| Check | Description |
|-------|-------------|
| Orphaned records | Lead's `client_id` references a non-existent Client record |
| Mismatched company | Client's `company_id` doesn't match the lead's `company_id` |
| Null owner | Lead has an empty or null `owner` field |

If `status` is `"healthy"` and `totalIssues` is 0, your data is clean. Otherwise, proceed to the next steps.

**Step 2 — Review issue details**

When issues are found, the `details` array contains specifics about each problem. Review the details to understand the scope.

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  https://api.leadgenius.app/api/automation/leads/validate-ownership | jq '.data.details'
```

Each detail entry includes the lead ID, the issue type, and relevant field values to help diagnose the problem.

**Step 3 — Fix orphaned records**

Orphaned leads reference a `client_id` that no longer exists. To fix:

1. List your available clients to find a valid target.

```bash
python lgp.py tables list Client
```

2. Transfer orphaned leads to a valid client using the transfer endpoint.

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "fromClientId": "ORPHANED_CLIENT_ID",
    "toClientId": "VALID_CLIENT_ID",
    "transferAll": true,
    "dryRun": false
  }' \
  https://api.leadgenius.app/api/automation/leads/transfer | jq
```

Alternatively, if the client was deleted accidentally, re-create it:

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"name": "Restored Client", "company_id": "YOUR_COMPANY_ID"}' \
  https://api.leadgenius.app/api/automation/tables/Client | jq
```

**Step 4 — Verify client-company relationships**

Confirm that each client belongs to the correct company by listing clients and checking their `company_id`.

```bash
python lgp.py tables list Client
```

Cross-reference with your company ID. If a client has a mismatched `company_id`, leads assigned to it will show as `mismatchedCompany` issues.

**Step 5 — Re-run validation to confirm fixes**

After resolving issues, run the ownership validation again to confirm all problems are resolved.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  https://api.leadgenius.app/api/automation/leads/validate-ownership | jq
```

**CLI:**

```bash
python lgp.py leads validate-ownership
```

Confirm `status` is `"healthy"` and `totalIssues` is 0.

### Common Failure Points and Recovery

| Failure | Cause | Recovery |
|---------|-------|----------|
| Large number of orphaned records | Client was deleted while leads still referenced it | Re-create the client or transfer leads to an existing client |
| Mismatched company IDs | Leads were imported with incorrect `company_id` (should be auto-set) | This typically indicates a data migration issue; contact support or re-import leads |
| Null owner records | Leads created through a non-standard path that bypassed owner assignment | Re-import the affected leads through the standard import endpoint, which auto-sets `owner` |
| Validation times out | Very large dataset (thousands of leads) | The endpoint scans all leads for your company; if it times out, try during off-peak hours or contact support |
| Transfer fails for orphaned leads | The orphaned `client_id` can't be used as `fromClientId` | Use the lead search endpoint to find orphaned leads by ID, then import them fresh into the target client |


---

## 7. ICP-First Campaign Setup Workflow

Define an Ideal Customer Profile, validate its Apify configuration, create an FSD campaign, run the pipeline, and verify results end-to-end.

### When to Use

- Launching a new lead generation campaign targeting a specific market segment
- Setting up ICP-driven automation for the first time
- Creating a repeatable campaign template from a well-defined ICP

### Steps

**Step 1 — Define the ICP with targeting criteria and Apify config**

Create an ICP record with all targeting criteria and the Apify actor configuration for lead generation.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT_ID",
    "name": "Enterprise SaaS Decision Makers",
    "description": "VP+ at SaaS companies, 200-1000 employees, US/UK",
    "industries": ["Software", "SaaS", "Cloud Computing"],
    "companySizes": ["201-500", "501-1000"],
    "geographies": ["United States", "United Kingdom"],
    "jobTitles": ["VP Sales", "VP Marketing", "CRO", "CMO"],
    "seniority": ["VP", "C-Suite", "Director"],
    "departments": ["Sales", "Marketing"],
    "keywords": ["B2B", "enterprise sales", "demand generation"],
    "technologies": ["Salesforce", "HubSpot", "Outreach"],
    "apifyActorId": "apify/linkedin-sales-navigator",
    "apifyInput": "{\"searchUrl\":\"https://www.linkedin.com/sales/search/people?query=...\",\"maxResults\":200}",
    "maxLeads": 200,
    "qualificationCriteria": "{\"minScore\":60,\"requiredFields\":[\"email\",\"companyName\"]}",
    "scoringWeights": "{\"industry\":0.3,\"seniority\":0.3,\"companySize\":0.2,\"technology\":0.2}"
  }' \
  https://api.leadgenius.app/api/automation/tables/ICP | jq
```

**CLI:**

```bash
python lgp.py tables create ICP --data '{
  "client_id": "YOUR_CLIENT_ID",
  "name": "Enterprise SaaS Decision Makers",
  "industries": ["Software", "SaaS"],
  "companySizes": ["201-500", "501-1000"],
  "geographies": ["United States", "United Kingdom"],
  "jobTitles": ["VP Sales", "VP Marketing", "CRO"],
  "seniority": ["VP", "C-Suite"],
  "apifyActorId": "apify/linkedin-sales-navigator",
  "apifyInput": "{\"searchUrl\":\"https://www.linkedin.com/sales/search/people?query=...\"}",
  "maxLeads": 200
}'
```

Save the returned `id` as `ICP_ID`.

**Step 2 — Validate the ICP has Apify configuration**

Retrieve the ICP and confirm `apifyActorId` is set. Without it, the FSD pipeline cannot generate leads.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/tables/ICP/ICP_ID" | jq '{apifyActorId, apifyInput, maxLeads}'
```

**CLI:**

```bash
python lgp.py tables get ICP ICP_ID
```

Verify that `apifyActorId` is non-null. If missing, the pipeline run will fail with `ICP_NO_APIFY`.

**Step 3 — Create an FSD campaign linked to the ICP**

Create a campaign that references the ICP. The pipeline will auto-resolve `apifyActorId` and `apifyInput` from the ICP record.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT_ID",
    "name": "Enterprise SaaS Q1 Campaign",
    "icpId": "ICP_ID",
    "frequency": "weekly",
    "targetLeadCount": 200,
    "enrichAfterGeneration": true,
    "scoreAfterEnrichment": true
  }' \
  https://api.leadgenius.app/api/automation/fsd/campaigns | jq
```

Save the returned campaign `id` as `CAMPAIGN_ID`.

**Step 4 — Run the FSD pipeline**

Trigger a pipeline run using the ICP. The API resolves `apifyActorId` and `apifyInput` from the ICP record automatically.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT_ID",
    "icpId": "ICP_ID",
    "targetLeadCount": 200,
    "enrichAfterGeneration": true,
    "scoreAfterEnrichment": true,
    "campaignId": "CAMPAIGN_ID"
  }' \
  https://api.leadgenius.app/api/automation/fsd/run | jq
```

**CLI:**

```bash
python lgp.py fsd run --client YOUR_CLIENT_ID --icp ICP_ID --target 200
```

Save the returned `pipelineId` as `PIPELINE_ID`.

**Step 5 — Monitor pipeline stage progression**

Poll the pipeline status to track progress through each stage: `generating` → `enriching` → `scoring` → `completed`.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/run/PIPELINE_ID" | jq '{stage, leadsGenerated, leadsEnriched, leadsScored, leadsQualified}'
```

**CLI:**

```bash
python lgp.py fsd status PIPELINE_ID
```

Repeat until `stage` is `completed` or `failed`.

**Step 6 — Verify generated leads**

List leads in the client to confirm they were generated and enriched.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/leads?client_id=YOUR_CLIENT_ID&limit=20" | jq
```

**CLI:**

```bash
python lgp.py leads list --client YOUR_CLIENT_ID --limit 20
```

Check that lead count matches `leadsGenerated` from the pipeline status and that enrichment/scoring fields are populated.

### Common Failure Points and Recovery

| Failure | Cause | Recovery |
|---------|-------|----------|
| `ICP_NOT_FOUND` | Invalid `icpId` or ICP belongs to a different company | Verify ICP ID with `tables get ICP ICP_ID` |
| `ICP_NO_APIFY` | ICP record missing `apifyActorId` | Update the ICP: `tables update ICP ICP_ID --data '{"apifyActorId":"apify/actor-id"}'` |
| `ICP_LOOKUP_FAILED` | Internal error resolving ICP | Retry the pipeline run; if persistent, verify ICP record integrity |
| Pipeline stuck at `generating` | Apify actor is slow or the search URL returns many results | Wait longer; check Apify dashboard for actor run status |
| Pipeline `failed` at enrichment | UrlSettings not configured | Create UrlSettings via `tables create UrlSettings` with required service URLs |
| Zero leads generated | Apify search parameters too narrow or actor misconfigured | Update ICP `apifyInput` with broader search criteria |


---

## 8. Multi-ICP Campaign Strategy Workflow

Create multiple ICPs for different market segments, run separate FSD campaigns per ICP, and compare generation results across segments.

### When to Use

- Targeting multiple market segments simultaneously (e.g., Enterprise vs. Mid-Market)
- A/B testing different ICP definitions to find the best-performing profile
- Running parallel campaigns for different geographies or industries

### Steps

**Step 1 — Create ICPs for each market segment**

Define separate ICP records for each target segment with distinct targeting criteria.

**Segment A — Enterprise SaaS:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT_ID",
    "name": "Enterprise SaaS",
    "industries": ["Software", "SaaS"],
    "companySizes": ["501-1000", "1001-5000"],
    "geographies": ["United States"],
    "jobTitles": ["VP Sales", "CRO", "Head of Revenue"],
    "seniority": ["VP", "C-Suite"],
    "apifyActorId": "apify/linkedin-sales-navigator",
    "apifyInput": "{\"searchUrl\":\"https://linkedin.com/sales/search/people?query=enterprise-saas\"}",
    "maxLeads": 150
  }' \
  https://api.leadgenius.app/api/automation/tables/ICP | jq
```

Save as `ICP_A_ID`.

**Segment B — Mid-Market FinTech:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT_ID",
    "name": "Mid-Market FinTech",
    "industries": ["Financial Technology", "Banking", "Payments"],
    "companySizes": ["51-200", "201-500"],
    "geographies": ["United States", "Canada"],
    "jobTitles": ["Head of Growth", "VP Marketing", "Director of Sales"],
    "seniority": ["Director", "VP"],
    "apifyActorId": "apify/linkedin-sales-navigator",
    "apifyInput": "{\"searchUrl\":\"https://linkedin.com/sales/search/people?query=fintech-midmarket\"}",
    "maxLeads": 100
  }' \
  https://api.leadgenius.app/api/automation/tables/ICP | jq
```

Save as `ICP_B_ID`.

**CLI (for each):**

```bash
python lgp.py tables create ICP --data '{"client_id":"YOUR_CLIENT_ID","name":"Enterprise SaaS","industries":["Software","SaaS"],"companySizes":["501-1000"],"apifyActorId":"apify/linkedin-sales-navigator","apifyInput":"{\"searchUrl\":\"...\"}","maxLeads":150}'
```

**Step 2 — Create separate FSD campaigns per ICP**

Each campaign targets a different ICP so results can be tracked independently.

**Campaign A:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT_ID",
    "name": "Enterprise SaaS Campaign",
    "icpId": "ICP_A_ID",
    "frequency": "weekly",
    "targetLeadCount": 150,
    "enrichAfterGeneration": true,
    "scoreAfterEnrichment": true
  }' \
  https://api.leadgenius.app/api/automation/fsd/campaigns | jq
```

**Campaign B:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT_ID",
    "name": "Mid-Market FinTech Campaign",
    "icpId": "ICP_B_ID",
    "frequency": "weekly",
    "targetLeadCount": 100,
    "enrichAfterGeneration": true,
    "scoreAfterEnrichment": true
  }' \
  https://api.leadgenius.app/api/automation/fsd/campaigns | jq
```

Save campaign IDs as `CAMPAIGN_A_ID` and `CAMPAIGN_B_ID`.

**Step 3 — Run pipelines for each campaign**

Trigger pipeline runs for both campaigns.

```bash
# Campaign A
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"client_id":"YOUR_CLIENT_ID","icpId":"ICP_A_ID","targetLeadCount":150,"enrichAfterGeneration":true,"scoreAfterEnrichment":true,"campaignId":"CAMPAIGN_A_ID"}' \
  https://api.leadgenius.app/api/automation/fsd/run | jq

# Campaign B
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"client_id":"YOUR_CLIENT_ID","icpId":"ICP_B_ID","targetLeadCount":100,"enrichAfterGeneration":true,"scoreAfterEnrichment":true,"campaignId":"CAMPAIGN_B_ID"}' \
  https://api.leadgenius.app/api/automation/fsd/run | jq
```

**CLI:**

```bash
python lgp.py fsd run --client YOUR_CLIENT_ID --icp ICP_A_ID --target 150
python lgp.py fsd run --client YOUR_CLIENT_ID --icp ICP_B_ID --target 100
```

Save both `pipelineId` values.

**Step 4 — Monitor both pipelines**

Track progress for each pipeline independently.

```bash
python lgp.py fsd status PIPELINE_A_ID
python lgp.py fsd status PIPELINE_B_ID
```

**Step 5 — Compare results across ICPs**

Once both pipelines complete, compare the campaign metrics.

```bash
# Get Campaign A metrics
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/campaigns/CAMPAIGN_A_ID" | jq '{name, totalLeadsGenerated, totalLeadsEnriched, totalLeadsScored}'

# Get Campaign B metrics
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/campaigns/CAMPAIGN_B_ID" | jq '{name, totalLeadsGenerated, totalLeadsEnriched, totalLeadsScored}'
```

**CLI:**

```bash
python lgp.py fsd campaign CAMPAIGN_A_ID
python lgp.py fsd campaign CAMPAIGN_B_ID
```

Compare `totalLeadsGenerated`, `totalLeadsEnriched`, `totalLeadsScored`, and `totalLeadsSent` across campaigns to determine which ICP performs better.

**Step 6 — Deactivate underperforming ICPs (optional)**

If one segment underperforms, deactivate its ICP.

```bash
curl -s -X PUT -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"isActive": false}' \
  https://api.leadgenius.app/api/automation/tables/ICP/ICP_B_ID | jq
```

**CLI:**

```bash
python lgp.py tables update ICP ICP_B_ID --data '{"isActive": false}'
```

### Common Failure Points and Recovery

| Failure | Cause | Recovery |
|---------|-------|----------|
| One pipeline fails, other succeeds | Different Apify configs or search parameters | Check the failed pipeline's `errorMessage`; fix the ICP's `apifyInput` and rerun |
| Both pipelines generate similar leads | ICP targeting criteria overlap too much | Narrow the criteria — use distinct `geographies`, `companySizes`, or `industries` per ICP |
| Campaign metrics show zero for one segment | ICP search parameters return no results from Apify | Broaden the ICP's `apifyInput` search URL or adjust `maxLeads` |
| Rate limiting on parallel runs | Two pipelines hitting Apify simultaneously | Stagger the runs by a few minutes; run one, wait for `generating` to complete, then run the other |


---

## 9. Iterative ICP Refinement Workflow

Run an initial ICP-based generation, review lead quality scores, update ICP targeting criteria based on results, run a refined generation, and compare before/after metrics.

### When to Use

- Initial ICP definition produced low-quality leads and needs tuning
- Optimizing an existing ICP to improve lead score averages
- Testing whether narrower or broader targeting criteria yield better results
- Continuous improvement of lead generation quality over time

### Steps

**Step 1 — Run an initial ICP-based generation**

Trigger a pipeline run with the current ICP to establish a baseline.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT_ID",
    "icpId": "ICP_ID",
    "targetLeadCount": 100,
    "enrichAfterGeneration": true,
    "scoreAfterEnrichment": true
  }' \
  https://api.leadgenius.app/api/automation/fsd/run | jq
```

**CLI:**

```bash
python lgp.py fsd run --client YOUR_CLIENT_ID --icp ICP_ID --target 100
```

Save the `pipelineId` as `PIPELINE_V1_ID`. Wait for the pipeline to reach `completed`.

```bash
python lgp.py fsd status PIPELINE_V1_ID
```

**Step 2 — Review lead quality scores**

List the generated leads and examine their `aiLeadScore` and `aiQualification` values.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/leads?client_id=YOUR_CLIENT_ID&limit=50" | jq '.data.items[] | {fullName, companyName, title, aiLeadScore, aiQualification}'
```

**CLI:**

```bash
python lgp.py leads list --client YOUR_CLIENT_ID --limit 50
```

Note the average `aiLeadScore`, the distribution of `aiQualification` values, and which leads scored lowest. Identify patterns — are low-scoring leads from the wrong industry, wrong seniority level, or wrong company size?

**Step 3 — Record baseline metrics from the pipeline run**

Capture the pipeline's per-stage metrics for comparison later.

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/run/PIPELINE_V1_ID" | jq '{leadsGenerated, leadsEnriched, leadsScored, leadsQualified, leadsSent}'
```

Record these as your V1 baseline: `leadsGenerated`, `leadsEnriched`, `leadsScored`, `leadsQualified`.

**Step 4 — Update ICP targeting criteria based on results**

Refine the ICP by narrowing or adjusting criteria that produced low-quality leads. For example, if leads from small companies scored poorly, remove smaller company sizes.

**API:**

```bash
curl -s -X PUT -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "companySizes": ["201-500", "501-1000"],
    "seniority": ["VP", "C-Suite"],
    "industries": ["Software", "SaaS"],
    "apifyInput": "{\"searchUrl\":\"https://linkedin.com/sales/search/people?query=refined-search\"}"
  }' \
  https://api.leadgenius.app/api/automation/tables/ICP/ICP_ID | jq
```

**CLI:**

```bash
python lgp.py tables update ICP ICP_ID --data '{
  "companySizes": ["201-500", "501-1000"],
  "seniority": ["VP", "C-Suite"],
  "apifyInput": "{\"searchUrl\":\"https://linkedin.com/sales/search/people?query=refined-search\"}"
}'
```

**Step 5 — Run a refined generation with the updated ICP**

Trigger a new pipeline run with the same ICP (now updated).

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT_ID",
    "icpId": "ICP_ID",
    "targetLeadCount": 100,
    "enrichAfterGeneration": true,
    "scoreAfterEnrichment": true
  }' \
  https://api.leadgenius.app/api/automation/fsd/run | jq
```

**CLI:**

```bash
python lgp.py fsd run --client YOUR_CLIENT_ID --icp ICP_ID --target 100
```

Save the `pipelineId` as `PIPELINE_V2_ID`. Wait for completion.

**Step 6 — Compare before/after metrics**

Compare V1 and V2 pipeline results side by side.

```bash
# V1 metrics
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/run/PIPELINE_V1_ID" | jq '{pipeline: "V1", leadsGenerated, leadsScored, leadsQualified}'

# V2 metrics
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/run/PIPELINE_V2_ID" | jq '{pipeline: "V2", leadsGenerated, leadsScored, leadsQualified}'
```

Key metrics to compare:
- `leadsQualified / leadsScored` ratio — higher means better targeting
- Average `aiLeadScore` across generated leads
- Number of leads matching the desired seniority and industry

If V2 shows improvement, keep the refined ICP. If not, iterate again from Step 4 with different adjustments.

### Common Failure Points and Recovery

| Failure | Cause | Recovery |
|---------|-------|----------|
| V2 scores worse than V1 | Criteria narrowed too aggressively, or Apify search URL doesn't match new criteria | Revert ICP changes and try smaller adjustments; ensure `apifyInput` search URL aligns with targeting criteria |
| Zero leads in V2 | Updated `apifyInput` search URL returns no results | Verify the search URL manually; broaden criteria slightly |
| Scores unchanged between V1 and V2 | Criteria changes didn't affect the lead pool meaningfully | Make more significant changes — try different `industries`, `geographies`, or `jobTitles` |
| Can't compare leads across runs | Both runs generated leads into the same client | Use `createdAt` filtering or create a separate client per run for clean comparison |


---

## 10. Full Automation Setup Workflow

Configure all prerequisites (UrlSettings, AgentSettings, SdrAiSettings, EmailPlatformSettings), create an ICP, create an FSD campaign with all automation flags enabled, and verify the pipeline runs end-to-end without manual intervention.

### When to Use

- Setting up a fully automated demand generation pipeline from scratch
- Onboarding a new client with complete automation capabilities
- Configuring a "set and forget" campaign that generates, enriches, scores, qualifies, and delivers leads automatically

### Steps

**Step 1 — Create UrlSettings for enrichment services**

Configure the URLs and API keys for enrichment services that the pipeline will use during the enrichment stage.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT_ID",
    "companyUrl": "https://enrichment-service.example.com/company",
    "companyUrl_Apikey": "enrich-api-key-1",
    "emailFinder": "https://enrichment-service.example.com/email",
    "emailFinder_Apikey": "enrich-api-key-2",
    "enrichment1": "https://enrichment-service.example.com/data",
    "enrichment1_Apikey": "enrich-api-key-3"
  }' \
  https://api.leadgenius.app/api/automation/tables/UrlSettings | jq
```

**CLI:**

```bash
python lgp.py tables create UrlSettings --data '{
  "client_id": "YOUR_CLIENT_ID",
  "companyUrl": "https://enrichment-service.example.com/company",
  "companyUrl_Apikey": "enrich-api-key-1",
  "emailFinder": "https://enrichment-service.example.com/email",
  "emailFinder_Apikey": "enrich-api-key-2"
}'
```

**Step 2 — Create AgentSettings for copyright (AI content generation)**

Configure the EpsimoAI agent IDs and project ID used during the copyright stage.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT_ID",
    "projectId": "epsimo-project-id",
    "enrichment1AgentId": "agent-id-for-copyright-1",
    "enrichment2AgentId": "agent-id-for-copyright-2"
  }' \
  https://api.leadgenius.app/api/automation/tables/AgentSettings | jq
```

**CLI:**

```bash
python lgp.py tables create AgentSettings --data '{
  "client_id": "YOUR_CLIENT_ID",
  "projectId": "epsimo-project-id",
  "enrichment1AgentId": "agent-id-for-copyright-1"
}'
```

**Step 3 — Create SdrAiSettings for scoring**

Configure the EpsimoAI agent IDs and project ID used during the scoring stage.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT_ID",
    "projectId": "epsimo-sdr-project-id",
    "aiLeadScoreAgentId": "agent-id-for-lead-score",
    "aiQualificationAgentId": "agent-id-for-qualification"
  }' \
  https://api.leadgenius.app/api/automation/tables/SdrAiSettings | jq
```

**CLI:**

```bash
python lgp.py tables create SdrAiSettings --data '{
  "client_id": "YOUR_CLIENT_ID",
  "projectId": "epsimo-sdr-project-id",
  "aiLeadScoreAgentId": "agent-id-for-lead-score",
  "aiQualificationAgentId": "agent-id-for-qualification"
}'
```

**Step 4 — Configure EmailPlatformSettings for delivery**

Set up the email platform integration so qualified leads can be sent automatically.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT_ID",
    "platform": "woodpecker",
    "apiKey": "woodpecker-api-key",
    "baseUrl": "https://api.woodpecker.co"
  }' \
  https://api.leadgenius.app/api/automation/tables/EmailPlatformSettings | jq
```

**CLI:**

```bash
python lgp.py tables create EmailPlatformSettings --data '{
  "client_id": "YOUR_CLIENT_ID",
  "platform": "woodpecker",
  "apiKey": "woodpecker-api-key",
  "baseUrl": "https://api.woodpecker.co"
}'
```

**Step 5 — Create an ICP with Apify configuration**

Define the target profile and lead generation source.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT_ID",
    "name": "Full Automation ICP",
    "industries": ["Software", "SaaS"],
    "companySizes": ["201-500", "501-1000"],
    "geographies": ["United States"],
    "jobTitles": ["VP Sales", "CRO", "Head of Revenue"],
    "seniority": ["VP", "C-Suite"],
    "apifyActorId": "apify/linkedin-sales-navigator",
    "apifyInput": "{\"searchUrl\":\"https://linkedin.com/sales/search/people?query=...\"}",
    "maxLeads": 200
  }' \
  https://api.leadgenius.app/api/automation/tables/ICP | jq
```

Save the returned `id` as `ICP_ID`.

**Step 6 — Create an FSD campaign with all automation flags enabled**

Create a campaign that will automatically enrich, score, qualify, and deliver leads.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT_ID",
    "name": "Full Automation Campaign",
    "icpId": "ICP_ID",
    "frequency": "weekly",
    "targetLeadCount": 200,
    "enrichAfterGeneration": true,
    "scoreAfterEnrichment": true,
    "sendToEmailPlatform": "woodpecker",
    "qualificationThreshold": 60,
    "emailCampaignId": "woodpecker-campaign-id"
  }' \
  https://api.leadgenius.app/api/automation/fsd/campaigns | jq
```

Save the returned `id` as `CAMPAIGN_ID`.

**Step 7 — Run the pipeline and verify end-to-end automation**

Trigger the pipeline. With all flags enabled, it will progress through every stage automatically.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT_ID",
    "icpId": "ICP_ID",
    "targetLeadCount": 200,
    "enrichAfterGeneration": true,
    "scoreAfterEnrichment": true,
    "sendToEmailPlatform": "woodpecker",
    "qualificationThreshold": 60,
    "campaignId": "CAMPAIGN_ID"
  }' \
  https://api.leadgenius.app/api/automation/fsd/run | jq
```

**CLI:**

```bash
python lgp.py fsd run --client YOUR_CLIENT_ID --icp ICP_ID --target 200
```

Monitor until `stage` reaches `completed`:

```bash
python lgp.py fsd status PIPELINE_ID
```

Verify the full pipeline completed all stages:

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/run/PIPELINE_ID" | jq '{stage, leadsGenerated, leadsEnriched, leadsScored, leadsQualified, leadsSent}'
```

Confirm `leadsSent > 0` to verify leads were delivered to the email platform.

### Common Failure Points and Recovery

| Failure | Cause | Recovery |
|---------|-------|----------|
| Pipeline fails at `enriching` | UrlSettings missing or misconfigured | Verify UrlSettings: `tables list UrlSettings`; ensure service URLs and API keys are correct |
| Pipeline fails at `scoring` | SdrAiSettings missing or agent IDs invalid | Verify SdrAiSettings: `tables get SdrAiSettings SETTINGS_ID`; check agent IDs with EpsimoAI |
| Pipeline completes but `leadsSent` is 0 | `qualificationThreshold` too high — no leads met the score cutoff | Lower the threshold: `fsd update-campaign CAMPAIGN_ID --data '{"qualificationThreshold":40}'` |
| Pipeline completes but `leadsQualified` is 0 | All leads scored below threshold | Review lead scores; consider lowering threshold or improving ICP targeting |
| Email platform delivery fails | EmailPlatformSettings API key invalid or platform unreachable | Verify EmailPlatformSettings; test the platform API key independently |
| `ICP_NO_APIFY` on run | ICP missing `apifyActorId` | Update ICP with Apify config before running |


---

## 11. Campaign Monitoring Dashboard Workflow

List active campaigns, check pipeline run status, review per-stage metrics, identify failed stages, and rerun failed pipelines.

### When to Use

- Daily or weekly review of active FSD campaign performance
- Identifying and recovering from pipeline failures
- Tracking cumulative campaign metrics over time
- Operational monitoring of automated demand generation

### Steps

**Step 1 — List all active campaigns**

Retrieve all FSD campaigns to see their status and cumulative metrics.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/campaigns?limit=50" | jq '.data.items[] | {id, name, isActive, frequency, totalRuns, totalLeadsGenerated, totalLeadsScored, totalLeadsSent, lastRunAt, nextRunAt}'
```

**CLI:**

```bash
python lgp.py fsd campaigns
```

Review the output for:
- `isActive`: Should be `true` for campaigns you expect to be running.
- `totalRuns`: Number of pipeline runs completed.
- `lastRunAt` / `nextRunAt`: Timing of recent and upcoming runs.
- Cumulative metrics: `totalLeadsGenerated`, `totalLeadsScored`, `totalLeadsSent`.

**Step 2 — Check the latest pipeline run status for a campaign**

Get the details of a specific campaign to find its most recent pipeline run.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/campaigns/CAMPAIGN_ID" | jq
```

**CLI:**

```bash
python lgp.py fsd campaign CAMPAIGN_ID
```

Note the `lastRunAt` timestamp and any associated pipeline run ID.

**Step 3 — Review per-stage metrics of a pipeline run**

Inspect the pipeline run to see how many leads progressed through each stage.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/run/PIPELINE_ID" | jq '{stage, leadsGenerated, leadsEnriched, leadsScored, leadsQualified, leadsSent, errorMessage, stageErrors, startedAt, finishedAt}'
```

**CLI:**

```bash
python lgp.py fsd status PIPELINE_ID
```

Key indicators:
- `stage: "completed"` — pipeline finished successfully.
- `stage: "failed"` — pipeline stopped at a stage; check `errorMessage` and `stageErrors`.
- Large drop between stages (e.g., 100 generated but only 10 enriched) — indicates issues at that stage.

**Step 4 — Identify and diagnose failed stages**

If `stage` is `failed`, examine the error details.

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/run/PIPELINE_ID" | jq '{stage, errorMessage, stageErrors}'
```

Common failure patterns:

| Failed Stage | Likely Cause | Diagnostic Step |
|-------------|-------------|-----------------|
| `generating` | Apify actor error or ICP misconfiguration | Check ICP's `apifyActorId` and `apifyInput` |
| `enriching` | UrlSettings missing or service down | Verify: `tables list UrlSettings` |
| `scoring` | SdrAiSettings missing or agent error | Verify: `tables list SdrAiSettings` |
| `qualifying` | No leads met the `qualificationThreshold` | Review lead scores; consider lowering threshold |
| `sending` | EmailPlatformSettings invalid or platform error | Verify: `tables list EmailPlatformSettings` |

**Step 5 — Rerun a failed pipeline**

After fixing the underlying issue (e.g., updating UrlSettings), trigger a new pipeline run for the same campaign and ICP.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "YOUR_CLIENT_ID",
    "icpId": "ICP_ID",
    "targetLeadCount": 200,
    "enrichAfterGeneration": true,
    "scoreAfterEnrichment": true,
    "campaignId": "CAMPAIGN_ID"
  }' \
  https://api.leadgenius.app/api/automation/fsd/run | jq
```

**CLI:**

```bash
python lgp.py fsd run --client YOUR_CLIENT_ID --icp ICP_ID --target 200
```

Monitor the new run to confirm it progresses past the previously failed stage.

```bash
python lgp.py fsd status NEW_PIPELINE_ID
```

**Step 6 — Deactivate a problematic campaign (optional)**

If a campaign is consistently failing and needs investigation, deactivate it to prevent further scheduled runs.

**API:**

```bash
curl -s -X DELETE -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/campaigns/CAMPAIGN_ID" | jq
```

**CLI:**

```bash
python lgp.py fsd deactivate-campaign CAMPAIGN_ID
```

This sets `isActive: false` (soft delete). Reactivate later by updating the campaign:

```bash
curl -s -X PUT -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"isActive": true}' \
  https://api.leadgenius.app/api/automation/fsd/campaigns/CAMPAIGN_ID | jq
```

### Common Failure Points and Recovery

| Failure | Cause | Recovery |
|---------|-------|----------|
| Campaign shows `isActive: false` unexpectedly | Campaign was deactivated manually or by a failed run | Reactivate: `PUT /fsd/campaigns/ID` with `{"isActive": true}` |
| `nextRunAt` is in the past | Scheduled run was missed (system downtime or campaign was inactive) | Trigger a manual run with `fsd run`; the next scheduled run will be set automatically |
| Cumulative metrics not updating | Pipeline runs are failing before completion | Check the latest pipeline run status for errors |
| Multiple failed runs in a row | Persistent configuration issue | Review all prerequisites (UrlSettings, AgentSettings, SdrAiSettings, EmailPlatformSettings); fix the root cause before rerunning |
| Pipeline stuck (not `completed` or `failed`) | Long-running Apify actor or enrichment service timeout | Wait longer; if stuck for hours, the run may need manual investigation |


---

## 12. Qualification and Delivery Workflow

Filter scored leads by `qualificationThreshold`, route qualified leads to an email platform via `sendToEmailPlatform`, and verify delivery through webhook events.

### When to Use

- After scoring leads and wanting to send only high-quality leads to outreach
- Setting up the qualification-to-delivery leg of an FSD pipeline
- Verifying that qualified leads actually reached the email platform
- Debugging delivery issues when leads are scored but not appearing in the outreach tool

### Steps

**Step 1 — Review scored leads and their qualification status**

After a pipeline run completes scoring, review the leads to understand the score distribution.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/leads?client_id=YOUR_CLIENT_ID&limit=50" | jq '.data.items[] | {id, fullName, companyName, aiLeadScore, aiQualification}'
```

**CLI:**

```bash
python lgp.py leads list --client YOUR_CLIENT_ID --limit 50
```

Note the range of `aiLeadScore` values. Leads with a score at or above the `qualificationThreshold` will be qualified for delivery.

**Step 2 — Understand the qualification threshold**

The `qualificationThreshold` (0–100) set on the FSD campaign or pipeline run determines the cutoff. Only leads with `aiLeadScore >= qualificationThreshold` pass to the `sending` stage.

Check the campaign's threshold:

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/campaigns/CAMPAIGN_ID" | jq '{qualificationThreshold, sendToEmailPlatform, emailCampaignId}'
```

If the threshold is too high (few leads qualify) or too low (too many unqualified leads sent), update it:

**API:**

```bash
curl -s -X PUT -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"qualificationThreshold": 55}' \
  https://api.leadgenius.app/api/automation/fsd/campaigns/CAMPAIGN_ID | jq
```

**CLI:**

```bash
python lgp.py fsd update-campaign CAMPAIGN_ID --data '{"qualificationThreshold": 55}'
```

**Step 3 — Verify email platform routing configuration**

Confirm that `sendToEmailPlatform` and `emailCampaignId` are set on the campaign so qualified leads are routed correctly.

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/campaigns/CAMPAIGN_ID" | jq '{sendToEmailPlatform, emailCampaignId, qualificationThreshold}'
```

If `sendToEmailPlatform` is null, update the campaign:

```bash
curl -s -X PUT -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "sendToEmailPlatform": "woodpecker",
    "emailCampaignId": "woodpecker-campaign-id"
  }' \
  https://api.leadgenius.app/api/automation/fsd/campaigns/CAMPAIGN_ID | jq
```

Also verify that EmailPlatformSettings exist for the platform:

```bash
python lgp.py tables list EmailPlatformSettings
```

**Step 4 — Check pipeline run delivery metrics**

After a pipeline run completes, verify how many leads were qualified and sent.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/run/PIPELINE_ID" | jq '{stage, leadsScored, leadsQualified, leadsSent, qualificationThreshold, sendToEmailPlatform}'
```

**CLI:**

```bash
python lgp.py fsd status PIPELINE_ID
```

Key metrics:
- `leadsScored`: Total leads that received scores.
- `leadsQualified`: Leads with `aiLeadScore >= qualificationThreshold`.
- `leadsSent`: Leads successfully sent to the email platform.
- If `leadsQualified > leadsSent`, some deliveries failed — check `stageErrors`.

**Step 5 — Verify delivery via webhook events**

Once leads are sent to the email platform, the platform sends webhook events back (e.g., email opened, clicked, replied). Check for incoming webhook events to confirm delivery.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/webhook-events?limit=20" | jq '.data.items[] | {id, eventType, matchStatus, matchedLeadId, createdAt}'
```

**CLI:**

```bash
python lgp.py webhooks list --limit 20
```

Look for events with `eventType` like `email_sent`, `email_opened`, or `email_clicked` that correspond to the leads you sent.

**Step 6 — Reprocess unmatched webhook events (if needed)**

If webhook events arrived but didn't match to leads (e.g., timing issue), reprocess them.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  https://api.leadgenius.app/api/automation/webhook-events/EVENT_ID/reprocess | jq
```

**CLI:**

```bash
python lgp.py webhooks reprocess EVENT_ID
```

See [Workflow 3: Webhook Reprocessing](#3-webhook-reprocessing-workflow) for the full reprocessing procedure.

**Step 7 — Send qualified leads manually (alternative)**

If the pipeline didn't have `sendToEmailPlatform` configured, you can send qualified leads manually using the email platforms API.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "platform": "woodpecker",
    "campaignId": "woodpecker-campaign-id",
    "leadIds": ["lead-1", "lead-2", "lead-3"]
  }' \
  https://api.leadgenius.app/api/automation/email-platforms/send | jq
```

### Common Failure Points and Recovery

| Failure | Cause | Recovery |
|---------|-------|----------|
| `leadsQualified` is 0 | All leads scored below `qualificationThreshold` | Lower the threshold on the campaign; or improve ICP targeting to generate higher-quality leads |
| `leadsSent` is 0 but `leadsQualified` > 0 | `sendToEmailPlatform` not configured, or EmailPlatformSettings missing/invalid | Set `sendToEmailPlatform` on the campaign; verify EmailPlatformSettings exist with valid API key |
| No webhook events after sending | Email platform not configured to send webhooks, or webhook URL not set | Configure webhook URL in the email platform's settings to point to your LeadGenius webhook endpoint |
| Webhook events unmatched | Leads were sent but webhook contact data doesn't match lead records | Reprocess unmatched events after verifying lead email addresses match the platform's contact data |
| Threshold too aggressive | Very few leads qualify, reducing campaign volume | Analyze score distribution; set threshold to capture the top 30-50% of scored leads |
| Duplicate sends | Pipeline rerun sends leads that were already delivered | Check if leads were already sent in a previous run before triggering a new pipeline |
