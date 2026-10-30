# Business Use Cases

End-to-end business scenario guides for LeadGenius Pro. Each use case includes business context, prerequisites, step-by-step execution with API and CLI commands, and expected outcomes.

---

## 1. New Customer Onboarding

### Business Context

When a new customer signs up for LeadGenius Pro, they need a fully provisioned environment before they can generate and process leads. This use case walks through the complete setup: creating the user account, company, client partition, all required configuration records, an initial ICP, and running the first FSD pipeline to verify everything works end-to-end.

### Prerequisites

- A valid LeadGenius Pro admin API key (`lgp_` prefix) with provisioning permissions
- Enrichment service URLs and API keys (for UrlSettings)
- EpsimoAI project ID and agent IDs (for AgentSettings and SdrAiSettings)
- An Apify actor ID and input configuration (for the initial ICP)

### Steps

**Step 1 — Provision the user**

Create a Cognito user, company, CompanyUser record, and API key in a single call.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "email": "jane@acmecorp.com",
    "password": "SecurePass123!",
    "name": "Jane Doe",
    "companyName": "Acme Corp",
    "role": "owner",
    "group": "admin",
    "createApiKey": true,
    "apiKeyName": "Jane - Primary Key"
  }' \
  https://api.leadgenius.app/api/automation/users/provision | jq
```

**CLI:**

```bash
python lgp.py users provision \
  --email jane@acmecorp.com \
  --password "SecurePass123!" \
  --company-name "Acme Corp"
```

**Expected outcome:** Response contains `cognito.sub`, `company.id`, `companyUser.id`, and `apiKey.plainTextKey`. Save the `plainTextKey` immediately — it is only returned once. Note the `company.id` for subsequent steps.

**Step 2 — Create a client for data isolation**

Clients partition lead data within a company (e.g., per campaign or market segment).

**API:**

```bash
curl -s -X POST -H "X-API-Key: $NEW_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "clientName": "Acme - Enterprise",
    "companyURL": "https://acmecorp.com",
    "description": "Enterprise segment leads"
  }' \
  https://api.leadgenius.app/api/automation/tables/Client | jq
```

**CLI:**

```bash
python lgp.py tables create Client \
  --data '{"clientName":"Acme - Enterprise","companyURL":"https://acmecorp.com","description":"Enterprise segment leads"}'
```

**Expected outcome:** A `Client` record is created with an auto-generated `id`. Note this `client_id` — it is required for all lead operations and campaign setup.

**Step 3 — Configure UrlSettings (enrichment services)**

UrlSettings provides the service URLs and API keys needed for lead enrichment.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $NEW_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "CLIENT_ID",
    "companyUrl": "https://company-lookup.example.com/api",
    "companyUrl_Apikey": "key_company_xxx",
    "emailFinder": "https://email-finder.example.com/api",
    "emailFinder_Apikey": "key_email_xxx",
    "enrichment1": "https://enrichment-svc.example.com/api",
    "enrichment1_Apikey": "key_enrich_xxx"
  }' \
  https://api.leadgenius.app/api/automation/tables/UrlSettings | jq
```

**CLI:**

```bash
python lgp.py tables create UrlSettings \
  --data '{
    "client_id": "CLIENT_ID",
    "companyUrl": "https://company-lookup.example.com/api",
    "companyUrl_Apikey": "key_company_xxx",
    "emailFinder": "https://email-finder.example.com/api",
    "emailFinder_Apikey": "key_email_xxx",
    "enrichment1": "https://enrichment-svc.example.com/api",
    "enrichment1_Apikey": "key_enrich_xxx"
  }'
```

**Expected outcome:** A `UrlSettings` record is created. Enrichment tasks can now resolve service endpoints for the company.

**Step 4 — Configure AgentSettings (copyright / AI content generation)**

AgentSettings maps copyright processes to EpsimoAI agents.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $NEW_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "CLIENT_ID",
    "projectId": "epsimo-project-xxx",
    "enrichment1AgentId": "agent-copyright-1",
    "enrichment2AgentId": "agent-copyright-2"
  }' \
  https://api.leadgenius.app/api/automation/tables/AgentSettings | jq
```

**CLI:**

```bash
python lgp.py tables create AgentSettings \
  --data '{
    "client_id": "CLIENT_ID",
    "projectId": "epsimo-project-xxx",
    "enrichment1AgentId": "agent-copyright-1",
    "enrichment2AgentId": "agent-copyright-2"
  }'
```

**Expected outcome:** An `AgentSettings` record is created. Copyright tasks can now invoke the configured AI agents.

**Step 5 — Configure SdrAiSettings (SDR AI scoring)**

SdrAiSettings maps scoring fields to EpsimoAI agents.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $NEW_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "CLIENT_ID",
    "projectId": "epsimo-project-xxx",
    "aiLeadScoreAgentId": "agent-score-lead",
    "aiQualificationAgentId": "agent-score-qual",
    "aiNextActionAgentId": "agent-score-action",
    "aiColdEmailAgentId": "agent-score-email"
  }' \
  https://api.leadgenius.app/api/automation/tables/SdrAiSettings | jq
```

**CLI:**

```bash
python lgp.py tables create SdrAiSettings \
  --data '{
    "client_id": "CLIENT_ID",
    "projectId": "epsimo-project-xxx",
    "aiLeadScoreAgentId": "agent-score-lead",
    "aiQualificationAgentId": "agent-score-qual",
    "aiNextActionAgentId": "agent-score-action",
    "aiColdEmailAgentId": "agent-score-email"
  }'
```

**Expected outcome:** An `SdrAiSettings` record is created. Scoring tasks can now invoke the configured AI agents.

**Step 6 — Create an initial ICP with Apify configuration**

The ICP defines the target customer profile and includes Apify actor configuration for automated lead generation.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $NEW_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "CLIENT_ID",
    "name": "Enterprise SaaS Decision Makers",
    "description": "VP+ at mid-market SaaS companies in North America",
    "industries": ["Software", "SaaS", "Cloud Computing"],
    "companySizes": ["51-200", "201-500", "501-1000"],
    "geographies": ["United States", "Canada"],
    "jobTitles": ["VP Sales", "VP Marketing", "CRO", "CMO"],
    "seniority": ["VP", "C-Suite", "Director"],
    "departments": ["Sales", "Marketing"],
    "keywords": ["B2B", "enterprise sales", "demand generation"],
    "technologies": ["Salesforce", "HubSpot"],
    "apifyActorId": "apify/linkedin-sales-navigator-scraper",
    "apifyInput": "{\"searchUrl\":\"https://www.linkedin.com/sales/search/people?query=...\",\"maxResults\":100}",
    "maxLeads": 100,
    "isActive": true
  }' \
  https://api.leadgenius.app/api/automation/tables/ICP | jq
```

**CLI:**

```bash
python lgp.py tables create ICP \
  --data '{
    "client_id": "CLIENT_ID",
    "name": "Enterprise SaaS Decision Makers",
    "industries": ["Software", "SaaS", "Cloud Computing"],
    "companySizes": ["51-200", "201-500", "501-1000"],
    "geographies": ["United States", "Canada"],
    "jobTitles": ["VP Sales", "VP Marketing", "CRO", "CMO"],
    "seniority": ["VP", "C-Suite", "Director"],
    "apifyActorId": "apify/linkedin-sales-navigator-scraper",
    "apifyInput": "{\"searchUrl\":\"https://www.linkedin.com/sales/search/people?query=...\",\"maxResults\":100}",
    "maxLeads": 100
  }'
```

**Expected outcome:** An `ICP` record is created with an auto-generated `id`. Note this `icpId` for the next step.

**Step 7 — Run the first FSD pipeline**

Trigger an FSD pipeline run using the ICP created in Step 6. This verifies the entire setup works end-to-end.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $NEW_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "CLIENT_ID",
    "icpId": "ICP_ID",
    "targetLeadCount": 25,
    "enrichAfterGeneration": true,
    "scoreAfterEnrichment": true
  }' \
  https://api.leadgenius.app/api/automation/fsd/run | jq
```

**CLI:**

```bash
python lgp.py fsd run \
  --client CLIENT_ID \
  --icp ICP_ID \
  --target 25
```

**Expected outcome:** Response returns a `pipelineId` with `stage: "generating"`. The pipeline will progress through `generating` → `enriching` → `scoring` → `completed` automatically because the automation flags are enabled. Use a small `targetLeadCount` (e.g., 25) for the first run to validate quickly.

**Step 8 — Monitor pipeline progress**

Poll the pipeline status until it reaches `completed` or `failed`.

**API:**

```bash
curl -s -H "X-API-Key: $NEW_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/run/PIPELINE_ID" | jq
```

**CLI:**

```bash
python lgp.py fsd status PIPELINE_ID
```

**Expected outcome:** The response shows the current `stage` and per-stage counts (`leadsGenerated`, `leadsEnriched`, `leadsScored`). When `stage` is `completed`, all counts should be populated. If `stage` is `failed`, check `errorMessage` and `stageErrors` for diagnostics.

### Expected Outcomes

After completing all steps, the new customer environment includes:

- A Cognito user with confirmed status and a stored API key
- A company with the user as owner/admin
- A client partition for lead data isolation
- UrlSettings configured for enrichment services
- AgentSettings configured for AI content generation
- SdrAiSettings configured for SDR AI scoring
- An active ICP with targeting criteria and Apify configuration
- A completed FSD pipeline run with generated, enriched, and scored leads

### Common Failure Points

| Failure | Cause | Recovery |
|---------|-------|----------|
| Provisioning returns "email already exists" | Cognito user already created | Use `POST /api/automation/users/cognito` with `action: "set-password"` to reset, or provision with a different email |
| Provisioning returns "invalid password" | Password does not meet Cognito policy (min 8 chars, mixed case, number, symbol) | Retry with a compliant password |
| FSD run returns `ICP_NOT_FOUND` | ICP ID is incorrect or belongs to a different company | Verify the ICP ID with `GET /api/automation/tables/ICP/ICP_ID` |
| FSD run returns `ICP_NO_APIFY` | ICP record is missing `apifyActorId` | Update the ICP: `PUT /api/automation/tables/ICP/ICP_ID` with `apifyActorId` |
| Pipeline stuck at `enriching` | UrlSettings not configured or service URLs unreachable | Verify UrlSettings exists and service endpoints are correct |
| Pipeline stuck at `scoring` | SdrAiSettings not configured or agent IDs invalid | Verify SdrAiSettings exists and agent IDs are correct |

---

## 2. ICP-Driven Campaign Launch

### Business Context

Once a customer environment is provisioned (see Use Case 1), the primary workflow is launching targeted lead generation campaigns driven by ICP definitions. This use case covers defining an ICP with specific targeting criteria and Apify configuration, creating an FSD campaign for recurring execution, running the pipeline, monitoring each stage, reviewing the generated leads, and verifying email platform delivery.

### Prerequisites

- A provisioned user with a valid API key (`lgp_` prefix)
- An existing client (`client_id`) with data isolation configured
- UrlSettings configured (for enrichment)
- AgentSettings configured (for copyright)
- SdrAiSettings configured (for scoring)
- EmailPlatformSettings configured (for email delivery — optional, only if `sendToEmailPlatform` is used)
- An Apify actor ID and search parameters for the target market

### Steps

**Step 1 — Define the ICP with targeting criteria and Apify config**

Create an ICP record that describes the ideal customer profile and includes the Apify actor configuration for lead scraping.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "CLIENT_ID",
    "name": "Mid-Market FinTech CTOs",
    "description": "Technical decision makers at FinTech companies, 50-500 employees",
    "industries": ["Financial Technology", "Banking Software", "Payments"],
    "companySizes": ["51-200", "201-500"],
    "geographies": ["United States", "United Kingdom", "Germany"],
    "jobTitles": ["CTO", "VP Engineering", "Head of Technology", "Director of Engineering"],
    "seniority": ["C-Suite", "VP", "Director"],
    "departments": ["Engineering", "Technology", "IT"],
    "functions": ["Technology", "Engineering"],
    "keywords": ["fintech", "digital payments", "banking API", "open banking"],
    "technologies": ["AWS", "Kubernetes", "Python", "Node.js"],
    "apifyActorId": "apify/linkedin-sales-navigator-scraper",
    "apifyInput": "{\"searchUrl\":\"https://www.linkedin.com/sales/search/people?query=(keywords:fintech CTO)&geoUrn=103644278\",\"maxResults\":200}",
    "apifySettings": "{\"proxyConfiguration\":{\"useApifyProxy\":true}}",
    "maxLeads": 200,
    "leadSources": ["LinkedIn Sales Navigator"],
    "qualificationCriteria": "{\"minCompanySize\":50,\"requiredIndustry\":\"FinTech\"}",
    "scoringWeights": "{\"industryMatch\":0.3,\"seniorityMatch\":0.3,\"companySize\":0.2,\"technologyMatch\":0.2}",
    "isActive": true
  }' \
  https://api.leadgenius.app/api/automation/tables/ICP | jq
```

**CLI:**

```bash
python lgp.py tables create ICP \
  --data '{
    "client_id": "CLIENT_ID",
    "name": "Mid-Market FinTech CTOs",
    "industries": ["Financial Technology", "Banking Software", "Payments"],
    "companySizes": ["51-200", "201-500"],
    "geographies": ["United States", "United Kingdom", "Germany"],
    "jobTitles": ["CTO", "VP Engineering", "Head of Technology"],
    "seniority": ["C-Suite", "VP", "Director"],
    "keywords": ["fintech", "digital payments", "banking API"],
    "apifyActorId": "apify/linkedin-sales-navigator-scraper",
    "apifyInput": "{\"searchUrl\":\"https://www.linkedin.com/sales/search/people?query=(keywords:fintech CTO)\",\"maxResults\":200}",
    "maxLeads": 200
  }'
```

**Expected outcome:** An `ICP` record is created. Note the returned `id` as `ICP_ID`.

**Step 2 — Create an FSD campaign**

Create a persistent campaign record that links the ICP and defines automation behavior. The campaign can be run once or on a recurring schedule.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "CLIENT_ID",
    "name": "FinTech CTO Outreach - Q1",
    "icpId": "ICP_ID",
    "frequency": "weekly",
    "targetLeadCount": 200,
    "enrichAfterGeneration": true,
    "scoreAfterEnrichment": true,
    "sendToEmailPlatform": "woodpecker",
    "qualificationThreshold": 60,
    "emailCampaignId": "woodpecker-campaign-123"
  }' \
  https://api.leadgenius.app/api/automation/fsd/campaigns | jq
```

**CLI:**

```bash
python lgp.py fsd create-campaign \
  --client CLIENT_ID \
  --name "FinTech CTO Outreach - Q1" \
  --icp ICP_ID \
  --frequency weekly \
  --target 200
```

**Expected outcome:** An `FsdCampaign` record is created with `isActive: true`. The campaign is configured to:
- Generate 200 leads per run from the ICP's Apify config
- Automatically enrich leads after generation
- Automatically score leads after enrichment
- Filter leads with `aiLeadScore >= 60`
- Send qualified leads to Woodpecker campaign `woodpecker-campaign-123`

Note the returned campaign `id` as `CAMPAIGN_ID`.

**Step 3 — Run the FSD pipeline**

Trigger a pipeline run for the campaign. The pipeline resolves the Apify actor and input from the linked ICP automatically.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "CLIENT_ID",
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
python lgp.py fsd run \
  --client CLIENT_ID \
  --icp ICP_ID \
  --target 200 \
  --campaign CAMPAIGN_ID
```

**Expected outcome:** Response returns `pipelineId` with `stage: "generating"` and the automation flags confirmed. Note the `pipelineId` for monitoring.

**Step 4 — Monitor stage progression**

Poll the pipeline status to track progress through each stage. The pipeline progresses automatically: `generating` → `enriching` → `scoring` → `qualifying` → `sending` → `completed`.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/run/PIPELINE_ID" | jq
```

**CLI:**

```bash
python lgp.py fsd status PIPELINE_ID
```

**Expected outcome at each stage:**

| Stage | Key Fields | What to Check |
|-------|-----------|---------------|
| `generating` | `leadsGenerated` increasing | Apify actor is running and producing leads |
| `enriching` | `leadsEnriched` increasing | Enrichment services are processing leads |
| `scoring` | `leadsScored` increasing | SDR AI agents are scoring leads |
| `qualifying` | `leadsQualified` populated | Leads filtered by `qualificationThreshold` (60) |
| `sending` | `leadsSent` increasing | Qualified leads being sent to Woodpecker |
| `completed` | `finishedAt` populated | All stages finished successfully |
| `failed` | `errorMessage`, `stageErrors` | Check which stage failed and why |

Poll every 30–60 seconds. Generation typically takes 2–10 minutes depending on `targetLeadCount`. Enrichment and scoring add 1–5 minutes each.

**Step 5 — Review generated and scored leads**

Once the pipeline reaches `completed` (or at least `scoring`), review the leads in the client.

**API:**

```bash
# List leads in the client
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/leads?client_id=CLIENT_ID&limit=20" | jq

# Get a specific lead with all enrichment and scoring data
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/leads/LEAD_ID" | jq
```

**CLI:**

```bash
# List leads
python lgp.py leads list --client CLIENT_ID --limit 20

# Get lead details
python lgp.py leads get LEAD_ID
```

**What to verify on each lead:**

- Identity fields populated: `firstName`, `lastName`, `email`, `linkedinUrl`, `title`, `companyName`
- Enrichment fields populated: `companyDomain`, `companyUrl`, `enrichment1` (etc.)
- Scoring fields populated: `aiLeadScore` (numeric 0–100), `aiQualification` (text assessment), `aiNextAction`
- Leads with `aiLeadScore >= 60` should have been sent to the email platform

**Step 6 — Verify email platform delivery**

Confirm that qualified leads were delivered to the configured email platform (Woodpecker).

**API:**

```bash
# List email platform integrations
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/email-platforms" | jq

# Check webhook events for delivery confirmations
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/webhook-events?limit=20" | jq
```

**CLI:**

```bash
# List email platforms
python lgp.py email-platforms list

# Check webhook events
python lgp.py webhooks list --limit 20
```

**Expected outcome:** The pipeline's `leadsSent` count matches the number of leads with `aiLeadScore >= qualificationThreshold`. Webhook events from the email platform confirm delivery and track engagement (opens, clicks, replies).

### Expected Outcomes

After completing all steps, the campaign produces:

- An ICP record with full targeting criteria and Apify configuration
- An FSD campaign configured for weekly recurring runs
- A completed pipeline run with metrics at each stage
- Leads generated, enriched, scored, qualified, and delivered to the email platform
- Webhook events tracking email engagement for delivered leads

### Common Failure Points

| Failure | Cause | Recovery |
|---------|-------|----------|
| `ICP_NOT_FOUND` on pipeline run | ICP ID incorrect or deleted | Verify with `GET /api/automation/tables/ICP/ICP_ID` |
| `ICP_NO_APIFY` on pipeline run | ICP missing `apifyActorId` field | Update ICP: `PUT /api/automation/tables/ICP/ICP_ID` with `apifyActorId` |
| `ICP_LOOKUP_FAILED` on pipeline run | Internal error resolving ICP | Retry the pipeline run; if persistent, recreate the ICP |
| Pipeline fails at `generating` | Apify actor ID invalid or input malformed | Verify `apifyActorId` exists and `apifyInput` is valid JSON |
| Pipeline fails at `enriching` | UrlSettings missing or service endpoints down | Check UrlSettings record and verify service URLs are reachable |
| Pipeline fails at `scoring` | SdrAiSettings missing or agent IDs invalid | Check SdrAiSettings record and verify agent IDs |
| `leadsQualified` is 0 | `qualificationThreshold` too high for the lead set | Lower the threshold or review scoring results to calibrate |
| `leadsSent` is 0 but `leadsQualified` > 0 | EmailPlatformSettings not configured or platform API key invalid | Verify EmailPlatformSettings exists with correct `platform`, `apiKey`, and `campaignId` |

---

## 3. Lead Qualification Pipeline

### Business Context

Raw leads imported from external sources (CSV files, CRM exports, partner lists) need to pass through a multi-stage qualification pipeline before they are ready for sales outreach. This use case covers the full journey: importing raw leads into a client, enriching them with external data services, generating AI content via copyright, scoring them with SDR AI, filtering by a qualification threshold, and sending qualified leads to an email platform for outreach. Each stage builds on the previous one — enrichment populates company and contact data, copyright generates personalized messaging, and scoring produces the numeric lead score used for qualification filtering.

### Prerequisites

- A valid API key (`lgp_` prefix) with access to the target client
- An existing `client_id` with data isolation configured
- UrlSettings configured for the company (enrichment service URLs and API keys)
- AgentSettings configured for the company (EpsimoAI agent IDs for copyright processes)
- SdrAiSettings configured for the company (EpsimoAI agent IDs for scoring fields)
- EmailPlatformSettings configured (optional — only if sending qualified leads to outreach)
- Raw lead data in JSON format with at least `firstName`, `lastName`, `email`, and `companyName`

### Steps

**Step 1 — Import raw leads**

Import a batch of raw leads into the target client. The API accepts up to 500 leads per request.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "CLIENT_ID",
    "leads": [
      {
        "firstName": "Sarah",
        "lastName": "Chen",
        "email": "sarah.chen@techstartup.io",
        "companyName": "TechStartup Inc",
        "title": "VP of Engineering",
        "linkedinUrl": "https://linkedin.com/in/sarah-chen"
      },
      {
        "firstName": "Marcus",
        "lastName": "Rivera",
        "email": "m.rivera@globalfinance.com",
        "companyName": "Global Finance Corp",
        "title": "CTO",
        "linkedinUrl": "https://linkedin.com/in/marcus-rivera"
      },
      {
        "firstName": "Aisha",
        "lastName": "Patel",
        "email": "aisha@cloudops.dev",
        "companyName": "CloudOps Solutions",
        "title": "Director of Technology"
      }
    ]
  }' \
  https://api.leadgenius.app/api/automation/leads/import | jq
```

**CLI:**

```bash
python lgp.py leads import \
  --client CLIENT_ID \
  --file raw_leads.json
```

**Expected outcome:** Response returns `imported` count and an array of created lead IDs. Cross-client duplicates are flagged as warnings but do not block the import. Note the lead IDs for subsequent steps.

**Step 2 — Enrich leads with external data**

Trigger enrichment for each imported lead. Enrichment populates company data (`companyDomain`, `companyUrl`), verifies emails, and runs configured enrichment services.

**API:**

```bash
# Enrich a single lead with all configured services
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"leadId": "LEAD_ID_1"}' \
  https://api.leadgenius.app/api/automation/tasks/enrich | jq

# Enrich with specific services only
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"leadId": "LEAD_ID_2", "services": ["companyUrl", "emailFinder", "enrichment1"]}' \
  https://api.leadgenius.app/api/automation/tasks/enrich | jq
```

**CLI:**

```bash
# Enrich with all services
python lgp.py tasks enrich --lead LEAD_ID_1

# Enrich with specific services
python lgp.py tasks enrich --lead LEAD_ID_2 --services companyUrl,emailFinder,enrichment1
```

**Expected outcome:** Each call returns a `jobId` and lists `triggered` and `skipped` services. Services are skipped if the corresponding URL is not configured in UrlSettings. Monitor the job until `status: "completed"`.

**Step 3 — Monitor enrichment jobs**

Poll each enrichment job until it completes.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/tasks/JOB_ID" | jq
```

**CLI:**

```bash
python lgp.py tasks status JOB_ID
```

**Expected outcome:** Job transitions from `running` → `completed`. The `completedTasks` and `failedTasks` counts indicate how many enrichment services succeeded. Once completed, the lead's enrichment fields (`companyDomain`, `companyUrl`, `enrichment1`, etc.) are populated.

**Step 4 — Generate AI content via copyright**

Trigger copyright processes to generate personalized messaging and AI content for each enriched lead.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"leadId": "LEAD_ID_1"}' \
  https://api.leadgenius.app/api/automation/tasks/copyright | jq
```

**CLI:**

```bash
python lgp.py tasks copyright --lead LEAD_ID_1
```

**Expected outcome:** Returns a `jobId` with `triggered` processes. Each process maps to an AI agent configured in AgentSettings (e.g., `enrichment1AgentId`). Once completed, the lead's AI content fields (`ai1`–`ai10`, `message1`–`message10`) are populated with generated content.

**Step 5 — Score leads with SDR AI**

Trigger scoring for all enriched leads. Use batch scoring (up to 100 leads) for efficiency.

**API:**

```bash
# Batch score multiple leads
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "leadIds": ["LEAD_ID_1", "LEAD_ID_2", "LEAD_ID_3"],
    "fields": ["aiLeadScore", "aiQualification", "aiNextAction", "aiColdEmail"]
  }' \
  https://api.leadgenius.app/api/automation/tasks/score | jq
```

**CLI:**

```bash
# Score a single lead with all fields
python lgp.py tasks score --lead LEAD_ID_1

# Score with specific fields
python lgp.py tasks score --lead LEAD_ID_1 --fields aiLeadScore,aiQualification
```

**Expected outcome:** Returns a `jobId` with the number of scoring tasks triggered (fields × leads). Once completed, each lead has:
- `aiLeadScore`: numeric score 0–100
- `aiQualification`: text assessment (e.g., "Highly Qualified", "Needs Nurturing")
- `aiNextAction`: recommended next step
- `aiColdEmail`: generated cold email draft

**Step 6 — Filter qualified leads by score threshold**

List leads and filter by score to identify those meeting the qualification bar.

**API:**

```bash
# List leads sorted by score — review those above your threshold
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/leads?client_id=CLIENT_ID&limit=100" | jq '.data[] | select(.aiScoreValue >= 60) | {id, fullName, companyName, aiScoreValue, aiQualification}'
```

**CLI:**

```bash
python lgp.py leads list --client CLIENT_ID --limit 100 --format json
```

**Expected outcome:** Leads with `aiLeadScore >= 60` (or your chosen threshold) are considered qualified and ready for outreach. Leads below the threshold may need further nurturing or ICP refinement.

**Step 7 — Send qualified leads to outreach**

Send qualified leads to the configured email platform for campaign delivery.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "leadIds": ["LEAD_ID_1", "LEAD_ID_2"],
    "platform": "woodpecker",
    "campaignId": "woodpecker-campaign-456"
  }' \
  https://api.leadgenius.app/api/automation/email-platforms/send | jq
```

**CLI:**

```bash
python lgp.py email-platforms send \
  --leads LEAD_ID_1,LEAD_ID_2 \
  --platform woodpecker \
  --campaign woodpecker-campaign-456
```

**Expected outcome:** Qualified leads are delivered to the email platform. The response confirms the number of leads sent and any delivery errors. Track engagement via webhook events (see Use Case 5 — Multi-Channel Outreach).

### Expected Outcomes

After completing the full pipeline, each lead has progressed through:

- **Import**: Raw lead data stored in the target client
- **Enrichment**: Company data, email verification, and external data populated
- **Copyright**: AI-generated personalized messaging and content
- **Scoring**: Numeric lead score (0–100), qualification assessment, and recommended actions
- **Qualification**: Leads filtered by score threshold into qualified and unqualified segments
- **Delivery**: Qualified leads sent to the email platform for outreach

### Common Failure Points

| Failure | Cause | Recovery |
|---------|-------|----------|
| Import returns `MISSING_CLIENT_ID` | `client_id` not provided in request body | Add `client_id` to the import payload |
| Enrichment job has many `failedTasks` | UrlSettings missing service URLs or API keys expired | Verify UrlSettings with `GET /api/automation/tables/UrlSettings` and update expired keys |
| Copyright returns `skipped` for all processes | AgentSettings not configured or agent IDs invalid | Verify AgentSettings with `GET /api/automation/tables/AgentSettings` and check `projectId` and agent IDs |
| Scoring returns `skipped` for all fields | SdrAiSettings not configured or agent IDs invalid | Verify SdrAiSettings with `GET /api/automation/tables/SdrAiSettings` and check `projectId` and agent IDs |
| All leads score below threshold | Threshold too high or leads are poor quality | Lower the threshold, review ICP targeting criteria, or enrich with additional services |
| Email platform send fails | EmailPlatformSettings not configured or platform API key invalid | Verify EmailPlatformSettings exists with correct `platform`, `apiKey`, and `campaignId` |

---

## 4. Territory Intelligence

### Business Context

Territory intelligence transforms raw lead data into company-level strategic insights. By aggregating leads into TerritoryCompany records, running content analysis, generating events, and viewing the radar dashboard, sales teams gain a bird's-eye view of their target market. This use case is valuable for account-based selling, competitive analysis, and identifying high-potential companies based on lead density, qualification rates, and content signals.

### Prerequisites

- A valid API key (`lgp_` prefix) with access to the target client
- An existing `client_id` with enriched and scored leads (run the Lead Qualification Pipeline first, or have leads from an FSD pipeline run)
- Leads should have populated company fields (`companyName`, `companyDomain`, `industry`) for meaningful aggregation

### Steps

**Step 1 — Aggregate companies from lead data**

Trigger company aggregation to create or update TerritoryCompany records from the EnrichLeads in a client. The aggregation groups leads by `companyName` and calculates metrics (total leads, qualified leads, average score).

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "CLIENT_ID",
    "forceRefresh": false,
    "maxLeads": 1000
  }' \
  https://api.leadgenius.app/api/automation/companies/aggregate | jq
```

**Expected outcome:** Response returns `companiesCreated`, `companiesUpdated`, and `totalLeadsProcessed`. Each unique company name in the client now has a TerritoryCompany record with aggregated metrics. Use `forceRefresh: true` to delete and recreate all records from scratch.

**Step 2 — List territory companies**

Browse the aggregated companies to identify high-value targets. Sort by lead count, qualification rate, or average score.

**API:**

```bash
# List companies sorted by total leads
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies?client_id=CLIENT_ID&sortBy=totalLeads&limit=20" | jq

# Filter by industry and minimum score
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies?client_id=CLIENT_ID&industry=Financial%20Technology&minScore=50" | jq
```

**CLI:**

```bash
# List companies sorted by total leads
python lgp.py companies list --client CLIENT_ID --sort totalLeads

# Filter by industry
python lgp.py companies list --client CLIENT_ID --industry "Financial Technology"
```

**Expected outcome:** A paginated list of TerritoryCompany records with `companyName`, `totalLeads`, `qualifiedLeads`, `averageLeadScore`, `industry`, and `country`. Companies with the highest lead density and scores are the strongest targets.

**Step 3 — Run content analysis on key companies**

For high-priority companies, run content analysis to extract strategic insights from their associated leads. This populates content topics, pain points, value propositions, and competitive intelligence.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  https://api.leadgenius.app/api/automation/companies/COMPANY_ID/content-analysis | jq
```

**Expected outcome:** The TerritoryCompany record is updated with:
- `contentTopics`: key themes from lead data
- `contentKeywords`: relevant keywords
- `painPoints`: identified challenges
- `valuePropositions`: potential value angles
- `competitorMentions`: competitors referenced in lead data
- `engagementInsights`: engagement patterns
- `contentRecommendations`: suggested content strategies
- `lastContentAnalysisDate`: timestamp of the analysis

**Step 4 — Get detailed company intelligence**

Retrieve the full TerritoryCompany record with all metrics and content analysis results.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies/COMPANY_ID" | jq
```

**CLI:**

```bash
python lgp.py companies get COMPANY_ID
```

**Expected outcome:** The full record includes aggregated metrics, content analysis fields, and a `leadsSummary` with the count and IDs of all associated leads. Use the `leadIds` to drill into individual lead records for deeper analysis.

**Step 5 — Generate company events**

Auto-generate CompanyEvent records from recent lead activity. Events track new leads, qualification changes, score increases, and new company discoveries.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "CLIENT_ID",
    "since": "2025-01-01T00:00:00Z",
    "maxLeads": 500
  }' \
  https://api.leadgenius.app/api/automation/companies/events/generate | jq
```

**Expected outcome:** Response returns `eventsCreated` and `eventsByType` breakdown (e.g., `new_lead: 15`, `lead_qualified: 10`, `score_increased: 5`, `new_company: 3`). Events are linked to their respective TerritoryCompany records.

**Step 6 — Browse company events**

List events to track territory activity over time. Filter by event type, company, or date range.

**API:**

```bash
# List all recent events
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies/events?client_id=CLIENT_ID&limit=50" | jq

# Filter by event type
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies/events?client_id=CLIENT_ID&eventType=lead_qualified" | jq

# Filter by specific company
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies/events?client_id=CLIENT_ID&territoryCompanyId=COMPANY_ID" | jq
```

**Expected outcome:** A chronological list of events showing territory activity. Each event includes `eventType`, `eventTitle`, `eventDescription`, `eventDate`, and the associated `territoryCompanyId`.

**Step 7 — View the radar dashboard**

Get a high-level radar summary with recent events, counts by type, top active companies, and a timeline view.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/companies/events/radar?client_id=CLIENT_ID" | jq
```

**Expected outcome:** The radar dashboard returns:
- `recentEvents`: latest events across all companies
- `eventCountsByType`: aggregate counts (e.g., `new_lead: 50`, `lead_qualified: 20`)
- `topActiveCompanies`: companies with the most recent activity
- `timeline`: event distribution over time for trend analysis

### Expected Outcomes

After completing the territory intelligence workflow:

- TerritoryCompany records aggregate lead data into company-level metrics (total leads, qualified leads, average score)
- Content analysis provides strategic insights: topics, pain points, value propositions, and competitive intelligence
- Company events create a chronological activity feed for tracking territory changes
- The radar dashboard provides a high-level overview for prioritizing accounts and identifying trends
- Sales teams can identify high-potential companies, understand their challenges, and tailor outreach based on content analysis insights

### Common Failure Points

| Failure | Cause | Recovery |
|---------|-------|----------|
| Aggregation returns 0 companies | No leads in the client or leads missing `companyName` | Verify leads exist with `GET /api/automation/leads?client_id=CLIENT_ID` and check that `companyName` is populated |
| Content analysis returns empty fields | Lead data lacks enrichment fields (headlines, titles, descriptions) | Run enrichment on leads first (see Use Case 3 — Lead Qualification Pipeline, Step 2) |
| Event generation returns 0 events | `since` date is in the future or no qualifying activity found | Adjust the `since` parameter to cover the period when leads were created or scored |
| Radar dashboard returns empty | No events generated yet | Run event generation first (Step 5) before viewing the radar |
| Company list shows low scores | Leads not scored yet | Run scoring on leads first (see Use Case 3 — Lead Qualification Pipeline, Step 5) |


---

## 5. Multi-Channel Outreach

### Business Context

After leads have been scored through the qualification pipeline (see Use Case 3), the next step is delivering qualified leads to email outreach platforms and tracking engagement. This use case covers the full outreach loop: filtering scored leads by a qualification threshold, sending qualified leads to Woodpecker (or another configured platform), monitoring inbound webhook events for engagement signals (opens, clicks, replies), and reprocessing unmatched webhooks when new leads are imported. The feedback loop from webhook events back into lead engagement scores enables continuous refinement of outreach strategy.

### Prerequisites

- A valid API key (`lgp_` prefix) with access to the target client
- An existing `client_id` with scored leads (run the Lead Qualification Pipeline first, or have leads from an FSD pipeline run with `scoreAfterEnrichment: true`)
- Leads must have `aiLeadScore` populated (numeric 0–100) from SDR AI scoring
- EmailPlatformSettings configured for the company with an active platform connection (e.g., Woodpecker)
- A campaign created on the email platform (e.g., Woodpecker campaign with sequences configured)
- Webhook endpoint configured on the email platform to send events to LeadGenius Pro

### Steps

**Step 1 — Identify qualified leads by score threshold**

List scored leads in the client and filter by your qualification threshold. A threshold of 60 is a common starting point — adjust based on your conversion data.

**API:**

```bash
# List leads in the client and filter by score
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/leads?client_id=CLIENT_ID&limit=200" | jq '[.data[] | select(.aiScoreValue >= 60) | {id, fullName, email, companyName, aiScoreValue, aiQualification}]'
```

**CLI:**

```bash
# List all leads and review scores
python lgp.py leads list --client CLIENT_ID --limit 200 --format json
```

**Expected outcome:** A filtered list of leads with `aiLeadScore >= 60`. Collect the `id` values of qualified leads for the next step. Leads below the threshold remain in the client for nurturing or ICP refinement.

**Step 2 — Send qualified leads to Woodpecker**

Send the qualified lead IDs to the configured email platform. The API accepts up to 200 leads per request. Leads without a valid email are automatically skipped.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "leadIds": ["LEAD_ID_1", "LEAD_ID_2", "LEAD_ID_3", "LEAD_ID_4"],
    "platform": "woodpecker",
    "campaignId": "woodpecker-campaign-789"
  }' \
  https://api.leadgenius.app/api/automation/email-platforms/send | jq
```

**CLI:**

```bash
python lgp.py email-platforms send \
  --platform woodpecker \
  --campaign woodpecker-campaign-789 \
  --leads LEAD_ID_1,LEAD_ID_2,LEAD_ID_3,LEAD_ID_4
```

**Expected outcome:** Response confirms the number of leads queued for delivery. Check the `sent`, `skipped`, and `errors` fields:
- `sent`: leads successfully queued on the platform
- `skipped`: leads missing email (reason: `missing_email`) — the API prefers the `emailFinder` field over `email` for verified addresses
- `errors`: platform-side delivery failures

If many leads are skipped for `missing_email`, run enrichment with the `emailFinder` service first (see Use Case 3, Step 2).

**Step 3 — Track inbound webhook events**

As the email platform sends emails and prospects engage (open, click, reply, bounce), webhook events are logged in LeadGenius Pro. Monitor these events to track campaign performance.

**API:**

```bash
# List recent webhook events from Woodpecker
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/webhook-events?platform=woodpecker&limit=50" | jq

# Filter by event type (e.g., replies only)
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/webhook-events?platform=woodpecker&eventType=email_replied&limit=20" | jq

# Filter by match status to find unmatched events
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/webhook-events?platform=woodpecker&matchStatus=unmatched&limit=50" | jq
```

**CLI:**

```bash
# List all Woodpecker webhook events
python lgp.py webhooks list --platform woodpecker --limit 50

# List only unmatched events
python lgp.py webhooks list --platform woodpecker --limit 50
```

**Expected outcome:** Each webhook event includes `eventType` (e.g., `email_opened`, `email_clicked`, `email_replied`, `email_bounced`), `matchStatus` (`matched` or `unmatched`), `matchedLeadId` (if matched), and `matchConfidence` (`high`, `medium`, `low`). Matched events have already updated the lead's `engagementHistory` and `engagementScore`.

**Step 4 — Inspect individual webhook event details**

For events of interest (e.g., replies, high-value opens), retrieve the full event record including the raw payload and normalized data.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/webhook-events/EVENT_ID" | jq
```

**CLI:**

```bash
python lgp.py webhooks get EVENT_ID
```

**Expected outcome:** The full WebhookLog record includes `normalizedData` (structured fields extracted from the raw payload), `requestBody` (original webhook payload), `matchMethod` (how the lead was matched: `email`, `linkedinUrl`, or `name`), and `processingTime`.

**Step 5 — Reprocess unmatched webhook events**

Some webhook events may arrive before the corresponding leads are imported, or the matching data may have been incomplete at the time. After importing new leads or enriching existing ones, reprocess unmatched events to attempt matching again.

**API:**

```bash
# Reprocess a single unmatched event
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  https://api.leadgenius.app/api/automation/webhook-events/EVENT_ID/reprocess | jq
```

**CLI:**

```bash
python lgp.py webhooks reprocess EVENT_ID
```

**Expected outcome:** The reprocess endpoint re-runs the matching logic with priority:
1. **Email match** (high confidence) — uses `email-index` GSI
2. **LinkedIn URL match** (medium confidence) — uses `company_id` GSI with filter
3. **First name + last name match** (low confidence) — uses `firstName-lastName-index` GSI

If a match is found, the event's `matchStatus` updates to `matched`, `matchedLeadId` is set, and the lead's `engagementHistory` and `engagementScore` are updated. If no match is found, `matchStatus` remains `unmatched`.

**Step 6 — Review lead engagement after outreach**

After webhook events have been matched, review the engagement data on individual leads to assess outreach effectiveness.

**API:**

```bash
# Get a lead with engagement data
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/leads/LEAD_ID" | jq '{id, fullName, email, engagementScore, lastEngagementAt, engagementHistory}'
```

**CLI:**

```bash
python lgp.py leads get LEAD_ID
```

**Expected outcome:** The lead record shows:
- `engagementScore`: calculated score (0–100) based on weighted activity types with time decay
- `engagementHistory`: array of engagement events with timestamps and types
- `lastEngagementAt`: most recent engagement timestamp

Leads with high engagement scores and recent activity (replies, clicks) are the strongest candidates for sales follow-up.

### Expected Outcomes

After completing the multi-channel outreach workflow:

- Qualified leads (above the score threshold) are delivered to the email platform for automated outreach
- Webhook events track prospect engagement: opens, clicks, replies, bounces
- Matched events update lead engagement scores automatically
- Unmatched events can be reprocessed after new lead imports to recover missed matches
- Sales teams can prioritize follow-up based on engagement scores and recent activity

### Common Failure Points

| Failure | Cause | Recovery |
|---------|-------|----------|
| Email platform send returns errors | EmailPlatformSettings not configured or platform API key expired | Verify with `GET /api/automation/email-platforms` that the platform is `isActive: true` and `connectionStatus: connected` |
| Most leads skipped with `missing_email` | Leads lack email addresses | Run enrichment with `emailFinder` service: `POST /api/automation/tasks/enrich` with `services: ["emailFinder"]` |
| No webhook events appearing | Webhook endpoint not configured on the email platform | Configure the platform to send webhooks to the LeadGenius Pro webhook URL |
| Many events show `matchStatus: unmatched` | Leads imported after webhooks arrived, or email/name mismatch | Reprocess unmatched events: `POST /api/automation/webhook-events/{id}/reprocess` after importing or enriching leads |
| Engagement scores not updating | Webhook events not matched to leads | Check `matchStatus` on events; reprocess unmatched events; verify lead email matches the platform contact email |
| Low reply rates | Qualification threshold too low (sending to unqualified leads) or email content needs improvement | Raise the `qualificationThreshold`, review `aiColdEmail` content on leads, or refine ICP targeting criteria |

---

## 6. Automated Demand Generation

### Business Context

Automated demand generation combines ICP-driven lead generation with a recurring FSD campaign to produce a continuous pipeline of qualified leads without manual intervention. This use case covers setting up a weekly FSD campaign with full automation flags (`enrichAfterGeneration`, `scoreAfterEnrichment`, `sendToEmailPlatform`), monitoring ongoing pipeline runs, reviewing cumulative campaign metrics, and adjusting ICP criteria based on performance data. It is the most advanced automation scenario — once configured, the system generates, enriches, scores, qualifies, and delivers leads on a recurring schedule.

### Prerequisites

- A fully provisioned environment (see Use Case 1 — New Customer Onboarding)
- UrlSettings configured (enrichment service URLs and API keys)
- AgentSettings configured (EpsimoAI agent IDs for copyright)
- SdrAiSettings configured (EpsimoAI agent IDs for scoring)
- EmailPlatformSettings configured with an active platform connection (e.g., Woodpecker)
- An Apify actor ID and search parameters for the target market
- A campaign created on the email platform for receiving qualified leads

### Steps

**Step 1 — Create an ICP with targeting criteria and Apify config**

Define the ideal customer profile that drives recurring lead generation. Include all targeting criteria and the Apify actor configuration.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "CLIENT_ID",
    "name": "Enterprise SaaS VP Sales - Weekly",
    "description": "VP+ Sales leaders at mid-market SaaS companies for weekly demand gen",
    "industries": ["Software", "SaaS", "Cloud Computing"],
    "companySizes": ["51-200", "201-500", "501-1000"],
    "geographies": ["United States", "Canada", "United Kingdom"],
    "jobTitles": ["VP Sales", "VP Revenue", "CRO", "Head of Sales"],
    "seniority": ["VP", "C-Suite", "Director"],
    "departments": ["Sales", "Revenue"],
    "keywords": ["B2B sales", "enterprise software", "revenue operations"],
    "technologies": ["Salesforce", "Outreach", "Gong"],
    "apifyActorId": "apify/linkedin-sales-navigator-scraper",
    "apifyInput": "{\"searchUrl\":\"https://www.linkedin.com/sales/search/people?query=(keywords:VP Sales SaaS)\",\"maxResults\":150}",
    "maxLeads": 150,
    "isActive": true
  }' \
  https://api.leadgenius.app/api/automation/tables/ICP | jq
```

**CLI:**

```bash
python lgp.py tables create ICP \
  --data '{
    "client_id": "CLIENT_ID",
    "name": "Enterprise SaaS VP Sales - Weekly",
    "industries": ["Software", "SaaS", "Cloud Computing"],
    "companySizes": ["51-200", "201-500", "501-1000"],
    "geographies": ["United States", "Canada", "United Kingdom"],
    "jobTitles": ["VP Sales", "VP Revenue", "CRO", "Head of Sales"],
    "seniority": ["VP", "C-Suite", "Director"],
    "apifyActorId": "apify/linkedin-sales-navigator-scraper",
    "apifyInput": "{\"searchUrl\":\"https://www.linkedin.com/sales/search/people?query=(keywords:VP Sales SaaS)\",\"maxResults\":150}",
    "maxLeads": 150
  }'
```

**Expected outcome:** An `ICP` record is created. Note the returned `id` as `ICP_ID`.

**Step 2 — Create a recurring FSD campaign with full automation**

Create a campaign with `weekly` frequency and all automation flags enabled. This ensures each pipeline run generates leads, enriches them, scores them, filters by qualification threshold, and sends qualified leads to the email platform — all without manual intervention.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "CLIENT_ID",
    "name": "Weekly SaaS VP Sales Demand Gen",
    "icpId": "ICP_ID",
    "frequency": "weekly",
    "targetLeadCount": 150,
    "enrichAfterGeneration": true,
    "scoreAfterEnrichment": true,
    "sendToEmailPlatform": "woodpecker",
    "qualificationThreshold": 65,
    "emailCampaignId": "woodpecker-campaign-weekly-001"
  }' \
  https://api.leadgenius.app/api/automation/fsd/campaigns | jq
```

**CLI:**

```bash
python lgp.py fsd create-campaign \
  --client CLIENT_ID \
  --name "Weekly SaaS VP Sales Demand Gen" \
  --icp ICP_ID \
  --frequency weekly \
  --target 150
```

**Expected outcome:** An `FsdCampaign` record is created with `isActive: true` and `frequency: "weekly"`. The campaign is configured to:
- Generate 150 leads per run from the ICP's Apify config
- Automatically enrich all generated leads
- Automatically score all enriched leads
- Filter leads with `aiLeadScore >= 65`
- Send qualified leads to Woodpecker campaign `woodpecker-campaign-weekly-001`

Note the returned campaign `id` as `CAMPAIGN_ID`. The `nextRunAt` field indicates when the first scheduled run will execute.

**Step 3 — Trigger the first pipeline run**

Manually trigger the first run to validate the full automation chain before relying on the recurring schedule.

**API:**

```bash
curl -s -X POST -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "client_id": "CLIENT_ID",
    "icpId": "ICP_ID",
    "targetLeadCount": 150,
    "enrichAfterGeneration": true,
    "scoreAfterEnrichment": true,
    "sendToEmailPlatform": "woodpecker",
    "qualificationThreshold": 65,
    "campaignId": "CAMPAIGN_ID"
  }' \
  https://api.leadgenius.app/api/automation/fsd/run | jq
```

**CLI:**

```bash
python lgp.py fsd run \
  --client CLIENT_ID \
  --icp ICP_ID \
  --target 150 \
  --campaign CAMPAIGN_ID
```

**Expected outcome:** Response returns a `pipelineId` with `stage: "generating"` and all automation flags confirmed. Note the `pipelineId` for monitoring.

**Step 4 — Monitor the pipeline run through all stages**

Poll the pipeline status to verify each stage completes successfully. The pipeline progresses automatically: `generating` → `enriching` → `scoring` → `qualifying` → `sending` → `completed`.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/run/PIPELINE_ID" | jq '{stage, leadsGenerated, leadsEnriched, leadsScored, leadsQualified, leadsSent, errorMessage}'
```

**CLI:**

```bash
python lgp.py fsd status PIPELINE_ID
```

**Expected outcome at completion:**

```json
{
  "stage": "completed",
  "leadsGenerated": 150,
  "leadsEnriched": 148,
  "leadsScored": 148,
  "leadsQualified": 62,
  "leadsSent": 62,
  "errorMessage": null
}
```

Key metrics to validate:
- `leadsGenerated` should be close to `targetLeadCount` (150)
- `leadsEnriched` may be slightly lower if some leads had enrichment failures
- `leadsQualified` depends on the `qualificationThreshold` (65) — typically 30–50% of scored leads
- `leadsSent` should equal `leadsQualified` if the email platform is configured correctly

If `stage` is `failed`, check `errorMessage` and `stageErrors` to identify which stage failed and why.

**Step 5 — Monitor ongoing campaign runs**

After the first run validates successfully, the campaign runs automatically on the weekly schedule. Monitor cumulative metrics by checking the campaign record.

**API:**

```bash
# Get campaign with cumulative metrics
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/campaigns/CAMPAIGN_ID" | jq '{name, frequency, isActive, totalRuns, totalLeadsGenerated, totalLeadsEnriched, totalLeadsScored, totalLeadsSent, lastRunAt, nextRunAt}'
```

**CLI:**

```bash
python lgp.py fsd campaign CAMPAIGN_ID
```

**Expected outcome after several weeks:**

```json
{
  "name": "Weekly SaaS VP Sales Demand Gen",
  "frequency": "weekly",
  "isActive": true,
  "totalRuns": 4,
  "totalLeadsGenerated": 580,
  "totalLeadsEnriched": 572,
  "totalLeadsScored": 572,
  "totalLeadsSent": 241,
  "lastRunAt": "2026-03-26T08:00:00.000Z",
  "nextRunAt": "2026-04-02T08:00:00.000Z"
}
```

The cumulative metrics (`totalLeadsGenerated`, `totalLeadsEnriched`, `totalLeadsScored`, `totalLeadsSent`) aggregate across all pipeline runs. Compare `totalLeadsSent / totalLeadsScored` to calculate the overall qualification rate.

**Step 6 — List all campaigns for a portfolio view**

If running multiple demand generation campaigns (e.g., different ICPs for different market segments), list all campaigns to compare performance.

**API:**

```bash
curl -s -H "X-API-Key: $LGP_API_KEY" \
  "https://api.leadgenius.app/api/automation/fsd/campaigns" | jq '.data[] | {name, frequency, isActive, totalRuns, totalLeadsGenerated, totalLeadsSent, lastRunAt}'
```

**CLI:**

```bash
python lgp.py fsd campaigns
```

**Expected outcome:** A list of all campaigns with their cumulative metrics. Compare `totalLeadsSent / totalLeadsGenerated` across campaigns to identify which ICPs produce the highest-quality leads.

**Step 7 — Adjust ICP criteria based on performance**

After reviewing campaign metrics and lead quality, refine the ICP targeting criteria to improve results. Common adjustments include narrowing geographies, adding or removing job titles, adjusting company sizes, or updating keywords.

**API:**

```bash
# Update ICP targeting criteria
curl -s -X PUT -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "jobTitles": ["VP Sales", "CRO", "Head of Sales"],
    "companySizes": ["201-500", "501-1000"],
    "keywords": ["B2B SaaS", "enterprise sales", "revenue operations", "sales automation"],
    "technologies": ["Salesforce", "Outreach", "Gong", "Clari"]
  }' \
  https://api.leadgenius.app/api/automation/tables/ICP/ICP_ID | jq
```

**CLI:**

```bash
python lgp.py tables update ICP ICP_ID \
  --data '{
    "jobTitles": ["VP Sales", "CRO", "Head of Sales"],
    "companySizes": ["201-500", "501-1000"],
    "keywords": ["B2B SaaS", "enterprise sales", "revenue operations", "sales automation"]
  }'
```

**Expected outcome:** The ICP record is updated with refined criteria. The next scheduled pipeline run will use the updated targeting, generating leads that better match the refined profile. Compare metrics before and after the adjustment to measure improvement.

**Step 8 — Adjust campaign parameters if needed**

If the qualification rate is too low or too high, adjust the campaign's `qualificationThreshold` or `targetLeadCount` without recreating the campaign.

**API:**

```bash
curl -s -X PUT -H "X-API-Key: $LGP_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "qualificationThreshold": 70,
    "targetLeadCount": 200
  }' \
  https://api.leadgenius.app/api/automation/fsd/campaigns/CAMPAIGN_ID | jq
```

**CLI:**

```bash
python lgp.py fsd update-campaign CAMPAIGN_ID --target 200
```

**Expected outcome:** The campaign is updated. Subsequent pipeline runs use the new threshold and target count. Raising the threshold produces fewer but higher-quality leads; lowering it increases volume at the cost of average quality.

### Expected Outcomes

After setting up automated demand generation:

- A recurring FSD campaign generates leads weekly from the ICP's Apify configuration
- Each pipeline run automatically enriches, scores, qualifies, and delivers leads without manual intervention
- Cumulative metrics (`totalLeadsGenerated`, `totalLeadsEnriched`, `totalLeadsScored`, `totalLeadsSent`) track campaign performance over time
- ICP criteria can be refined based on lead quality data, with changes taking effect on the next scheduled run
- Campaign parameters (threshold, target count, frequency) can be adjusted without recreating the campaign
- Multiple campaigns with different ICPs can run in parallel for different market segments

### Common Failure Points

| Failure | Cause | Recovery |
|---------|-------|----------|
| Campaign not running on schedule | `isActive` is `false` or `nextRunAt` is in the past | Verify with `GET /api/automation/fsd/campaigns/CAMPAIGN_ID`; reactivate with `PUT` setting `isActive: true` |
| `totalLeadsSent` is 0 across multiple runs | `sendToEmailPlatform` not set, or EmailPlatformSettings not configured | Update campaign with `sendToEmailPlatform: "woodpecker"` and verify EmailPlatformSettings exists |
| Qualification rate too low (< 20%) | `qualificationThreshold` too high or ICP targeting too broad | Lower the threshold or narrow ICP criteria (fewer industries, more specific job titles) |
| Qualification rate too high (> 80%) | `qualificationThreshold` too low | Raise the threshold to be more selective; review lead scores to calibrate |
| `leadsGenerated` consistently below target | Apify actor exhausting the search results or search parameters too narrow | Update ICP `apifyInput` with broader search terms or increase `maxResults`; consider rotating search queries |
| Pipeline runs failing at `enriching` stage | UrlSettings expired or service endpoints down | Check UrlSettings with `GET /api/automation/tables/UrlSettings` and update expired API keys |
| Pipeline runs failing at `scoring` stage | SdrAiSettings misconfigured or agent IDs invalid | Check SdrAiSettings with `GET /api/automation/tables/SdrAiSettings` and verify agent IDs |
| Duplicate leads across weekly runs | Same Apify search returning overlapping results | The system handles cross-run deduplication; if duplicates persist, adjust the ICP `apifyInput` search parameters to target different segments each week |
