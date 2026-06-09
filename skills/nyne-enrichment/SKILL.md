---
name: nyne-enrichment
description: >
  Enrich any person by email, phone, LinkedIn URL, or name using the Nyne Enrichment API.
  Returns contact info, social profiles, work history, education, and optional social media posts.
  Supports lite mode (3 credits), newsfeed add-on, and AI-enhanced deep search. Async with polling.
---

# Nyne Enrichment Skill

Enrich any person by email, phone, LinkedIn URL, or name. Returns contact info, social profiles, work history, education, and optional social media posts.

**Important:** This API is async. You POST to submit, get a `request_id`, then poll GET until complete.

## Agent Instructions

When presenting results to the user, show **all available data**. Walk through each section:

1. **Identity** — displayname, bio, location, gender
2. **Contact** — emails (work + personal + alt), phones with type
3. **Social Profiles** — LinkedIn, Twitter, GitHub, Instagram with follower counts
4. **Work History** — all organizations with title, dates, current status
5. **Education** — schools with degree, field, dates
6. **Newsfeed** (if requested) — recent posts with engagement metrics

If a field is missing from the response, it means no data was found — skip it silently.

For lite mode responses, note that only 5 fields are returned (displayname, firstname, lastname, first organization, LinkedIn URL).

## Setup

**Required environment variables:**
- `NYNE_API_KEY` — your Nyne API key
- `NYNE_API_SECRET` — your Nyne API secret

Get credentials at [https://api.nyne.ai](https://api.nyne.ai).

```bash
export NYNE_API_KEY="your-api-key"
export NYNE_API_SECRET="your-api-secret"
```

Verify they're set:
```bash
echo "Key: ${NYNE_API_KEY:0:8}... Secret: ${NYNE_API_SECRET:0:6}..."
```

## Important: JSON Handling

The API response can contain control characters in JSON string values that break `jq`. All examples use a `nyne_parse` helper that cleans and re-encodes JSON via `python3`. Define it once per session:

```bash
nyne_parse() {
  python3 -c "
import sys, json, re
raw = sys.stdin.read()
clean = re.sub(r'[\x00-\x1f]+', ' ', raw)
data = json.loads(clean)
json.dump(data, sys.stdout)
"
}
```

## Quick Start

Submit an enrichment request by email and poll until complete:

```bash
nyne_parse() {
  python3 -c "
import sys, json, re
raw = sys.stdin.read()
clean = re.sub(r'[\x00-\x1f]+', ' ', raw)
data = json.loads(clean)
json.dump(data, sys.stdout)
"
}

# Submit enrichment request
curl -s -X POST "https://api.nyne.ai/person/enrichment" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"email": "someone@example.com"}' | nyne_parse > /tmp/nyne_enrich.json

REQUEST_ID=$(jq -r '.data.request_id' /tmp/nyne_enrich.json)
echo "Request submitted: $REQUEST_ID"

# Poll until complete (checks every 3s, times out after 6 min)
SECONDS_WAITED=0
while [ $SECONDS_WAITED -lt 360 ]; do
  curl -s "https://api.nyne.ai/person/enrichment?request_id=$REQUEST_ID" \
    -H "X-API-Key: $NYNE_API_KEY" \
    -H "X-API-Secret: $NYNE_API_SECRET" | nyne_parse > /tmp/nyne_enrich.json
  STATUS=$(jq -r '.data.status' /tmp/nyne_enrich.json)
  echo "Status: $STATUS ($SECONDS_WAITED seconds elapsed)"
  if [ "$STATUS" = "completed" ]; then
    jq '.data.result' /tmp/nyne_enrich.json
    break
  elif [ "$STATUS" = "failed" ]; then
    echo "Enrichment failed."
    jq . /tmp/nyne_enrich.json
    break
  fi
  sleep 3
  SECONDS_WAITED=$((SECONDS_WAITED + 3))
done

if [ $SECONDS_WAITED -ge 360 ]; then
  echo "Timed out after 6 minutes. Resume polling with request_id: $REQUEST_ID"
fi
```

## Submit Enrichment (POST)

**Endpoint:** `POST https://api.nyne.ai/person/enrichment`

**Headers:**
```
Content-Type: application/json
X-API-Key: $NYNE_API_KEY
X-API-Secret: $NYNE_API_SECRET
```

### Input Parameters

At least one identifier is required.

| Parameter | Type | Description |
|-----------|------|-------------|
| `email` | string | Email address (work email preferred) |
| `phone` | string | Phone number (e.g., "+14155551234") |
| `social_media_url` | string | LinkedIn, Twitter, or GitHub URL |
| `name` | string | Full name (use with `company` or `city` to disambiguate) |
| `company` | string | Company name (helps disambiguate name lookups) |
| `city` | string | City (accepts abbreviations: SF, NYC, LA) |

**Input priority ranking:** LinkedIn URL (best) > Email (work > personal) > Phone (lowest match rate). LinkedIn + email together yields best results.

### Feature Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `ai_enhanced_search` | boolean | false | AI-powered deep search for additional social profiles. Longer processing time. |
| `lite_enrich` | boolean | false | Minimal enrichment: only 5 fields, 3 credits instead of 6 |
| `newsfeed` | array | omit | Social posts to fetch: `["linkedin", "twitter", "instagram", "github", "facebook"]` or `["all"]`. Cannot mix `"all"` with specific sources. +6 credits when data found. |
| `strict_email_check` | boolean | false | Strict email validation (may return no results) |
| `callback_url` | string | omit | Webhook URL for async delivery |

### Examples

**By email:**
```bash
curl -s -X POST "https://api.nyne.ai/person/enrichment" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"email": "someone@example.com"}' | nyne_parse > /tmp/nyne_enrich.json

REQUEST_ID=$(jq -r '.data.request_id' /tmp/nyne_enrich.json)
echo "Request ID: $REQUEST_ID"
```

**By LinkedIn URL:**
```bash
curl -s -X POST "https://api.nyne.ai/person/enrichment" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"social_media_url": "https://linkedin.com/in/johndoe"}' | nyne_parse > /tmp/nyne_enrich.json

REQUEST_ID=$(jq -r '.data.request_id' /tmp/nyne_enrich.json)
```

**By name + company:**
```bash
curl -s -X POST "https://api.nyne.ai/person/enrichment" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"name": "Jane Smith", "company": "Acme Corp", "city": "SF"}' | nyne_parse > /tmp/nyne_enrich.json

REQUEST_ID=$(jq -r '.data.request_id' /tmp/nyne_enrich.json)
```

**With newsfeed:**
```bash
curl -s -X POST "https://api.nyne.ai/person/enrichment" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"email": "someone@example.com", "newsfeed": ["linkedin", "twitter"]}' | nyne_parse > /tmp/nyne_enrich.json

REQUEST_ID=$(jq -r '.data.request_id' /tmp/nyne_enrich.json)
```

**Lite mode (3 credits):**
```bash
curl -s -X POST "https://api.nyne.ai/person/enrichment" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"email": "someone@example.com", "lite_enrich": true}' | nyne_parse > /tmp/nyne_enrich.json

REQUEST_ID=$(jq -r '.data.request_id' /tmp/nyne_enrich.json)
```

**With AI-enhanced search:**
```bash
curl -s -X POST "https://api.nyne.ai/person/enrichment" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"email": "someone@example.com", "ai_enhanced_search": true}' | nyne_parse > /tmp/nyne_enrich.json

REQUEST_ID=$(jq -r '.data.request_id' /tmp/nyne_enrich.json)
```

**Submit response:**
```json
{
  "success": true,
  "data": {
    "request_id": "abc123-...",
    "status": "queued",
    "message": "Enrichment request queued. Use GET /person/enrichment?request_id=... to check status."
  }
}
```

## Poll for Results (GET)

**Endpoint:** `GET https://api.nyne.ai/person/enrichment?request_id={id}`

**Headers:** Same `X-API-Key` and `X-API-Secret` as above.

### Check status once
```bash
curl -s "https://api.nyne.ai/person/enrichment?request_id=$REQUEST_ID" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" | nyne_parse > /tmp/nyne_enrich.json

jq '{status: .data.status, completed: .data.completed}' /tmp/nyne_enrich.json
```

### Full polling loop

```bash
SECONDS_WAITED=0
TIMEOUT=360  # 6 minutes

while [ $SECONDS_WAITED -lt $TIMEOUT ]; do
  curl -s "https://api.nyne.ai/person/enrichment?request_id=$REQUEST_ID" \
    -H "X-API-Key: $NYNE_API_KEY" \
    -H "X-API-Secret: $NYNE_API_SECRET" | nyne_parse > /tmp/nyne_enrich.json
  STATUS=$(jq -r '.data.status' /tmp/nyne_enrich.json)

  echo "[$(date +%H:%M:%S)] Status: $STATUS ($SECONDS_WAITED s)"

  case "$STATUS" in
    completed)
      jq '.data.result' /tmp/nyne_enrich.json
      break
      ;;
    failed)
      echo "Enrichment failed:"
      jq '.data' /tmp/nyne_enrich.json
      break
      ;;
    *)
      sleep 3
      SECONDS_WAITED=$((SECONDS_WAITED + 3))
      ;;
  esac
done

if [ "$STATUS" != "completed" ] && [ "$STATUS" != "failed" ]; then
  echo "Timed out. Resume polling with request_id: $REQUEST_ID"
fi
```

## Response Structure

When `status` is `completed`:

```json
{
  "success": true,
  "timestamp": "2025-09-05T21:45:25Z",
  "data": {
    "request_id": "abc123-...",
    "status": "completed",
    "completed": true,
    "created_on": "2025-09-05T21:45:06",
    "completed_on": "2025-09-05T21:45:12",
    "result": {
      "displayname": "...",
      "firstname": "...",
      "lastname": "...",
      "bio": "...",
      "location": "...",
      "gender": "...",
      "fullphone": [...],
      "altemails": [...],
      "best_work_email": "...",
      "best_personal_email": "...",
      "social_profiles": {...},
      "organizations": [...],
      "schools_info": [...],
      "newsfeed": [...],
      "probability": "high"
    }
  }
}
```

**All fields are optional** — only included when data is found. No charges if person cannot be located.

### Result Fields

| Field | Type | Description |
|-------|------|-------------|
| `displayname` | string | Full display name |
| `firstname` | string | First name |
| `lastname` | string | Last name |
| `bio` | string | Bio/headline |
| `location` | string | Location |
| `gender` | string | Gender |
| `fullphone` | array | Phone numbers, each: `{fullphone, type}` |
| `altemails` | array | Alternative email addresses |
| `best_work_email` | string | Most probable work email |
| `best_personal_email` | string | Most probable personal email |
| `social_profiles` | object | LinkedIn, Twitter, GitHub, Instagram with URLs, usernames, follower counts |
| `organizations` | array | Work history: `{name, title, startDate, endDate, is_current}` |
| `schools_info` | array | Education: `{name, degree, title, startDate, endDate}` |
| `newsfeed` | array | Social posts (if requested): `{source, type, content, date_posted, url, engagement}` |
| `probability` | string | Match confidence: "high", "medium", "low" (only if `probability_score: true`) |

### Social Profiles Object

```json
{
  "linkedin": {"url": "...", "username": "...", "followers": 542, "connections": 1243},
  "twitter": {"url": "...", "username": "...", "followers": 1234, "following": 567, "posts": 892},
  "github": {"url": "...", "username": "...", "followers": 89, "following": 45},
  "instagram": {"url": "...", "username": "...", "followers": 500}
}
```

### Newsfeed Item

```json
{
  "source": "linkedin",
  "type": "post",
  "content": "...",
  "date_posted": "2025-09-01T14:30:00Z",
  "url": "...",
  "author": {"display_name": "...", "username": "...", "profile_url": "..."},
  "engagement": {"likes": 42, "comments": 5, "shares": 3, "total_reactions": 50}
}
```

### Lite Mode Response

When `lite_enrich: true`, only these fields are returned:
- `displayname`, `firstname`, `lastname`
- First organization (name + title)
- LinkedIn URL

## Useful jq Filters

After polling completes, the clean response is at `/tmp/nyne_enrich.json`:

```bash
# Full result
jq '.data.result' /tmp/nyne_enrich.json

# Identity summary
jq '.data.result | {displayname, bio, location, gender}' /tmp/nyne_enrich.json

# All emails
jq '.data.result | {best_work_email, best_personal_email, altemails}' /tmp/nyne_enrich.json

# Social profiles
jq '.data.result.social_profiles' /tmp/nyne_enrich.json

# Work history
jq '.data.result.organizations' /tmp/nyne_enrich.json

# Education
jq '.data.result.schools_info' /tmp/nyne_enrich.json

# Phone numbers
jq '.data.result.fullphone' /tmp/nyne_enrich.json

# Newsfeed posts (if requested)
jq '.data.result.newsfeed[] | {source, date_posted, content, engagement}' /tmp/nyne_enrich.json

# LinkedIn info specifically
jq '.data.result.social_profiles.linkedin' /tmp/nyne_enrich.json

# Current job
jq '[.data.result.organizations[] | select(.endDate_formatted.is_current == true)]' /tmp/nyne_enrich.json
```

## Error Handling

| HTTP Code | Error | Description |
|-----------|-------|-------------|
| 400 | `missing_parameters` | No identifier provided |
| 400 | `invalid_newsfeed` | Bad newsfeed param (can't mix "all" with specific sources) |
| 401 | `invalid_credentials` | Invalid API key/secret |
| 403 | `subscription_required` | Plan lacks access |
| 404 | `request_not_found` | Invalid request_id for status check |
| 429 | `rate_limit_exceeded` | Too many requests |
| 500 | `internal_error` | Server error |

## Modes & When to Use Each

### Standard Enrichment (6 credits)
The default. Returns full contact info, social profiles, work history, and education. Use this for most lookups.
```json
{"email": "someone@example.com"}
```

### Lite Enrichment (3 credits)
`lite_enrich: true` — Performs a minimal enrichment workflow. Returns only 5 essential fields: `displayname`, `firstname`, `lastname`, first organization in the `organizations` array, and LinkedIn URL in `social_profiles.linkedin.url`. When enabled, all advanced features are disabled — `ai_enhanced_search`, `newsfeed`, and `strict_email_check` parameters are ignored (emails are not returned in lite mode). Use when you only need basic profile identification at reduced cost.
```json
{"email": "someone@example.com", "lite_enrich": true}
```

### AI-Enhanced Search (6 credits, longer processing)
`ai_enhanced_search: true` — Enables AI-powered deep search to discover additional social profiles and gather more comprehensive social data. Performs extensive searches and can take significantly longer to complete (up to several minutes). Only enable when comprehensive results are needed and extended processing time is acceptable. Use when standard enrichment returns sparse social profile data and you want broader coverage.
```json
{"email": "someone@example.com", "ai_enhanced_search": true}
```

### Newsfeed Add-on (+6 credits when data found)
`newsfeed: [...]` — Requests social media newsfeed data from specified sources. Valid sources: `"linkedin"`, `"twitter"`, `"instagram"`, `"github"`, `"facebook"`, or `"all"`. Cannot mix `"all"` with specific sources. Additional charges apply only when newsfeed data is actually found. Stacks on top of standard or AI-enhanced enrichment. Use when you need to see what someone is posting about or gauge their activity level.
```json
{"email": "someone@example.com", "newsfeed": ["linkedin", "twitter"]}
{"email": "someone@example.com", "newsfeed": ["all"]}
```

### Strict Email Check
`strict_email_check: true` — Enables strict email validation for the best email to use. May return nothing due to its strictness. Use when email accuracy is critical and you'd rather get no result than a questionable one.
```json
{"email": "someone@example.com", "strict_email_check": true}
```

### No Match (0 credits)
If the person cannot be found, you are not charged.

## Rate Limits

- **Per minute:** 60 requests
- **Per hour:** 1,000 requests
- **Monthly:** Plan-dependent
