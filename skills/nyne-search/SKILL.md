---
name: nyne-search
description: >
  Search for people using natural language queries with the Nyne Search API. Find professionals by
  role, company, location, industry, or any combination. Supports custom filters, AI relevance scoring,
  contact enrichment (emails + phones), pagination, and three search tiers (light, medium, premium). Async with polling.
---

# Nyne Search Skill

Search for people using natural language queries. Find professionals by role, company, location, industry, or any combination. Returns matching profiles with contact info, work history, education, and optional AI relevance scoring.

**Important:** This API is async. You POST to submit, get a `request_id`, then poll GET until `status: "completed"`. Light searches complete in 3-40 seconds; premium searches take 30-300 seconds.

## Agent Instructions

When presenting search results to the user, show **all returned data** for each person. Walk through:

1. **Result count** — total_stored, total_estimate, has_more, credits_charged
2. **Each person** — displayname, headline, bio, location, gender, estimated_age, total_experience_years, is_decision_maker
3. **Contact info** — best_business_email, best_personal_email, altemails, fullphone (if show_emails/show_phone_numbers were enabled)
4. **Social profiles** — LinkedIn URL, username, connections, followers
5. **Work history** — all organizations with title, dates, company details (industries, num_employees, funding, technologies)
6. **Education** — schools with degree, major, dates; note is_top_universities flag
7. **Interests** — work interests and certifications
8. **Patents** — title, date, reference, URL (if present)
9. **Languages** — spoken languages
10. **Score** — AI relevance score 0-1 (if profile_scoring was enabled)
11. **Insights** — AI-generated match reasoning (if insights were enabled)

If `has_more` is true, tell the user there are more results available and offer to paginate using the `next_cursor`.

If a field is missing from the response, it means no data was found — skip it silently.

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

Search for people by natural language query and poll until complete:

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

# Submit search request
curl -s -X POST "https://api.nyne.ai/person/search" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"query": "Software engineers at Google in San Francisco", "limit": 10, "type": "premium", "show_emails": true}' | nyne_parse > /tmp/nyne_search.json

STATUS=$(jq -r '.data.status' /tmp/nyne_search.json)

if [ "$STATUS" = "completed" ]; then
  echo "Search completed immediately."
  jq '.data | {total_stored, total_estimate, has_more, credits_charged}' /tmp/nyne_search.json
  jq '.data.results[] | {displayname, headline, location}' /tmp/nyne_search.json
else
  REQUEST_ID=$(jq -r '.data.request_id' /tmp/nyne_search.json)
  echo "Request submitted: $REQUEST_ID (status: $STATUS)"

  # Poll until complete (checks every 5s, times out after 10 min)
  SECONDS_WAITED=0
  while [ $SECONDS_WAITED -lt 600 ]; do
    curl -s "https://api.nyne.ai/person/search?request_id=$REQUEST_ID" \
      -H "X-API-Key: $NYNE_API_KEY" \
      -H "X-API-Secret: $NYNE_API_SECRET" | nyne_parse > /tmp/nyne_search.json
    STATUS=$(jq -r '.data.status' /tmp/nyne_search.json)
    echo "Status: $STATUS ($SECONDS_WAITED seconds elapsed)"
    if [ "$STATUS" = "completed" ]; then
      jq '.data | {total_stored, total_estimate, has_more, credits_charged}' /tmp/nyne_search.json
      jq '.data.results[] | {displayname, headline, location}' /tmp/nyne_search.json
      break
    elif [ "$STATUS" = "failed" ]; then
      echo "Search failed."
      jq . /tmp/nyne_search.json
      break
    fi
    sleep 5
    SECONDS_WAITED=$((SECONDS_WAITED + 5))
  done

  if [ $SECONDS_WAITED -ge 600 ]; then
    echo "Timed out after 10 minutes. Resume polling with request_id: $REQUEST_ID"
  fi
fi
```

## Submit Search (POST)

**Endpoint:** `POST https://api.nyne.ai/person/search`

**Headers:**
```
Content-Type: application/json
X-API-Key: $NYNE_API_KEY
X-API-Secret: $NYNE_API_SECRET
```

### Query Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `query` | string | *required* | Natural language search query (max 1000 chars). Examples: "Software engineers at Microsoft in Seattle", "Marketing directors at Fortune 500" |
| `type` | string | `"premium"` | Search quality tier: `"light"` (fast, 3-40s), `"medium"` (balanced), `"premium"` (best quality, 30-300s) |
| `limit` | integer | 10 | Results per request (max 100) |
| `offset` | integer | 0 | Starting position, 0-indexed (max 999). `offset + limit` must be ≤ 1000 |
| `show_emails` | boolean | false | Include email addresses in results (+2 credits). **Significantly increases latency** — search will take longer to complete as emails are enriched per result |
| `show_phone_numbers` | boolean | false | Include phone numbers in results (+14 credits). **Significantly increases latency** — search will take longer to complete as phone numbers are enriched per result |
| `require_emails` | boolean | false | Only return profiles that have email addresses (+1 credit) |
| `require_phone_numbers` | boolean | false | Only return profiles that have phone numbers (+1 credit) |
| `require_phones_or_emails` | boolean | false | Only return profiles with either phone or email (+1 credit) |
| `insights` | boolean | false | AI-generated insights per result explaining match relevance (+1 credit per result). Not available for `light` type |
| `profile_scoring` | boolean | false | Include AI relevance score (0-1) per result (+1 credit) |
| `high_freshness` | boolean | false | Prioritize recently updated profiles (+2 credits). Not available for `light` type |
| `force_new` | boolean | false | Force fresh search, ignore cached results |
| `custom_filters` | object | omit | Structured filters for precise targeting (see Custom Filters below) |
| `callback_url` | string | omit | Webhook URL for async results delivery |

### Custom Filters

Pass as a `custom_filters` object to narrow results beyond the natural language query.

**Array fields** (pass as arrays of strings):

| Filter | Description |
|--------|-------------|
| `locations` | Geographic locations (e.g., `["San Francisco", "New York"]`) |
| `languages` | Languages spoken (e.g., `["English", "Spanish"]`) |
| `titles` | Job titles (e.g., `["CTO", "VP Engineering"]`) |
| `industries` | Industry sectors (e.g., `["Technology", "Healthcare"]`) |
| `companies` | Company names, current or past (e.g., `["Google", "Meta"]`) |
| `universities` | Universities attended (e.g., `["Stanford", "MIT"]`) |
| `keywords` | Profile keywords (e.g., `["machine learning", "AI"]`) |
| `degrees` | Education degrees (e.g., `["bachelor", "master", "phd"]`) |
| `specialization_categories` | Academic specialization categories |

**Numeric range fields** (pass as integers):

| Filter | Description |
|--------|-------------|
| `min_linkedin_followers` / `max_linkedin_followers` | LinkedIn follower count range |
| `min_total_experience_years` / `max_total_experience_years` | Total work experience range |
| `min_current_experience_years` / `max_current_experience_years` | Current role tenure range |
| `min_estimated_age` / `max_estimated_age` | Estimated age range |

**Exact match fields**:

| Filter | Type | Description |
|--------|------|-------------|
| `first_name` | string | Exact first name match |
| `middle_name` | string | Exact middle name match |
| `last_name` | string | Exact last name match |
| `gender` | string | `"male"` or `"female"` |
| `studied_at_top_universities` | boolean | Attended a top-ranked university |

### Examples

**Basic search:**
```bash
curl -s -X POST "https://api.nyne.ai/person/search" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"query": "Software engineers at Google in San Francisco", "limit": 10}' | nyne_parse > /tmp/nyne_search.json

jq '{status: .data.status, request_id: .data.request_id}' /tmp/nyne_search.json
```

**With emails and phone numbers:**
```bash
curl -s -X POST "https://api.nyne.ai/person/search" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"query": "Marketing directors at tech startups in Austin", "limit": 25, "show_emails": true, "show_phone_numbers": true}' | nyne_parse > /tmp/nyne_search.json
```

**With custom filters:**
```bash
curl -s -X POST "https://api.nyne.ai/person/search" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{
    "query": "Engineering leaders in fintech",
    "limit": 20,
    "type": "premium",
    "show_emails": true,
    "custom_filters": {
      "locations": ["New York", "San Francisco"],
      "titles": ["CTO", "VP Engineering", "Head of Engineering"],
      "min_total_experience_years": 10,
      "industries": ["Financial Services", "Technology"]
    }
  }' | nyne_parse > /tmp/nyne_search.json
```

**Light search (fast, 1 credit):**
```bash
curl -s -X POST "https://api.nyne.ai/person/search" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"query": "Data scientists at Amazon", "type": "light", "limit": 10}' | nyne_parse > /tmp/nyne_search.json
```

**With AI scoring and insights:**
```bash
curl -s -X POST "https://api.nyne.ai/person/search" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"query": "AI researchers in healthcare", "type": "premium", "profile_scoring": true, "insights": true, "limit": 10}' | nyne_parse > /tmp/nyne_search.json
```

**With freshness priority:**
```bash
curl -s -X POST "https://api.nyne.ai/person/search" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"query": "Product managers who recently changed jobs", "type": "premium", "high_freshness": true, "show_emails": true}' | nyne_parse > /tmp/nyne_search.json
```

**Require contact info:**
```bash
curl -s -X POST "https://api.nyne.ai/person/search" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"query": "Sales directors at SaaS companies", "require_emails": true, "show_emails": true, "limit": 50}' | nyne_parse > /tmp/nyne_search.json
```

**Submit response:**
```json
{
  "success": true,
  "data": {
    "request_id": "abc12345_1737123456_1234",
    "status": "completed",
    "results": [...],
    "offset": 0,
    "limit": 10,
    "total_stored": 47,
    "total_estimate": 2500,
    "has_more": true,
    "next_cursor": "eyJvIjoxMCwiciI6ImFiYzEyMzQ1XzE3MzcxMjM0NTZfMTIzNCJ9",
    "from_cache": false,
    "credits_charged": 7
  },
  "timestamp": "2026-02-19T..."
}
```

Note: The POST may return `status: "completed"` immediately (especially for cached or light searches) or `status: "processing"` requiring polling. Always check the status.

## Poll for Results (GET)

**Endpoint:** `GET https://api.nyne.ai/person/search?request_id={id}`

**Headers:** Same `X-API-Key` and `X-API-Secret` as above.

### Check status once
```bash
curl -s "https://api.nyne.ai/person/search?request_id=$REQUEST_ID" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" | nyne_parse > /tmp/nyne_search.json

jq '{status: .data.status, total_stored: .data.total_stored}' /tmp/nyne_search.json
```

### Full polling loop

```bash
SECONDS_WAITED=0
TIMEOUT=600  # 10 minutes

while [ $SECONDS_WAITED -lt $TIMEOUT ]; do
  curl -s "https://api.nyne.ai/person/search?request_id=$REQUEST_ID" \
    -H "X-API-Key: $NYNE_API_KEY" \
    -H "X-API-Secret: $NYNE_API_SECRET" | nyne_parse > /tmp/nyne_search.json
  STATUS=$(jq -r '.data.status' /tmp/nyne_search.json)

  echo "[$(date +%H:%M:%S)] Status: $STATUS ($SECONDS_WAITED s)"

  case "$STATUS" in
    completed)
      jq '.data | {total_stored, total_estimate, has_more, credits_charged}' /tmp/nyne_search.json
      jq '.data.results[] | {displayname, headline, location}' /tmp/nyne_search.json
      break
      ;;
    failed)
      echo "Search failed:"
      jq '.data' /tmp/nyne_search.json
      break
      ;;
    *)
      sleep 5
      SECONDS_WAITED=$((SECONDS_WAITED + 5))
      ;;
  esac
done

if [ "$STATUS" != "completed" ] && [ "$STATUS" != "failed" ]; then
  echo "Timed out. Resume polling with request_id: $REQUEST_ID"
fi
```

## Pagination

After the initial search completes, paginate through results for free (cached results, no additional credits).

### Cursor-based pagination (recommended)

Use the `next_cursor` from the previous response:

```bash
curl -s -X POST "https://api.nyne.ai/person/search" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"cursor": "eyJvIjoxMCwiciI6ImFiYzEyMzQ1XzE3MzcxMjM0NTZfMTIzNCJ9"}' | nyne_parse > /tmp/nyne_search.json

jq '.data | {total_stored, offset, limit, has_more}' /tmp/nyne_search.json
jq '.data.results[] | {displayname, headline, location}' /tmp/nyne_search.json
```

### Offset-based pagination

Use `request_id` + `offset` from the original search:

```bash
curl -s -X POST "https://api.nyne.ai/person/search" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"request_id": "abc12345_1737123456_1234", "offset": 25, "limit": 25}' | nyne_parse > /tmp/nyne_search.json

jq '.data | {total_stored, offset, limit, has_more}' /tmp/nyne_search.json
jq '.data.results[] | {displayname, headline, location}' /tmp/nyne_search.json
```

**Pagination notes:**
- Paginating through cached results is free — no additional credits charged
- Maximum 1000 results per search (`offset + limit` ≤ 1000)
- `has_more` indicates whether more results are available
- `next_cursor` is only present when `has_more` is true
- Results are cached for 30 days

## Response Structure

When `status` is `completed`:

```json
{
  "success": true,
  "timestamp": "2026-02-19T...",
  "data": {
    "request_id": "abc12345_1737123456_1234",
    "status": "completed",
    "results": [
      {
        "displayname": "Jane Smith",
        "headline": "Senior Software Engineer at Google",
        "bio": "...",
        "location": "San Francisco, CA",
        "gender": "female",
        "estimated_age": 35,
        "total_experience_years": 12,
        "is_decision_maker": 1,
        "is_top_universities": true,
        "languages": ["English", "Spanish"],
        "interests": {
          "work": ["software engineering", "machine learning", "distributed systems"],
          "certification": ["AWS Solutions Architect"]
        },
        "patents": [],
        "best_business_email": "jane@google.com",
        "best_personal_email": "jane@gmail.com",
        "altemails": ["j.smith@gmail.com"],
        "fullphone": [{"fullphone": "+14155551234", "type": "mobile"}],
        "social_profiles": {
          "linkedin": {
            "url": "https://www.linkedin.com/in/janesmith",
            "username": "janesmith",
            "connections": 1243,
            "followers": 542,
            "photo_url": "..."
          }
        },
        "organizations": [
          {
            "name": "Google",
            "title": "Senior Software Engineer",
            "startDate": "3-2020",
            "location": "San Francisco",
            "company_website": "google.com",
            "industries": ["Technology"],
            "num_employees": "10001+"
          }
        ],
        "schools_attended": ["Stanford University"],
        "schools_info": [
          {
            "name": "Stanford University",
            "degree": "Master's",
            "title": "Computer Science",
            "startDate": "2012",
            "endDate": "2014"
          }
        ],
        "score": 0.92,
        "insights": {
          "match_reasoning": "Strong match based on..."
        }
      }
    ],
    "offset": 0,
    "limit": 10,
    "total_stored": 47,
    "total_estimate": 2500,
    "has_more": true,
    "next_cursor": "eyJvIjoxMCwi...",
    "from_cache": false,
    "credits_charged": 7
  }
}
```

### Result Fields

| Field | Type | Description |
|-------|------|-------------|
| `displayname` | string | Person's full name |
| `headline` | string | Current job title/headline |
| `bio` | string | Professional biography |
| `location` | string | Geographic location |
| `gender` | string | `"male"` or `"female"` |
| `estimated_age` | integer | Estimated age |
| `total_experience_years` | integer | Years of total work experience |
| `is_decision_maker` | integer | Whether person holds decision-making authority (1 = yes) |
| `is_top_universities` | boolean | Whether person attended a top-ranked university |
| `languages` | array | Languages spoken (array of strings) |
| `interests` | object | `{work: [...], certification: [...]}` — work interests and certifications |
| `patents` | array | Patents held: `{title, description, date, reference, url}` |
| `best_business_email` | string | Primary business email (requires `show_emails: true`) |
| `best_personal_email` | string | Primary personal email (requires `show_emails: true`) |
| `altemails` | array | Alternative email addresses (requires `show_emails: true`) |
| `fullphone` | array | Phone numbers with type (requires `show_phone_numbers: true`). Each: `{fullphone, type}` |
| `social_profiles` | object | Social profile data (see below) |
| `organizations` | array | Work history (see below) |
| `schools_attended` | array | University names as strings |
| `schools_info` | array | Detailed education: `{name, degree, major, startDate, endDate}` |
| `score` | number | AI relevance score 0-1 (requires `profile_scoring: true`) |
| `insights` | object | AI-generated match reasoning (requires `insights: true`) |

### Social Profiles Object

```json
{
  "linkedin": {
    "url": "https://www.linkedin.com/in/...",
    "username": "...",
    "connections": 1243,
    "followers": 542,
    "photo_url": "..."
  }
}
```

### Organization Object

```json
{
  "name": "Windfall Bio",
  "title": "Vice President of Software Engineering",
  "startDate": "2024-08-01",
  "endDate": null,
  "location": "San Mateo, California, United States",
  "company_website": "http://www.windfall.bio",
  "company_linkedin_url": "https://www.linkedin.com/company/windfallbio",
  "company_domain": "windfall.bio",
  "industries": ["Manufacturing"],
  "num_employees": 37,
  "num_employees_range": "11-50",
  "is_startup": true,
  "is_b2b": true,
  "is_b2c": false,
  "is_saas": false,
  "founded_in": 2022,
  "latest_funding_round": "Series A",
  "latest_funding_amount": 28000000,
  "funding_total_usd": 37000000,
  "annual_revenue": 345000,
  "specialties": ["methane", "climate", "agtech"],
  "technologies": ["Google Analytics", "AWS Lambda", "Webflow"],
  "companyDesc": "...",
  "logo_url": "..."
}
```

Organizations include rich company intelligence: funding data, tech stack, employee counts, and B2B/B2C/SaaS flags. Not all fields are present for every organization.

### Response Metadata Fields

| Field | Type | Description |
|-------|------|-------------|
| `total_stored` | integer | Number of results stored from this search |
| `total_estimate` | integer | Estimated total matching profiles |
| `has_more` | boolean | Whether more results are available for pagination |
| `next_cursor` | string | Opaque pagination token for next page (present when `has_more` is true) |
| `from_cache` | boolean | Whether results came from cache (30-day TTL) |
| `credits_charged` | integer | Total credits charged for this request |
| `offset` | integer | Current offset in result set |
| `limit` | integer | Results per page |

## Useful jq Filters

After polling completes, the clean response is at `/tmp/nyne_search.json`:

```bash
# Search metadata
jq '.data | {total_stored, total_estimate, has_more, credits_charged, from_cache}' /tmp/nyne_search.json

# List all people (name + headline + location)
jq '.data.results[] | {displayname, headline, location}' /tmp/nyne_search.json

# All emails
jq '.data.results[] | {displayname, best_business_email, best_personal_email, altemails}' /tmp/nyne_search.json

# Phone numbers
jq '.data.results[] | {displayname, fullphone}' /tmp/nyne_search.json

# LinkedIn profiles
jq '.data.results[] | {displayname, linkedin: .social_profiles.linkedin.url}' /tmp/nyne_search.json

# Work history per person
jq '.data.results[] | {displayname, orgs: [.organizations[] | {name, title}]}' /tmp/nyne_search.json

# Decision makers only
jq '[.data.results[] | select(.is_decision_maker == true)] | length' /tmp/nyne_search.json
jq '[.data.results[] | select(.is_decision_maker == true) | {displayname, headline}]' /tmp/nyne_search.json

# Sort by relevance score (if profile_scoring enabled)
jq '[.data.results | sort_by(-.score)[] | {displayname, headline, score}]' /tmp/nyne_search.json

# Experience range
jq '.data.results[] | {displayname, total_experience_years} | select(.total_experience_years >= 10)' /tmp/nyne_search.json

# Education
jq '.data.results[] | {displayname, schools: .schools_attended}' /tmp/nyne_search.json

# Interests and certifications
jq '.data.results[] | {displayname, work_interests: .interests.work, certifications: .interests.certification}' /tmp/nyne_search.json

# Patents
jq '.data.results[] | select(.patents | length > 0) | {displayname, patents: [.patents[] | {title, date}]}' /tmp/nyne_search.json

# Company intelligence (funding, tech stack)
jq '.data.results[] | {displayname, companies: [.organizations[] | {name, funding_total_usd, latest_funding_round, num_employees, is_startup}]}' /tmp/nyne_search.json

# Get next_cursor for pagination
jq -r '.data.next_cursor' /tmp/nyne_search.json

# Count results
jq '.data.results | length' /tmp/nyne_search.json
```

## Error Handling

| HTTP Code | Error | Description |
|-----------|-------|-------------|
| 400 | `invalid_parameters` | Invalid parameter value or missing query |
| 400 | `invalid_custom_filters` | Malformed custom_filters object |
| 401 | `invalid_credentials` | Invalid API key/secret |
| 404 | `request_not_found` | Invalid request_id for status check (GET only) |
| 429 | `rate_limit_exceeded` | Too many requests |
| 429 | `insufficient_credits` | Not enough credits for this search |
| 500 | `internal_error` | Server error |

## Search Tiers & When to Use Each

### Fast Search — `type: "light"` (1 credit per result)
Basic search with fast results in 3-40 seconds. Best for quick lookups when you need a broad list of names and don't need deep profile data. **AI features (`insights`, `high_freshness`) are NOT available for light type.** Profile scoring is available.
```json
{"query": "Software engineers at Google", "type": "light", "limit": 50}
```

### Smart Search — `type: "medium"`
Balanced tier between speed and quality. Use when you want better matching than light but don't need the full depth of premium. Supports all AI features.
```json
{"query": "Engineering managers in fintech", "type": "medium", "limit": 25}
```

### Pro Search — `type: "premium"` (5 credits per result)
Comprehensive search taking 30-300 seconds. Best quality results with deepest profile matching. Required for maximum-quality `insights` and `high_freshness` results. Use when result quality matters more than speed.
```json
{"query": "AI researchers at top universities", "type": "premium", "limit": 10, "insights": true, "profile_scoring": true}
```

## AI-Powered Analysis Features

These features add intelligence on top of search results. **Insights and High Freshness are NOT available for `light` type searches** — use `medium` or `premium`.

### Query Insights (`insights: true`, +1 credit per result)
AI-generated analysis for each result explaining **why this person matches your search query**. Returns structured reasoning about the match relevance — how their background, role, and experience align with what you're looking for. Invaluable for qualifying leads or evaluating candidates at scale. Use when you need to understand the "why" behind each match, not just the "who".
```json
{"query": "AI researchers in healthcare", "type": "premium", "insights": true, "limit": 10}
```

### Profile Scoring (`profile_scoring: true`, +1 credit)
AI relevance scoring that assigns each result a score from 0 to 1, where 1.0 is a perfect match. Use to **rank and prioritize** results by relevance. Works with all search tiers including light. Combine with insights for both a score and an explanation.
```json
{"query": "Senior engineers at fintech startups", "profile_scoring": true, "limit": 25}
```

### High Freshness (`high_freshness: true`, +2 credits)
Prioritizes profiles that have been **recently updated** — people who recently changed jobs, updated their LinkedIn, or have fresh activity. Use when recency matters: hiring recently active candidates, targeting people who just moved to a new role, or finding profiles with current contact info. **Not available for `light` type.**
```json
{"query": "Product managers who recently changed jobs", "type": "premium", "high_freshness": true, "show_emails": true}
```

### Combining AI Features
Stack insights + scoring + freshness for maximum intelligence:
```json
{
  "query": "VP of Engineering at Series B startups in San Francisco",
  "type": "premium",
  "insights": true,
  "profile_scoring": true,
  "high_freshness": true,
  "show_emails": true,
  "limit": 10
}
```

## Credit Costs

Credits are charged based on features used per request. Pagination within cached results is free.

| Feature | Credits | Description |
|---------|---------|-------------|
| Fast Search (`type: "light"`) | 1 | Basic search, fastest response (3-40 seconds) |
| Pro Search (`type: "premium"`) | 5 | Comprehensive search, best quality (30-300 seconds) |
| Smart Ranking (`profile_scoring`, boolean) | 1 | AI-powered relevance scoring of results |
| Candidate Insights (`insights`, boolean) | 1 | AI-generated insights about each result |
| Realtime Profiles (`high_freshness`, boolean) | 2 | Prioritize recently updated profiles |
| Filter Without Contact Data | 1 | Search without email/phone enrichment |
| Enrich Phones (`show_phone_numbers`, boolean) | 14 | Include phone numbers in results. **Significantly increases latency** |
| Enrich Emails (`show_emails`, boolean) | 2 | Include email addresses in results. **Significantly increases latency** |
| Require Emails (`require_emails`, boolean) | 1 | Only return profiles with email addresses |
| Require Phones (`require_phone_numbers`, boolean) | 1 | Only return profiles with phone numbers |
| Require Contact Info (`require_phones_or_emails`, boolean) | 1 | Only return profiles with phone OR email |
| Pagination (cached) | 0 | Free after initial search (30-day cache) |

## Rate Limits

- **Per minute:** 60 requests
- **Per hour:** 1,000 requests
- **Monthly:** Plan-dependent
