---
name: nyne-deep-research
description: >
  Research any person using the Nyne Deep Research API. Submit an email, phone, social URL,
  or name and receive a comprehensive intelligence dossier with psychographic profile, social graph,
  career analysis, conversation starters, and approach strategy. Async with 2-5 min processing.
---

# Nyne Deep Research Skill

Research any person by email, phone, social URL, or name. Returns a comprehensive intelligence dossier with psychographic profile, social graph, career analysis, conversation starters, and approach strategy.

**Important:** This API is async with high latency (2-5 min processing). You submit a request, get a `request_id`, then poll until complete.

## Agent Instructions

When presenting results to the user, show **maximum depth** — display every section of the dossier in full. Do not summarize or truncate. Walk through each section sequentially:

1. **Identity Snapshot** — who they are
2. **Career DNA** — trajectory and superpower
3. **Psychographic Profile** — values, motivations, archetypes
4. **Personal Life & Hobbies** — interests outside work
5. **Social Graph Analysis** — inner circle, professional network, interest graph
6. **Interest Cluster Deep Dive** — all 9 clusters with detail
7. **Content & Voice Analysis** — topics, tone, opinions, quotes
8. **Key Relationships** — full list with relationship nature and importance
9. **Conversation Starters** — all 4 hook categories
10. **Recommendations / How Others See Them** — reputation signals
11. **Warnings & Landmines** — topics to avoid, sensitivities
12. **Creepy-Good Insights** — non-obvious findings with evidence
13. **Approach Strategy** — best angle, topics, what not to do

Also include `enrichment` data (contact info, work history, education) and note whether `following` and `articles` sections have data.

If `dossier` is null, present the `enrichment` data and let the user know the full dossier was not generated (this can happen with duplicate or cached requests — resubmit with a different identifier).

If `following` or `articles` are null, simply note they were not available for this person.

## Setup

**Required environment variables:**
- `NYNE_API_KEY` — your Nyne API key
- `NYNE_API_SECRET` — your Nyne API secret

Get credentials at [https://api.nyne.ai](https://api.nyne.ai).

Set these in your shell before running any commands:
```bash
export NYNE_API_KEY="your-api-key"
export NYNE_API_SECRET="your-api-secret"
```

To persist across sessions, add the exports to your shell profile (`~/.zshrc`, `~/.bashrc`, etc.) or create a `.env` file and source it:
```bash
# Create .env file (keep out of version control)
echo 'export NYNE_API_KEY="your-api-key"' >> ~/.nyne_env
echo 'export NYNE_API_SECRET="your-api-secret"' >> ~/.nyne_env
source ~/.nyne_env
```

Verify they're set:
```bash
echo "Key: ${NYNE_API_KEY:0:8}... Secret: ${NYNE_API_SECRET:0:6}..."
```

## Important: JSON Handling

The API response can contain control characters in JSON string values that break `jq`. All examples below use a `nyne_parse` helper that pipes through `python3` to clean and re-encode the JSON before passing to `jq`. Define it once per session:

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

Submit a research request by email and poll until complete:

```bash
# Define helper (strips control chars, re-encodes clean JSON)
nyne_parse() {
  python3 -c "
import sys, json, re
raw = sys.stdin.read()
clean = re.sub(r'[\x00-\x1f]+', ' ', raw)
data = json.loads(clean)
json.dump(data, sys.stdout)
"
}

# Submit research request
REQUEST_ID=$(curl -s -X POST "https://api.nyne.ai/person/deep-research" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"email": "someone@example.com"}' | nyne_parse | jq -r '.data.request_id')

echo "Request submitted: $REQUEST_ID"

# Poll until complete (checks every 5s, times out after 10 min)
SECONDS_WAITED=0
while [ $SECONDS_WAITED -lt 600 ]; do
  curl -s "https://api.nyne.ai/person/deep-research?request_id=$REQUEST_ID" \
    -H "X-API-Key: $NYNE_API_KEY" \
    -H "X-API-Secret: $NYNE_API_SECRET" | nyne_parse > /tmp/nyne_response.json
  STATUS=$(jq -r '.data.status' /tmp/nyne_response.json)
  echo "Status: $STATUS ($SECONDS_WAITED seconds elapsed)"
  if [ "$STATUS" = "completed" ]; then
    jq '.data.result' /tmp/nyne_response.json
    break
  elif [ "$STATUS" = "failed" ]; then
    echo "Research failed."
    jq . /tmp/nyne_response.json
    break
  fi
  sleep 5
  SECONDS_WAITED=$((SECONDS_WAITED + 5))
done

if [ $SECONDS_WAITED -ge 600 ]; then
  echo "Timed out after 10 minutes. Try polling manually with request_id: $REQUEST_ID"
fi
```

## Submit Research (POST)

**Endpoint:** `POST https://api.nyne.ai/person/deep-research`

**Headers:**
```
Content-Type: application/json
X-API-Key: $NYNE_API_KEY
X-API-Secret: $NYNE_API_SECRET
```

**Parameters:**

| Parameter | Type | Description |
|-----------|------|-------------|
| `email` | string | Email address |
| `phone` | string | Phone number |
| `social_media_url` | string or array | Social profile URL(s), up to 3 |
| `name` | string | Full name (use with `company` or `city` for disambiguation) |
| `company` | string | Company name (helps disambiguate `name`) |
| `city` | string | City (helps disambiguate `name`) |
| `callback_url` | string | Webhook URL to POST results when complete |

At least one identifier is required: `email`, `phone`, `social_media_url`, or `name` with `company`/`city`.

### Examples

**By email:**
```bash
curl -s -X POST "https://api.nyne.ai/person/deep-research" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"email": "someone@example.com"}' | nyne_parse | jq .
```

**By social media URL:**
```bash
curl -s -X POST "https://api.nyne.ai/person/deep-research" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"social_media_url": "https://twitter.com/elonmusk"}' | nyne_parse | jq .
```

**By multiple social URLs:**
```bash
curl -s -X POST "https://api.nyne.ai/person/deep-research" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"social_media_url": ["https://twitter.com/elonmusk", "https://linkedin.com/in/elonmusk"]}' | nyne_parse | jq .
```

**By name + company:**
```bash
curl -s -X POST "https://api.nyne.ai/person/deep-research" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"name": "Jane Smith", "company": "Acme Corp"}' | nyne_parse | jq .
```

**By phone:**
```bash
curl -s -X POST "https://api.nyne.ai/person/deep-research" \
  -H "Content-Type: application/json" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" \
  -d '{"phone": "+14155551234"}' | nyne_parse | jq .
```

**Submit response (HTTP 202):**
```json
{
  "success": true,
  "data": {
    "request_id": "abc123-def456-...",
    "status": "pending"
  }
}
```

## Poll for Results (GET)

**Endpoint:** `GET https://api.nyne.ai/person/deep-research?request_id={id}`

**Headers:** Same `X-API-Key` and `X-API-Secret` as above.

**Status progression:** `pending` → `enriching` → `gathering` → `analyzing` → `completed` (or `failed`)

This typically takes 2-3 minutes.

### Check status once
```bash
curl -s "https://api.nyne.ai/person/deep-research?request_id=$REQUEST_ID" \
  -H "X-API-Key: $NYNE_API_KEY" \
  -H "X-API-Secret: $NYNE_API_SECRET" | nyne_parse | jq '{status: .data.status, completed: .data.completed}'
```

### Full polling loop

```bash
SECONDS_WAITED=0
TIMEOUT=600  # 10 minutes

while [ $SECONDS_WAITED -lt $TIMEOUT ]; do
  curl -s "https://api.nyne.ai/person/deep-research?request_id=$REQUEST_ID" \
    -H "X-API-Key: $NYNE_API_KEY" \
    -H "X-API-Secret: $NYNE_API_SECRET" | nyne_parse > /tmp/nyne_response.json
  STATUS=$(jq -r '.data.status' /tmp/nyne_response.json)

  echo "[$(date +%H:%M:%S)] Status: $STATUS ($SECONDS_WAITED s)"

  case "$STATUS" in
    completed)
      jq '.data.result' /tmp/nyne_response.json
      break
      ;;
    failed)
      echo "Research failed:"
      jq '.data' /tmp/nyne_response.json
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

## Response Structure

When `status` is `completed`, the response looks like:

```json
{
  "success": true,
  "timestamp": "2025-01-15T12:00:00Z",
  "data": {
    "status": "completed",
    "completed": true,
    "request_id": "abc123-...",
    "created_on": "2025-01-15T11:57:00Z",
    "completed_on": "2025-01-15T12:00:00Z",
    "result": {
      "enrichment": { ... },
      "dossier": { ... },
      "following": { ... },
      "articles": [ ... ]
    }
  }
}
```

### `result` sections

| Section | Description |
|---------|-------------|
| `enrichment` | Contact info, social profiles, bio, schools, work history (20+ keys) |
| `dossier` | The main intelligence output — 15 sections (see below) |
| `following` | Twitter/Instagram following data (can be null) |
| `articles` | Press and media mentions (can be null) |

## Dossier Sections Reference

The `dossier` object contains 15 sections:

### `identity_snapshot`
Top-level identity summary.
- `full_name`, `current_role`, `company`, `location`, `age_estimate`, `emails`, `social_profiles`, `headline`, `birthday`, `self_description`

### `career_dna`
Career trajectory and strengths.
- `trajectory`, `superpower`

### `psychographic_profile`
Values, motivations, and personality archetypes.
- `values`, `motivations`, `archetypes`, `political_leanings`, `cluster_analysis`

### `personal_life_hobbies`
Interests and personality outside of work.
- `life_outside_work`, `entertainment_culture`, `personal_passions`, `active_hobbies_sports`, `quirks_personality`

### `social_graph_analysis`
Network and relationship mapping.
- `inner_circle`, `professional_network`, `personal_interest_graph`

### `interest_cluster_deep_dive`
Deep analysis across 9 interest clusters.
- `tech`, `sports_fitness`, `music_entertainment`, `food_lifestyle`, `causes_politics`, `intellectual_interests`, `geographic_ties`, `personal_network`, `unexpected_surprising`

### `content_voice_analysis`
How they communicate and what they care about.
- `topics`, `tone`, `humor_style`, `strong_opinions`, `frustrations`, `notable_quotes`, `recent_wins`

### `content_analysis`
Alias of `content_voice_analysis` (kept for backward compatibility).

### `key_relationships`
List of ~25 objects describing important connections.
- Each: `name`, `handle`, `followers`, `relationship_nature`, `why_important`

### `key_influencers`
Alias of `key_relationships`.

### `conversation_starters`
Hooks to open conversation, in 4 categories.
- `professional_hooks`, `personal_interest_hooks`, `current_events_hooks`, `shared_experience_hooks`

### `recommendations_how_others_see_them`
Public perception and reputation signals.
- `highlighted_qualities`, `colleague_descriptions`, `patterns_in_praise`

### `warnings_landmines`
Topics and areas to avoid.
- `topics_to_avoid`, `political_hot_buttons`, `sensitive_career_history`, `competitors_they_dislike`

### `creepy_good_insights`
Non-obvious insights derived from data.
- List of objects: `insight`, `evidence`

### `approach_strategy`
How to approach this person.
- `best_angle`, `topics_that_resonate`, `personal_interests_to_reference`, `shared_connections`, `what_not_to_do`

## Useful jq Filters

After polling completes, the clean response is at `/tmp/nyne_response.json`. Use `jq` directly on the file:

```bash
# Extract identity snapshot
jq '.data.result.dossier.identity_snapshot' /tmp/nyne_response.json

# Get all conversation starters
jq '.data.result.dossier.conversation_starters' /tmp/nyne_response.json

# List key relationships (name + why important)
jq '.data.result.dossier.key_relationships[] | {name, why_important}' /tmp/nyne_response.json

# Get approach strategy
jq '.data.result.dossier.approach_strategy' /tmp/nyne_response.json

# Extract a specific dossier section by name
jq --arg s "psychographic_profile" '.data.result.dossier[$s]' /tmp/nyne_response.json

# Get enrichment contact info
jq '.data.result.enrichment | {emails, phones, linkedin_url, twitter_url}' /tmp/nyne_response.json

# Check processing status only
jq '{status: .data.status, completed: .data.completed, request_id: .data.request_id}' /tmp/nyne_response.json

# Get warnings and landmines
jq '.data.result.dossier.warnings_landmines' /tmp/nyne_response.json

# List all creepy-good insights
jq '.data.result.dossier.creepy_good_insights[].insight' /tmp/nyne_response.json
```

## Error Handling

| HTTP Code | Error | Description |
|-----------|-------|-------------|
| 400 | `INVALID_PARAMETERS` | Malformed request body |
| 400 | `MISSING_PARAMETER` | No identifier provided (need email, phone, social_media_url, or name+company/city) |
| 401 | `AUTHENTICATION_FAILED` | Invalid or missing API key/secret |
| 402 | `INSUFFICIENT_CREDITS` | Not enough credits (100 credits per request) |
| 403 | `NO_ACTIVE_SUBSCRIPTION` | Subscription required |
| 403 | `ACCESS_DENIED` | Account does not have access |
| 429 | `RATE_LIMIT_EXCEEDED` | Too many requests |
| 500 | `QUEUE_ERROR` | Internal processing error |

## Rate Limits & Costs

- **Rate limits:** 10 requests/minute, 100 requests/hour
- **Cost:** 100 credits per research request
- **Processing time:** Typically 2-3 minutes, up to 5 minutes
