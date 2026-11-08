---
name: csv2site
description: Turn a CSV file into a live listing website on JamstackAI. Use when the user uploads or pastes a CSV, mentions spreadsheet data, or asks to "turn this data into a site", "make a listing site", "create a product catalog", "build a directory from this CSV". Triggers on words like csv, spreadsheet, listings, catalog, directory, products, recipes, properties, jobs.
allowed-tools: Bash(bash *), Bash(curl *), Bash(cat *), Bash(python3 *)
---

# csv2site

Turn any CSV into a live listing website via JamstackAI. Analyzes columns automatically, picks the right template, deploys server-side.

---

## Prerequisites

Requires a JamstackAI API key from **jamstackai.com/api-keys**

```bash
export JAMSTACKAI_API_KEY=jsai_...
```

---

## Workflow

### Step 1 — Get the CSV

If a file path is provided:
```bash
cat /path/to/file.csv
```

If pasted inline — use as-is. Ask if unclear.

---

### Step 2 — Analyze the CSV (no auth needed)

```bash
curl -s -X POST "https://www.jamstackai.com/api/v1/analyze-csv" \
  -H "Content-Type: application/json" \
  -d "{\"csv\": $(python3 -c 'import json,sys; print(json.dumps(sys.stdin.read()))' < /path/to/file.csv)}"
```

Parse the response:
- `fields` — column names + types + samples
- `suggestions` — `{ titleField, descriptionField, priceField, imageField, categoryField }`
- `rowCount` — number of rows

---

### Step 3 — Choose template

| Content signals | Template |
|---|---|
| price, product, sku, buy | `csv-products` |
| address, city, phone, business | `csv-listings` |
| name, bio, role, department | `csv-directory` |
| date, time, venue, event | `csv-events` |
| ingredients, cook_time, calories | `csv-recipes` |

Default: `csv-listings`

---

### Step 4 — Ask for site name

> "What should the site be called?"

Pick a default color per template:
- Products: `#6366f1` · Listings: `#0ea5e9` · Directory: `#10b981`
- Events: `#f59e0b` · Recipes: `#ef4444`

---

### Step 5 — Generate via JamstackAI API

```bash
curl -s -X POST "https://www.jamstackai.com/api/mcp/call" \
  -H "Content-Type: application/json" \
  -H "x-api-key: $JAMSTACKAI_API_KEY" \
  -d "{
    \"tool\": \"generate_csv_site\",
    \"params\": {
      \"csv\": $(python3 -c 'import json,sys; print(json.dumps(sys.stdin.read()))' < /path/to/file.csv),
      \"template\": \"<template-id>\",
      \"site_name\": \"<site name>\",
      \"primary_color\": \"<hex>\",
      \"mapping\": {
        \"title\": \"<column>\",
        \"description\": \"<column>\",
        \"price\": \"<column>\",
        \"image\": \"<column>\",
        \"category\": \"<column>\"
      }
    }
  }"
```

Only include mapping fields that exist in the CSV. Skip null ones.

---

### Step 6 — Return result

```
✅ Site is live!

📊 <rowCount> items imported
🔗 https://jamstackai.com/sites/<slug>
🆔 Site ID: <id>

Want me to improve any descriptions with AI?
```

---

## Optional: Improve text with AI

```bash
curl -s -X POST "https://www.jamstackai.com/api/mcp/call" \
  -H "Content-Type: application/json" \
  -H "x-api-key: $JAMSTACKAI_API_KEY" \
  -d '{
    "tool": "improve_text",
    "params": {
      "field": "description",
      "currentValue": "<existing text>",
      "projectName": "<site name>"
    }
  }'
```

---

## List existing CSV sites

```bash
curl -s -X POST "https://www.jamstackai.com/api/mcp/call" \
  -H "Content-Type: application/json" \
  -H "x-api-key: $JAMSTACKAI_API_KEY" \
  -d '{"tool": "list-csv-sites", "params": {}}'
```

---

## Gotchas
- `analyze-csv` needs NO auth — call it directly without the API key
- All other calls go through `/api/mcp/call` with `x-api-key`
- Only include mapping fields that actually exist in the CSV
- `primary_color` must be a valid hex string with `#`
