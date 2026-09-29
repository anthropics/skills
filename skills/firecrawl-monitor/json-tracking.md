# JSON-mode change tracking (structured per-field diffs)

Reference for structured change tracking. Read from [SKILL.md](SKILL.md) when the user cares about specific structured fields (price, headline, in-stock flag, items in a list) rather than whole-page markdown diffs.

By default monitors diff each page's markdown and return a unified text diff. JSON-mode change tracking returns keyed per-field diffs instead — e.g. `plans[0].price: "$19/mo" → "$24/mo"` — which drop straight into a Slack message, CI step, or internal tool. The CLI flags don't cover this — pass a JSON body via positional file or piped stdin:

```bash
cat > pricing-monitor.json <<'EOF'
{
  "name": "Pricing watch",
  "goal": "Alert when plan prices or headline features change.",
  "schedule": { "text": "hourly", "timezone": "UTC" },
  "targets": [{
    "type": "scrape",
    "urls": ["https://example.com/pricing"],
    "scrapeOptions": {
      "formats": [{
        "type": "changeTracking",
        "modes": ["json"],
        "prompt": "Extract pricing tiers and headline features for each plan.",
        "schema": {
          "type": "object",
          "properties": {
            "plans": {
              "type": "array",
              "items": {
                "type": "object",
                "properties": {
                  "name":     { "type": "string" },
                  "price":    { "type": "string" },
                  "features": { "type": "array", "items": { "type": "string" } }
                }
              }
            }
          }
        }
      }]
    }
  }]
}
EOF
firecrawl monitor create pricing-monitor.json
# or: cat pricing-monitor.json | firecrawl monitor create
```

Each changed page in the check response then carries a per-field diff plus a snapshot of the current full extraction:

```json
{
  "url": "https://example.com/pricing",
  "status": "changed",
  "diff": {
    "json": {
      "plans[0].price": { "previous": "$19/mo", "current": "$24/mo" },
      "plans[1].features[2]": {
        "previous": "10 GB storage",
        "current": "25 GB storage"
      }
    }
  },
  "snapshot": {
    "json": {
      "plans": [
        { "name": "Pro", "price": "$49/mo", "features": ["25 GB storage"] }
      ]
    }
  }
}
```

Use `modes: ["json", "git-diff"]` for **mixed mode** — you get both `diff.json` (per-field) and `diff.text` (markdown sidecar), and the page is marked `changed` whenever either surface changed. For markdown-only monitors, `diff.text` holds the unified diff and `diff.json` is a `parse-diff` AST (`{ files: [...] }`); there is no `snapshot`.
