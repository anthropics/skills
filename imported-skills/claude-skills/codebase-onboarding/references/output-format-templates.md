# codebase-onboarding reference

## Output Formats

### Notion Export

```javascript
// Use Notion API to create onboarding page
const { Client } = require('@notionhq/client')
const notion = new Client({ auth: process.env.NOTION_TOKEN })

const blocks = markdownToNotionBlocks(onboardingMarkdown) // use notion-to-md
await notion.pages.create({
  parent: { page_id: ONBOARDING_PARENT_PAGE_ID },
  properties: { title: { title: [{ text: { content: 'Engineer Onboarding — MyApp' } }] } },
  children: blocks,
})
```

### Confluence Export

```bash
# Using confluence-cli or REST API
curl -X POST \
  -H "Content-Type: application/json" \
  -u "user@example.com:$CONFLUENCE_TOKEN" \
  "https://yourorg.atlassian.net/wiki/rest/api/content" \
  -d '{
    "type": "page",
    "title": "Codebase Onboarding",
    "space": {"key": "ENG"},
    "body": {
      "storage": {
        "value": "<p>Generated content...</p>",
        "representation": "storage"
      }
    }
  }'
```

---
