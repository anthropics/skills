# MCP Tool Spec — instant-deploy

## Overview
Add a new server-side MCP tool `instant-deploy` to the existing `/api/mcp/call` endpoint.

This enables Claude Code skills to deploy HTML pages to Cloudflare Pages without exposing the CF token to users. The server handles all Cloudflare operations internally.

Auth: existing `x-api-key` (`jsai_...`) pipeline — no changes needed.

---

## Tool Definition

Add to the tools array in `/api/mcp/tools` response:

```json
{
  "name": "instant-deploy",
  "description": "Deploy a complete HTML page to a live Cloudflare Pages URL. Accepts raw HTML, slugifies the title, creates or reuses the CF Pages project, deploys, and returns the live URL.",
  "cost": 100,
  "inputSchema": {
    "type": "object",
    "properties": {
      "html": {
        "type": "string",
        "description": "Complete HTML document to deploy (full page with <!DOCTYPE html>)"
      },
      "title": {
        "type": "string",
        "description": "Page title used to generate the Cloudflare Pages project slug (English, kebab-case friendly)"
      }
    },
    "required": ["html", "title"]
  }
}
```

---

## Server Implementation

### Location
Add handler in the existing MCP tool executor (wherever `generate_csv_site`, `create_site` etc. are handled).

### Logic

```typescript
case 'instant-deploy': {
  const { html, title } = params

  // 1. Slugify title
  const slug = title
    .toLowerCase()
    .replace(/[^a-z0-9 _-]/g, '')
    .replace(/[ _]+/g, '-')
    .replace(/-+/g, '-')
    .replace(/^-|-$/g, '')
    .slice(0, 50) || 'instant-page'

  // 2. Write HTML to temp dir
  const tmpDir = `/tmp/instant-deploy-${slug}-${Date.now()}`
  fs.mkdirSync(tmpDir, { recursive: true })
  fs.writeFileSync(`${tmpDir}/index.html`, html)

  // 3. Check/create CF Pages project
  const accountId = process.env.CLOUDFLARE_ACCOUNT_ID
  const cfToken = process.env.CLOUDFLARE_API_TOKEN

  const projectCheck = await fetch(
    `https://api.cloudflare.com/client/v4/accounts/${accountId}/pages/projects/${slug}`,
    { headers: { Authorization: `Bearer ${cfToken}` } }
  )

  if (projectCheck.status !== 200) {
    await fetch(
      `https://api.cloudflare.com/client/v4/accounts/${accountId}/pages/projects`,
      {
        method: 'POST',
        headers: {
          Authorization: `Bearer ${cfToken}`,
          'Content-Type': 'application/json'
        },
        body: JSON.stringify({ name: slug, production_branch: 'main' })
      }
    )
  }

  // 4. Deploy via wrangler (child_process)
  const { execSync } = require('child_process')
  execSync(
    `wrangler pages deploy ${tmpDir} --project-name ${slug} --branch main --commit-dirty=true`,
    { env: { ...process.env, CLOUDFLARE_API_TOKEN: cfToken } }
  )

  // 5. Cleanup
  fs.rmSync(tmpDir, { recursive: true })

  return {
    success: true,
    result: {
      url: `https://${slug}.pages.dev`,
      slug
    },
    cost: 100
  }
}
```

### Environment variables needed (server-side only, never exposed)
```
CLOUDFLARE_API_TOKEN=...   # existing if already used for other deploys
CLOUDFLARE_ACCOUNT_ID=...  # your CF account ID
```

---

## Cost
100 tokens per deploy — covers CF API calls + wrangler execution time. Adjust as needed.

---

## Notes
- `wrangler` must be installed on the server (`npm i -g wrangler`)
- Multiple users can deploy simultaneously — each gets a unique `slug` derived from their title
- If two users deploy the same slug, the second deploy updates the existing project (fine)
- HTML size limit: suggest 5MB max (enforce in validation before exec)
- No user Cloudflare account needed — all deploys go to your CF account

---

## Testing

```bash
curl -X POST https://www.jamstackai.com/api/mcp/call \
  -H "Content-Type: application/json" \
  -H "x-api-key: jsai_your_test_key" \
  -d '{
    "tool": "instant-deploy",
    "params": {
      "html": "<!DOCTYPE html><html><body><h1>Test</h1></body></html>",
      "title": "test-page"
    }
  }'

# Expected response:
# { "success": true, "result": { "url": "https://test-page.pages.dev", "slug": "test-page" }, "cost": 100 }
```