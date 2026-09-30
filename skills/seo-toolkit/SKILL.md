---
name: seo-toolkit
description: Use this skill for any SEO-related task. This includes analyzing robots.txt files for AI crawlers, generating Schema.org JSON-LD markup, submitting URLs for instant indexing via IndexNow, scoring and optimizing content for search engines, and tracking brand visibility across AI platforms (ChatGPT, Perplexity, Claude, Gemini). Covers technical SEO, on-page optimization, structured data, and AI search visibility.
---

# SEO Toolkit

A comprehensive set of SEO tools that work as MCP servers. Install any of them to add SEO capabilities to Claude Code.

## Available MCP Servers

### 1. robots.txt AI Manager (`robotstxt-ai-mcp`)

Analyze and generate robots.txt files with awareness of 20+ AI crawlers.

```json
{"mcpServers":{"robotstxt-ai":{"command":"npx","args":["-y","robotstxt-ai-mcp"]}}}
```

**Tools:** `fetch_robots`, `analyze_robots`, `generate_robots`, `list_ai_bots`, `check_bot_status`

**Known AI Bots:** GPTBot (OpenAI), ClaudeBot (Anthropic), Google-Extended, PerplexityBot, CCBot, Bytespider (ByteDance), Meta-ExternalAgent, Applebot-Extended, Amazonbot, cohere-ai, YouBot, Diffbot, and more.

**Key facts:**
- Google-Extended controls Gemini training but does NOT affect Google Search
- Blocking Googlebot removes site from Google Search — never do this unless asked
- CCBot feeds Common Crawl, widely used for AI training

### 2. Schema.org Generator (`schema-gen-mcp`)

Generate JSON-LD structured data for 12 Schema.org types.

```json
{"mcpServers":{"schema-gen":{"command":"npx","args":["-y","schema-gen-mcp"]}}}
```

**Tools:** `generate_schema`, `list_schema_types`, `generate_person_schema`, `generate_product_schema`, `generate_faq_schema`, `generate_article_schema`, `generate_organization_schema`, `validate_schema`

**Supported types:** Person, Organization, Product, Article, FAQPage, HowTo, LocalBusiness, Event, WebSite, BreadcrumbList, VideoObject, SoftwareApplication

**Output format:**
```html
<script type="application/ld+json">
{
  "@context": "https://schema.org",
  "@type": "Person",
  "name": "...",
  "jobTitle": "..."
}
</script>
```

### 3. IndexNow (`indexnow-mcp`)

Submit URLs for instant indexing across search engines.

```json
{"mcpServers":{"indexnow":{"command":"npx","args":["-y","indexnow-mcp"]}}}
```

**Tools:** `indexnow_submit`, `google_indexing_submit`, `google_indexing_status`, `indexnow_submit_sitemap`, `indexnow_generate_key`, `indexnow_list_engines`

**Supported engines:** Bing, Yandex, Naver, Seznam (via IndexNow), Google (via Indexing API)

### 4. Content Optimizer (`content-optimizer-mcp`)

Score and optimize content for search engines using SERP-based analysis.

```json
{"mcpServers":{"content-optimizer":{"command":"npx","args":["-y","content-optimizer-mcp"]}}}
```

**Tools:** `score_content`, `analyze_keyword`, `get_content_recommendations`, `check_readability`, `find_missing_topics`, `optimize_headings`

**Scoring categories (100 points):**
- Word Count (15) — vs SERP average
- Keyword Usage (20) — in title, headings, body
- Heading Structure (15) — H1/H2/H3 hierarchy
- Readability (15) — Flesch-Kincaid score
- Entity Coverage (15) — topics from competitors
- Content Depth (10) — paragraphs, unique words
- Internal Structure (10) — meta description, title

### 5. AI Visibility Tracker (`ai-visibility-mcp`)

Track brand visibility across AI platforms.

```json
{"mcpServers":{"ai-visibility":{"command":"npx","args":["-y","ai-visibility-mcp"]}}}
```

**Tools:** `check_brand_visibility`, `check_single_query`, `get_visibility_score`, `compare_brands`, `get_recommendations`, `list_platforms`

**Platforms tracked:** ChatGPT (OpenAI), Perplexity, Claude (Anthropic), Gemini (Google)

## Common Workflows

### Technical SEO Audit
1. Use `robotstxt-ai-mcp` to analyze robots.txt and check AI bot access
2. Use `schema-gen-mcp` to generate missing structured data
3. Use `content-optimizer-mcp` to score existing content
4. Use `indexnow-mcp` to submit fixed pages for re-indexing

### Content Optimization
1. Use `content-optimizer-mcp` → `analyze_keyword` for target keyword
2. Write/edit content based on SERP analysis
3. Use `score_content` to check score and get recommendations
4. Use `schema-gen-mcp` to add Article schema
5. Use `indexnow-mcp` to submit for instant indexing

### AI Visibility Improvement
1. Use `ai-visibility-mcp` → `get_visibility_score` for current score
2. Use `get_recommendations` for improvement suggestions
3. Use `compare_brands` vs competitors
4. Implement recommendations (structured data, FAQ content, etc.)

## Links

- [awesome-seo-mcp-servers](https://github.com/sharozdawa/awesome-seo-mcp-servers) — Full directory of SEO MCP servers
- All tools: MIT licensed, on npm, registered on Official MCP Registry
