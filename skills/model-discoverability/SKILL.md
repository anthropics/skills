---
name: model-discoverability
description: Deploy AI model discoverability for any website — llms.txt, Schema.org JSON-LD, companion data files with computation guides, and OpenAPI specs. Makes your content findable and computable by ChatGPT, Claude, Gemini, and Perplexity.
---

# /model-discoverability

Deploy a complete AI model discoverability stack for any website. Makes your content discoverable by frontier AI models (ChatGPT, Claude, Gemini, Perplexity) and your data computable by models with code execution.

## What This Skill Does

When invoked, this skill:

1. **Audits** your current AI discoverability (checks for llms.txt, Schema.org markup, robots.txt, structured data)
2. **Generates** all missing discoverability files
3. **Deploys** them to your web server
4. **Tests** that all endpoints are accessible
5. **Reports** what was deployed and what AI models can now do with your content

## The Four Layers

### Layer 1: llms.txt (Discovery)
A markdown file at `yoursite.com/llms.txt` following the [llmstxt.org](https://llmstxt.org) standard. Describes your organization and content in a format optimized for AI model consumption. This is the first thing a web-searching AI model reads when it hits your domain.

### Layer 2: Schema.org JSON-LD (Structured Metadata)
Structured data embedded in your HTML pages using Schema.org vocabulary. Pages with proper schema markup are 3x more likely to appear in Google AI Overviews. Supports Organization, Product, Book, Article, FAQPage, and Dataset types.

### Layer 3: Companion Data + Computation Guide (Computable Data)
Machine-readable JSON/CSV files published alongside your content with embedded `_computation_guide` fields that tell AI models:
- What the data means (column definitions)
- What analyses to perform (suggested queries)
- Where to download in different formats
- How to cite the source

AI models with code execution (ChatGPT Code Interpreter, Claude artifacts) can download and analyze this data live.

### Layer 4: OpenAPI Specification (Programmatic Access)
An OpenAPI 3.0 spec describing your data endpoints. Tool-using AI models look for these to understand what data is available and how to access it.

## Usage

```
/model-discoverability                    — Audit current state and generate all files
/model-discoverability audit              — Audit only, report what's missing
/model-discoverability generate           — Generate all discoverability files
/model-discoverability deploy             — Deploy generated files to web server
/model-discoverability test               — Test all endpoints are accessible
/model-discoverability add-data <file>    — Add a data file with computation guide
```

## Audit Mode (`/model-discoverability audit`)

Checks your website for:
- [ ] `llms.txt` at domain root
- [ ] `llms-full.txt` (extended catalog version)
- [ ] `robots.txt` referencing llms.txt
- [ ] Schema.org JSON-LD on key pages
- [ ] Companion data files in `/data/`
- [ ] OpenAPI spec describing data endpoints
- [ ] Proper CORS headers for AI agent access
- [ ] Sitemap.xml

Reports a score (0-8) and lists what's missing.

## Generate Mode (`/model-discoverability generate`)

For each missing component, generates the file:

### llms.txt Generation
Asks for:
- Organization name and description
- Key products/content areas
- Contact information

Produces a markdown file following the llmstxt.org spec with:
- Organization overview
- Content catalog (products, articles, datasets)
- Links to detailed pages
- Contact and licensing information

### Schema.org JSON-LD Generation
Scans your pages and generates JSON-LD blocks for:
- **Organization** — on homepage
- **Product/Book/Article** — on content pages
- **FAQPage** — on FAQ/help pages
- **Dataset** — on data/research pages

Outputs injectable `<script type="application/ld+json">` blocks.

### Companion Data + Computation Guide
For any structured data (CSV, JSON, database):
1. Analyzes the data schema
2. Generates column definitions
3. Suggests 5-10 analyses AI models can perform
4. Creates download URLs in multiple formats
5. Adds citation and license information
6. Wraps everything in a `_computation_guide` field

### OpenAPI Spec Generation
Creates an OpenAPI 3.0 spec describing:
- Available data endpoints
- Response schemas
- Data types and formats
- Authentication (if any)

## Deploy Mode (`/model-discoverability deploy`)

Deploys generated files to your web server. Supports:

### Apache (reverse proxy)
Adds `Alias` directives and `ProxyPass !` exclusions to serve static files before the proxy:
```apache
Alias /llms.txt /var/www/yoursite/static/llms.txt
ProxyPass /llms.txt !
```

### Nginx
Adds `location` blocks:
```nginx
location = /llms.txt {
    alias /var/www/yoursite/static/llms.txt;
    add_header Access-Control-Allow-Origin "*";
}
```

### Static hosting (Vercel, Netlify, S3)
Places files in the public/static directory.

### Streamlit / Flask / Express
Adds route handlers for static file serving.

## Add Data Mode (`/model-discoverability add-data <file>`)

Takes any CSV or JSON data file and:
1. Analyzes its structure
2. Generates a computation guide
3. Creates JSON + CSV versions
4. Generates an OpenAPI spec entry
5. Updates llms.txt with the new data source
6. Deploys to the data directory

Example:
```
/model-discoverability add-data data/rankings.csv
```

Produces:
- `data/rankings.json` (with `_computation_guide`)
- `data/rankings.csv` (original, clean)
- Updated `data/api.json` (OpenAPI spec)
- Updated `llms.txt` (new data source listed)

## Computation Guide Format

The `_computation_guide` field is the key innovation. It tells AI models what they can DO with your data:

```json
{
  "_computation_guide": {
    "description": "Human-readable description of the dataset",
    "suggested_analyses": [
      "Compare X and Y on dimension Z",
      "Rank all entries by column W",
      "Calculate group averages",
      "Find outliers above threshold T"
    ],
    "column_definitions": {
      "column_name": "What this column means, units, scale"
    },
    "download_formats": {
      "json": "https://yoursite.com/data/file.json",
      "csv": "https://yoursite.com/data/file.csv"
    },
    "citation": "How to cite this data",
    "license": "Usage terms"
  }
}
```

## Testing

After deployment, the skill tests:
- Each URL returns 200 with correct content type
- CORS headers allow cross-origin access
- JSON files are valid JSON
- CSV files have correct headers
- Schema.org validates against Google's Structured Data Testing Tool format
- llms.txt follows the llmstxt.org spec

## Best Practices

1. **Update llms.txt when you publish new content** — it's your AI-facing catalog
2. **Add computation guides to every data-rich page** — this is what makes your data computable, not just findable
3. **Use CC-BY-SA or similar open license for companion data** — AI models are more likely to cite freely available data
4. **Include suggested analyses** — models with code execution will actually run them
5. **Keep Schema.org markup current** — stale metadata is worse than no metadata
6. **Test with real AI queries** — ask ChatGPT/Claude/Perplexity about your content and see if they find it

## References

- [llmstxt.org](https://llmstxt.org) — The llms.txt standard
- [Schema.org/Book](https://schema.org/Book) — Book structured data
- [Schema.org/Dataset](https://schema.org/Dataset) — Dataset structured data
- [OpenAPI 3.0 Specification](https://spec.openapis.org/oas/v3.0.0)
- [Google Structured Data Testing](https://search.google.com/structured-data/testing-tool)
