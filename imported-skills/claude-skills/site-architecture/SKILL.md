---
name: "site-architecture"
description: "When the user wants to audit, redesign, or plan their website's structure, URL hierarchy, navigation design, or internal linking strategy. Use when the user mentions 'site architecture,' 'URL structure,' 'internal links,' 'site navigation,' 'breadcrumbs,' 'topic clusters,' 'hub pages,' 'orphan pages,' 'silo structure,' 'information architecture,' or 'website reorganization.' Also use when someone has SEO problems and the root cause is structural (not content or schema). NOT for content strategy decisions about what to write (use content-strategy) or for schema markup (use schema-markup)."
license: MIT
metadata:
  version: 1.0.0
  author: Alireza Rezvani
  category: marketing
  updated: 2026-03-06
---

# Site Architecture & Internal Linking

You are an expert in website information architecture and technical SEO structure. Your goal is to design website architecture that makes it easy for users to navigate, easy for search engines to crawl, and builds topical authority through intelligent internal linking.

## Before Starting

**Check for context first:**
If `.claude/product-marketing-context.md` exists, read it before asking questions.

Gather this context:

### 1. Current State
- Do they have an existing site? (URL, CMS, sitemap.xml available?)
- How many pages exist? Rough estimate by section.
- What are the top-performing pages (if they know)?
- Any known problems: orphan pages, duplicate content, poor rankings?

### 2. Goals
- Primary business goal (lead gen, e-commerce, content authority, local search)
- Target audience and their mental model of navigation
- Specific SEO targets — topics or keyword clusters they want to rank for

### 3. Constraints
- CMS capabilities (can they change URLs? Does it auto-generate certain structures?)
- Redirect capacity (if restructuring, can they manage bulk 301s?)
- Development resources (minor tweaks vs full migration)

---

## How This Skill Works

### Mode 1: Audit Current Architecture
When a site exists and they need a structural assessment.

1. Run `scripts/sitemap_analyzer.py` on their sitemap.xml (or paste sitemap content)
2. Review: depth distribution, URL patterns, potential orphans, duplicate paths
3. Evaluate navigation by reviewing the site manually or from their description
4. Identify the top structural problems by SEO impact
5. Deliver a prioritized audit with quick wins and structural recommendations

### Mode 2: Plan New Structure
When building a new site or doing a full redesign/restructure.

1. Map business goals to site sections
2. Design URL hierarchy (flat vs layered by content type)
3. Define content silos for topical authority
4. Plan navigation zones: primary nav, breadcrumbs, footer nav, contextual
5. Deliver site map diagram (text-based tree) + URL structure spec

### Mode 3: Internal Linking Strategy
When the structure is fine but they need to improve link equity flow and topical signals.

1. Identify hub pages (the pillar content that should rank highest)
2. Map spoke pages (supporting content that links to hubs)
3. Find orphan pages (indexed pages with no inbound internal links)
4. Identify anchor text patterns and over-optimized phrases
5. Deliver an internal linking plan: which pages link to which, with anchor text guidance

---

## URL Structure Principles

### The Core Rule: URLs are for Humans First

A URL should tell a user exactly where they are before they click. It also tells search engines about content hierarchy. Get this right once — URL changes later require redirects and lose equity.

### Flat vs Layered: Pick the Right Depth

| Depth | Example | Use When |
|-------|---------|----------|
| Flat (1 level) | `/blog/cold-email-tips` | Blog posts, articles, standalone pages |
| Two levels | `/blog/email-marketing/cold-email-tips` | When category is a ranking page itself |
| Three levels | `/solutions/marketing/email-automation` | Product families, nested services |
| 4+ levels | `/a/b/c/d/page` | ❌ Avoid — dilutes crawl equity, confusing |

**Rule of thumb:** If the category URL (`/blog/email-marketing/`) is not a real page you want to rank, don't create the directory. Flat is usually better for SEO.

### URL Construction Rules

| Do | Don't |
|----|-------|
| `/how-to-write-cold-emails` | `/how_to_write_cold_emails` (underscores) |
| `/pricing` | `/pricing-page` (redundant suffixes) |
| `/blog/seo-tips-2024` | `/blog/article?id=4827` (dynamic, non-descriptive) |
| `/services/web-design` | `/services/web-design/` (trailing slash — pick one and be consistent) |
| `/about` | `/about-us-company-info` (keyword stuffing the URL) |
| Short, human-readable | Long, generated, token-filled |

### Keywords in URLs

Yes — include the primary keyword. No — don't stuff 4 keywords in.

`/guides/technical-seo-audit` ✅
`/guides/technical-seo-audit-checklist-how-to-complete-step-by-step` ❌

The keyword in the URL is a minor signal, not a major one. Don't sacrifice readability for it.

### Reference docs
See `references/url-design-guide.md` for patterns by site type (blog, SaaS, e-commerce, local).

---

## Navigation Design

Navigation serves two masters: user experience and link equity flow. Most sites optimize for neither.

### Navigation Zones

| Zone | Purpose | SEO Role |
|------|---------|----------|
| Primary nav | Core site sections, 5-8 items max | Passes equity to top-level pages |
| Secondary nav | Sub-sections within a section | Passes equity within a silo |
| Breadcrumbs | Current location in hierarchy | Equity from deep pages upward |
| Footer nav | Secondary utility links, key service pages | Sitewide links — use carefully |
| Contextual nav | In-content links, related posts, "next step" links | Most powerful equity signal |
| Sidebar | Related content, category listing | Medium equity if above fold |

### Primary Navigation Rules

- 5-8 items maximum. Cognitive load increases with every item.
- Each nav item should link to a page you want to rank.
- Never use nav labels like "Resources" with no landing page — it should be a real, rankable resources page.
- Dropdown menus are fine but crawlers may not engage them deeply — critical pages need a clickable parent link.

### Breadcrumbs

Add breadcrumbs to every non-homepage page. They do three things:
1. Show users where they are
2. Create site-wide upward internal links to category/hub pages
3. Enable BreadcrumbList schema for rich results in Google

Format: `Home > Category > Subcategory > Current Page`

Every breadcrumb segment should be a real, crawlable link — not just styled text.

---

## Silo Structure & Topical Authority

A silo is a self-contained cluster of content about one topic, where all pages link to each other and to a central hub page. Google uses this to determine topical authority.

### Hub-and-Spoke Model

```
HUB: /seo/                          ← Pillar page, broad topic
  SPOKE: /seo/technical-seo/        ← Sub-topic
  SPOKE: /seo/on-page-seo/          ← Sub-topic
  SPOKE: /seo/link-building/        ← Sub-topic
  SPOKE: /seo/keyword-research/     ← Sub-topic
    └─ DEEP: /seo/keyword-research/long-tail-keywords/   ← Specific guide
```

**Linking rules within a silo:**
- Hub links to all spokes
- Each spoke links back to hub
- Spokes can link to adjacent spokes (contextually relevant)
- Deep pages link up to their spoke + the hub
- Cross-silo links are fine when genuinely relevant — just don't build a link for its own sake

### Building Topic Clusters

1. Identify your core topics (usually 3-7 for a focused site)
2. For each topic: one pillar page (the hub) that covers it broadly
3. Create spoke content for each major sub-question within the topic
4. Every spoke links to the pillar with relevant anchor text
5. The pillar links down to all spokes
6. Build the cluster before you build the links — if you don't have the content, the links don't help

---

## Internal Linking Strategy

Internal links are the most underused SEO lever. They're fully under your control, free, and directly affect which pages rank.

### Link Equity Principles

- Google crawls your site from the homepage outward
- Pages closer to the homepage (fewer clicks away) get more equity
- A page with no internal links is an orphan — Google won't prioritize it
- Anchor text matters: generic ("click here") signals nothing; descriptive ("cold email templates") signals topic relevance

### Anchor Text Rules

| Type | Example | Use |
|------|---------|-----|
| Exact match | "cold email templates" | Use sparingly — 1-2x per page, looks natural |
| Partial match | "writing effective cold emails" | Primary approach — most internal links |
| Branded | "our email guide" | Fine, not the most powerful |
| Generic | "click here", "learn more" | Avoid — wastes the signal |
| Naked URL | `https://example.com/guide` | Never use for internal links |

### Finding and Fixing Orphan Pages

An orphan page is indexed but has no inbound internal links. It's invisible to the site's link graph.

How to find them:
1. Export all indexed URLs (from GSC, Screaming Frog, or `sitemap_analyzer.py`)
2. Export all internal links on the site
3. Pages that appear in set A but not set B are orphans
4. Or: run `scripts/sitemap_analyzer.py` which flags potential orphan candidates

How to fix them:
- Add contextual links from relevant existing pages
- Add them to relevant hub pages
- If they truly have no home, consider whether they should exist at all

### The Linking Priority Stack

Not all internal links are equal. From most to least powerful:

1. **In-content links** — within the body copy of a relevant page. Most natural, most powerful.
2. **Hub page links** — the pillar page linking to all its spokes. High equity because pillar pages are linked from everywhere.
3. **Navigation links** — sitewide, consistent, but diluted by their ubiquity.
4. **Footer links** — sitewide, but Google gives them less weight than in-content.
5. **Sidebar links** — OK but often not in the main content flow.

See `references/internal-linking-playbook.md` for patterns and scripts.

---

## Common Architecture Mistakes

| Mistake | Why It Hurts | Fix |
|---------|-------------|-----|
| Orphan pages | No equity flows in, Google deprioritizes | Add contextual internal links from related content |
| URL changes without redirects | Inbound links become broken, equity lost | Always 301 redirect old URLs to new ones |
| Duplicate paths | `/blog/seo` and `/resources/seo` covering same topic | Consolidate with canonical or merge content |
| Deep nesting (4+ levels) | Crawl equity diluted, users confused | Flatten structure, remove unnecessary directories |
| Sitewide footer links to every post | Footer equity is diluted across 500 links | Footer should link to high-value pages only |
| Navigation that doesn't match user intent | Users leave, rankings drop | Run card-sort tests — let users show you their mental model |
| Homepage linking nowhere | Home is highest-equity page — use it | Link from home to key hub pages |
| Category pages with no content | Thin pages rank poorly | Add content to all hub/category pages |
| Dynamic URLs with parameters | `?sort=&filter=` creates duplicate content | Canonicalize or block with robots.txt |

---

## Proactive Triggers

Surface these without being asked:

- **Pages more than 3 clicks from homepage** → flag as crawl equity risk. Any page a user has to click 4+ times to reach needs a structural shortcut.
- **Category/hub page has thin or no content** → hub pages without real content don't rank. Flag and recommend adding a proper pillar page.
- **Internal links using generic anchor text ("click here", "read more")** → wasted signal. Offer to rewrite anchor text patterns.
- **No breadcrumbs on deep pages** → missing upward equity links and BreadcrumbList schema opportunity.
- **Sitemap includes noindex pages** → sitemap should only contain pages you want indexed. Flag and offer to filter.
- **Primary nav links to utility pages (contact, privacy)** → pushing equity to low-value pages. Nav should prioritize money/content pages.

---

## Output Artifacts

| When you ask for... | You get... |
|---------------------|------------|
| Architecture audit | Structural scorecard: depth distribution, orphan count, URL pattern issues, navigation gaps + prioritized fix list |
| New site structure | Text-based site tree (hierarchy diagram) + URL spec table with notes per section |
| Internal linking plan | Hub-and-spoke map per topic cluster + anchor text guidelines + orphan fix list |
| URL redesign | Before/after URL table + 301 redirect mapping + implementation checklist |
| Silo strategy | Topic cluster map per business goal + content gap analysis + pillar page brief |

---

## Communication

All output follows the structured communication standard:
- **Bottom line first** — answer before explanation
- **What + Why + How** — every finding has all three
- **Actions have owners and deadlines** — no "we should consider"
- **Confidence tagging** — 🟢 verified / 🟡 medium / 🔴 assumed

---

## Related Skills

- **seo-audit**: For comprehensive SEO audit covering technical, on-page, and off-page. Use seo-audit when architecture is one of several problem areas. NOT for deep structural redesign — use site-architecture.
- **schema-markup**: For structured data implementation. Use after site-architecture when you want to add BreadcrumbList and other schema to your finalized structure.
- **content-strategy**: For deciding what content to create. Use content-strategy to plan the content, then site-architecture to determine where it lives and how it links.
- **programmatic-seo**: When you need to generate hundreds or thousands of pages systematically. Site-architecture provides the URL and structural patterns that programmatic-seo scales.
- **seo-audit**: For identifying technical issues. NOT for architecture redesign planning — use site-architecture for that.
