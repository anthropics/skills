# Internal Linking Playbook

Patterns for building an internal link structure that distributes equity intelligently and reinforces topical authority.

---

## The Three Goals of Internal Linking

1. **Crawlability** — every page should be reachable from the homepage in 3 clicks or fewer
2. **Equity flow** — link equity flows from authoritative pages to pages you want to rank
3. **Topical signals** — anchor text and link context tell Google what a page is about

Most sites get none of these right. The ones that do compound their SEO advantage over time.

---

## Linking Architecture Patterns

### Pattern 1: Hub-and-Spoke (Topic Cluster)

Best for: Content sites, blogs, SaaS feature/solution pages.

```
Hub (Pillar) Page
├── Spoke 1 (Sub-topic)
│   └── Deep 1a (Specific guide within sub-topic)
│   └── Deep 1b
├── Spoke 2 (Sub-topic)
│   └── Deep 2a
└── Spoke 3 (Sub-topic)
```

**Link rules:**
- Hub → all spokes (contextual, in-body links)
- Each spoke → hub (with anchor text matching hub's target keyword)
- Each spoke → adjacent spokes (only when genuinely relevant)
- Deep pages → parent spoke + hub

**What makes this work:** The hub becomes the authority page because it receives links from everything in the cluster. Google sees a well-linked hub as the definitive resource on the topic.

---

### Pattern 2: Linear (Sequential Content)

Best for: Course content, multi-part guides, documentation, step-by-step processes.

```
Introduction → Part 1 → Part 2 → Part 3 → Summary/CTA
```

**Link rules:**
- Each page links forward (next) and back (previous)
- An index page links to all parts
- Summary page links back to each key section

**What makes this work:** Clear navigation for users, clear sequence for crawlers.

---

### Pattern 3: Conversion Funnel Linking

Best for: SaaS sites, lead gen sites — moving users from content to conversion.

```
Blog Post (awareness) → Feature Page (consideration) → Pricing Page (decision)
Blog Post (awareness) → Case Study (social proof) → Free Trial / Demo CTA
```

**Link rules:**
- Every blog post should have at least one contextual link to a product/feature page
- Case studies link to the relevant feature/solution and to pricing
- Feature pages link to relevant case studies and to pricing
- Pricing page links to FAQ and to demo/trial

**What makes this work:** Equity flows from content (high link volume) to money pages (low link volume). Most SaaS sites have this backwards — money pages get links from the nav only.

---

### Pattern 4: Star / Authority Distribution

Best for: Homepage and top-level hub pages that have lots of external links.

```
Homepage (authority source)
├── Service Page A (direct link from homepage)
├── Feature Page B (direct link from homepage)
├── Blog Category Hub (direct link from homepage)
└── Case Studies Hub (direct link from homepage)
```

**Link rules:**
- Homepage links only to the most important pages
- Not to every blog post — to the category hubs
- Each hub then distributes equity downward

**What makes this work:** Homepage equity isn't diluted across 200 blog links. It concentrates on 5-8 priority pages, which then funnel it to their children.

---

## Anchor Text Strategy

### The Right Mix

| Type | Target % of Internal Links | Example |
|------|--------------------------|---------|
| Descriptive partial match | 50-60% | "cold email writing guide" |
| Exact match keyword | 10-15% | "cold email templates" |
| Page title / branded | 20-25% | "our guide to cold outreach" |
| Generic | <5% | "learn more" |
| Naked URL | 0% | Never |

### Writing Good Anchor Text

**Good:** Uses the target keyword naturally in a sentence.
> "For tactical patterns, see our [cold email frameworks](link)."

**Bad:** Forces exact match where it sounds unnatural.
> "Click here to read our cold email templates cold email cold outreach guide."

**Bad:** Generic — signals nothing.
> "For more information, [click here](link)."

### Anchor Text Diversification

Don't link to the same page with the same anchor every time. Vary it. If you have 15 internal links to your "cold email templates" page:
- 8 using variations: "email outreach templates," "cold outreach scripts," "first-email frameworks"
- 4 using exact: "cold email templates"
- 3 using title/branded: "our template library"

This looks natural and covers a wider keyword base.

---

## Finding Linking Opportunities

### Method 1: Keyword Overlap Search (Manual)

When you publish new content, search your site for pages that mention the topic but don't link to the new page.

```
site:yourdomain.com "cold email"
```

Any page that mentions "cold email" and doesn't already link to your cold email guide is a candidate for adding a contextual link.

### Method 2: Screaming Frog Crawl

Crawl your site with Screaming Frog → Bulk Export → Internal links. Then filter:
- Pages with 0 inbound internal links = orphans (fix immediately)
- Pages with 1-2 inbound internal links = at-risk (add more)
- Pages with high outbound links but low inbound = over-givers (these should be receiving, not just giving)

### Method 3: Content Gap Linking

When you audit your content clusters, look for spokes that aren't linked from the hub. The hub should explicitly link to every key spoke page. If it doesn't, the cluster is broken.

---

## Orphan Page Recovery

An orphan page has no internal links pointing to it. It's effectively invisible to Google's link graph.

**Step 1: Find your orphans**
- Run `scripts/sitemap_analyzer.py` to get all indexed URLs
- Cross-reference with your internal link graph (from Screaming Frog or GSC)
- Pages in sitemap but not in internal link graph = candidates

**Step 2: Classify them**

| Type | Action |
|------|--------|
| Valuable content, no home | Find existing relevant pages to add contextual links from; add to relevant hub |
| Landing pages (PPC, events) | These are intentionally unlinked — check if they're accidentally indexed |
| Duplicate / thin content | Consolidate with canonical or noindex |
| Old content no longer relevant | Consider 301 redirect to updated version or 410 |

**Step 3: Fix in priority order**
1. Orphans with inbound external links first (equity is flowing in but going nowhere)
2. Orphans with good content and search potential
3. Orphans with thin content (fix content first, then link)

---

## Internal Link Audit Checklist

Run this quarterly:

- [ ] Every key page is reachable in ≤3 clicks from homepage
- [ ] Pillar/hub pages have links from all their spokes
- [ ] All spoke pages link back to their hub
- [ ] No orphan pages (pages with zero internal inbound links)
- [ ] Homepage links to 5-8 priority sections only
- [ ] Footer links limited to high-value pages (10-15 max)
- [ ] New content published in the last 30 days has at least 3 contextual inbound internal links
- [ ] No broken internal links (404s from internal sources)
- [ ] Anchor text is descriptive, not generic
- [ ] Pages with highest external backlinks are linking to money/conversion pages

---

## Common Patterns That Fail

### The Footer Dump
Putting 80 links in the footer because "they should be accessible." Google gives footer links minimal weight and won't thank you for linking to every blog post from there. Footer = navigation to key sections + legal. That's it.

### The "Related Posts" Widget Approach Only
Auto-generated related posts widgets are fine as supplemental linking, but they don't replace intentional contextual linking. The widget links to "related" content by tag or category — not necessarily to what you actually want to rank. Do the manual work.

### The Nav-Only Money Pages
Feature pages and pricing pages that only appear in the navigation get equity from nav links only. Powerful nav links are sitewide — but adding 5-10 contextual blog links to your pricing page is a significant equity boost. Write one blog post that organically links to pricing. That's real.

### Linking to Pages You Want to Rank for the Wrong Topic
If your /blog/seo-guide has 30 internal links to it but all the anchor text says "our guide" and "learn more," you're not sending a topical signal. The link equity flows in, but Google doesn't know what topic to attribute. Fix anchor text.

### Never Touching Old Posts
Old blog posts accumulate internal links over time because new posts link to them. But they rarely link out to newer, better content. When you publish new content, go back and update old posts to add contextual links to the new piece. This is one of the highest-ROI activities in content SEO.
