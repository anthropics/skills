---
name: bot-traffic-analysis
description: Use when analyzing web access logs or proxy logs that contain bot/crawler traffic alongside human traffic. Triggers: "分析爬虫流量", "bot 分类", "AI 爬虫", "SEO bot", "bot traffic", "crawler analysis", "access log", "user agent classification", "identify bots".
---

# Bot Traffic Analysis Skill

Extends `data-analysis` skill for access log datasets that mix bots, crawlers, and human visitors. Covers classification, disguised-bot detection, and client-facing report structure.

**Prerequisite:** Load and enrich data following `data-analysis` Steps 0–2 first.

---

## Bot Classification

Write a `classify_ua(row)` function with explicit priority ordering (most specific first):

```python
SUSPICIOUS_UA = 'exact UA string of known disguised bot wave'

def classify_ua(row):
    ua = row['ua']
    if pd.isna(ua): return 'human'
    v = str(ua).lower()
    # AI Index (search crawlers that directly affect search recommendations)
    if 'oai-searchbot' in v: return 'ai_index'
    # AI Training (model training crawlers)
    if 'gptbot' in v or 'claudebot' in v or 'anthropic' in v: return 'ai_training'
    if 'amazonbot' in v or 'googleother' in v: return 'ai_training'
    # AI Search (live search crawlers with direct user impact)
    if 'perplexitybot' in v or 'chatgpt-user' in v or 'bytespider' in v: return 'ai_search'
    # SEO Bots (traditional search & SEO tools)
    if 'petalbot' in v or 'bingbot' in v or 'googlebot' in v: return 'seo_bot'
    if 'ahrefs' in v or 'semrush' in v or 'dataforseo' in v: return 'seo_bot'
    # Social Bots
    if 'facebookexternalhit' in v or 'twitterbot' in v: return 'social_bot'
    # Known disguised scraper
    if ua == SUSPICIOUS_UA: return 'disguised_scraper'
    return 'human'
```

**Standard category taxonomy:**

| Category | Examples | Business meaning |
|---|---|---|
| `ai_index` | OAI-SearchBot | Directly entering search recommendation pools (ChatGPT Search) |
| `ai_training` | ClaudeBot, GPTBot, AmazonBot | Content entering AI model training datasets |
| `ai_search` | PerplexityBot, ChatGPT-User | Live AI search with direct user traffic potential |
| `seo_bot` | Bingbot, PetalBot, AhrefsBot | Traditional search engine indexing & SEO tools |
| `social_bot` | FacebookExternalHit | Social platform preview crawlers |
| `disguised_scraper` | Suspicious human-like UAs | Automated scraping misclassified as human |
| `human` | No bot fingerprint | Genuine user visits |

Adapt categories to match your reference classification document if provided.

---

## Disguised Scraper Detection

After initial classification, check for bots masquerading as `human`. Apply as a second `.loc[]` pass:

**Wave 1 — Single UA, high frequency:**
```python
# Same UA string hitting 50+ unique product pages within 1 hour → reclassify
suspect_mask = (
    (df['category'] == 'human') &
    (df['ua'] == SUSPICIOUS_UA) &
    (df['uri'].str.contains('/products/', na=False))
)
df.loc[suspect_mask, 'category'] = 'disguised_scraper'
```

**Wave 2 — Rotating UAs, suspiciously uniform distribution:**

Signals: 200+ visits, hourly distribution σ < 3 across 24h, 95%+ targeting product pages.

```python
hourly = df[df['category'] == 'human'].groupby('hour').size()
if hourly.std() < 3 and len(df[df['category'] == 'human']) > 200:
    # Flag period + host combination for review
    print("WARNING: Suspiciously uniform human traffic — possible disguised scraper wave")
```

When confirmed, reclassify by date range + host + URI pattern using `.loc[]`.

---

## Key Metrics to Report

For each entity (shop / site / property):

| Metric | Formula | Note |
|---|---|---|
| AI-related visits | Count of ai_index + ai_training + ai_search | Exclude seo_bot, human, disguised_scraper from "AI" headline |
| Daily average | Total ÷ observation days | Always use this for cross-entity comparison |
| Category % | Category count ÷ total visits × 100 | Include all categories in denominator |
| SEO Bot breakdown | Value counts by bot name | Shows which search engines are indexing |
| Week-over-week | See `data-analysis` multi-period section | Exclude disguised_scraper and human |

---

## Report Structure (Per Entity)

Each shop / site gets these sections in order:

1. **最重要发现** — Single highlighted callout (green box = positive signal, blue = opportunity, amber = caution). One sentence, max two.

2. **AI 来源与访问量** — Classification table with columns: Bot/Platform, 分类, 访问次数, 日均, 占比, 业务意义. Add a 合计 row. Include methodology block.

3. **AI 流量趋势** — Daily line/bar chart for AI categories only (ai_index + ai_training). Do NOT mix SEO bot or human into this chart. Annotate peaks with explanations.

4. **SEO Bot 分析** — Horizontal bar chart of top SEO bots by name + bullet interpretation per bot. Separate from AI trend.

5. **访问行为（页面分布）** — Stacked bar by URI category (llms.txt / sitemap.xml / 产品页 / 其他), grouped by bot category. Note any anomalous human access patterns (time-of-day clustering, URI targeting).

6. **周维度趋势** — 3-panel chart (① total volume ② daily avg ③ by category). Only for entities with ≥10 days of data.

---

## Methodology Block Template

Include under every metric section in the internal report:

```
统计口径：[what is counted — which categories/filters are included/excluded]
计算方法：[the formula — e.g., 日均 = 总次数 ÷ 11 天；占比 = 各分类次数 ÷ 该店铺总访问次数 × 100%]
注意：[any caveats about data quality, short windows, known anomalies]
```

---

## Multi-Client Report Pattern

When analyzing multiple clients from the same dataset:

- **One combined overview report** — cross-entity comparison table, shared insights, common patterns
- **One individual report per client** — only their data, client-appropriate framing, no competitor references

Both use the same charts (generate per-entity chart files: `06_{slug}_ai_types.png`).

### Client-facing framing rules

| Internal language | Client-facing equivalent |
|---|---|
| "disguised_scraper" | Omit entirely, or mention as "filtered noise" in footnote |
| "ai_training" | "产品信息进入 [Platform] 训练数据" |
| "ai_index" | "产品页正在进入 [Platform] 搜索候选池" |
| Raw bot UA strings | Platform names only (OAI-SearchBot → "OpenAI 搜索爬虫") |
| Absolute visit counts | Lead with business implication, counts as supporting evidence |

---

## Stage Model for AI Discoverability

Use this to frame where each entity currently sits in the AI adoption funnel:

| Stage | Name | Detection signal | Client messaging |
|---|---|---|---|
| 1 | 发现 | llms.txt or sitemap first read by any bot | "已被 AI 系统发现" |
| 2 | 训练收录 | AI training crawlers ≥5 visits cumulative | "产品信息进入 AI 训练数据" |
| 3 | AI 索引 | OAI-SearchBot appears | "进入 ChatGPT 搜索候选池" |
| 4 | 推荐展示 | ChatGPT-User or PerplexityBot click-through | "AI 平台用户直接访问验证" |

Each entity gets a current stage assessment. Makes progress tangible to non-technical clients.

---

## Common Issues

| Problem | Fix |
|---|---|
| "Human" traffic count implausibly high | Check for disguised scrapers (same UA high frequency, uniform hourly σ) |
| AI visit count seems low | Verify UA matching covers all variants (e.g., `anthropic-ai` vs `claudebot`) |
| Cross-entity comparison misleading | Normalize to daily avg — entities may have different observation periods |
| Client confused by bot category names | Map all technical names to platform names in client report |
| Week 2 pct change looks dramatic | Week 2 often has fewer days (4 vs 7) — note sample size in methodology |
