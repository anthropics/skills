# APIClaw Scenarios — Listing Optimization

> Load when handling listing writing, bullet points optimization, or product page content creation.
> For API parameters, see `reference.md`.
>
> **Data source:** `realtime/product` provides features, description, topReviews, ratingBreakdown.
> `competitors`/`products` provides sales, pricing, and competitive data.
> Combine both for data-driven listing creation.

---

## 8.1 Competitive Listing Analysis

> Trigger: "analyze competitor listing" / "their selling points" / "listing comparison" / "what are they saying"

```bash
# Step 1: Pull 2-3 top competitor ASINs for listing content
python3 scripts/apiclaw.py product --asin B09XXXXX
python3 scripts/apiclaw.py product --asin B08YYYYY
python3 scripts/apiclaw.py product --asin B07ZZZZZ

# Step 2: AI review analysis across all competitors (one call)
python3 scripts/apiclaw.py analyze --asins B09XXXXX,B08YYYYY,B07ZZZZZ --label-type positives,painPoints,buyingFactors
```

**Data source priority:** Use `analyze` consumerInsights for structured findings (covers ALL reviews). Use `realtime/product` features/topReviews for specific listing copy examples and quotes.

**Extract from each ASIN:**

| Data Point | Field | What to Analyze |
|------------|-------|-----------------|
| Bullet Points | `features` | Common selling points across competitors |
| Negative Reviews | `topReviews` (1-2★) | Pain points = differentiation opportunities |
| Star Distribution | `ratingBreakdown` | High 1★% = product flaw to avoid/solve |
| Product Specs | `specifications` | Feature gaps competitors miss |
| Image Count | `images` | Benchmark for visual content |

**Analysis Framework:**

1. **Shared selling points** — What do ALL competitors emphasize? (These are table stakes, must include)
2. **Pain point mining** — What do negative reviews complain about? (These are your differentiation angle)
3. **White space** — What does NO competitor mention? (These are untapped positioning opportunities)
4. **AI-validated insights** — What does `analyze` confirm as top buying factors and pain points across all competitors? (data-driven, not manual impression)

**Output Template**

```markdown
# 🔍 Competitive Listing Analysis — [Category/Product]

## Competitor Overview
| # | ASIN | Brand | Rating | Reviews | Bullet Points Count | Has A+ | Has Video |
|---|------|-------|--------|---------|---------------------|--------|-----------|

## Selling Points Matrix
| Selling Point | Competitor A | Competitor B | Competitor C | Frequency |
|---------------|:---:|:---:|:---:|-----------|
| [e.g. Waterproof] | ✅ | ✅ | ❌ | 2/3 |

## Top 5 Negative Review Pain Points
| # | Pain Point | Frequency | Opportunity |
|---|-----------|-----------|-------------|

## Differentiation Opportunities
[Specific angles competitors miss + evidence from reviews]
```

---

## 8.2 Listing Copy Generation

> Trigger: "write listing" / "generate bullet points" / "write title" / "listing optimization" / "help me write product page"

```bash
# Step 1: Pull top 3 competitors for reference
python3 scripts/apiclaw.py product --asin B09XXXXX
python3 scripts/apiclaw.py product --asin B08YYYYY
python3 scripts/apiclaw.py product --asin B07ZZZZZ

# Step 2: Get category competitive data
python3 scripts/apiclaw.py competitors --keyword "product keyword" --page-size 20

# Step 3: Consumer insights for data-driven copy
python3 scripts/apiclaw.py analyze --asins B09XXXXX,B08YYYYY,B07ZZZZZ --label-type buyingFactors,scenarios,userProfiles
```

**⚠️ Important:** Use `realtime/product` for listing content (features, reviews). Use `competitors` for market positioning data (price range, review counts). Use `analyze` for consumer-driven copy direction (buying factors, scenarios, user profiles). Do NOT expect sales data from realtime/product.

**Before generating, ask the user for:**

| Info Needed | Why |
|-------------|-----|
| Product name & key features | Core content |
| Target price point | Positioning |
| Key differentiators vs competitors | Unique selling angles |
| Target customer | Tone and language |
| Brand name (if any) | Title prefix |

**Generation Rules:**

### Title (max 200 characters)
- Format: `[Brand] + [Core Product] + [Top 2-3 Features] + [Use Case/Audience]`
- Front-load the highest-search-volume keyword
- Example: `BRANDX Wireless Earbuds — 40H Battery, ANC Noise Cancelling, IPX7 Waterproof — for Running & Gym`

### Bullet Points (5 total)
- Each bullet: **[BENEFIT IN CAPS]** — Supporting detail with keyword
- Bullet 1: Primary differentiator (what you do better than competitors)
- Bullet 2: Key feature addressing top pain point from reviews
- Bullet 3-4: Important features (table stakes)
- Bullet 5: Trust builder (warranty, compatibility, what's in the box)
- Embed 1-2 search keywords naturally per bullet
- Use `buyingFactors` from analyze to prioritize which benefits to lead with
- Use `scenarios` from analyze to craft the product description opening
- Use `userProfiles` to match tone and language to target audience

### Product Description
- Opening: Problem or scenario the customer relates to
- Middle: How this product solves it (features → benefits)
- Close: Brand story or trust statement
- Length: 1000-2000 characters

### Backend Search Terms (5 lines, each <500 chars)
- Line 1: Primary keyword variations
- Line 2: Synonym keywords
- Line 3: Use case keywords
- Line 4: Compatible product keywords
- Line 5: Misspellings and alternate terms
- Do NOT repeat words already in title/bullets

**Output Template**

```markdown
# ✍️ Listing Copy — [Product Name]

## Title
[Generated title]

## Bullet Points
• **[BENEFIT 1]** — [Detail]
• **[BENEFIT 2]** — [Detail]
• **[BENEFIT 3]** — [Detail]
• **[BENEFIT 4]** — [Detail]
• **[BENEFIT 5]** — [Detail]

## Product Description
[Generated description]

## Backend Search Terms
1. [Line 1]
2. [Line 2]
3. [Line 3]
4. [Line 4]
5. [Line 5]

---
**Based on:** [X] competitor listings analyzed, [Y] reviews mined
**Key differentiation angle:** [What makes this listing unique]
```

---

## 8.3 Listing Optimization Diagnosis

> Trigger: "optimize my listing" / "what's wrong with my listing" / "listing diagnosis" / "improve my listing"

```bash
# Step 1: Pull user's own ASIN
python3 scripts/apiclaw.py product --asin B09XXXXX

# Step 2: Pull top 3 competitors in same category
python3 scripts/apiclaw.py competitors --keyword "product keyword" --page-size 10
# Then pull realtime detail for top 3
python3 scripts/apiclaw.py product --asin [competitor1]
python3 scripts/apiclaw.py product --asin [competitor2]
python3 scripts/apiclaw.py product --asin [competitor3]

# Step 3: Review-based competitive intelligence
python3 scripts/apiclaw.py analyze --asins B09XXXXX,[competitor1],[competitor2] --label-type positives,painPoints
```

**⚠️ Note:** `realtime/product` provides listing content for diagnosis. `competitors` provides competitive benchmarks (sales, reviews, price). `analyze` provides AI-analyzed consumer insights across your ASIN and competitors. All three are needed for a thorough diagnosis.

**Diagnosis Scorecard:**

| Dimension | Check | Scoring |
|-----------|-------|---------|
| Title | Length, keyword placement, readability | 🟢 >150 chars with keywords / 🟡 100-150 / 🔴 <100 or keyword-stuffed |
| Bullet Points | Count, structure, keyword density | 🟢 5 bullets, benefit-led / 🟡 3-4 bullets / 🔴 <3 or feature-only |
| Images | Count from `images` field | 🟢 7+ images / 🟡 4-6 / 🔴 <4 |
| A+ Content | `hasAPlus` from competitors data | 🟢 Has A+ / 🔴 No A+ (competitors have it) |
| Video | `hasVideo` from competitors data | 🟢 Has video / 🟡 No video but competitors don't either / 🔴 No video but competitors do |
| Reviews | `ratingCount` vs competitor avg | 🟢 Above avg / 🟡 50-100% of avg / 🔴 Below 50% |
| Rating | `rating` vs category avg | 🟢 >4.3 / 🟡 4.0-4.3 / 🔴 <4.0 |
| Negative Review % | `ratingBreakdown` 1+2 star | 🟢 <10% / 🟡 10-20% / 🔴 >20% |
| Pain Point Coverage | analyze painPoints vs your bullets | 🟢 Addresses top 3 / 🟡 Addresses 1-2 / 🔴 Ignores top pain points |

**Output Template**

```markdown
# 🏥 Listing Diagnosis — [ASIN]

## Overall Score: [X/10]

## Scorecard
| Dimension | Your ASIN | Top Competitor | Score | Action |
|-----------|-----------|----------------|-------|--------|
| Title | [length, keywords] | [benchmark] | 🟢/🟡/🔴 | [Fix] |
| Bullet Points | [count, style] | [benchmark] | 🟢/🟡/🔴 | [Fix] |
| Images | [count] | [avg count] | 🟢/🟡/🔴 | [Fix] |
| ... | ... | ... | ... | ... |

## Priority Fixes (Top 3)
1. [Most impactful fix with specific suggestion]
2. [Second fix]
3. [Third fix]

## Rewritten Listing (Optional)
[If score < 6/10, offer to rewrite — see 8.2]
```

---

## Flow Guidance

| Current Conclusion | Next Step | Load File |
|-------------------|-----------|-----------|
| Listing generated | → Monitor performance | `scenarios-ops.md` |
| Diagnosis score low | → Rewrite listing | This file → 8.2 |
| Need competitive data first | → Competitor analysis | `scenarios-eval.md` → 4.3 |
| Need product selection first | → Find products | SKILL.md → products |
