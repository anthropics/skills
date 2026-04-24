# APIClaw Scenarios — Product Evaluation

> Load when handling product evaluation, risk assessment, review analysis, or multi-product comparison.
> For API parameters, see `reference.md`.

---

## 4.2 Review Insights

> Trigger: "consumer pain points" / "negative review analysis" / "review insights" / "pain points"

```bash
# Step 1 (primary): AI-powered review analysis — covers ALL reviews
python3 scripts/apiclaw.py analyze --asin B09V3KXJPB --label-type painPoints,issues,positives,improvements

# Step 2 (supplement): Raw review samples for quoting specific examples
python3 scripts/apiclaw.py product --asin B09V3KXJPB
# → Use topReviews for specific review quotes to support analyze findings
```

**Data combination:**
- Use `analyze` `consumerInsights` as primary structured findings (covers ALL reviews)
- Use `realtime/product` `topReviews` for specific quotes to illustrate key pain points
- Use `analyze` `sentimentDistribution` for overall sentiment overview

**Key Information Extracted from analyze + topReviews**:

| Analysis Dimension | Focus Points |
|---------|-------|
| Negative review keywords | broke, defect, quality, returned, disappointed, cheap, flimsy, doesn't work |
| Positive review highlights | easy, great value, love, perfect, amazing, sturdy, well-made, exactly as described |
| Negative review ratio | 1-2 star ratio in ratingBreakdown (> 20% is high risk) |
| Improvement opportunities | Specific problems repeatedly mentioned in negative reviews → Product differentiation direction |

**Output Template**

```markdown
# 💬 [ASIN] Review Insights

## Rating Distribution
| Star Rating | Percentage | Count |
|------|------|------|

## Positive Review Themes
[Extract top 3 positive review themes from topReviews]

## Negative Review Pain Points
[Extract top 3 negative review themes → These are differentiation opportunities]

## Improvement Suggestions
[Product improvement directions based on pain points]
```

---

## 4.3 Multi-Product Comparison

> Trigger: "Which of these products is more worth pursuing" / "compare evaluation" / "compare products"

```bash
# Primary: use competitors for quantitative comparison (sales, price, margins)
python3 scripts/apiclaw.py competitors --keyword "yoga mat" --page-size 20
# Or for specific ASINs:
python3 scripts/apiclaw.py competitors --asin B09XXXXX

# Optional supplement: use realtime/product for qualitative details (reviews, features)
python3 scripts/apiclaw.py product --asin B09XXXXX
```

**⚠️ Important:** Use `competitors` (not `product`) as the primary data source for comparison.
`realtime/product` does NOT return sales, profitMargin, fbaFee, or sellerCount.

**Horizontal Comparison Dimensions**:

| Dimension | Field | Source |
|------|------|------|
| Price | `price` | competitors |
| Monthly Sales | `atLeastMonthlySales` | competitors |
| BSR | `bsrRank` | competitors |
| Rating | `rating` | competitors |
| Review Count | `ratingCount` | competitors |
| Profit Margin | `profitMargin` | competitors |
| Variant Count | `variantCount` | competitors |
| FBA Fee | `fbaFee` | competitors |
| Seller Count | `sellerCount` | competitors |
| Tags | `isBestSeller` / `isAmazonChoice` | competitors |
| A+/Video | `hasAPlus` / `hasVideo` | competitors |
| Review Details | `topReviews` / `ratingBreakdown` | realtime/product (optional) |
| Listing Quality | `features` / `description` | realtime/product (optional) |

---

## 4.4 Risk Assessment

> Trigger: "What are the risks" / "can I do this" / "risk assessment"

```bash
# Step 1: Competitive landscape (primary data: sales, margins, seller count)
python3 scripts/apiclaw.py competitors --keyword "product keyword" --page-size 20
# Step 2: Market context (category-level metrics)
python3 scripts/apiclaw.py market --category "category path" --topn 10
# Step 3 (optional): Review details for the target ASIN
python3 scripts/apiclaw.py product --asin B09XXXXX
# Step 4 (recommended): Review sentiment for risk signal
python3 scripts/apiclaw.py analyze --asin B09XXXXX --label-type issues,painPoints
```

**⚠️ Note:** Step 1 (`competitors`) provides sales, margins, and seller data needed for risk scoring.
Step 3 (`product`) only adds review details and listing content — do NOT expect sales/profitMargin from it.
Step 4 (`analyze`) provides AI-analyzed sentiment distribution and structured issues for risk assessment.

**Six-Dimensional Risk Assessment Matrix**:

| Risk Dimension | Data Source | 🟢 Low Risk | 🟡 Medium Risk | 🔴 High Risk |
|---------|---------|---------|---------|---------|
| Competition Intensity | topSalesRate | < 40% | 40-60% | > 60% |
| Review Barrier | Top avg ratingCount | < 200 | 200-1000 | > 1000 |
| Brand Barrier/Moat | topBrandSalesRate | < 30% | 30-50% | > 50% |
| Price War Risk | Top price variance | High variance | Medium | Low variance |
| Compliance Risk | categories | Regular | Requires certification | High-risk |
| Review Sentiment | sentimentDistribution (negative) | < 15% | 15-30% | > 30% |
| Seasonality | AI judgment | Year-round | Seasonal fluctuation | Strong seasonality |

**High-risk Category Compliance Alerts**:

| Category | Compliance Requirements |
|------|---------|
| Health/Supplements | FDA compliance |
| Children's Products | CPSC certification (CPSIA) |
| Electronics | FCC certification |
| Food | FDA registration |
| Cosmetics | FDA compliance |
| Toys | ASTM F963 |

**Output Template**

```markdown
# ⚠️ [ASIN/Category] Risk Assessment Report

## Risk Matrix
| Risk Dimension | Risk Level | Description |
|---------|---------|------|

## Overall Risk Level: 🟢/🟡/🔴
[Analysis and recommendations]
```

---

## 4.5 Sales Estimation

> Trigger: "How much monthly sales does this product have" / "sales forecast" / "estimate sales"

```bash
python3 scripts/apiclaw.py competitors --asin B09XXXXX
# → Get bsrRank and atLeastMonthlySales
```

**Three Estimation Methods**:

| Method | Formula/Logic | Accuracy |
|-----|---------|------|
| API Direct Return | `atLeastMonthlySales` field | ⭐⭐⭐⭐ Most accurate (lower bound) |
| BSR Rough Estimate | Monthly sales ≈ 300,000 / BSR^0.65 | ⭐⭐ Rough |
| Review Reverse Calculation | Monthly sales ≈ reviewMonthlyNew / Review rate(1-3%) | ⭐⭐ Reference only |

**Usage Priority**: atLeastMonthlySales → BSR estimate → Review reverse calculation

**Note**: `atLeastMonthlySales` is a lower bound — Amazon shows "10,000+ bought in past month", so actual sales may be higher. Current API has no historical trends, only current snapshot.

---

## 4.6 Category Consumer Insights

> Trigger: "category pain points" / "what do users want" / "consumer portrait" / "category user analysis" / "who is buying"

```bash
python3 scripts/apiclaw.py analyze --category "Pet Supplies,Dogs,Toys" --period 90d
```

**Use case:** Understand the consumer landscape of a category **before** product selection. Not about specific ASINs, but about what users in this category care about, complain about, and value.

**Key dimensions to analyze:**

| Dimension | labelType | Insight |
|-----------|-----------|---------|
| Who is buying | `userProfiles` | Target audience definition |
| What they want | `buyingFactors` | Key purchase decision drivers |
| Where/when they use it | `usageLocations`, `usageTimes` | Scene-based marketing angles |
| What they hate | `painPoints` | Differentiation opportunities |
| What they love | `positives` | Table-stakes features |
| How to improve | `improvements` | Product development direction |

**Output Template**

```markdown
# 👥 [Category] Consumer Insights

## Overview
| Metric | Value |
|--------|-------|
| Reviews Analyzed | [totalReviews] |
| Avg Rating | [avgRating] |
| Verified Purchase Ratio | [verifiedRatio] |
| Sentiment | 👍 [positive]% / 😐 [neutral]% / 👎 [negative]% |

## User Profiles
[From userProfiles dimension — who is buying]

## Top Pain Points
| # | Pain Point | Mention % | Avg Rating |
|---|-----------|-----------|------------|
[From painPoints dimension]

## Buying Decision Factors
| # | Factor | Mention % |
|---|--------|-----------|
[From buyingFactors dimension]

## Usage Scenarios
[From scenarios dimension]

## Product Opportunity Signals
[Cross-reference painPoints + positives → gaps = opportunities]
```

---

## Flow Guidance

| Current Conclusion | Next Step | Load File |
|-------------------|-----------|-----------|
| Want to understand users first | → Category insights | This file → 4.6 |
| Pain points identified | → Product selection | SKILL.md → products |
| Product selected, need risk check | → Risk assessment | This file → 4.4 |
| Need competitive analysis | → Competitor comparison | This file → 4.3 |
