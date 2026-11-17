# APIClaw API Reference

> Load this file only when you need exact field names, filter parameters, or response structure details.
> For most tasks, the SKILL.md quick reference is sufficient.
>
> **OpenAPI Spec (live)**: https://apiclaw.io/api/v1/openapi-spec

---

## Endpoints

| # | Endpoint | Purpose |
|---|----------|---------|
| 1 | `categories` | Category tree lookup |
| 2 | `markets/search` | Market-level aggregate metrics |
| 3 | `products/competitor-lookup` | Competitor discovery |
| 4 | `products/search` | Product selection with filters |
| 5 | `realtime/product` | Live single-ASIN detail |
| 6 | `reviews/analyze` | AI review analysis (sentiment + insights) |

Base URL: `https://api.apiclaw.io/openapi/v2`
Auth: `Bearer $APICLAW_API_KEY`
Method: All POST with JSON body

---

## 1. categories

Query modes (mutually exclusive):
- No params → root categories
- `categoryKeyword` → keyword search
- `categoryPath` → exact path lookup
- `parentCategoryPath` → child categories

Response fields: `categoryId`, `categoryName`, `categoryPath`, `hasChildren`, `isRoot`, `level`, `productCount`, `link`

---

## 2. markets/search

### Core parameters

| Parameter | Type | Note |
|-----------|------|------|
| categoryPath | List\<String\> | e.g. `["Pet Supplies", "Dogs"]` |
| categoryKeyword | String | keyword match across all levels |
| topN | **String** | `"3"` / `"5"` / `"10"` / `"20"` — must be string, not integer |
| newProductPeriod | **String** | `"1"` / `"3"` / `"6"` / `"12"` — must be string |
| sampleType | String | `by_sale_100` / `by_bsr_100` / `avg` |
| dateRange | String | default `30d` |
| pageSize | Integer | default 20 |
| sortBy | String | default `sampleAvgMonthlySaleAmt` |
| sortOrder | String | `asc` / `desc` |

### Filter parameters (all Min/Max pairs, optional)

| Filter pair | Meaning |
|-------------|---------|
| sampleAvgMonthlySalesMin/Max | Avg monthly unit sales |
| sampleAvgMonthlyRevenueMin/Max | Avg monthly revenue |
| sampleAvgPriceMin/Max | Avg price |
| sampleAvgBsrMin/Max | Avg BSR |
| sampleAvgRatingMin/Max | Avg rating |
| sampleAvgReviewCountMin/Max | Avg review count |
| sampleAvgGrossMarginMin/Max | Avg gross margin |
| totalSkuCountMin/Max | Total SKU count |
| sampleSkuCountMin/Max | Sample SKU count |
| topAvgMonthlySalesMin/Max | Top N avg monthly sales |
| topAvgMonthlyRevenueMin/Max | Top N avg monthly revenue |
| topSalesRateMin/Max | Product concentration (Top N sales / total) |
| topBrandSalesRateMin/Max | Brand concentration |
| topSellerSalesRateMin/Max | Seller concentration |
| sampleBrandCountMin/Max | Brand count |
| sampleSellerCountMin/Max | Seller count |
| sampleFbaRateMin/Max | FBA rate |
| sampleAmzRateMin/Max | Amazon direct rate |
| sampleNewSkuCountMin/Max | New SKU count |
| sampleNewSkuRateMin/Max | New SKU rate |

### Key response fields

| Field | Meaning |
|-------|---------|
| categories | Category path array |
| totalSkuCount | Active SKUs in category |
| sampleAvgPrice | Average price (USD) |
| sampleAvgMonthlySales | Average monthly units per product |
| sampleAvgMonthlyRevenue | Average monthly revenue per product |
| sampleAvgRating | Average rating |
| sampleAvgReviewCount | Average reviews |
| sampleBrandCount | Number of brands |
| sampleSellerCount | Number of sellers |
| sampleFbaRate | FBA ratio (decimal) |
| sampleNewSkuRate | New product ratio |
| **topSalesRate** | **Product concentration** — Top N share of total sales |
| **topBrandSalesRate** | **Brand concentration** — Top N brands' share |
| **topSellerSalesRate** | **Seller concentration** — Top N sellers' share |

### sortBy values

`totalSkuCnt`, `sampleSkuCnt`, `sampleAvgPrice`, `sampleAvgMonthlySaleCnt`, `sampleAvgMonthlySaleAmt`, `sampleAvgBigCategoryBsr`, `sampleAvgRatingAmt`, `sampleAvgRatingCnt`, `sampleAvgGrossMarginRate`, `sampleBrandCnt`, `sampleSellerCnt`, `sampleFbaSkuRate`, `sampleNewSkuRate`, `topAvgMonthlySaleCnt`, `topAvgMonthlySaleAmt`, `topSaleCntRate`, `topBrandSaleCntRate`, `topSellerSaleCntRate`

---

## 3. products/competitor-lookup

| Parameter | Type | Note |
|-----------|------|------|
| keyword | String | Search keyword |
| brand | String | Brand filter |
| seller | String | Seller filter |
| asin | String | ASIN filter |
| categoryPath | List\<String\> | Category filter |
| sortBy | String | `atLeastMonthlySales` / `atLeastMonthlyRevenue` / `bsr` / `price` / `rating` / `reviewCount` / `listingDate` |
| sortOrder | String | `asc` / `desc` |
| pageSize | Integer | default 20 |

Response: List of Product objects (see shared fields below).

---

## 4. products/search

### Core parameters

Same as competitor-lookup plus:

| Parameter | Type | Note |
|-----------|------|------|
| mode | String | Search mode |
| onlyCategoryRank | Boolean | Category-only ranking |
| keywordMatchType | String | `fuzzy` / `phrase` / `exact` |

### Filter parameters (all Min/Max pairs, optional)

| Filter pair | Meaning |
|-------------|---------|
| monthlySalesMin/Max | Monthly unit sales |
| revenueMin/Max | Monthly revenue |
| childSalesMin/Max | Child ASIN sales |
| salesGrowthRateMin/Max | Sales growth rate |
| bsrMin/Max | BSR range |
| subBsrMin/Max | Sub-category BSR |
| bsrGrowthRateMin/Max | BSR growth rate |
| priceMin/Max | Price range |
| ratingMin/Max | Rating range |
| reviewCountMin/Max | Review count range |
| fbaShippingMin/Max | FBA shipping cost |
| variantCountMin/Max | Variant count |
| qaCountMin/Max | Q&A count |
| monthlyNewReviewsMin/Max | Monthly new reviews |
| reviewRateMin/Max | Review rate |
| grossMarginMin/Max | Gross margin |
| lqsMin/Max | Listing quality score |
| sellerCountMin/Max | Seller count |

### Additional filters

| Parameter | Type | Note |
|-----------|------|------|
| listingAge | **String** | Max listing age in days |
| includeBrands | String | Comma-separated brand names to include |
| excludeBrands | String | Comma-separated brand names to exclude |
| includeSellers | String | Comma-separated seller names |
| excludeSellers | String | Comma-separated seller names |
| fulfillment | List\<String\> | `["FBA"]`, `["FBM"]` |
| badges | List\<String\> | `["New Release"]`, `["Best Seller"]` |
| excludeKeywords | String | Keywords to exclude |
| videoFilter | String | Video filter |

---

## 5. realtime/product

| Parameter | Required | Note |
|-----------|----------|------|
| asin | **Yes** | Product ASIN |
| marketplace | No | `US`/`UK`/`DE`/`FR`/`IT`/`ES`/`JP`/`CA`/`AU`/`IN`/`MX`/`BR` (default: US) |

### Response fields

| Field | Meaning |
|-------|---------|
| asin, title, brand | Basic product info |
| rating, ratingCount | Rating data |
| ratingBreakdown | Star distribution: `{five_star: {percentage, count}, ...}` |
| features | Bullet points (list of strings) |
| description | Product description |
| specifications | Key-value tech specs |
| categories | Category path |
| variants | Variant list with dimensions |
| topReviews | Top reviews with title, body, rating, date, helpful_votes |
| bestsellersRank | BSR info: `[{category, rank}, ...]` |
| buyboxWinner | Buy Box: price, fulfillment, seller |
| images | All image URLs |
| dimensions, weight | Physical attributes |

---

## 6. reviews/analyze

AI-powered review analysis. Returns sentiment, rating distribution, and structured consumer insights.
Requires at least 50 reviews for meaningful analysis.

### Request parameters

| Parameter | Type | Required | Note |
|-----------|------|----------|------|
| mode | String | **Yes** | `asin` or `category` |
| asins | List\<String\> | When mode=asin | Max 100 ASINs |
| categoryPath | String | When mode=category | Category path |
| labelType | String | No | Filter to specific dimension. Omit for all |
| period | String | No | Analysis time range (e.g. `90d`) |

### labelType values

`scenarios`, `issues`, `positives`, `improvements`, `buyingFactors`, `painPoints`, `keywords`, `userProfiles`, `usageTimes`, `usageLocations`, `behaviors`

### Response fields

| Field | Type | Meaning |
|-------|------|---------|
| queryMode | String | `asin` or `category` |
| asins | List | ASINs analyzed |
| category | String | Category analyzed |
| totalReviews | Integer | Total reviews analyzed |
| avgRating | Float | Average rating |
| verifiedRatio | Float | Verified purchase ratio (decimal) |
| dateRangeStart | Date | Analysis start date |
| dateRangeEnd | Date | Analysis end date |
| ratingDistribution | Object | `{"1": count, "2": count, ..., "5": count}` |
| sentimentDistribution | Object | `{"positive": ratio, "neutral": ratio, "negative": ratio}` |
| consumerInsights | List\<InsightItem\> | Structured insights by dimension |
| topKeywords | List\<InsightItem\> | Top keywords with counts |

### InsightItem fields

| Field | Type | Meaning |
|-------|------|---------|
| element | String | Insight text |
| labelType | String | Dimension (e.g. `painPoints`) |
| count | Integer | Occurrence count |
| reviewPercentage | Float | % of reviews mentioning this |
| avgRating | Float | Avg rating for reviews with this element |

---

## Shared Product Object (competitor-lookup & products/search)

### Core fields

| Field | Type | Meaning |
|-------|------|---------|
| asin | String | ASIN |
| parentAsin | String | Parent ASIN |
| title | String | Product title |
| brand | String | Brand |
| price | Float | Price (USD) |
| listingDate | String | Listing date |
| fulfillment | String | FBA/FBM/AMZ |
| categories | List | Category path |

### Sales fields

| Field | Type | Meaning |
|-------|------|---------|
| atLeastMonthlySales | Integer | Estimated monthly sales (lower bound, actual may be higher) |
| salesRevenue | Float | Monthly revenue |
| salesGrowthRate | Float | Sales growth rate |
| childSalesMonthly | Integer | Child ASIN monthly sales |
| bsrRank | Integer | BSR rank |
| bsrGrowthRate | Float | BSR growth rate |
| subBsrRank | Integer | Sub-category BSR |

### Review & quality

| Field | Type | Meaning |
|-------|------|---------|
| rating | Float | Rating (0-5) |
| ratingCount | Integer | Total ratings |
| reviewMonthlyNew | Integer | Monthly new reviews |
| isBestSeller | Boolean | Best Seller badge |
| isAmazonChoice | Boolean | Amazon's Choice badge |
| hasAPlus | Boolean | A+ content |
| hasVideo | Boolean | Has video |
| lqs | Float | Listing quality score |

### Commercial fields

| Field | Type | Meaning |
|-------|------|---------|
| fbaFee | Float | FBA fee |
| profitMargin | Float | Profit margin |
| sellerCount | Integer | Number of sellers |
| buyboxSeller | String | Buy Box winner |
| sellerLocation | String | Seller location |
| variantCount | Integer | Number of variants |

---

## Scoring Criteria

### Market evaluation thresholds

| Metric | Source | Good | Medium | Warning |
|--------|--------|------|--------|---------|
| Monthly market value | sampleAvgMonthlyRevenue × sampleSkuCount | > $10M | $5M–$10M | < $5M |
| Product concentration | topSalesRate (topN=10) | < 40% | 40–60% | > 60% |
| New SKU rate | sampleNewSkuRate | > 15% | 5–15% | < 5% |
| FBA rate | sampleFbaRate | > 50% | 30–50% | < 30% |
| Brand count | sampleBrandCount | > 50 | 20–50 | < 20 |

### Product evaluation thresholds

| Metric | Source | High potential | Medium | Low potential |
|--------|--------|---------------|--------|---------------|
| BSR rank | bestsellersRank | Top 1000 | 1000–5000 | > 5000 |
| Review count | reviewCount | < 200 | 200–1000 | > 1000 |
| Rating | rating | > 4.3 | 4.0–4.3 | < 4.0 |
| Negative review % | ratingBreakdown (1+2 star) | < 10% | 10–20% | > 20% |

### BSR to sales estimation

When `atLeastMonthlySales` is null, estimate: **Monthly sales ≈ 300,000 / BSR^0.65**

---

## Common response structure

```json
{
  "success": true,
  "data": { ... },
  "error": { "code": "...", "message": "..." },
  "meta": {
    "requestId": "...",
    "timestamp": "...",
    "total": 100,
    "page": 1,
    "pageSize": 20,
    "totalPages": 5
  }
}
```

---

## Known quirks

1. `topN` and `newProductPeriod` are **strings** — use `"10"` not `10`
2. `listingAge` is a **string** — use `"180"` not `180`
3. All parameters are flat (top-level), no nested objects
4. Database endpoints mainly support US; `realtime/product` supports 12 marketplaces
5. Rate limit: 100 req/min, 10 req/sec burst
6. Concentration = Top N sales / sample total sales (topN value matters)

> The `scripts/apiclaw.py` script handles all these quirks automatically.
