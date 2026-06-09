# APIClaw Scenarios — Daily Operations

> Load when handling market monitoring, competitor tracking, or anomaly detection.
> For API parameters, see `reference.md`.
>
> **Limitation**: Snapshot data only, no historical comparison. Run periodically and compare manually for continuous monitoring.

---

## 6.1 Market Dynamics Monitoring

```bash
# Step 1: Market overview
python3 scripts/apiclaw.py market --category "Pet Supplies,Dogs" --topn 10

# Step 2: New products in last 90 days
python3 scripts/apiclaw.py products --keyword "dog toys" --listing-age 90 --page-size 20
```

---

## 6.2 Competitor Dynamics

```bash
python3 scripts/apiclaw.py competitors --brand "CompetitorBrand" --sort listingDate
```

---

## 6.3 Top Products Changes

```bash
python3 scripts/apiclaw.py products --category "Pet Supplies,Dogs,Toys" --page-size 20
```

---

## 6.4 Anomaly Alerts

```bash
# Step 1: Market indicators
python3 scripts/apiclaw.py market --category "Pet Supplies,Dogs,Toys" --topn 10

# Step 2: Current top products
python3 scripts/apiclaw.py products --category "Pet Supplies,Dogs,Toys" --page-size 20

# Step 3: High-growth new products (potential threats)
python3 scripts/apiclaw.py products --category "Pet Supplies,Dogs,Toys" --listing-age 90 --growth-min 0.2 --page-size 10
```

**Alert Signal Detection**:

⚠️ API provides snapshot data only (no historical comparison). Detect anomalies by comparing **current values against standard thresholds**, not by tracking changes over time.

| Alert Type | Detection Method | Trigger Condition |
|------------|-----------------|-------------------|
| New blockbuster invasion | Step 3 results | New product (<90 days) already in Top 20 by sales |
| Price war risk | Step 2 price distribution | Multiple top products clustered at same low price point |
| High concentration | Step 1 `topSalesRate` | Currently > 60% (Warning threshold from evaluation criteria) |
| Low new SKU rate | Step 1 `sampleNewSkuRate` | Currently < 5% (market may be frozen) or > 30% (flooding) |

**For continuous monitoring:** Run this workflow periodically (weekly/monthly) and compare results manually across snapshots. The API does not provide historical trend data.

**Output Template**

```markdown
# Anomaly Alert Report - [Category]

## Alert Signals
| Signal | Level | Description |
|--------|-------|-------------|

## Detailed Analysis
[Each alert signal with specific data]

## Recommended Actions
[Response strategy for each alert]
```
