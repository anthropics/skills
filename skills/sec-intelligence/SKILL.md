---
name: sec-intelligence
description: SEC EDGAR research tool. Fetches 10-K, 10-Q, 8-K filings, insider transactions, executive compensation, and ownership disclosures for any US public company. No API key required. Use when researching public companies, insider trading activity, SEC filings, annual reports, quarterly earnings, regulatory disclosures, or financial due diligence. Triggers on phrases like "SEC filing", "10-K", "10-Q", "8-K", "insider trading", "EDGAR", "company filings", "annual report", "quarterly report", "executive compensation".
license: Complete terms in LICENSE.txt
allowed-tools: Bash(python:*) WebFetch
metadata:
  author: Maksim Soltan
  version: 1.0.0
  apis: SEC EDGAR, EDGAR EFTS
  auth: none-required
---

# SEC Intelligence

US public company filings research via SEC EDGAR. Zero auth required — all US regulatory data is public.

## APIs Used

- **EDGAR Company Search**: `https://efts.sec.gov/LATEST/search-index?q=COMPANY&dateRange=custom&startdt=DATE&enddt=DATE&forms=FORM`
- **EDGAR Submissions**: `https://data.sec.gov/submissions/CIK{CIK_PADDED}.json`
- **EDGAR Full-Text Search**: `https://efts.sec.gov/LATEST/search-index?q=TEXT`
- **EDGAR XBRL Facts**: `https://data.sec.gov/api/xbrl/companyfacts/CIK{CIK_PADDED}.json`

Headers required: `User-Agent: money-brain contact@example.com` (EDGAR requires this)

## Workflow

### Step 1: Resolve Company → CIK

```python
scripts/edgar_lookup.py --company "COMPANY NAME" --resolve-cik
```

Or via EDGAR API:
```
GET https://efts.sec.gov/LATEST/search-index?q=%22COMPANY+NAME%22&forms=10-K
```

Extract CIK from results. Pad to 10 digits: `0000320193` for Apple.

### Step 2: Fetch Filings List

```python
scripts/edgar_lookup.py --cik CIK --list-filings --form 10-K
```

API call:
```
GET https://data.sec.gov/submissions/CIK{10-digit-CIK}.json
```

Returns: company metadata + all filings index (form type, date, accession number).

### Step 3: Fetch Specific Filing

For 10-K / 10-Q analysis:
```python
scripts/edgar_lookup.py --cik CIK --form 10-K --latest
```

EDGAR filing URL pattern:
```
https://www.sec.gov/cgi-bin/browse-edgar?action=getcompany&CIK={CIK}&type={FORM}&dateb=&owner=include&count=10
```

### Step 4: Parse Key Sections

From 10-K, extract:
- **Item 1**: Business description
- **Item 1A**: Risk factors
- **Item 7**: MD&A (Management Discussion & Analysis)
- **Item 8**: Financial statements

From 10-Q, extract:
- Revenue/earnings vs prior period
- Any material changes disclosed

From 8-K, extract:
- Event type (earnings, M&A, leadership change, etc.)
- Date
- Summary

From Form 4 (insider transactions):
- Insider name + title
- Transaction type (buy/sell)
- Shares + price
- Date

### Step 5: Generate Intelligence Report

```
## SEC Intelligence: [COMPANY]
CIK: [N] | Ticker: [X] | Industry: [Y]
Data source: SEC EDGAR | [DATE]

### Company Overview
[From 10-K Item 1]

### Recent Filings
| Date | Form | Summary |
|------|------|---------|
| DATE | 10-K | Annual report for FY[YEAR] |
| DATE | 8-K  | [Event description] |

### Financial Highlights (from latest 10-K/10-Q)
- Revenue: $X (YoY: +/-%)
- Net Income: $X
- Key metrics from MD&A

### Insider Activity (Form 4, last 90 days)
| Date | Insider | Role | Action | Shares | Price |
|------|---------|------|--------|--------|-------|

### Risk Factors (top 5 from latest 10-K)
1. [Risk]
2. [Risk]

### Recent 8-K Events
[Material events disclosed]
```

## Key Use Cases

**Due diligence on a company:**
→ Pull latest 10-K + 10-Q + recent 8-Ks + Form 4s

**Insider activity watch:**
→ Form 4 filings (required within 2 days of transaction)

**Earnings research:**
→ 10-Q for quarterly results

**Executive compensation:**
→ DEF 14A (proxy statement)

**Short thesis research:**
→ Risk factors in 10-K + revenue trends in 10-Q

## Error Handling

- CIK not found: try ticker lookup, try alternate company name spelling
- Rate limited: EDGAR asks for polite crawling — add 0.1s delay between requests
- Filing too large to parse fully: focus on key sections (MD&A, risk factors)

## Examples

User: "Pull Apple's latest 10-K"
→ CIK: 0000320193, form: 10-K

User: "Show me insider selling at Tesla"
→ CIK: 0001318605, form: 4, last 90 days

User: "What are Nvidia's risk factors?"
→ CIK: 0001045810, form: 10-K, Item 1A
