---
name: company-investigator
description: Comprehensive company research from public sources. Combines SEC filings, financial data, news coverage, job postings, and GitHub activity into investment-grade due diligence briefs. Use when researching a company, doing due diligence, analyzing competitors, checking a company before investing or joining, or building company intelligence. Triggers on phrases like "research company", "due diligence on", "company analysis", "is this company a good investment", "competitor analysis", "tell me about this company".
license: Complete terms in LICENSE.txt
allowed-tools: Bash(python:*) WebFetch
metadata:
  author: Maksim Soltan
  version: 1.0.0
  apis: SEC EDGAR, Yahoo Finance, NewsAPI, GitHub, Hacker News
  auth: newsapi-key-optional
---

# Company Investigator

Investment-grade company research assembled from public sources. Cross-signal intelligence: financials vs. news vs. hiring vs. code activity.

## APIs Used

**No auth:**
- **SEC EDGAR**: Filings, financials for public companies
- **Yahoo Finance (unofficial)**: Stock data, fundamentals
- **GitHub**: Repository activity, contributor counts (if tech company)
- **Hacker News**: Community mentions, sentiment
- **Adzuna**: Job postings (UK-heavy but global)

**Optional API key:**
- **NewsAPI**: `$NEWSAPI_KEY` — recent news coverage

## Workflow

### Step 1: Company Type Detection

Determine:
- Public (NYSE/NASDAQ) → EDGAR + Yahoo Finance
- Private → skip financials, focus news + jobs + GitHub
- Tech → add GitHub analysis
- Location (US, UK, global) → adjust data sources

### Step 2: Parallel Fetch

```python
scripts/company_fetch.py --company "Tesla" --ticker TSLA
```

**Public company financials:**
```python
# SEC EDGAR CIK lookup + submissions
scripts/edgar_lookup.py --company "Tesla" --resolve-cik
scripts/edgar_lookup.py --cik {CIK} --financials
scripts/edgar_lookup.py --cik {CIK} --list-filings --form 10-K --latest
```

**Stock data (Yahoo Finance):**
```
GET https://query1.finance.yahoo.com/v8/finance/chart/{TICKER}?interval=1d&range=90d
```

**News coverage:**
```
GET https://newsapi.org/v2/everything?q={COMPANY}&sortBy=publishedAt&pageSize=10&apiKey={KEY}
```
Fallback (no key): Hacker News search
```
GET https://hn.algolia.com/api/v1/search?query={COMPANY}&tags=story&hitsPerPage=10
```

**GitHub (for tech companies):**
```
GET https://api.github.com/search/repositories?q={COMPANY}+in:name&sort=stars&per_page=10
GET https://api.github.com/orgs/{ORG_NAME}
```

**Job postings (growth signal):**
```
GET https://api.adzuna.com/v1/api/jobs/us/search/1?app_id={ID}&app_key={KEY}&what={COMPANY}&results_per_page=20
```
Fallback: search LinkedIn/Indeed manually noted in output

### Step 3: Signal Synthesis

**Growth signals:**
- Job postings up YoY → expanding
- GitHub commits/contributors increasing → active engineering
- New office mentions in news → growth
- Large funding rounds → runway

**Risk signals:**
- Mass layoffs in news
- SEC enforcement actions
- Insider selling (Form 4)
- Revenue declining in 10-Q
- Key exec departures (8-K)
- Job postings in decline

**Contradiction detection:**
- Stock up but insider selling → distribution?
- Positive PR but layoffs → narrative management?
- Revenue growth but cash burn → unit economics problem?

### Step 4: Generate Brief

```
## Company Intelligence: [COMPANY]
Type: [Public/Private] | Ticker: [X] | Industry: [X]
Date: [DATE]

### At a Glance
[3-4 sentence summary: what they do, current state, key fact]

### Financial Snapshot (public companies)
| Metric | Value | YoY |
|--------|-------|-----|
| Revenue | $X | +X% |
| Net Income | $X | +X% |
| Market Cap | $X | |
| P/E Ratio | X | |
| Stock 90d | +X% | |

### Recent News (last 30 days)
- [Headline] — [Source], [Date]

### Hiring Signals
- Open roles: [N] (growth indicator)
- Hiring in: [Engineering/Sales/Marketing — shows strategic focus]

### GitHub Activity (tech companies)
- Top repos: [N stars, N forks]
- Recent activity: [commits/week]

### SEC/Regulatory (public companies)
- Latest 10-K: [date, key findings]
- Recent 8-Ks: [material events]
- Insider activity: [net buy/sell]

### Contradictions & Risks
[What signals conflict with each other]

### Verdict
[1 paragraph synthesis: opportunity / caution / avoid]
```

## Error Handling

- Private company → EDGAR unavailable, note and skip
- Yahoo Finance blocked → note, provide last known data
- News API no key → use HN only, note limitation
- GitHub org not found → skip GitHub section

## Examples

User: "Research Anthropic"
→ Private company, no EDGAR → news + HN + GitHub + job postings

User: "Due diligence on NVDA before buying"
→ EDGAR (CIK 1045810) + Yahoo Finance + news + insider activity

User: "Tell me about OpenAI"
→ Private, focus on news + HN community signals + GitHub (microsoft org for Azure OpenAI) + job postings

User: "Analyze Tesla vs Rivian"
→ Run both in parallel, compare signal matrices
