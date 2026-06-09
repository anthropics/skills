# Data Gathering Reference

## Core principle
Training data is stale. Every live analysis requires fresh web searches. Do not analyze a stock from memory. Flag loudly if web search is unavailable — the analysis is degraded and the user should know it.

---

## What to pull — in order of priority

### 1. Latest earnings (most recent Q + full year)
- Revenue, YoY growth rate, beat/miss vs. consensus
- Gross margin, operating margin, net margin
- Adjusted EBITDA and EBITDA margin
- Free cash flow and FCF margin
- EPS (GAAP and non-GAAP)
- Forward guidance for next quarter and full year
- **Critical**: Note whether the stock went up or down after the print. A strong beat that triggered a selloff is a market signal worth analyzing.

### 2. Current valuation multiples
- Trailing P/E and Forward P/E
- Price/Sales (trailing and forward)
- EV/EBITDA
- Price/FCF
- PEG ratio (P/E divided by growth rate)
- Compare each to the company's own 5-year median — available on Macrotrends, Wisesheets, or similar
- Compare to 2–3 closest sector peers

### 3. Balance sheet snapshot
- Cash and short-term investments
- Total debt (short-term + long-term)
- Net debt (or net cash)
- Net debt / EBITDA ratio
- Interest coverage ratio
- Operating cash flow trend (3 years)

### 4. Material news (last 6–12 months)
Search for:
- Management changes (CEO, CFO, CTO departures or appointments)
- M&A activity (acquisitions, divestitures, strategic investments)
- Regulatory actions (investigations, fines, antitrust, SEC/DOJ/FTC activity)
- Product launches or discontinuations
- Major customer wins or losses
- Competitor actions that affect the thesis
- Short-seller reports (Hindenburg, Muddy Waters, Citron, Fuzzy Panda, Culper, etc.)

### 5. Analyst sentiment
- Current consensus rating (Strong Buy / Buy / Hold / Sell)
- Price target range (low / median / high)
- Recent upgrades or downgrades and the stated rationale
- Note: Analyst consensus is a lagging indicator. Use it as a reference point, not a conclusion.

### 6. Primary sources — always prioritize over secondary commentary
- Investor Relations page: earnings slides, press releases, SEC filings (10-K, 10-Q, 8-K)
- Earnings call transcripts (Q&A section is most valuable — management hedges in prepared remarks, reveals in Q&A)
- CEO/founder letters, shareholder communications, public blog posts from management
- Short-seller reports if they exist — these are hostile but often forensically detailed

### 7. Competitive landscape
- Most recent earnings from 2–3 direct competitors (for relative performance comparison)
- Any new entrants or adjacent threats announced in the period
- Market share data if available (industry reports, third-party trackers)

---

## Search strategy

**Start broad, then narrow:**
- First search: `[TICKER] earnings [most recent quarter] results`
- Second search: `[Company name] news [current year]`
- Third search: `[Company name] SEC investigation` or `[Company name] short seller`
- Fourth search: `[Company name] competitors [current year]`
- Fifth search: `[Company name] valuation multiples` or check Macrotrends/Finviz directly

**Always fetch the actual article/page when the snippet is insufficient.** Headlines lie. Snippets truncate. Get the full text.

**Prefer original sources:**
- Company IR pages > earnings call transcripts > financial news > analyst aggregators > Reddit/Twitter

---

## What to do with what you find

After gathering data, present a structured summary to the user before starting analysis. Format:

```
**Data summary as of [date]**
Price: $X | 52-week range: $X–$X | Market cap: $XB
Latest earnings: [one sentence summary, beat/miss/guide]
Key news: [2–3 bullet points on most material items]
Major risks flagged: [what came up in the search]
Valuation: [P/E / P/S vs. history in one line]
```

Invite the user to correct anything before proceeding. Wrong assumptions at Stage 1 compound into wrong conclusions at Stage 8.

---

## Red flags to note explicitly

These warrant special attention in the analysis if found:

- Active SEC, DOJ, or FTC investigation
- Short-seller report with specific, falsifiable allegations (not just valuation disagreements)
- Management exodus (CEO + CFO departing within 12 months)
- Guidance cut in the most recent quarter (especially with "macro uncertainty" language)
- Revenue growth rate decelerating faster than consensus expected
- FCF negative while net income is positive (often SBC/working capital games)
- Customer concentration above 20% in a single customer
- Debt covenant risks or upcoming debt maturities without clear refinancing path
- Earnings beat + stock down > 10%: Market is pricing something the headline numbers don't show

---

## If data is unavailable or conflicting

State the gap explicitly. Do not fill data gaps with guesses or stale training data.

Format: `[DATA GAP: Unable to confirm [X] from search results. Proceeding with [Y] from [source] but flagging uncertainty.]`

When sources conflict, use the most recent primary source and note the conflict.
