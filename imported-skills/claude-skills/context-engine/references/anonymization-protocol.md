# Anonymization Protocol

Rules for stripping sensitive company data before any external API call, web search, or tool invocation that sends data outside the local environment.

---

## When This Protocol Applies

**Trigger:** Any time company context or conversation content will leave the local session.

Examples:
- Web search that includes company specifics
- External API call with company data in the payload
- Any tool call where conversation content is part of the request

**Does NOT apply to:**
- Local file reads/writes (`~/.claude/company-context.md`)
- In-session reasoning and analysis
- Generating advice or documents that stay local

---

## Rule 1: Financial Figures → Relative Ranges

Never send specific financial data externally.

| Raw data | Anonymized version |
|----------|-------------------|
| "$2.4M ARR" | "early-stage ARR (sub-$5M)" |
| "$180K MRR" | "growing MRR, Series A range" |
| "14 months runway" | "runway is healthy for stage" |
| "burn rate is $320K/month" | "burn rate is moderate for stage" |
| "raised $8M Series A" | "Series A company" |
| "customer LTV is $4,200" | "LTV is above industry average for segment" |
| "CAC is $680" | "CAC is in a sustainable range" |

**Rule:** No dollar amounts. No month counts for runway. Use stage-relative descriptors.

---

## Rule 2: Customer Names → Anonymized Labels

Never send customer or client names externally.

| Raw data | Anonymized version |
|----------|-------------------|
| "Acme Corp is our biggest customer" | "Customer A (largest account)" |
| "we're working with NHS England" | "a large public-sector customer" |
| "BMW, Volkswagen, and Stellantis" | "three major automotive OEMs" |
| "10 enterprise customers including..." | "10 enterprise customers" |

**Rule:** Use "Customer A/B/C" for named accounts, or describe by segment without naming.

---

## Rule 3: Revenue Figures → Percentage Changes or Stage Descriptors

Revenue trajectory is safer than absolute numbers.

| Raw data | Anonymized version |
|----------|-------------------|
| "growing from $1M to $2M ARR" | "2x revenue growth year-over-year" |
| "revenue dropped from $500K to $430K" | "revenue declined ~15% in the period" |
| "hit $10M ARR last quarter" | "crossed a significant ARR milestone" |
| "doing $50K MRR" | "pre-Series A revenue, strong growth trajectory" |

**Rule:** Percentages and directional signals (growing / declining / flat) are safe. Absolutes are not.

---

## Rule 4: Employee Names → Roles Only

Never send individual names externally.

| Raw data | Anonymized version |
|----------|-------------------|
| "Our CTO, Sarah Chen, is struggling" | "our CTO is struggling with the transition" |
| "James is the best performer on the team" | "our strongest performer is in the engineering lead role" |
| "we're about to let go of Michael" | "we're about to make a leadership change" |
| "the founding team is me, Alex, and Priya" | "a three-person founding team" |

**Exception:** Publicly known executives (CEO of a public company, named in press releases) can be referenced by name. If in doubt, use role.

---

## Rule 5: Investor Names → Generic Descriptors

| Raw data | Anonymized version |
|----------|-------------------|
| "Sequoia led our round" | "a top-tier VC led our round" |
| "our lead investor is pushing for an exit" | "pressure from investors toward exit" |
| "Y Combinator alumni" | "accelerator alumni" |

**Exception:** YC, Techstars, and similar well-known accelerators are commonly referenced and safe if the founder has publicly disclosed. When in doubt, omit.

---

## Rule 6: Location → Country or Region

| Raw data | Anonymized version |
|----------|-------------------|
| "Berlin-based startup" | "European startup" |
| "we're in San Francisco" | "US-based startup" |
| "expanding to Munich and Vienna" | "expanding in the DACH region" |

**Exception:** Location is less sensitive than financials. Use judgment — if it's on their website, it's fine.

---

## Anonymization Decision Tree

```
Before sending data externally:

1. Does it include a specific dollar amount?
   → YES: Replace with range or relative descriptor
   
2. Does it include a person's name?
   → YES: Replace with role only (unless publicly known)
   
3. Does it include a company or customer name?
   → YES: Replace with "Customer A" or segment descriptor
   
4. Does it include specific headcount or runway months?
   → YES: Replace with range (1–10, 10–50) or "healthy/tight/critical"
   
5. Does it include proprietary data, roadmap, or unreleased product info?
   → YES: Do not include. Reference only generically ("product expansion planned")
   
6. Is it publicly available information?
   → YES: Safe to send as-is
```

---

## Required vs Optional Anonymization

### Required (always strip before external calls)
- Revenue figures (absolute)
- Burn rate (absolute)
- Runway (specific months)
- Customer names
- Employee names
- Investor names (unless public)
- Funding amounts (unless public)

### Optional (use judgment based on sensitivity)
- Industry vertical (usually fine)
- Company stage (usually fine)
- Team size ranges (usually fine)
- Geographic region (usually fine)
- General challenge category (usually fine)

---

## What to Do If You're Unsure

Default to stricter anonymization. The cost of over-anonymizing is slightly less useful external results. The cost of under-anonymizing is a privacy breach.

When in doubt: **remove it**.

---

## Audit Log (Internal Only)

When running external calls with company context, note internally:
```
[EXTERNAL CALL: {tool/API used}]
[ANONYMIZED: {fields stripped}]
[RETAINED: {fields kept and why}]
```

This is for internal reasoning only — never included in output to the founder.
