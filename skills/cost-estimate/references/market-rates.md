# Market rates (Step 6)

Use WebSearch for current-year rates. Rotate queries; adapt to the detected stack.

## Queries

- `"senior [primary_language] developer hourly rate"`
- `"senior [framework] contractor rate [United States / EU / India]"`
- `"[specialist_domain] developer freelance rate"`
- `"software engineer hourly rate [city]"` (regional anchor)

Collect 3 – 5 data points. Report regionally.

## Report table

| Region | Low | Avg | High | Notes |
|---|---|---|---|---|
| Remote (global) | | | | LATAM, Eastern Europe, SE Asia |
| Remote (US) | | | | Mid-tier US markets |
| SF/NYC onsite | | | | Premium markets |
| Specialist (e.g. Rust, CUDA, Solidity) | | | | Niche premium |

## Fallback anchors

If WebSearch is unavailable or returns obvious rot, use these anchors and state "rates from skill defaults, not live search":

- Generalist senior: **$75 – $150/hr** (US remote), **$150 – $250/hr** (SF/NYC), **$35 – $75/hr** (offshore)
- Specialist (Rust, ML infra, GPU, crypto): **+30 – 50%**

## Pick a Recommended Rate

One sentence of justification. Use the region most representative of how this codebase would actually be rebuilt. If unsure, default to the US-remote average and flag the assumption in the sensitivity section.
