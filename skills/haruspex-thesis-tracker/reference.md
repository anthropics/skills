# Reference: haruspex-thesis-tracker

## Thesis archetype → dimension mapping

This table is a starting prior. Always think about whether the specific
thesis the user stated maps cleanly to these dimensions, or needs a
custom mapping.

| Thesis archetype                              | Primary dimensions                                                   | Predicted direction (high score is supportive unless noted) |
|-----------------------------------------------|----------------------------------------------------------------------|------------------------------------------------------------|
| AI capex / AI demand tailwind                 | `ai-exposure`, `competitors`, `supplychain`                           | high or rising                                              |
| Earnings growth / beat-and-raise              | `earnings`, `fundamentals`, `management`                              | high or rising                                              |
| Strong fundamentals / financial health        | `fundamentals`, `earnings`                                            | high or rising                                              |
| Regulatory tailwind                           | `regulatory`, `macro`                                                  | high or rising                                              |
| Regulatory headwind they'll survive           | `regulatory`, `management`                                             | regulatory may be low; management should be high            |
| Macro / rates beneficiary                     | `macro`, `earnings`, `institutional`                                   | high or rising                                              |
| Geopolitical hedge or insulation              | `geopolitical`, `macro`                                                | high (= less geopolitical pressure)                         |
| China exposure (positive contrarian)          | `geopolitical`, `competitors`                                          | low (= elevated exposure) but trajectory should be rising   |
| Open-source / dev ecosystem moat              | `github-activity`, `competitors`                                       | high or rising                                              |
| IP / patent moat                              | `patents`, `competitors`                                               | high or rising                                              |
| Insider conviction                            | `insider-trading`                                                      | high or rising                                              |
| Institutional accumulation                    | `institutional`                                                        | high or rising                                              |
| ESG / climate-aligned investment              | `esg`, `climate-risk`                                                  | high                                                        |
| Climate-resilient / low-climate-risk          | `climate-risk`                                                         | high (= low risk)                                           |
| Diversified / low concentration risk          | `concentration-risk`                                                   | high (= diversified)                                        |
| Supply-chain advantaged                       | `supplychain`, `concentration-risk`                                    | high                                                        |
| Management quality / capital allocation       | `management`, `earnings`, `institutional`                              | high or rising                                              |
| Competitive moat / pricing power              | `competitors`, `earnings`                                              | high or rising                                              |
| Hiring momentum / talent gravity              | `job-market`, `management`, `competitors`                              | high or rising                                              |
| Sentiment / retail-led recovery               | `sentiment`, `options-flow`, `short-interest`                          | high or rising                                              |
| Short squeeze setup                           | `short-interest`, `options-flow`, `sentiment`                          | high or rising on `short-interest` (favorable for longs)    |
| Options-driven momentum                       | `options-flow`, `technical`, `sentiment`                                | high or rising                                              |
| Technical breakout / momentum                 | `technical`, `options-flow`                                            | high or rising                                              |
| Liquidity / quality-of-execution thesis       | `microstructure`, `institutional`                                       | high or rising                                              |
| Crypto-correlated / blockchain exposure       | `crypto`, `technical`                                                   | direction matches the user's crypto stance                  |

## How to read the dimensions for a thesis

For each thesis-relevant dimension, ask three questions:

1. **Is the current score in the range the thesis predicts?** (Above 50 for
   "high"; the trend direction matters more than absolute level for
   "rising".)
2. **Is the recent change in the predicted direction?** A bullish thesis
   wants positive `change`; a "stable" thesis wants `change` near 0.
3. **Over the 90-day history, is the trend consistent or noisy?** Use the
   history endpoint to see if the current reading is a one-day blip or a
   real trend.

## Custom thesis mapping

When a user states a thesis that doesn't fit the table cleanly, do this:

1. Restate the thesis in one sentence — confirm with the user before mapping.
2. Identify the 2–4 dimensions that are the **closest available proxies**
   for the thesis. Be explicit: "I'm reading your thesis through the
   `regulatory` and `macro` dimensions because Haruspex doesn't have a
   dedicated rate-sensitivity dimension."
3. Acknowledge the gap. A thesis about, say, "advertising revenue
   recovery" doesn't have a perfect Haruspex dimension. Say so. Use
   `earnings` and `macro` as proxies and flag the imperfection.

## How to weight conflicting signals

When some thesis-relevant dimensions support and others contradict:

- A **direction** (recent change) signal generally outweighs a **level**
  (current score) signal of the same magnitude. The thesis evaluation is
  about whether things are moving with or against the thesis *now*.
- A **headline** score moving sharply against the thesis (≥ |10| change in
  the wrong direction) bumps the status to at least **Mixed**, regardless
  of dimensional reads.
- A **risk** dimension (`climate-risk`, `concentration-risk`,
  `us_china_official`, `us_china_unofficial`) deteriorating sharply in a
  thesis that didn't account for it doesn't necessarily challenge the
  thesis — but it should be flagged in the evidence summary as "the thesis
  may not have priced this in."

## When to use a shorter or longer history window

- Default: 90 days.
- For a thesis the user just formed ("I just bought NVDA last week
  because…"), use 30 days — the user wants to know if conditions have
  shifted since they entered.
- For a long-term hold ("I've owned NVDA since 2023…"), 90 days is still
  the right window unless the user explicitly asks for longer; the API's
  default history is a few months.

## NOT_FOUND under thesis-tracker

If `get_stock_score` returns `NOT_FOUND`, tell the user honestly: the
ticker isn't in the analysis universe, so a thesis evaluation can't be
run from Haruspex data. Offer to evaluate a related ticker that is in the
universe, or to use `search_stocks` to find one.

## Don't oversell precision

Thesis tracking is structured opinion-mapping over noisy data. Make this
visible:

- "The data leans supportive over 90 days, but two of the four
  thesis-relevant dimensions barely moved — consider this a soft read."
- "The headline is challenging the thesis sharply this week; one week is
  short, but the move is large enough to flag."

These hedges aren't filler — they're calibration. A thesis-tracker that
sounds certain on a 4-dimension snapshot is misleading.
