# Examples: haruspex-stock-analyst

Each example below uses real data captured from the live Haruspex API. Live
scores will differ from these by the time you read them.

*All examples captured: 2026-04-29.*

---

## Example 1: NVDA — clear signal, large positive move

**User:** What do you think about NVDA?

**Claude (with this skill active):**

> ## NVDA — Haruspex Analysis
>
> **Score:** 78/100 (bullish) · **Signal:** buy · **Change:** +16
>
> **Strongest positive dimensions:**
> - `competitors`: 75/100 (+5) — competitive position strengthening, consistent with sustained share leadership in data-center compute
> - `earnings`: 72/100 (0) — earnings strength, stable reading
> - `github-activity`: 69/100 (0) — strong open-source ecosystem footprint
>
> **Watch dimensions:**
> - `us_china_official`: 35/100 (-9) — official US–China policy pressure intensifying (export-control–type risk)
> - `us_china_unofficial`: 35/100 (-9) — unofficial US–China dynamics deteriorating in tandem
> - `supplychain`: 44/100 (0) — supply chain stress signals; not worsening but a structural watch
>
> **30-day trajectory:** Score moved sharply upward in the most recent reading — from 62 to 78 — after sitting in the low 60s for most of the month. The macro dimension picked up (+6) alongside the competitors move. ESG data is not currently available for NVDA so that dimension shows 0; ignore it.
>
> **News context:**
> - "AI Chips Update — AMD's AI Innovations Take Center Stage at 2026 Event" — Simply Wall St., today
> - "Why OpenAI whiffs should still worry Oracle and CoreWeave investors" — Yahoo Finance, today
>
> **Verify:** https://haruspex.guru/s/9JWj9_sZzYKtcBgfhpkB4K3m
>
> > **Disclaimer:** Haruspex scores are quantitative signals derived from public data and are provided for informational purposes only. They are not investment advice, financial advice, or recommendations to buy, sell, or hold any security. Past performance and current scores are not guarantees of future results. Always do your own research and consider consulting a licensed financial advisor before making investment decisions. Data via haruspex.guru.

---

## Example 2: AAPL — bullish with a large positive change, no recent news call

**User:** Score on AAPL?

**Claude (with this skill active):**

> ## AAPL — Haruspex Analysis
>
> **Score:** 75/100 (bullish) · **Signal:** buy · **Change:** +23
>
> **Strongest positive dimensions:**
> - `competitors`: 68/100 (+9) — competitive position strengthening
> - `earnings`: 72/100 (0) — earnings strength, stable
> - `regulatory`: 68/100 (0) — regulatory environment supportive
>
> **Watch dimensions:**
> - `insider-trading`: 23/100 (0) — insider activity skewed unfavorably; structural rather than newly worsening
> - `us_china_unofficial`: 35/100 (-26) — unofficial US–China dynamics sharply worse this period
> - `supplychain`: 44/100 (0) — supply chain stress, stable
>
> **30-day trajectory:** Headline score jumped 23 points this reading — a large move. The competitors dimension carried most of it (+9) alongside macro (+3). The unofficial US–China dimension swung sharply negative; worth watching as a counter-signal even while the overall score is bullish. ESG data is not currently available for AAPL.
>
> **Verify:** https://haruspex.guru/s/ZDNQy8h7TjMoNTk84OFTMFR9
>
> > **Disclaimer:** Haruspex scores are quantitative signals derived from public data and are provided for informational purposes only. They are not investment advice, financial advice, or recommendations to buy, sell, or hold any security. Past performance and current scores are not guarantees of future results. Always do your own research and consider consulting a licensed financial advisor before making investment decisions. Data via haruspex.guru.

---

## Example 3: handling the "should I buy?" question

**User:** Should I buy MSFT?

**Claude (with this skill active):**

> I can show you what the Haruspex data says, but I can't tell you whether to buy — that's a decision that depends on your own situation, time horizon, and risk tolerance. Here's the analysis:
>
> ## MSFT — Haruspex Analysis
>
> **Score:** 77/100 (bullish) · **Signal:** buy · **Change:** +19
>
> **Strongest positive dimensions:**
> - `competitors`: [captured value]/100 — competitive position read
> - `earnings`: [captured value]/100 — earnings strength
> - `ai-exposure`: [captured value]/100 — AI positioning
>
> **Watch dimensions:**
> - [as captured at runtime]
>
> **30-day trajectory:** Headline score rose 19 points to 77, putting MSFT in the bullish zone with a `buy` signal. Trajectory and dimension drivers should be confirmed against the live page.
>
> **Verify:** [shareUrl from get_stock_score]
>
> > **Disclaimer:** Haruspex scores are quantitative signals derived from public data and are provided for informational purposes only. They are not investment advice, financial advice, or recommendations to buy, sell, or hold any security. Past performance and current scores are not guarantees of future results. Always do your own research and consider consulting a licensed financial advisor before making investment decisions. Data via haruspex.guru.

Note how the response opens by **redirecting the buy question** before
showing the analysis. This is mandatory — never answer "should I buy?"
directly.

---

## Example 4: NOT_FOUND — coverage gap handled honestly

**User:** What's the score on TOYOF?

**Claude (with this skill active):**

> The Haruspex universe doesn't currently include TOYOF (Toyota OTC). The analysis universe is primarily US large-caps; OTC tickers and Japan-listed shares aren't covered today.
>
> If you'd like analysis on a Japan-exposed name, I can search for related tickers — `search_stocks("Toyota")` returns options like `TM` (Toyota Motor Corporation on NYSE), `7203.T` (Tokyo), and several international listings — but the current API only returns scores for a subset of these.
>
> > **Disclaimer:** Haruspex scores are quantitative signals derived from public data and are provided for informational purposes only. They are not investment advice, financial advice, or recommendations to buy, sell, or hold any security. Past performance and current scores are not guarantees of future results. Always do your own research and consider consulting a licensed financial advisor before making investment decisions. Data via haruspex.guru.

This pattern — **honest coverage admission, no fabrication, no fake score** —
is mandatory whenever the API returns `NOT_FOUND`.
