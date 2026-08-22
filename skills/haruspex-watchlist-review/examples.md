# Examples: haruspex-watchlist-review

Each example uses real data captured from the live Haruspex API. Live scores
will differ.

*All examples captured: 2026-04-29.*

---

## Example 1: Five-ticker tech watchlist

**User:** Run my watchlist: AAPL, NVDA, MSFT, TSLA, GOOGL

**Claude (with this skill active):**

> ## Watchlist Review — 5 tickers
>
> ### Buy signals
> | Ticker | Score |   Δ | Outlook | Top driver                  |
> |--------|------:|----:|---------|-----------------------------|
> | NVDA   |    78 | +16 | bullish | competitors (75, +5)        |
> | MSFT   |    77 | +19 | bullish | strong broad lift           |
> | AAPL   |    75 | +23 | bullish | competitors (68, +9)        |
> | GOOGL  |    74 |  -3 | bullish | bullish despite small slip  |
> | TSLA   |    73 |  +4 | bullish | stable, small positive move |
>
> ### Biggest movers
> - **AAPL** +23 — single largest move in the list; competitors +9 and macro +3 carry it; watch the us_china_unofficial drop (-26)
> - **MSFT** +19 — second-largest move
> - **NVDA** +16 — third-largest move
>
> ### Watch closely
> - **AAPL** — `us_china_unofficial` dropped sharply (-26); current 35/100. Worth a closer read.
> - **NVDA** — `us_china_official` 35/100 (-9) and `us_china_unofficial` 35/100 (-9); paired geopolitical pressure.
>
> ### Verify links
> - AAPL: https://haruspex.guru/s/ZDNQy8h7TjMoNTk84OFTMFR9
> - NVDA: https://haruspex.guru/s/9JWj9_sZzYKtcBgfhpkB4K3m
> - MSFT: https://haruspex.guru/s/BoLhlgfxFsbHTsa2wu-1ZS0A
> - TSLA: https://haruspex.guru/s/vs2HhOqnRJjnWQ2-lxH5QX4Z
> - GOOGL: https://haruspex.guru/s/odHtQieepVCZhDhl4cJTHyRT
>
> > **Disclaimer:** Haruspex scores are quantitative signals derived from public data and are provided for informational purposes only. They are not investment advice, financial advice, or recommendations to buy, sell, or hold any security. Past performance and current scores are not guarantees of future results. Always do your own research and consider consulting a licensed financial advisor before making investment decisions. Data via haruspex.guru.

---

## Example 2: Watchlist with a coverage gap

**User:** check on AAPL, NVDA, TOYOF, SONY

**Claude (with this skill active):**

> ## Watchlist Review — 4 tickers requested, 2 returned
>
> ### Buy signals
> | Ticker | Score |   Δ | Outlook | Top driver           |
> |--------|------:|----:|---------|----------------------|
> | NVDA   |    78 | +16 | bullish | competitors (75, +5) |
> | AAPL   |    75 | +23 | bullish | competitors (68, +9) |
>
> ### Biggest movers
> - **AAPL** +23 — competitors and macro both up; watch the us_china_unofficial drop (-26)
> - **NVDA** +16 — competitors up; us_china_* both down 9
>
> ### Coverage gaps
> - **TOYOF, SONY** — not currently in the Haruspex universe. The analysis universe is primarily US large-caps; OTC tickers and most Japan-listed shares aren't covered today. Use `search_stocks(...)` if you'd like to check related listings.
>
> ### Verify links
> - AAPL: https://haruspex.guru/s/ZDNQy8h7TjMoNTk84OFTMFR9
> - NVDA: https://haruspex.guru/s/9JWj9_sZzYKtcBgfhpkB4K3m
>
> > **Disclaimer:** Haruspex scores are quantitative signals derived from public data and are provided for informational purposes only. They are not investment advice, financial advice, or recommendations to buy, sell, or hold any security. Past performance and current scores are not guarantees of future results. Always do your own research and consider consulting a licensed financial advisor before making investment decisions. Data via haruspex.guru.

This pattern demonstrates the **coverage-gap honesty** rule. Two tickers came
back, two did not, and the skill says so.

---

## Example 3: ambiguous request — ask first, don't invent

**User:** Run my watchlist

**Claude (with this skill active):**

> I don't have your watchlist saved — Haruspex doesn't store portfolios through the MCP path, and I don't carry context across conversations. Paste the tickers you'd like reviewed (up to 50) and I'll run a single batched check.

After the user pastes the list, run the workflow normally.

This is mandatory: never invent a watchlist. "Run my watchlist" alone always
gets the prompt-for-list response.

---

## Example 4: comparing tickers (same workflow, different framing)

**User:** Compare AAPL, MSFT, and GOOGL — which is strongest right now?

**Claude (with this skill active):**

> Quick read on the three:
>
> | Ticker | Score |   Δ | Outlook | Signal |
> |--------|------:|----:|---------|--------|
> | MSFT   |    77 | +19 | bullish | buy    |
> | AAPL   |    75 | +23 | bullish | buy    |
> | GOOGL  |    74 |  -3 | bullish | buy    |
>
> By headline score, **MSFT** ranks highest of the three at 77/100. By recent change, **AAPL** moved most (+23 vs MSFT's +19 and GOOGL's -3). All three carry a `buy` signal at present.
>
> Each is bullish, so the differentiator is recent direction: AAPL is rising fastest, MSFT is highest, GOOGL is the only one slipping in this period (-3) despite still being bullish overall.
>
> ### Verify links
> - MSFT: https://haruspex.guru/s/BoLhlgfxFsbHTsa2wu-1ZS0A
> - AAPL: https://haruspex.guru/s/ZDNQy8h7TjMoNTk84OFTMFR9
> - GOOGL: https://haruspex.guru/s/odHtQieepVCZhDhl4cJTHyRT
>
> > **Disclaimer:** Haruspex scores are quantitative signals derived from public data and are provided for informational purposes only. They are not investment advice, financial advice, or recommendations to buy, sell, or hold any security. Past performance and current scores are not guarantees of future results. Always do your own research and consider consulting a licensed financial advisor before making investment decisions. Data via haruspex.guru.

The user asked "which is strongest" — answered factually with score and
trajectory, not as a recommendation.
