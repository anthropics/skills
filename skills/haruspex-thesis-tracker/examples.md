# Examples: haruspex-thesis-tracker

Each example uses real data captured from the live Haruspex API. Live scores
will differ.

*All examples captured: 2026-04-29.*

---

## Example 1: AI demand thesis on NVDA — Mixed read

**User:** I'm long NVDA because of AI capex demand. Is my thesis still good?

**Claude (with this skill active):**

> ## Thesis Status: **Mixed**
>
> **Ticker:** NVDA
> **Stated thesis:** Long NVDA on continued AI capex demand.
> **Headline score:** 78/100 (bullish), change +16, signal `buy`
>
> ### Thesis → dimension mapping
> | Dimension      | Predicted by thesis | Current | Δ  | Read     |
> |----------------|---------------------|--------:|---:|----------|
> | ai-exposure    | high or rising      |      57 |  0 | mixed    |
> | competitors    | high or rising      |      75 | +5 | supports |
> | supplychain    | high or rising      |      44 |  0 | against  |
>
> ### Evidence summary
> The headline score is solidly bullish (78/100, +16) and competitors is moving favorably (+5), so the broad backdrop for NVDA is supportive of an AI-demand thesis. However, two of the three thesis-relevant dimensions push against it: `ai-exposure` is flat at 57 — neither high nor rising — and `supplychain` sits at 44, structurally weak for a thesis that requires uninterrupted AI buildout. Geopolitical pressure has also intensified (`us_china_official` -9, `us_china_unofficial` -9), which is a risk vector this thesis doesn't directly account for. Headline says yes; the thesis-specific lens says cautiously.
>
> **Verify:** https://haruspex.guru/s/9JWj9_sZzYKtcBgfhpkB4K3m
>
> > **Disclaimer:** Haruspex scores are quantitative signals derived from public data and are provided for informational purposes only. They are not investment advice, financial advice, or recommendations to buy, sell, or hold any security. Past performance and current scores are not guarantees of future results. Always do your own research and consider consulting a licensed financial advisor before making investment decisions. Data via haruspex.guru.

Note the **Mixed** status: bullish headline plus weak dimension-specific
backing.

---

## Example 2: Competitive moat thesis on AAPL — Supported

**User:** I'm bullish on AAPL because their competitive position keeps strengthening despite the China noise.

**Claude (with this skill active):**

> ## Thesis Status: **Supported**
>
> **Ticker:** AAPL
> **Stated thesis:** Long AAPL on a strengthening competitive position, accepting some China-related headwinds.
> **Headline score:** 75/100 (bullish), change +23, signal `buy`
>
> ### Thesis → dimension mapping
> | Dimension      | Predicted by thesis | Current | Δ   | Read     |
> |----------------|---------------------|--------:|----:|----------|
> | competitors    | high or rising      |      68 |  +9 | supports |
> | earnings       | high or rising      |      72 |   0 | supports |
> | regulatory     | high or rising      |      68 |   0 | supports |
>
> ### Evidence summary
> The thesis lines up with the data. Competitors strengthened materially this period (+9), earnings sit at 72 (stable, in supportive territory), and regulatory remains supportive at 68. The headline score moved up sharply (+23) — the largest single-period move among major US large-caps in this batch — which is consistent with a "competitive position keeps strengthening" framing. Worth flagging: `us_china_unofficial` fell -26 to 35/100, which the user explicitly accepted in the thesis ("despite the China noise"); the magnitude is larger than typical noise and merits a closer look even though it doesn't undermine the core thesis.
>
> **Verify:** https://haruspex.guru/s/ZDNQy8h7TjMoNTk84OFTMFR9
>
> > **Disclaimer:** Haruspex scores are quantitative signals derived from public data and are provided for informational purposes only. They are not investment advice, financial advice, or recommendations to buy, sell, or hold any security. Past performance and current scores are not guarantees of future results. Always do your own research and consider consulting a licensed financial advisor before making investment decisions. Data via haruspex.guru.

---

## Example 3: position without a thesis — ask first

**User:** I'm long TSLA. What's the read?

**Claude (with this skill active):**

> Before I run a thesis evaluation: what's your reason for being long? "Thesis tracker" works by mapping the *why* of your position to the dimensions that test it. Without a stated thesis, this is just generic analysis — I can do that with the `haruspex-stock-analyst` skill, but you'd get a more focused read by telling me what you're betting on (e.g., FSD adoption, energy storage, EV pricing power, China demand recovery, etc.).

After the user provides the thesis, run the workflow normally. **Never invent
the thesis** — every "long X" without a stated reason gets this prompt.

---

## Example 4: Challenged status example pattern

(Pattern shown without specific captured numbers — actual values vary by
ticker and date.)

> ## Thesis Status: **Challenged**
>
> **Ticker:** [SYMBOL]
> **Stated thesis:** [user's stated thesis]
> **Headline score:** [score]/100 ([outlook]), change [-X], signal [signal]
>
> ### Thesis → dimension mapping
> | Dimension      | Predicted by thesis | Current | Δ  | Read    |
> |----------------|---------------------|--------:|---:|---------|
> | [dim_a]        | [predicted]          |     [N] | -N | against |
> | [dim_b]        | [predicted]          |     [N] |  0 | mixed   |
> | [dim_c]        | [predicted]          |     [N] | -N | against |
>
> ### Evidence summary
> The data has moved against the thesis as stated. [Specific dimensional read.] [Specific magnitude of change vs. expected direction.] [Note any redeeming countervailing dimension if one exists.] [Hedge: "one read isn't a final verdict, but the direction is clear."]
>
> **Verify:** [shareUrl]
>
> > **Disclaimer:** [full disclaimer]

The structure is the same as the other statuses; the language is calibrated
— "data has moved against the thesis" is allowed; "you should exit" is not.
