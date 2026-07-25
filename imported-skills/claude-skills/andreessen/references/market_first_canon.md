# Market-First Canon — Andreessen's "The Only Thing That Matters"

The single load-bearing idea of this skill. When you evaluate any venture, project, feature,
career move, or bet, the dominant variable is **the market**, not the team and not the product.

## The thesis

In "The Pmarca Guide to Startups, part 4: The only thing that matters" (blog.pmarca.com,
June 25, 2007), Marc Andreessen argues that a startup's outcome is determined primarily by the
market it is in — the size, the growth, and whether real customers with real money exist. His
formulation (paraphrased; the exact wording is widely quoted):

> "When a great team meets a lousy market, market wins. When a lousy team meets a great market,
> market wins. When a great team meets a great market, something special happens."

And the line that anchors the whole essay:

> "Markets that don't exist don't care how smart you are."

**Confidence: high.** These quotes are among the most-cited lines in startup writing and are
archived in multiple reproductions of the pmarca guide (the original blog is defunct; the essay
was later collected in *The Pmarca Blog Archives* PDF, a16z).

## Why market dominates (the mechanism)

Andreessen's argument is not sentiment — it is about where the *pull* comes from:

> "In a great market — a market with lots of real potential customers — the market pulls product
> out of the startup. The market needs to be fulfilled and the market will be fulfilled, by the
> first viable product that comes along."

Implication: in a great market you can have a mediocre product and an average team and still
succeed, because demand drags the product into existence. In a terrible market you can have the
best product and team in the world and fail, because there is no demand to pull on.

This is why `market_first_evaluator.py` weights the market cluster at 0.55 and applies a **hard
gate**: a sub-4.0 market overrides any team/product score. That is not a modeling convenience —
it is the literal claim of the essay.

## Team, product, market — Andreessen's ranking

Andreessen explicitly ranks the three classic startup variables:

1. **Market** — most important. (Confidence: high.)
2. **Team** — second. (Confidence: high.)
3. **Product** — third. (Confidence: high.)

This inverts the instinct of most builders, who fall in love with their product first and rarely
interrogate the market hard enough. The skill's posture is designed to break that instinct.

## The corollary: "do whatever is necessary to get to a good market"

Andreessen's practical advice for a startup in a bad market is blunt: **change the market.** Pivot
the same team toward demand that actually exists, rather than trying to out-execute a non-market.
The `KILL-OR-REPICK-MARKET` verdict encodes exactly this — it is rarely "give up", it is "point this
team at a real market."

## Steel-manning the counterargument (per the operating prompt)

The honest counter-case, stated first as the prompt requires:

- **Some categories are product-led, not market-led.** Consumer social and developer tools have
  produced winners where the "market" did not visibly exist until the product created it
  (e.g., the market for a microblogging service was not measurable before it existed).
  Confidence: moderate.
- **Andreessen himself later nuanced this**, emphasizing founder and team quality more heavily in
  a16z's actual investing practice than the 2007 essay's market-absolutism implies.
  Confidence: moderate (inferred from a16z's stated thesis; not a single citable retraction).
- **Timing is doing a lot of work** inside "market." A market that does not exist *yet* but will
  is the highest-return bet and the hardest to score. This is why the evaluator scores `timing`
  ("why now?") as a distinct market sub-factor.

Even granting these, the operating posture holds: builders systematically over-weight product and
team and under-weight market, so a tool that forces the market question first corrects the more
common and more expensive error. Confidence: high.

## Sources

1. Marc Andreessen, "The Pmarca Guide to Startups, part 4: The only thing that matters,"
   blog.pmarca.com, June 25, 2007. Confidence: high.
2. *The Pmarca Blog Archives* (collected essays, a16z PDF). Confidence: high.
3. Andy Rachleff (co-founder, Benchmark) — origin of the "product/market fit" framing that
   Andreessen popularized; Rachleff attributes the underlying idea to Don Valentine / Sequoia.
   Confidence: moderate (attribution chain is well-reported but secondhand).
4. Don Valentine (Sequoia) lectures on market size as the primary driver of returns. Confidence: moderate.
5. Marc Andreessen, "Software Is Eating the World," Wall Street Journal, August 20, 2011 — the
   macro case for why software markets keep expanding. Confidence: high.
6. a16z published investing thesis (firm website) — team/founder emphasis in practice. Confidence: moderate.
7. Bill Gurley, "All Markets Are Not Created Equal" (above-the-crowd.com) — independent
   reinforcement of market primacy from a peer investor. Confidence: high.
