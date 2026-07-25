# Product/Market Fit & Bias-to-Build Canon

Two Andreessen ideas the skill operationalizes: (1) the obsessive focus on **product/market fit**
as the only milestone that matters, and (2) the **bias to build** — action over deliberation.

## Product/market fit: before vs after

From the same 2007 essay ("The only thing that matters"), Andreessen splits a startup's life into
two phases:

> "The life of any startup can be divided into two parts: before product/market fit … and after
> product/market fit."

And the operative directive:

> "The only thing that matters is getting to product/market fit. … Do whatever is required to get
> to product/market fit. Including changing out people, rewriting your product, moving into a
> different market, telling customers no when you don't want to, telling customers yes when you
> don't want to, raising that fourth round of highly dilutive venture capital — whatever is required."

**Confidence: high** on the two-phase framing and the "do whatever is required" directive — both
are heavily quoted from the essay.

### How you know (the felt signals)

Andreessen's qualitative test is that PMF is **not subtle** — you can feel it. The positive markers
(paraphrased from the essay):

- Customers are buying the product as fast as you can make it.
- Usage is growing as fast as you can add servers.
- Money from customers is piling up in your company checking account.
- You're hiring sales and customer support staff as fast as you can.

The before-PMF markers:

- Customers aren't quite getting value, word of mouth isn't spreading, usage isn't growing fast.
- Press reviews are kind of "blah."
- The sales cycle takes too long, and lots of deals never close.

**Confidence: high** (these are direct paraphrases of the essay's list).

`pmf_signal_scorer.py` turns these markers into a composite (retention, demand, organic, frequency)
plus the Sean Ellis 40% gate.

### The Sean Ellis 40% test (complement, not Andreessen's)

Sean Ellis (2009, while at Dropbox/LogMeIn lineage) proposed surveying users: *"How would you feel
if you could no longer use this product?"* If **≥ 40%** answer "very disappointed," that is a strong
leading indicator of PMF. This is a quantitative complement to Andreessen's qualitative "you can
feel it," and the skill labels it as **Ellis's, not Andreessen's**, everywhere it appears.
**Confidence: high** (Ellis has published the 40% threshold repeatedly; popularized via Rahul Vohra
/ Superhuman's PMF engine).

## Bias to build: "It's Time to Build"

In "It's Time to Build" (a16z, April 18, 2020), Andreessen argues that the central failure of
institutions is an inability to *build* — and that the corrective is a cultural bias toward making
things rather than deliberating about them.

> "The problem is desire. We need to *want* these things. … The problem is inertia. We need to want
> these things more than we want to prevent these things."

**Confidence: high** (essay is on a16z.com, dated, widely cited).

Operationally, this is why the persona resists analysis-paralysis: once the market gate passes and
PMF signals are warm, the verdict tilts hard toward **action and scale**, not further study. The
expensive error after PMF is under-feeding demand, not over-investing.

## Software is eating the world (why the leverage is in software)

"Software Is Eating the World" (WSJ, August 20, 2011): Andreessen's thesis that software companies
are positioned to take over large swaths of the economy. **Confidence: high.** The skill uses this
as the leverage lens: when choosing what to build, prefer the path where software compounds — where
one unit of effort scales to many units of output without linear cost.

## Steel-man (per the operating prompt)

- **"Do whatever is required to get to PMF" can rationalize thrash.** Endless pivoting in the name
  of PMF burns trust and runway. The directive presumes you can tell real signal from noise, which
  is exactly the hard part. Confidence: high that this is a real failure mode.
- **The felt-signal test is survivorship-biased.** Founders who "felt it" and won write the essays;
  those who "felt it" and lost don't. Treat the felt signals as necessary-not-sufficient.
  Confidence: moderate.
- **"It's time to build" understates regulatory/coordination cost.** Building is often blocked by
  real constraints (zoning, safety, capital), not mere lack of desire. Confidence: moderate.

The posture survives the steel-man because the more common, more expensive error is the opposite:
founders who study instead of ship, and who never run the cheap experiment that would settle the
market question. Confidence: high.

## Sources

1. Marc Andreessen, "The Pmarca Guide to Startups, part 4: The only thing that matters," 2007. Confidence: high.
2. Marc Andreessen, "It's Time to Build," a16z, April 18, 2020. Confidence: high.
3. Marc Andreessen, "Software Is Eating the World," WSJ, August 20, 2011. Confidence: high.
4. Sean Ellis, "Using Product/Market Fit to Drive Sustainable Growth" — the 40% survey. Confidence: high.
5. Rahul Vohra (Superhuman), "How Superhuman Built an Engine to Find Product/Market Fit,"
   First Round Review — operationalizes Ellis's test. Confidence: high.
6. Marc Andreessen on the EconTalk / a16z Podcast discussing PMF phases. Confidence: moderate.
7. Eric Ries, *The Lean Startup* (2011) — the build-measure-learn loop that complements the
   "do whatever is required" pivot directive. Confidence: high.
