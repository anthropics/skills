# Example — A Product/Market Fit Check

A worked example of `/cs:pmf-check`: scoring the felt-signals plus the Sean Ellis 40% gate, then
issuing a before/after verdict with one next move. No inflation — "approaching" is the honest verdict
for warm-but-ambiguous signals.

---

**The situation (hypothetical):** "We're a B2B scheduling tool. 12% MoM growth, mostly paid
acquisition. Retention curve flattens around 35% at month 6. NPS is 42. We're debating whether to
raise a Series A and hire a sales team."

---

**The felt-signal test (Andreessen):**

- Buying as fast as you can make it? — No; growth is *bought*, not pulled.
- Usage growing as fast as you can add servers? — No.
- Money piling up? — No; CAC is roughly equal to 12-month LTV.
- Hiring support as fast as you can? — No.

**The Sean Ellis 40% gate (Ellis, not Andreessen):** survey says **31%** "very disappointed." Below 40%.

**Deterministic score:**

```
python scripts/pmf_signal_scorer.py --ellis-pct 31 --retention 5 --organic 3 --demand 4 --frequency 6
```

Composite ≈ 4.4. Ellis gate: FAIL.

**Verdict:** `BEFORE-PMF`. **Confidence: high.**

You are before product/market fit and the data is not ambiguous: 31% on the Ellis test, retention
flattening at 35% (a leaky bucket), and growth that stops the moment you stop paying for it. Organic
growth at 3/10 is the tell — if the product were pulling, users would be dragging colleagues in for
free, and they're not.

**One next move:** do **not** raise a Series A to fund a sales team. That would pour expensive
acquisition into a leaky bucket and convert investor money into churn. Instead, find the sub-segment
inside your 31% who *are* "very disappointed" — they exist — and figure out what's true for them that
isn't true for everyone else. Rebuild around that wedge until the Ellis number clears 40% and
retention stops leaking. Sales and fundraising are after-PMF moves; you're not there yet.
