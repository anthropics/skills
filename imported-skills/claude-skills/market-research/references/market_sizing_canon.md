# Market Sizing Canon

Reference for TAM/SAM/SOM. Pairs with `market_sizer.py`.

## The three numbers

- **TAM (Total Addressable Market)** — total revenue if you captured 100% of the market for your category.
- **SAM (Serviceable Addressable Market)** — the portion of TAM you can serve given your geography, segment focus, and product scope.
- **SOM (Serviceable Obtainable Market)** — the realistic, capacity-constrained share of SAM you can win in the planning window.

## Two methods — always do both

- **Top-down**: start from a published total market value (analyst report, government statistic) and apply serviceable and reachable fractions. Fast, but only as good as the source and inherits its biases. The classic failure is "1% of a huge number" — a TAM that sounds enormous and means nothing.
- **Bottoms-up**: start from the number of potential customers × the price they would pay, then apply serviceable and adoption fractions. Slower but grounded in units you can defend. The discipline is that bottoms-up forces you to name customer counts and price points.

When the two methods diverge by more than a tolerance, **triangulation has failed** — you do not yet have a defensible number. The tool flags this rather than averaging the two (averaging hides the disagreement).

## Fermi discipline

Good sizing is Fermi estimation: decompose the unknown into knowable factors, estimate each with a stated assumption, and carry the uncertainty through. A market size is a chain of assumptions; surfacing the chain is the deliverable, not the point estimate.

## Common fallacies

- **Double counting** — summing overlapping segments or counting the same revenue at multiple layers of the value chain.
- **Percent-of-a-big-number** — anchoring on "if we just get 1%" without a bottoms-up cross-check.
- **Confusing TAM growth with your growth** — a growing TAM does not entitle you to a fixed share.
- **Spurious precision** — quoting a TAM to four significant figures when the inputs are order-of-magnitude estimates.

## Sources

1. Bessemer Venture Partners, *State of the Cloud* and market-sizing memos (TAM/SAM/SOM discipline).
2. Andreessen Horowitz (a16z), *The truth about market sizing* and bottoms-up TAM essays.
3. Gartner / Forrester / IDC market-model methodology notes (forecast construction conventions).
4. Weinstein, L., & Adam, J., *Guesstimation* (Princeton, 2008) — Fermi estimation.
5. Blank, S., *The Four Steps to the Epiphany* — market-type and sizing in customer development.
6. Damodaran, A., *Narrative and Numbers* (Columbia, 2017) — disciplining market-size narratives with numbers.
