#!/usr/bin/env python3
"""wtp_analyzer.py — Van Westendorp Price Sensitivity Meter (PSM).

Implements the classical PSM analysis (van Westendorp, 1976). Each respondent answers
4 questions:

  1. Too cheap     — price at which you'd doubt the quality
  2. Bargain       — price that feels like a great deal
  3. Getting expensive — price where you'd start to hesitate
  4. Too expensive — price at which you would never buy

Computes the 4 intersection points:

  - OPP (Optimal Price Point):    intersection of "too cheap" and "too expensive"
  - IDP (Indifference Price Point): intersection of "bargain" and "getting expensive"
  - PMC (Point of Marginal Cheapness):  intersection of "too cheap" and "getting expensive"
  - PME (Point of Marginal Expensiveness): intersection of "bargain" and "too expensive"

Range of Acceptable Prices (RAP) = [PMC, PME].

Output: markdown or JSON. Stdlib only.

Usage:
    wtp_analyzer.py --input survey.json --output markdown
    wtp_analyzer.py --sample
"""
from __future__ import annotations

import argparse
import json
import math
import random
import statistics
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


@dataclass
class Curves:
    prices: list[float]
    too_cheap: list[float]          # P(too cheap >= price)  — decreasing in price
    bargain: list[float]            # P(bargain >= price)    — decreasing in price
    getting_expensive: list[float]  # P(getting expensive <= price) — increasing
    too_expensive: list[float]      # P(too expensive <= price)     — increasing


def build_price_grid(respondents: list[dict[str, float]]) -> list[float]:
    """Build a sorted unique-price grid from all responses."""
    prices: set[float] = set()
    for r in respondents:
        for k in ("too_cheap", "bargain", "getting_expensive", "too_expensive"):
            v = r.get(k)
            if v is not None:
                prices.add(float(v))
    grid = sorted(prices)
    if not grid:
        return []
    # Densify with intermediate steps to make intersection detection stable.
    densified: list[float] = []
    for i, p in enumerate(grid):
        densified.append(p)
        if i + 1 < len(grid):
            nxt = grid[i + 1]
            mid = (p + nxt) / 2.0
            if mid not in prices:
                densified.append(mid)
    return sorted(set(densified))


def cumulative_curves(respondents: list[dict[str, float]], grid: list[float]) -> Curves:
    n = len(respondents)
    too_cheap: list[float] = []
    bargain: list[float] = []
    getting_expensive: list[float] = []
    too_expensive: list[float] = []
    for p in grid:
        tc = sum(1 for r in respondents if (r.get("too_cheap") is not None) and float(r["too_cheap"]) >= p)
        bg = sum(1 for r in respondents if (r.get("bargain") is not None) and float(r["bargain"]) >= p)
        ge = sum(1 for r in respondents if (r.get("getting_expensive") is not None) and float(r["getting_expensive"]) <= p)
        te = sum(1 for r in respondents if (r.get("too_expensive") is not None) and float(r["too_expensive"]) <= p)
        too_cheap.append(tc / n)
        bargain.append(bg / n)
        getting_expensive.append(ge / n)
        too_expensive.append(te / n)
    return Curves(grid, too_cheap, bargain, getting_expensive, too_expensive)


def find_intersection(prices: list[float], a: list[float], b: list[float]) -> float | None:
    """Find first price where curve a crosses curve b (linear interp between grid points)."""
    if len(prices) < 2:
        return None
    prev_diff = a[0] - b[0]
    for i in range(1, len(prices)):
        diff = a[i] - b[i]
        if prev_diff == 0:
            return prices[i - 1]
        if (prev_diff < 0 < diff) or (prev_diff > 0 > diff):
            # Linear interpolation
            p0, p1 = prices[i - 1], prices[i]
            t = prev_diff / (prev_diff - diff)
            return p0 + t * (p1 - p0)
        prev_diff = diff
    return None


@dataclass
class PSMResult:
    n: int
    opp: float | None
    idp: float | None
    pmc: float | None
    pme: float | None
    rap_low: float | None
    rap_high: float | None
    warnings: list[str]


def analyze(respondents: list[dict[str, float]]) -> PSMResult:
    warnings: list[str] = []
    n = len(respondents)
    if n < 30:
        warnings.append(
            f"Sample size N={n} is below 30. PSM results are directional only; "
            "treat the range as a hypothesis, not a recommendation. Aim for N≥100."
        )
    elif n < 100:
        warnings.append(f"Sample size N={n} is acceptable but below the preferred N≥100 threshold.")

    # Sanity-check monotonicity (too_cheap < bargain < getting_expensive < too_expensive per respondent)
    inconsistent = 0
    for r in respondents:
        try:
            tc = float(r["too_cheap"])
            bg = float(r["bargain"])
            ge = float(r["getting_expensive"])
            te = float(r["too_expensive"])
        except (KeyError, TypeError, ValueError):
            inconsistent += 1
            continue
        if not (tc <= bg <= ge <= te):
            inconsistent += 1
    if inconsistent:
        warnings.append(
            f"{inconsistent} of {n} respondents have inconsistent price ordering "
            "(expected too_cheap ≤ bargain ≤ getting_expensive ≤ too_expensive). "
            "Consider screening these before reporting."
        )

    grid = build_price_grid(respondents)
    if not grid:
        return PSMResult(n=n, opp=None, idp=None, pmc=None, pme=None, rap_low=None, rap_high=None, warnings=warnings)

    c = cumulative_curves(respondents, grid)
    opp = find_intersection(c.prices, c.too_cheap, c.too_expensive)
    idp = find_intersection(c.prices, c.bargain, c.getting_expensive)
    pmc = find_intersection(c.prices, c.too_cheap, c.getting_expensive)
    pme = find_intersection(c.prices, c.bargain, c.too_expensive)

    return PSMResult(n=n, opp=opp, idp=idp, pmc=pmc, pme=pme, rap_low=pmc, rap_high=pme, warnings=warnings)


def _fmt(v: float | None) -> str:
    return f"{v:,.2f}" if v is not None else "n/a"


def render_markdown(res: PSMResult) -> str:
    lines: list[str] = []
    lines.append("# Van Westendorp PSM Analysis")
    lines.append("")
    lines.append(f"**Respondents:** N = {res.n}")
    lines.append("")
    if res.warnings:
        lines.append("> **Warnings:**")
        for w in res.warnings:
            lines.append(f"> - {w}")
        lines.append("")
    lines.append("## Four intersection points")
    lines.append("")
    lines.append("| Point | Definition | Value |")
    lines.append("|---|---|---|")
    lines.append(f"| **OPP** — Optimal Price Point | too cheap ↔ too expensive | {_fmt(res.opp)} |")
    lines.append(f"| **IDP** — Indifference Price Point | bargain ↔ getting expensive | {_fmt(res.idp)} |")
    lines.append(f"| **PMC** — Point of Marginal Cheapness | too cheap ↔ getting expensive | {_fmt(res.pmc)} |")
    lines.append(f"| **PME** — Point of Marginal Expensiveness | bargain ↔ too expensive | {_fmt(res.pme)} |")
    lines.append("")
    lines.append("## Range of Acceptable Prices (RAP)")
    lines.append("")
    if res.rap_low is not None and res.rap_high is not None:
        lines.append(f"**RAP = [{_fmt(res.rap_low)}, {_fmt(res.rap_high)}]**")
        lines.append("")
        lines.append("Prices outside this range are likely to be rejected as either too cheap (quality doubt) or too expensive (no purchase).")
    else:
        lines.append("RAP could not be computed — check input data and sample size.")
    lines.append("")
    lines.append("## Interpretation guidance")
    lines.append("")
    lines.append("- PSM gives a **range**, not the price. Final price is a commercial decision.")
    lines.append("- OPP is a theoretical mid-point — the price at which equal % of respondents reject as too cheap and too expensive.")
    lines.append("- IDP is the median respondent's perceived 'fair' price.")
    lines.append("- Re-run with segmented samples (ICP vs non-ICP) — overall PSM averages across segments hide structure.")
    lines.append("- Validate the upper end with willingness-to-pay experiments in market before anchoring at PME.")
    return "\n".join(lines)


def synthetic_sample(n: int = 50, seed: int = 17) -> list[dict[str, float]]:
    """Generate N synthetic respondents with realistic price ordering and segmentation noise."""
    rng = random.Random(seed)
    respondents: list[dict[str, float]] = []
    for _ in range(n):
        anchor = rng.gauss(80, 20)  # respondent's reference price
        anchor = max(20.0, anchor)
        tc = max(5.0, anchor * rng.uniform(0.3, 0.5))
        bg = anchor * rng.uniform(0.6, 0.85)
        ge = anchor * rng.uniform(0.95, 1.15)
        te = anchor * rng.uniform(1.3, 1.8)
        respondents.append({
            "too_cheap": round(tc, 2),
            "bargain": round(bg, 2),
            "getting_expensive": round(ge, 2),
            "too_expensive": round(te, 2),
        })
    return respondents


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--input", type=Path, help="Path to survey JSON: {respondents: [{too_cheap, bargain, getting_expensive, too_expensive}]}.")
    p.add_argument("--output", default="markdown", choices=["markdown", "json"], help="Output format.")
    p.add_argument("--sample", action="store_true", help="Run with synthetic 50-respondent sample.")
    args = p.parse_args(argv)

    if args.sample:
        respondents = synthetic_sample(50)
    elif args.input:
        data = json.loads(args.input.read_text())
        respondents = data.get("respondents", data) if isinstance(data, dict) else data
    else:
        p.error("Provide --input or --sample.")
        return 2

    if not isinstance(respondents, list) or not respondents:
        print("ERROR: respondents must be a non-empty list.", file=sys.stderr)
        return 1

    res = analyze(respondents)
    if args.output == "json":
        out = {
            "n": res.n,
            "opp": res.opp,
            "idp": res.idp,
            "pmc": res.pmc,
            "pme": res.pme,
            "rap": [res.rap_low, res.rap_high],
            "warnings": res.warnings,
        }
        print(json.dumps(out, indent=2))
    else:
        print(render_markdown(res))
    return 0


if __name__ == "__main__":
    sys.exit(main())
