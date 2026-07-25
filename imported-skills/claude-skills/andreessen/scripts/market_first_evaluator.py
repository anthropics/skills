#!/usr/bin/env python3
"""market_first_evaluator.py — Score an idea/project/feature the Andreessen way: market dominates.

Operationalizes the core thesis of Marc Andreessen's 2007 essay "The Pmarca Guide to
Startups, part 4: The only thing that matters" (blog.pmarca.com, June 25, 2007):

  "When a great team meets a lousy market, market wins. When a lousy team meets a
   great market, market wins. ... Markets that don't exist don't care how smart you are."

So the math here is deliberately lopsided. Market factors are weighted far above team and
product, and a weak market is a HARD GATE — no amount of team or product brilliance rescues
a verdict when the market evidence is thin. This is the whole point. Do not "balance" it.

Inputs are 0-10 scores. Market cluster = mean(size, growth, timing, pull).

Composite weighting:  market 0.55 | team 0.25 | product 0.20

Verdict logic (deterministic, market-first):
  - market_cluster < 4.0              -> KILL-OR-REPICK-MARKET   (market wins; team/product irrelevant)
  - market_cluster >= 7.0 and pull>=7 -> BUILD-POUR-FUEL         (the market is pulling product out of you)
  - market_cluster >= 5.5             -> MARKET-FIRST-DERISK     (promising; prove demand before scaling)
  - otherwise                         -> MARKET-FIRST-DERISK / weak-lean

NO LLM CALLS. Pure arithmetic + thresholds.

Usage:
    python market_first_evaluator.py --size 8 --growth 7 --timing 9 --pull 8 --team 6 --product 5
    python market_first_evaluator.py --sample
    python market_first_evaluator.py --sample --output-format json
"""

import argparse
import json
import sys
from typing import Any, Dict, List

WEIGHTS = {"market": 0.55, "team": 0.25, "product": 0.20}

ANDREESSEN_QUOTE = (
    "When a great team meets a lousy market, market wins. When a lousy team meets a "
    "great market, market wins. — Marc Andreessen, \"The Only Thing That Matters\" (2007)"
)


def _clamp(v: float) -> float:
    return max(0.0, min(10.0, float(v)))


def evaluate(size: float, growth: float, timing: float, pull: float,
             team: float, product: float) -> Dict[str, Any]:
    size, growth, timing, pull = (_clamp(size), _clamp(growth), _clamp(timing), _clamp(pull))
    team, product = _clamp(team), _clamp(product)

    market_cluster = round((size + growth + timing + pull) / 4.0, 2)
    composite = round(
        market_cluster * WEIGHTS["market"]
        + team * WEIGHTS["team"]
        + product * WEIGHTS["product"],
        2,
    )

    notes: List[str] = []

    if market_cluster < 4.0:
        verdict = "KILL-OR-REPICK-MARKET"
        headline = (
            "Market evidence is too thin. Andreessen's rule is brutal here: market wins. "
            "A strong team and a polished product do NOT rescue a non-market. Kill this, "
            "or aim the same team at a market that actually exists and is pulling."
        )
        if team >= 7 or product >= 7:
            notes.append(
                "You scored team/product highly. That is exactly the trap the thesis warns "
                "about — strong builders talk themselves into weak markets. The score is "
                "intentionally not letting team/product override a sub-4 market."
            )
    elif market_cluster >= 7.0 and pull >= 7:
        verdict = "BUILD-POUR-FUEL"
        headline = (
            "The market is pulling product out of you. This is the after-PMF posture: stop "
            "polishing, stop deliberating — pour fuel on the fire and feed demand as fast as "
            "you can. The dominant risk now is under-investing, not over-investing."
        )
    elif market_cluster >= 5.5:
        verdict = "MARKET-FIRST-DERISK"
        headline = (
            "Promising market, but not yet proven to be pulling. Before you scale team or "
            "burn runway on product polish, run the cheapest experiment that proves real "
            "demand. De-risk the market question first; everything else is downstream."
        )
    else:
        verdict = "MARKET-FIRST-DERISK"
        headline = (
            "Market is marginal (4.0-5.5). Lean toward NO unless you have a specific, "
            "testable reason the demand is bigger than it looks. Prove pull before commitment."
        )

    # Dominant-factor diagnostic
    contributions = {
        "market": round(market_cluster * WEIGHTS["market"], 2),
        "team": round(team * WEIGHTS["team"], 2),
        "product": round(product * WEIGHTS["product"], 2),
    }
    dominant = max(contributions, key=contributions.get)

    if pull < 5 and market_cluster >= 5.5:
        notes.append(
            "Pull signal is weak. A big TAM with no pull is a thesis, not a business. The "
            "single highest-value thing you can do is generate evidence the market pulls."
        )
    if timing < 4:
        notes.append(
            "Timing ('why now?') scored low. Most failed startups are right but early. If you "
            "cannot articulate what changed in the world to make this possible NOW, that is a red flag."
        )

    return {
        "inputs": {
            "size": size, "growth": growth, "timing": timing, "pull": pull,
            "team": team, "product": product,
        },
        "market_cluster": market_cluster,
        "weights": WEIGHTS,
        "contributions": contributions,
        "dominant_factor": dominant,
        "composite_score": composite,
        "verdict": verdict,
        "headline": headline,
        "notes": notes,
        "andreessen_quote": ANDREESSEN_QUOTE,
    }


def render_human(r: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append("Market-First Evaluation (Andreessen thesis: market > team > product)")
    out.append("=" * 68)
    i = r["inputs"]
    out.append(f"  Market  -> size {i['size']}  growth {i['growth']}  timing {i['timing']}  pull {i['pull']}")
    out.append(f"            market cluster = {r['market_cluster']}/10")
    out.append(f"  Team    -> {i['team']}/10        Product -> {i['product']}/10")
    out.append("")
    out.append(f"  Weighted contributions: market {r['contributions']['market']} | "
               f"team {r['contributions']['team']} | product {r['contributions']['product']}")
    out.append(f"  Dominant factor: {r['dominant_factor'].upper()}")
    out.append(f"  Composite score: {r['composite_score']}/10")
    out.append("")
    out.append(f"  VERDICT: {r['verdict']}")
    out.append("")
    for line in _wrap(r["headline"], 66):
        out.append(f"  {line}")
    if r["notes"]:
        out.append("")
        out.append("  Notes:")
        for n in r["notes"]:
            for j, line in enumerate(_wrap(n, 62)):
                out.append(f"    {'- ' if j == 0 else '  '}{line}")
    out.append("")
    out.append(f"  {r['andreessen_quote']}")
    return "\n".join(out)


def _wrap(text: str, width: int) -> List[str]:
    words, lines, cur = text.split(), [], ""
    for w in words:
        if len(cur) + len(w) + 1 > width:
            lines.append(cur)
            cur = w
        else:
            cur = f"{cur} {w}".strip()
    if cur:
        lines.append(cur)
    return lines


SAMPLE = dict(size=8, growth=7, timing=9, pull=8, team=6, product=5)


def main(argv: List[str]) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--size", type=float, help="Market size / real demand (0-10)")
    p.add_argument("--growth", type=float, help="Market growth rate (0-10)")
    p.add_argument("--timing", type=float, help="Timing / 'why now?' (0-10)")
    p.add_argument("--pull", type=float, help="Pull signal — is the market pulling product out of you? (0-10)")
    p.add_argument("--team", type=float, help="Team strength (0-10)")
    p.add_argument("--product", type=float, help="Product quality (0-10)")
    p.add_argument("--sample", action="store_true", help="Run the embedded sample")
    p.add_argument("--output-format", choices=["human", "json"], default="human")
    args = p.parse_args(argv)

    if args.sample:
        vals = SAMPLE
    elif all(v is not None for v in (args.size, args.growth, args.timing, args.pull, args.team, args.product)):
        vals = dict(size=args.size, growth=args.growth, timing=args.timing,
                    pull=args.pull, team=args.team, product=args.product)
    else:
        p.print_help()
        print("\nerror: provide all six scores (--size --growth --timing --pull --team --product) or --sample",
              file=sys.stderr)
        return 2

    result = evaluate(**vals)
    if args.output_format == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
