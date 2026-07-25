#!/usr/bin/env python3
"""pmf_signal_scorer.py — Are you before or after product/market fit? Score the signals.

Encodes the qualitative markers Marc Andreessen laid out in "The Only Thing That Matters"
(2007). His framing: "You can always feel when product/market fit isn't happening." The
positive markers (paraphrased from the essay):

  - Customers are buying the product as fast as you can make it.
  - Usage is growing as fast as you can add servers.
  - Money from customers is piling up in your checking account.
  - You're hiring sales and support staff as fast as you can.

The negative markers (before PMF):

  - Word of mouth isn't spreading.
  - Usage isn't growing very fast.
  - Press reviews are kind of "blah".
  - The sales cycle takes too long and lots of deals never close.

This tool also folds in the Sean Ellis test (NOT Andreessen's — Sean Ellis, 2009): the
"% of users who would be very disappointed if they could no longer use the product",
where >= 40% is the widely-used leading indicator of PMF. It is included as a quantitative
complement to Andreessen's qualitative "you can feel it", and is labeled as Ellis's, not
Andreessen's, throughout.

Inputs are 0-10 scores except --ellis-pct which is a 0-100 percentage.

NO LLM CALLS. Pure thresholds + weighted composite.

Usage:
    python pmf_signal_scorer.py --ellis-pct 45 --retention 8 --organic 7 --demand 8 --frequency 7
    python pmf_signal_scorer.py --sample
    python pmf_signal_scorer.py --sample --output-format json
"""

import argparse
import json
import sys
from typing import Any, Dict, List

# Weights for the 0-10 qualitative signals (Ellis % handled separately as a gate).
SIGNAL_WEIGHTS = {
    "retention": 0.30,    # cohort retention flattening = the single strongest signal
    "demand": 0.30,       # "buying as fast as you can make it"
    "organic": 0.25,      # word of mouth spreading
    "frequency": 0.15,    # usage frequency / habit
}


def _clamp10(v: float) -> float:
    return max(0.0, min(10.0, float(v)))


def score(ellis_pct: float, retention: float, organic: float,
          demand: float, frequency: float) -> Dict[str, Any]:
    ellis_pct = max(0.0, min(100.0, float(ellis_pct)))
    retention, organic = _clamp10(retention), _clamp10(organic)
    demand, frequency = _clamp10(demand), _clamp10(frequency)

    composite = round(
        retention * SIGNAL_WEIGHTS["retention"]
        + demand * SIGNAL_WEIGHTS["demand"]
        + organic * SIGNAL_WEIGHTS["organic"]
        + frequency * SIGNAL_WEIGHTS["frequency"],
        2,
    )

    ellis_pass = ellis_pct >= 40.0

    # Deterministic verdict: composite AND the Ellis gate together.
    if composite >= 7.5 and ellis_pass:
        verdict = "AFTER-PMF"
        headline = (
            "You can feel it — the market is pulling. Per Andreessen, the only mistake now is "
            "under-feeding demand. Stop deliberating about product direction and pour everything "
            "into scaling: servers, sales, support, supply. The fire is lit; add fuel."
        )
    elif composite >= 5.5 or (composite >= 5.0 and ellis_pass):
        verdict = "APPROACHING-PMF"
        headline = (
            "Signals are warming but not unmistakable. Real PMF is not subtle — if you have to "
            "squint to see it, you do not have it yet. Concentrate every resource on the single "
            "wedge segment showing the strongest pull and ignore everything else until it clicks."
        )
    else:
        verdict = "BEFORE-PMF"
        headline = (
            "You are before product/market fit, and Andreessen's directive is unambiguous: "
            "do whatever is required to get there. Change the product, change the segment, "
            "change the team if you must. Nothing else you do matters until this flips."
        )

    flags: List[str] = []
    if not ellis_pass:
        flags.append(
            f"Sean Ellis test at {ellis_pct:.0f}% — below the 40% PMF threshold. If fewer than "
            "40% of users would be 'very disappointed' without you, you have not found fit."
        )
    if retention < 5:
        flags.append(
            "Retention is weak. If your cohort curves don't flatten, you have a leaky bucket — "
            "every dollar of growth spend drains out. Fix retention before spending on acquisition."
        )
    if organic < 5:
        flags.append(
            "Word of mouth isn't spreading. Andreessen lists this as a primary before-PMF marker. "
            "If the product were truly pulling, users would be dragging others in for free."
        )
    if demand < 5:
        flags.append(
            "Demand isn't outpacing supply. After PMF you struggle to keep UP with demand; "
            "before PMF you struggle to CREATE it. You're in the second state."
        )

    return {
        "inputs": {
            "ellis_pct": ellis_pct, "retention": retention,
            "organic": organic, "demand": demand, "frequency": frequency,
        },
        "ellis_gate_pass": ellis_pass,
        "composite_signal": composite,
        "verdict": verdict,
        "headline": headline,
        "flags": flags,
        "attribution": {
            "qualitative_markers": "Marc Andreessen, \"The Only Thing That Matters\" (2007)",
            "ellis_40pct_test": "Sean Ellis (2009) — leading-indicator survey, not Andreessen's",
        },
    }


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


def render_human(r: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append("Product/Market Fit Signal Scorer")
    out.append("=" * 68)
    i = r["inputs"]
    out.append(f"  Sean Ellis 'very disappointed' %: {i['ellis_pct']:.0f}%  "
               f"(gate {'PASS' if r['ellis_gate_pass'] else 'FAIL'} @ 40%)")
    out.append(f"  retention {i['retention']}  demand {i['demand']}  "
               f"organic {i['organic']}  frequency {i['frequency']}")
    out.append(f"  Composite signal: {r['composite_signal']}/10")
    out.append("")
    out.append(f"  VERDICT: {r['verdict']}")
    out.append("")
    for line in _wrap(r["headline"], 66):
        out.append(f"  {line}")
    if r["flags"]:
        out.append("")
        out.append("  Flags:")
        for f in r["flags"]:
            for j, line in enumerate(_wrap(f, 62)):
                out.append(f"    {'- ' if j == 0 else '  '}{line}")
    out.append("")
    out.append(f"  Qualitative markers: {r['attribution']['qualitative_markers']}")
    out.append(f"  40% test: {r['attribution']['ellis_40pct_test']}")
    return "\n".join(out)


SAMPLE = dict(ellis_pct=45, retention=8, organic=7, demand=8, frequency=7)


def main(argv: List[str]) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--ellis-pct", type=float, help="%% of users 'very disappointed' without product (0-100)")
    p.add_argument("--retention", type=float, help="Cohort retention strength / curve flattening (0-10)")
    p.add_argument("--organic", type=float, help="Organic / word-of-mouth growth (0-10)")
    p.add_argument("--demand", type=float, help="Demand outpacing supply (0-10)")
    p.add_argument("--frequency", type=float, help="Usage frequency / habit formation (0-10)")
    p.add_argument("--sample", action="store_true", help="Run the embedded sample")
    p.add_argument("--output-format", choices=["human", "json"], default="human")
    args = p.parse_args(argv)

    if args.sample:
        vals = SAMPLE
    elif all(v is not None for v in (args.ellis_pct, args.retention, args.organic, args.demand, args.frequency)):
        vals = dict(ellis_pct=args.ellis_pct, retention=args.retention,
                    organic=args.organic, demand=args.demand, frequency=args.frequency)
    else:
        p.print_help()
        print("\nerror: provide all signals (--ellis-pct --retention --organic --demand --frequency) or --sample",
              file=sys.stderr)
        return 2

    result = score(**vals)
    if args.output_format == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
