#!/usr/bin/env python3
"""market_sizer.py - Compute TAM / SAM / SOM by BOTH top-down and bottoms-up methods.

Stdlib-only. Deterministic. NO LLM calls. NEVER returns a single number: it computes both
methods side-by-side, reports the delta, and prints a mandatory method + assumptions block.

Top-down:   TAM = total_market_value ; SAM = TAM * serviceable_fraction ; SOM = SAM * reachable_share
Bottoms-up: TAM = total_potential_customers * annual_price
            SAM = TAM * serviceable_fraction
            SOM = SAM * realistic_adoption (capacity-constrained)

If the two TAMs diverge by more than the tolerance, the tool flags it: triangulation failed.

Usage:
    python3 market_sizer.py --sample
    python3 market_sizer.py --input market.json --method both
    python3 market_sizer.py --input market.json --profile b2b-saas --output json
"""

from __future__ import annotations

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
try:
    import config_loader as _cfg
except ImportError:  # pragma: no cover
    _cfg = None

# Profiles tune the divergence tolerance and a sanity note.
PROFILES = {
    "b2b-saas": {"tolerance": 0.30},
    "consumer": {"tolerance": 0.40},
    "enterprise": {"tolerance": 0.25},
    "marketplace": {"tolerance": 0.40},
    "hardware": {"tolerance": 0.30},
    "services": {"tolerance": 0.35},
}

SAMPLE = {
    "market_name": "Mid-market HR analytics SaaS (US)",
    "top_down": {
        "total_market_value": 4200000000,
        "serviceable_fraction": 0.35,
        "reachable_share": 0.04,
    },
    "bottoms_up": {
        "total_potential_customers": 62000,
        "annual_price": 18000,
        "serviceable_fraction": 0.35,
        "realistic_adoption": 0.03,
    },
}


def top_down(td: dict) -> dict:
    tam = float(td.get("total_market_value", 0.0))
    sam = tam * float(td.get("serviceable_fraction", 0.0))
    som = sam * float(td.get("reachable_share", 0.0))
    return {"method": "top-down", "TAM": round(tam, 0), "SAM": round(sam, 0), "SOM": round(som, 0)}


def bottoms_up(bu: dict) -> dict:
    customers = float(bu.get("total_potential_customers", 0.0))
    price = float(bu.get("annual_price", 0.0))
    tam = customers * price
    sam = tam * float(bu.get("serviceable_fraction", 0.0))
    som = sam * float(bu.get("realistic_adoption", 0.0))
    return {"method": "bottoms-up", "TAM": round(tam, 0), "SAM": round(sam, 0),
            "SOM": round(som, 0), "implied_customers_at_SOM": round((sam / price) * float(bu.get("realistic_adoption", 0.0))) if price else None}


def size_market(data: dict, method: str, profile: str) -> dict:
    if profile not in PROFILES:
        raise ValueError(f"Unknown profile '{profile}'. Choose from {list(PROFILES)}.")
    tol = PROFILES[profile]["tolerance"]
    out = {"market_name": data.get("market_name", "UNSPECIFIED"), "profile": profile}

    td = top_down(data.get("top_down", {})) if method in ("top-down", "both") else None
    bu = bottoms_up(data.get("bottoms_up", {})) if method in ("bottoms-up", "both") else None
    if td:
        out["top_down"] = td
    if bu:
        out["bottoms_up"] = bu

    flags = []
    if td and bu and td["TAM"] > 0:
        delta = abs(td["TAM"] - bu["TAM"]) / td["TAM"]
        out["tam_divergence"] = round(delta, 3)
        if delta > tol:
            flags.append(f"TRIANGULATION FAILED: top-down and bottoms-up TAM differ by {delta:.0%} "
                         f"(> {tol:.0%} tolerance). Reconcile before quoting a number.")
        else:
            flags.append(f"Triangulation OK: TAMs within {delta:.0%} (tolerance {tol:.0%}).")
    out["flags"] = flags
    out["method_and_assumptions"] = [
        "NEVER quote a single TAM number without stating the method and the assumptions below.",
        "Top-down TAM = total market value (cite the source: analyst report, gov stat).",
        "Bottoms-up TAM = total potential customers x annual price (cite both counts).",
        "SAM = TAM x serviceable fraction (geography/segment you can actually serve).",
        "SOM = SAM x realistic, capacity-constrained share you can win in the planning window.",
    ]
    return out


def _fmt(n):
    return f"${n:,.0f}" if isinstance(n, (int, float)) else str(n)


def _render_human(r: dict) -> str:
    lines = [f"Market Sizing: {r['market_name']}  (profile: {r['profile']})", ""]
    for key in ("top_down", "bottoms_up"):
        if key in r:
            m = r[key]
            lines.append(f"  [{m['method']}]  TAM {_fmt(m['TAM'])} | SAM {_fmt(m['SAM'])} | SOM {_fmt(m['SOM'])}")
            if m.get("implied_customers_at_SOM") is not None:
                lines.append(f"      implied customers at SOM: {m['implied_customers_at_SOM']:,}")
    if "tam_divergence" in r:
        lines.append(f"  TAM divergence (top-down vs bottoms-up): {r['tam_divergence']:.1%}")
    lines.append("")
    for f in r["flags"]:
        lines.append(f"  ! {f}")
    lines.append("")
    lines.append("Method & assumptions (must travel with the number):")
    for a in r["method_and_assumptions"]:
        lines.append(f"  - {a}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Compute TAM/SAM/SOM by top-down AND bottoms-up (never a single number).")
    p.add_argument("--input", help="Path to JSON with top_down{} and bottoms_up{}")
    p.add_argument("--method", choices=["top-down", "bottoms-up", "both"], default=None,
                   help="overrides onboarding sizing_method")
    p.add_argument("--profile", default=None, choices=list(PROFILES),
                   help="overrides onboarding default_profile")
    p.add_argument("--output", choices=["human", "json"], default="human")
    p.add_argument("--sample", action="store_true", help="use the embedded sample")
    args = p.parse_args(argv)

    conf = _cfg.load_config() if _cfg else {}
    method = args.method or conf.get("sizing_method", "both")
    profile = args.profile or conf.get("default_profile", "b2b-saas")
    data = SAMPLE if (args.sample or not args.input) else json.load(open(args.input))
    try:
        result = size_market(data, method, profile)
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(_render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
