#!/usr/bin/env python3
"""cs_coverage_calculator.py — Calculate CS team headcount per coverage model.

Stdlib-only. Takes a book of business and outputs:
  - Required CSM headcount per tier
  - Coverage model recommendation (tech-touch / pooled / named / named+exec)
  - Manager-trigger threshold (when to add a CS manager)
  - 12-month hiring plan if growth_target_pct is provided

Deterministic logic based on ratios + model thresholds.

Input schema (JSON):
{
  "book": {
    "strategic": {"customer_count": 8, "total_arr_usd": 3200000, "current_csm_count": 1},
    "enterprise": {"customer_count": 42, "total_arr_usd": 2100000, "current_csm_count": 2},
    "mid_market": {"customer_count": 120, "total_arr_usd": 1080000, "current_csm_count": 1},
    "smb_long_tail": {"customer_count": 280, "total_arr_usd": 560000, "current_csm_count": 0}
  },
  "growth_target_pct": 0.40   # expected book growth in next 12 months
}

Usage:
    python cs_coverage_calculator.py                       # uses embedded sample
    python cs_coverage_calculator.py path/to/book.json
    python cs_coverage_calculator.py book.json --output json
"""

import argparse
import json
import math
import sys
from typing import Any, Dict, List


SAMPLE: Dict[str, Any] = {
    "book": {
        "strategic": {"customer_count": 8, "total_arr_usd": 3_200_000, "current_csm_count": 1},
        "enterprise": {"customer_count": 42, "total_arr_usd": 2_100_000, "current_csm_count": 2},
        "mid_market": {"customer_count": 120, "total_arr_usd": 1_080_000, "current_csm_count": 1},
        "smb_long_tail": {"customer_count": 280, "total_arr_usd": 560_000, "current_csm_count": 0},
    },
    "growth_target_pct": 0.40,
}


# Coverage model ratios (ARR-per-CSM target by tier)
COVERAGE_MODELS = {
    "strategic": {
        "model": "Named CSM + exec sponsor",
        "arr_per_csm_target": 800_000,    # mid-range of $300K-$1M ratio
        "accounts_per_csm_max": 8,        # named coverage cap
        "fully_loaded_cost_yr": 220_000,  # CSM total comp at strategic
    },
    "enterprise": {
        "model": "Named CSM",
        "arr_per_csm_target": 1_200_000,  # mid-range of $500K-$2M
        "accounts_per_csm_max": 25,       # named caps at 20-30
        "fully_loaded_cost_yr": 180_000,
    },
    "mid_market": {
        "model": "Pooled CSM + automation",
        "arr_per_csm_target": 3_500_000,  # mid-range of $2M-$5M
        "accounts_per_csm_max": 150,      # pooled allows higher count
        "fully_loaded_cost_yr": 140_000,
    },
    "smb_long_tail": {
        "model": "Tech-touch + self-serve",
        "arr_per_csm_target": 10_000_000, # 1 CSM for escalations only
        "accounts_per_csm_max": 1000,     # primarily tech-touch
        "fully_loaded_cost_yr": 110_000,
    },
}


def required_csms(tier_book: Dict[str, Any], model: Dict[str, Any]) -> Dict[str, Any]:
    arr = tier_book.get("total_arr_usd", 0)
    accounts = tier_book.get("customer_count", 0)
    if arr == 0 and accounts == 0:
        return {"required": 0, "binding_constraint": "no book"}

    by_arr = math.ceil(arr / model["arr_per_csm_target"]) if arr else 0
    by_accounts = math.ceil(accounts / model["accounts_per_csm_max"]) if accounts else 0
    required = max(by_arr, by_accounts)
    binding = "arr" if by_arr >= by_accounts else "accounts"

    return {
        "required": required,
        "by_arr_constraint": by_arr,
        "by_accounts_constraint": by_accounts,
        "binding_constraint": binding,
    }


def analyze(payload: Dict[str, Any]) -> Dict[str, Any]:
    book = payload.get("book", {})
    growth = payload.get("growth_target_pct", 0)

    per_tier = []
    total_required_now = 0
    total_required_future = 0
    total_current = 0
    total_cost_now = 0
    total_cost_future = 0

    for tier_key in ("strategic", "enterprise", "mid_market", "smb_long_tail"):
        tier_book = book.get(tier_key, {})
        model = COVERAGE_MODELS[tier_key]

        req_now = required_csms(tier_book, model)

        # Future book (12mo with growth)
        future_arr = tier_book.get("total_arr_usd", 0) * (1 + growth)
        future_accounts = math.ceil(tier_book.get("customer_count", 0) * (1 + growth))
        future_book = {"total_arr_usd": future_arr, "customer_count": future_accounts}
        req_future = required_csms(future_book, model)

        current = tier_book.get("current_csm_count", 0)
        gap_now = req_now["required"] - current
        gap_future = req_future["required"] - current

        per_tier.append({
            "tier": tier_key,
            "model": model["model"],
            "arr_per_csm_target": model["arr_per_csm_target"],
            "current_arr": tier_book.get("total_arr_usd", 0),
            "current_customers": tier_book.get("customer_count", 0),
            "current_csm_count": current,
            "required_csm_now": req_now["required"],
            "required_csm_12mo": req_future["required"],
            "binding_constraint": req_now["binding_constraint"],
            "gap_now": gap_now,
            "gap_12mo": gap_future,
            "annual_cost_required_now": req_now["required"] * model["fully_loaded_cost_yr"],
            "annual_cost_required_12mo": req_future["required"] * model["fully_loaded_cost_yr"],
        })

        total_required_now += req_now["required"]
        total_required_future += req_future["required"]
        total_current += current
        total_cost_now += req_now["required"] * model["fully_loaded_cost_yr"]
        total_cost_future += req_future["required"] * model["fully_loaded_cost_yr"]

    # Manager trigger: a CS manager is needed when a single function has 5+ ICs
    manager_triggers = []
    for t in per_tier:
        if t["required_csm_12mo"] >= 5:
            manager_triggers.append({
                "tier": t["tier"],
                "trigger": "5+ ICs in tier",
                "recommendation": f"Add CS manager for {t['tier']} when scaling to {t['required_csm_12mo']}+ CSMs",
            })
    # Overall function trigger
    if total_required_future >= 8 and not manager_triggers:
        manager_triggers.append({
            "tier": "overall",
            "trigger": "8+ CSMs across team",
            "recommendation": "Add CS manager / Head of CS",
        })

    # Hiring sequencing (largest gap first, but cap at one hire per quarter per tier)
    hiring_plan = []
    sorted_gaps = sorted(per_tier, key=lambda x: -x["gap_12mo"])
    quarter = 1
    for t in sorted_gaps:
        if t["gap_12mo"] <= 0:
            continue
        for i in range(t["gap_12mo"]):
            hiring_plan.append({
                "quarter": f"Q{quarter}",
                "tier": t["tier"],
                "role": f"CSM ({t['model']})",
            })
            quarter = (quarter % 4) + 1

    return {
        "per_tier": per_tier,
        "manager_triggers": manager_triggers,
        "hiring_plan_12mo": hiring_plan,
        "totals": {
            "current_csm_count": total_current,
            "required_csm_now": total_required_now,
            "required_csm_12mo": total_required_future,
            "gap_now": total_required_now - total_current,
            "gap_12mo": total_required_future - total_current,
            "annual_cost_required_now": total_cost_now,
            "annual_cost_required_12mo": total_cost_future,
            "growth_target_pct": payload.get("growth_target_pct", 0),
        },
    }


def render_text(result: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("CS TEAM COVERAGE CALCULATION")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")

    t = result["totals"]
    lines.append(f"Book growth assumption (12mo): {t['growth_target_pct']*100:.0f}%")
    lines.append("")
    lines.append(f"Current CSMs: {t['current_csm_count']}")
    lines.append(f"Required now: {t['required_csm_now']}  (gap: {t['gap_now']:+d})")
    lines.append(f"Required in 12mo: {t['required_csm_12mo']}  (gap: {t['gap_12mo']:+d})")
    lines.append("")
    lines.append(f"Annual CSM cost (now): ${t['annual_cost_required_now']:,}")
    lines.append(f"Annual CSM cost (12mo at growth): ${t['annual_cost_required_12mo']:,}")
    lines.append("")
    lines.append("-" * 72)
    lines.append("PER-TIER BREAKDOWN:")
    lines.append("")

    for r in result["per_tier"]:
        gap_marker = "⚠️ " if r["gap_now"] > 0 else "✓"
        lines.append(f"  {r['tier']:<16} {r['model']}")
        lines.append(f"    Book: ${r['current_arr']:,.0f} across {r['current_customers']} customers")
        lines.append(f"    Target ratio: ${r['arr_per_csm_target']:,}/CSM (binding: {r['binding_constraint']})")
        lines.append(f"    Current CSMs: {r['current_csm_count']}  |  Required now: {r['required_csm_now']}  |  Required 12mo: {r['required_csm_12mo']}")
        lines.append(f"    {gap_marker} Gap now: {r['gap_now']:+d}  |  Gap 12mo: {r['gap_12mo']:+d}")
        lines.append("")

    lines.append("-" * 72)

    if result["manager_triggers"]:
        lines.append("MANAGER TRIGGER(S):")
        for mt in result["manager_triggers"]:
            lines.append(f"  • {mt['tier']:<12} — {mt['trigger']}: {mt['recommendation']}")
        lines.append("")

    if result["hiring_plan_12mo"]:
        lines.append(f"12-MONTH HIRING PLAN ({len(result['hiring_plan_12mo'])} hires):")
        for h in result["hiring_plan_12mo"]:
            lines.append(f"  {h['quarter']}: {h['role']:<45} (tier: {h['tier']})")
        lines.append("")

    lines.append("-" * 72)
    lines.append("REMINDER: ARR-per-CSM ratios are starting points, not laws. ACV, product complexity,")
    lines.append("and customer maturity shift the ratios materially. Re-run quarterly with updated book.")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Calculate CS team headcount per coverage model + 12-month hiring plan.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to book JSON (uses embedded sample if omitted)")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    args = parser.parse_args()

    if args.path:
        try:
            with open(args.path, "r", encoding="utf-8") as f:
                payload = json.load(f)
            source = args.path
        except (IOError, OSError) as e:
            print(f"error: could not read {args.path}: {e}", file=sys.stderr)
            return 1
        except json.JSONDecodeError as e:
            print(f"error: invalid JSON in {args.path}: {e}", file=sys.stderr)
            return 1
    else:
        payload = SAMPLE
        source = "<embedded sample: 450-customer B2B SaaS book at $6.9M ARR>"

    result = analyze(payload)

    if args.output == "json":
        print(json.dumps({"source": source, **result}, indent=2))
    else:
        print(render_text(result, source))

    return 0


if __name__ == "__main__":
    sys.exit(main())
