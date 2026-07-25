#!/usr/bin/env python3
"""capex_vs_opex_router.py - Decision-SUPPORT for R&D capitalize-vs-expense treatment.

Stdlib-only. Deterministic. NO LLM calls. This tool NEVER books an entry and NEVER
auto-decides accounting treatment. It scores each cost item against capitalization
criteria and ROUTES it to a named finance owner for the actual determination.

Criteria reflect IAS 38 (development-phase capitalization test) and US GAAP ASC 730
(R&D expensed as incurred) / ASC 985-20 (internal-use & sold software). The six IAS 38
development-phase conditions:
  1. technical feasibility established
  2. intention to complete
  3. ability to use or sell
  4. probable future economic benefit
  5. adequate resources to complete
  6. reliable measurement of expenditure

Verdicts:
  - CAPITALIZE-CANDIDATE   (development phase, all criteria met) -> still routes to finance owner
  - EXPENSE                (research phase, or criteria not met)
  - FINANCE-OWNER-REVIEW   (ambiguous / partial criteria)

Usage:
    python3 capex_vs_opex_router.py --sample
    python3 capex_vs_opex_router.py --input costs.json --standard ifrs
    python3 capex_vs_opex_router.py --input costs.json --standard usgaap --output json
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

IAS38_CRITERIA = [
    "technical_feasibility",
    "intention_to_complete",
    "ability_to_use_or_sell",
    "probable_future_benefit",
    "adequate_resources",
    "reliable_measurement",
]

# Profiles only annotate context; they do not change the accounting test.
PROFILES = {
    "pharma-rd": "Most drug R&D is expensed; capitalization rare pre-approval.",
    "biotech": "Similar to pharma; pre-approval development typically expensed.",
    "medtech": "Some development capitalizable post-feasibility under IFRS.",
    "deep-tech": "Prototype-to-product transition is the key feasibility line.",
    "software-rd": "ASC 985-20 / IAS 38: capitalize after technological feasibility / working model.",
    "university-lab": "Grant-funded research almost always expensed per funder terms.",
}

SAMPLE = {
    "standard": "ifrs",
    "items": [
        {
            "name": "Exploratory target screening",
            "phase": "research",
            "criteria": {},
        },
        {
            "name": "Pilot-line tooling for validated design",
            "phase": "development",
            "criteria": {
                "technical_feasibility": True, "intention_to_complete": True,
                "ability_to_use_or_sell": True, "probable_future_benefit": True,
                "adequate_resources": True, "reliable_measurement": True,
            },
        },
        {
            "name": "Software build (post working-model, pre-release)",
            "phase": "development",
            "criteria": {
                "technical_feasibility": True, "intention_to_complete": True,
                "ability_to_use_or_sell": True, "probable_future_benefit": True,
                "adequate_resources": False, "reliable_measurement": True,
            },
        },
    ],
}


def route_item(item: dict, standard: str) -> dict:
    phase = (item.get("phase") or "").lower()
    crit = item.get("criteria", {}) or {}
    met = [c for c in IAS38_CRITERIA if crit.get(c)]
    missing = [c for c in IAS38_CRITERIA if not crit.get(c)]

    # US GAAP ASC 730: R&D expensed as incurred (software is the main exception via ASC 985-20).
    if standard == "usgaap" and phase != "software-development":
        verdict = "EXPENSE"
        rationale = "ASC 730: R&D is expensed as incurred (non-software). Confirm software exceptions separately."
        owner = "R&D Finance Controller"
    elif phase == "research":
        verdict = "EXPENSE"
        rationale = "Research phase: cannot capitalize (IAS 38.54)."
        owner = "R&D Finance Controller"
    elif phase in ("development", "software-development") and not missing:
        verdict = "CAPITALIZE-CANDIDATE"
        rationale = "Development phase with all 6 IAS 38 criteria asserted. Routed for finance confirmation."
        owner = "R&D Finance Controller + External Auditor sign-off"
    else:
        verdict = "FINANCE-OWNER-REVIEW"
        rationale = f"Development phase but {len(missing)} criteria unmet/unstated: {', '.join(missing) or 'n/a'}."
        owner = "R&D Finance Controller"

    return {
        "name": item.get("name", "UNNAMED"),
        "phase": phase or "UNSPECIFIED",
        "criteria_met": met,
        "criteria_missing": missing,
        "verdict": verdict,
        "rationale": rationale,
        "named_owner": owner,
    }


def route(data: dict, standard: str, profile: str) -> dict:
    if profile not in PROFILES:
        raise ValueError(f"Unknown profile '{profile}'. Choose from {list(PROFILES)}.")
    items = [route_item(i, standard) for i in data.get("items", [])]
    return {
        "standard": standard,
        "profile": profile,
        "profile_note": PROFILES[profile],
        "items": items,
        "disclaimer": "DECISION SUPPORT ONLY. This tool does not book entries or decide treatment. "
                      "A named finance owner (and auditor where required) makes the determination.",
    }


def _render_human(r: dict) -> str:
    lines = [f"Capitalize-vs-Expense routing  (standard: {r['standard']}, profile: {r['profile']})",
             f"  {r['profile_note']}", ""]
    for it in r["items"]:
        lines.append(f"[{it['verdict']}] {it['name']}  (phase: {it['phase']})")
        lines.append(f"      {it['rationale']}")
        if it["criteria_missing"]:
            lines.append(f"      missing/unstated: {', '.join(it['criteria_missing'])}")
        lines.append(f"      -> route to: {it['named_owner']}")
        lines.append("")
    lines.append(f"!! {r['disclaimer']}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Route R&D costs to capitalize/expense/review (DECISION SUPPORT ONLY).")
    p.add_argument("--input", help="Path to JSON with items[]")
    p.add_argument("--standard", default=None, choices=["ifrs", "usgaap"],
                   help="overrides onboarding accounting_standard")
    p.add_argument("--profile", default=None, choices=list(PROFILES),
                   help="overrides onboarding default_profile")
    p.add_argument("--output", choices=["human", "json"], default="human")
    p.add_argument("--sample", action="store_true", help="use the embedded sample")
    args = p.parse_args(argv)

    conf = _cfg.load_config() if _cfg else {}
    profile = args.profile or conf.get("default_profile", "biotech")
    cli_standard = args.standard or conf.get("accounting_standard", "ifrs")
    data = SAMPLE if (args.sample or not args.input) else json.load(open(args.input))
    standard = data.get("standard", cli_standard) if (args.sample or not args.input) else cli_standard
    try:
        result = route(data, standard, profile)
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    finance_owner = conf.get("finance_owner")
    if finance_owner:
        for it in result["items"]:
            it["named_owner"] = it["named_owner"].replace(
                "R&D Finance Controller", f"R&D Finance Controller ({finance_owner})")

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(_render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
