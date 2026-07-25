#!/usr/bin/env python3
"""
SaaS Metrics Calculator — zero external dependencies (stdlib only).

Usage (interactive): python metrics_calculator.py
Usage (CLI):         python metrics_calculator.py --mrr 48000 --customers 160 --json
Usage (import):
    from metrics_calculator import calculate, report
    results = calculate(mrr=48000, mrr_last=42000, customers=160,
                        churned=4, new_customers=22, sm_spend=18000,
                        gross_margin=0.72)
    print(report(results))
"""

import json
import sys


def calculate(
    mrr=None,
    mrr_last=None,
    customers=None,
    churned=None,
    new_customers=None,
    sm_spend=None,
    gross_margin=0.70,
    expansion_mrr=0,
    churned_mrr=0,
    contraction_mrr=0,
    profit_margin=None,
):
    r, missing = {}, []

    # ── Core revenue ─────────────────────────────────────────────────────────
    if mrr is not None:
        r["MRR"] = round(mrr, 2)
        r["ARR"] = round(mrr * 12, 2)
    else:
        missing.append("ARR/MRR — need current MRR")

    if mrr and customers:
        r["ARPA"] = round(mrr / customers, 2)
    else:
        missing.append("ARPA — need MRR + customer count")

    # ── Growth ────────────────────────────────────────────────────────────────
    if mrr and mrr_last and mrr_last > 0:
        r["MoM_Growth_Pct"] = round(((mrr - mrr_last) / mrr_last) * 100, 2)
    else:
        missing.append("MoM Growth — need last month MRR")

    # ── Churn ─────────────────────────────────────────────────────────────────
    if churned is not None and customers:
        r["Churn_Pct"] = round((churned / customers) * 100, 2)
    else:
        missing.append("Churn Rate — need churned + total customers")

    # ── CAC ───────────────────────────────────────────────────────────────────
    if sm_spend and new_customers and new_customers > 0:
        r["CAC"] = round(sm_spend / new_customers, 2)
    else:
        missing.append("CAC — need S&M spend + new customers")

    # ── LTV ───────────────────────────────────────────────────────────────────
    arpa = r.get("ARPA")
    churn_dec = r.get("Churn_Pct", 0) / 100
    if arpa and churn_dec > 0:
        r["LTV"] = round((arpa / churn_dec) * gross_margin, 2)
    else:
        missing.append("LTV — need ARPA and churn rate")

    # ── LTV:CAC ───────────────────────────────────────────────────────────────
    if r.get("LTV") and r.get("CAC") and r["CAC"] > 0:
        r["LTV_CAC"] = round(r["LTV"] / r["CAC"], 2)
    else:
        missing.append("LTV:CAC — need both LTV and CAC")

    # ── Payback ───────────────────────────────────────────────────────────────
    if r.get("CAC") and arpa and arpa > 0:
        r["Payback_Months"] = round(r["CAC"] / (arpa * gross_margin), 1)
    else:
        missing.append("Payback Period — need CAC and ARPA")

    # ── NRR ───────────────────────────────────────────────────────────────────
    if mrr_last and mrr_last > 0 and (expansion_mrr or churned_mrr or contraction_mrr):
        nrr = ((mrr_last + expansion_mrr - churned_mrr - contraction_mrr) / mrr_last) * 100
        r["NRR_Pct"] = round(nrr, 2)
    elif r.get("Churn_Pct"):
        r["NRR_Est_Pct"] = round((1 - r["Churn_Pct"] / 100) * 100, 2)
        missing.append("NRR (accurate) — using churn-only estimate; provide expansion MRR for full NRR")

    # ── Rule of 40 ────────────────────────────────────────────────────────────
    if r.get("MoM_Growth_Pct") and profit_margin is not None:
        r["Rule_of_40"] = round(r["MoM_Growth_Pct"] * 12 + profit_margin, 1)

    r["_missing"] = missing
    r["_gross_margin"] = gross_margin
    return r


def report(r):
    labels = [
        ("MRR",            "Monthly Recurring Revenue",     "$"),
        ("ARR",            "Annual Recurring Revenue",       "$"),
        ("ARPA",           "Avg Revenue Per Account/mo",     "$"),
        ("MoM_Growth_Pct", "MoM MRR Growth",                "%"),
        ("Churn_Pct",      "Monthly Churn Rate",             "%"),
        ("CAC",            "Customer Acquisition Cost",      "$"),
        ("LTV",            "Customer Lifetime Value",        "$"),
        ("LTV_CAC",        "LTV:CAC Ratio",                  ":1"),
        ("Payback_Months", "CAC Payback Period",             " months"),
        ("NRR_Pct",        "NRR (Net Revenue Retention)",    "%"),
        ("NRR_Est_Pct",    "NRR Estimate (churn-only)",      "%"),
        ("Rule_of_40",     "Rule of 40 Score",               ""),
    ]

    lines = ["=" * 54, "  SAAS METRICS CALCULATOR", "=" * 54, ""]
    for key, label, unit in labels:
        val = r.get(key)
        if val is None:
            continue
        if unit == "$":
            fmt = f"${val:,.2f}"
        elif unit == "%":
            fmt = f"{val}%"
        elif unit == ":1":
            fmt = f"{val}:1"
        else:
            fmt = f"{val}{unit}"
        lines.append(f"  {label:<40} {fmt}")

    if r.get("_missing"):
        lines += ["", "  Missing / estimated:"]
        for m in r["_missing"]:
            lines.append(f"    - {m}")

    lines.append("=" * 54)
    return "\n".join(lines)


# ── Interactive mode ──────────────────────────────────────────────────────────

def _ask(prompt, required=False):
    while True:
        v = input(f"  {prompt}: ").strip()
        if not v:
            if required:
                print("    Required — please enter a value.")
                continue
            return None
        try:
            return float(v)
        except ValueError:
            print("    Enter a number (e.g. 48000 or 72).")


if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description="SaaS Metrics Calculator")
    parser.add_argument("--mrr", type=float, help="Current MRR")
    parser.add_argument("--mrr-last", type=float, help="MRR last month")
    parser.add_argument("--customers", type=int, help="Total active customers")
    parser.add_argument("--churned", type=int, help="Customers churned this month")
    parser.add_argument("--new-customers", type=int, help="New customers acquired")
    parser.add_argument("--sm-spend", type=float, help="Sales & Marketing spend")
    parser.add_argument("--gross-margin", type=float, default=70, help="Gross margin %% (default: 70)")
    parser.add_argument("--expansion-mrr", type=float, default=0, help="Expansion MRR")
    parser.add_argument("--churned-mrr", type=float, default=0, help="Churned MRR")
    parser.add_argument("--contraction-mrr", type=float, default=0, help="Contraction MRR")
    parser.add_argument("--profit-margin", type=float, help="Net profit margin %%")
    parser.add_argument("--json", action="store_true", help="Output JSON format")
    
    args = parser.parse_args()
    
    # CLI mode
    if args.mrr is not None:
        inputs = {
            "mrr": args.mrr,
            "mrr_last": args.mrr_last,
            "customers": args.customers,
            "churned": args.churned,
            "new_customers": args.new_customers,
            "sm_spend": args.sm_spend,
            "gross_margin": args.gross_margin / 100 if args.gross_margin > 1 else args.gross_margin,
            "expansion_mrr": args.expansion_mrr,
            "churned_mrr": args.churned_mrr,
            "contraction_mrr": args.contraction_mrr,
            "profit_margin": args.profit_margin,
        }
        result = calculate(**inputs)
        
        if args.json:
            print(json.dumps(result, indent=2))
        else:
            print("\n" + report(result))
        sys.exit(0)
    
    # Interactive mode
    print("\nSaaS Metrics Calculator  (press Enter to skip)\n")

    gm = _ask("Gross margin % (default 70)", required=False) or 70
    inputs = dict(
        mrr=_ask("Current MRR ($)", required=True),
        mrr_last=_ask("MRR last month ($)"),
        customers=_ask("Total active customers"),
        churned=_ask("Customers churned this month"),
        new_customers=_ask("New customers acquired this month"),
        sm_spend=_ask("Sales & Marketing spend this month ($)"),
        gross_margin=gm / 100 if gm > 1 else gm,
        expansion_mrr=_ask("Expansion MRR (upsells) ($)") or 0,
        churned_mrr=_ask("Churned MRR ($)") or 0,
        contraction_mrr=_ask("Contraction MRR (downgrades) ($)") or 0,
        profit_margin=_ask("Net profit margin % (for Rule of 40, optional)"),
    )

    print("\n" + report(calculate(**inputs)))
