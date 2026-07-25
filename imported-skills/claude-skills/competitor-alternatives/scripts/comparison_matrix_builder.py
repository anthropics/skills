#!/usr/bin/env python3
"""
comparison_matrix_builder.py — Competitive Feature Comparison Matrix Builder
100% stdlib, no pip installs required.

Usage:
    python3 comparison_matrix_builder.py                        # demo mode
    python3 comparison_matrix_builder.py --input matrix.json
    python3 comparison_matrix_builder.py --input matrix.json --json
    python3 comparison_matrix_builder.py --input matrix.json --markdown > comparison.md

matrix.json format:
    {
      "your_product": "YourProduct",
      "features": [
        {
          "name": "SSO / SAML",
          "category": "Security",
          "your_status": "full",           # full | partial | no | planned
          "competitors": {
            "CompetitorA": "no",
            "CompetitorB": "partial",
            "CompetitorC": "full"
          },
          "notes": "Enterprise tier only"  # optional
        }
      ]
    }
"""

import argparse
import json
import sys
from collections import defaultdict


# ---------------------------------------------------------------------------
# Status helpers
# ---------------------------------------------------------------------------

STATUS_SCORE = {
    "full":    2,
    "partial": 1,
    "no":      0,
    "planned": 0,  # planned ≠ shipped; conservative scoring
}

STATUS_LABEL = {
    "full":    "✅",
    "partial": "🔶",
    "no":      "❌",
    "planned": "🗓",
}

STATUS_TEXT = {
    "full":    "Full",
    "partial": "Partial",
    "no":      "No",
    "planned": "Planned",
}

FEATURE_IMPORTANCE = {
    # Generic defaults — override per-feature with "weight" in JSON
    "default": 1,
}


# ---------------------------------------------------------------------------
# Core builder
# ---------------------------------------------------------------------------

def normalise_status(s: str) -> str:
    s = (s or "no").strip().lower()
    return s if s in STATUS_SCORE else "no"


def build_matrix(data: dict) -> dict:
    your_product = data.get("your_product", "Your Product")
    features     = data.get("features", [])

    if not features:
        raise ValueError("No features provided in input.")

    # Collect competitor names (ordered, deduplicated)
    competitors = []
    seen        = set()
    for f in features:
        for c in f.get("competitors", {}):
            if c not in seen:
                competitors.append(c)
                seen.add(c)

    categories = sorted(set(f.get("category", "General") for f in features))

    # --- per-feature analysis ---
    feature_rows = []
    for f in features:
        fname     = f.get("name", "?")
        category  = f.get("category", "General")
        weight    = f.get("weight", 1)
        your_raw  = normalise_status(f.get("your_status", "no"))
        your_s    = STATUS_SCORE[your_raw]
        comp_raw  = {c: normalise_status(f.get("competitors", {}).get(c, "no"))
                     for c in competitors}
        comp_s    = {c: STATUS_SCORE[comp_raw[c]] for c in competitors}

        you_win   = all(your_s > comp_s[c] for c in competitors) if competitors else False
        you_lose  = any(your_s < comp_s[c] for c in competitors)
        your_max  = max(comp_s.values()) if comp_s else 0
        advantage = your_s - your_max   # positive = you're better overall

        feature_rows.append({
            "name":          fname,
            "category":      category,
            "weight":        weight,
            "your_status":   your_raw,
            "your_score":    your_s,
            "competitors":   comp_raw,
            "comp_scores":   comp_s,
            "you_win":       you_win,
            "you_lose":      you_lose,
            "advantage":     advantage,
            "notes":         f.get("notes", ""),
        })

    # --- competitive scores per competitor ---
    comp_scores = {}
    for c in competitors:
        wins   = sum(1 for r in feature_rows if r["your_score"] > r["comp_scores"].get(c, 0))
        ties   = sum(1 for r in feature_rows if r["your_score"] == r["comp_scores"].get(c, 0))
        losses = sum(1 for r in feature_rows if r["your_score"] < r["comp_scores"].get(c, 0))
        total  = len(feature_rows)
        score  = round((wins / total) * 100) if total else 0
        comp_scores[c] = {
            "wins": wins, "ties": ties, "losses": losses,
            "win_pct": score,
            "verdict": _verdict(score),
        }

    # Overall competitive score (average win% across all competitors)
    overall_win_pct = (
        round(sum(v["win_pct"] for v in comp_scores.values()) / len(comp_scores))
        if comp_scores else 0
    )

    # Advantages and gaps
    advantages = [r["name"] for r in feature_rows if r["advantage"] > 0]
    gaps       = [r["name"] for r in feature_rows if r["advantage"] < 0]
    parity     = [r["name"] for r in feature_rows if r["advantage"] == 0]

    return {
        "meta": {
            "your_product":     your_product,
            "competitors":      competitors,
            "categories":       categories,
            "total_features":   len(feature_rows),
            "overall_win_pct":  overall_win_pct,
            "verdict":          _verdict(overall_win_pct),
        },
        "competitor_scores": comp_scores,
        "advantages":        advantages,
        "gaps":              gaps,
        "parity":            parity,
        "features":          feature_rows,
    }


def _verdict(win_pct: int) -> str:
    if win_pct >= 70: return "Strong advantage"
    if win_pct >= 50: return "Slight advantage"
    if win_pct >= 35: return "Competitive parity"
    return "Trailing"


# ---------------------------------------------------------------------------
# Markdown output
# ---------------------------------------------------------------------------

def build_markdown(result: dict) -> str:
    m    = result["meta"]
    rows = result["features"]
    comp = m["competitors"]

    lines = []
    lines.append(f"# Feature Comparison: {m['your_product']} vs Competitors\n")
    lines.append(f"_Generated by comparison_matrix_builder.py — {m['total_features']} features, "
                 f"{len(comp)} competitor(s)_\n")

    # Summary table
    lines.append("## Competitive Score Summary\n")
    lines.append("| Competitor | You Win | Tie | You Lose | Win % | Verdict |")
    lines.append("|---|---|---|---|---|---|")
    for c, s in result["competitor_scores"].items():
        lines.append(f"| {c} | {s['wins']} | {s['ties']} | {s['losses']} | "
                     f"**{s['win_pct']}%** | {s['verdict']} |")
    lines.append(f"\n**Overall win rate: {m['overall_win_pct']}% — {m['verdict']}**\n")

    # Feature matrix by category
    lines.append("## Feature Matrix\n")
    header = f"| Feature | {m['your_product']} | " + " | ".join(comp) + " | Notes |"
    sep    = "|---|---|" + "|".join(["---"] * len(comp)) + "|---|"
    lines.append(header)
    lines.append(sep)

    current_cat = None
    for r in rows:
        cat = r["category"]
        if cat != current_cat:
            lines.append(f"| **{cat}** | | " + " | ".join([""] * len(comp)) + " |  |")
            current_cat = cat
        you_icon  = STATUS_LABEL[r["your_status"]]
        comp_icons = " | ".join(STATUS_LABEL[r["competitors"].get(c, "no")] for c in comp)
        note      = r["notes"] or ""
        # Highlight row if it's a unique advantage
        fname = f"**{r['name']}**" if r["advantage"] > 0 else r["name"]
        lines.append(f"| {fname} | {you_icon} | {comp_icons} | {note} |")

    lines.append("")

    # Advantages
    if result["advantages"]:
        lines.append("## ✅ Your Advantages\n")
        for a in result["advantages"]:
            lines.append(f"- {a}")
        lines.append("")

    # Gaps
    if result["gaps"]:
        lines.append("## ⚠️ Feature Gaps (competitors ahead)\n")
        for g in result["gaps"]:
            lines.append(f"- {g}")
        lines.append("")

    # Legend
    lines.append("## Legend\n")
    for k, v in STATUS_LABEL.items():
        lines.append(f"- {v} {STATUS_TEXT[k]}")
    lines.append("")

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Pretty terminal output
# ---------------------------------------------------------------------------

def pretty_print(result: dict) -> None:
    m = result["meta"]
    print("\n" + "=" * 70)
    print(f"  COMPETITIVE MATRIX: {m['your_product'].upper()} vs {', '.join(m['competitors'])}")
    print("=" * 70)
    print(f"\n  Total features analysed : {m['total_features']}")
    print(f"  Overall win rate        : {m['overall_win_pct']}%  ({m['verdict']})")

    print(f"\n{'─'*70}")
    print(f"  {'COMPETITOR':<22}  {'WIN%':>5}  {'WINS':>5}  {'TIES':>5}  {'LOSSES':>7}  VERDICT")
    print(f"{'─'*70}")
    for c, s in result["competitor_scores"].items():
        bar = "█" * (s["win_pct"] // 10) + "░" * (10 - s["win_pct"] // 10)
        print(f"  {c:<22}  {s['win_pct']:>4}%  {s['wins']:>5}  {s['ties']:>5}  "
              f"{s['losses']:>7}  {bar}  {s['verdict']}")

    print(f"\n{'─'*70}")
    col_w = 20
    header = f"  {'FEATURE':<28} | {'YOU':^8}"
    for c in m["competitors"]:
        header += f" | {c[:8]:^8}"
    print(header)
    print("─" * (30 + 11 * (1 + len(m["competitors"]))))

    current_cat = None
    for r in result["features"]:
        if r["category"] != current_cat:
            print(f"\n  [{r['category']}]")
            current_cat = r["category"]
        you_icon  = STATUS_LABEL[r["your_status"]]
        line = f"  {'  '+r['name']:<28} | {you_icon:^8}"
        for c in m["competitors"]:
            ci = STATUS_LABEL[r["competitors"].get(c, "no")]
            line += f" | {ci:^8}"
        if r["advantage"] > 0:
            line += "  ← advantage"
        elif r["advantage"] < 0:
            line += "  ← gap"
        print(line)

    print(f"\n  ✅ YOUR ADVANTAGES  ({len(result['advantages'])} features)")
    for a in result["advantages"]:
        print(f"    • {a}")

    print(f"\n  ⚠️  FEATURE GAPS  ({len(result['gaps'])} features)")
    for g in result["gaps"]:
        print(f"    • {g}")

    print(f"\n  Legend: {STATUS_LABEL['full']} Full  {STATUS_LABEL['partial']} Partial  "
          f"{STATUS_LABEL['no']} No  {STATUS_LABEL['planned']} Planned\n")


# ---------------------------------------------------------------------------
# Sample data
# ---------------------------------------------------------------------------

DEMO_DATA = {
    "your_product": "SwiftBase",
    "features": [
        {"name": "SSO / SAML",          "category": "Security",     "weight": 3, "your_status": "full",    "competitors": {"AcmeSaaS": "no",      "ProStack": "partial"}, "notes": "All plans"},
        {"name": "2FA / MFA",            "category": "Security",     "weight": 3, "your_status": "full",    "competitors": {"AcmeSaaS": "full",    "ProStack": "full"},    "notes": ""},
        {"name": "SOC 2 Type II",        "category": "Security",     "weight": 3, "your_status": "planned", "competitors": {"AcmeSaaS": "full",    "ProStack": "no"},      "notes": "Q3 target"},
        {"name": "Role-based access",    "category": "Security",     "weight": 2, "your_status": "full",    "competitors": {"AcmeSaaS": "partial", "ProStack": "full"},    "notes": ""},
        {"name": "REST API",             "category": "Integrations", "weight": 3, "your_status": "full",    "competitors": {"AcmeSaaS": "full",    "ProStack": "full"},    "notes": ""},
        {"name": "GraphQL API",          "category": "Integrations", "weight": 2, "your_status": "full",    "competitors": {"AcmeSaaS": "no",      "ProStack": "partial"}, "notes": ""},
        {"name": "Zapier Integration",   "category": "Integrations", "weight": 2, "your_status": "partial", "competitors": {"AcmeSaaS": "full",    "ProStack": "full"},    "notes": "10 zaps only"},
        {"name": "Webhooks",             "category": "Integrations", "weight": 2, "your_status": "full",    "competitors": {"AcmeSaaS": "full",    "ProStack": "no"},      "notes": ""},
        {"name": "Custom domain",        "category": "Branding",     "weight": 2, "your_status": "full",    "competitors": {"AcmeSaaS": "partial", "ProStack": "full"},    "notes": ""},
        {"name": "White-label / rebrand","category": "Branding",     "weight": 2, "your_status": "full",    "competitors": {"AcmeSaaS": "no",      "ProStack": "partial"}, "notes": "Agency plan"},
        {"name": "Priority support",     "category": "Support",      "weight": 2, "your_status": "full",    "competitors": {"AcmeSaaS": "partial", "ProStack": "full"},    "notes": "24/7"},
        {"name": "Dedicated CSM",        "category": "Support",      "weight": 2, "your_status": "no",      "competitors": {"AcmeSaaS": "full",    "ProStack": "full"},    "notes": "Enterprise only"},
        {"name": "SLA guarantee",        "category": "Support",      "weight": 3, "your_status": "no",      "competitors": {"AcmeSaaS": "full",    "ProStack": "no"},      "notes": "Roadmap"},
    ],
}


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def parse_args():
    parser = argparse.ArgumentParser(
        description="Build a competitive feature comparison matrix (stdlib only).",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("--input",    type=str, default=None,
                        help="Path to JSON input file")
    parser.add_argument("--json",     action="store_true",
                        help="Output analysis as JSON")
    parser.add_argument("--markdown", action="store_true",
                        help="Output comparison table as Markdown")
    return parser.parse_args()


def main():
    args = parse_args()

    if args.input:
        with open(args.input) as f:
            data = json.load(f)
    else:
        print("🔬  DEMO MODE — using sample SaaS product matrix\n", file=sys.stderr)
        data = DEMO_DATA

    result = build_matrix(data)

    if args.json:
        # Serialise (remove non-JSON-safe keys)
        print(json.dumps(result, indent=2))
    elif args.markdown:
        print(build_markdown(result))
    else:
        pretty_print(result)
        print("\n💡  TIP: Re-run with --markdown to get a copyable Markdown table.\n")


if __name__ == "__main__":
    main()
