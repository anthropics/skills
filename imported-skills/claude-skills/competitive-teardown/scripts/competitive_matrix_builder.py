#!/usr/bin/env python3
"""Competitive Matrix Builder — Analyze and score competitors across feature dimensions.

Generates weighted competitive matrices, gap analysis, and positioning insights
from structured competitor data.

Usage:
    python competitive_matrix_builder.py competitors.json --format json
    python competitive_matrix_builder.py competitors.json --format text
    python competitive_matrix_builder.py competitors.json --format text --weights pricing=2,ux=1.5
"""

import argparse
import json
import sys
from typing import Dict, List, Any, Optional
from datetime import datetime
from statistics import mean, stdev


def load_competitors(path: str) -> Dict[str, Any]:
    """Load competitor data from JSON file."""
    with open(path, "r") as f:
        return json.load(f)


def normalize_score(value: float, min_val: float = 1.0, max_val: float = 10.0) -> float:
    """Normalize a score to 0-100 scale."""
    return max(0.0, min(100.0, ((value - min_val) / (max_val - min_val)) * 100))


def calculate_weighted_scores(
    competitors: List[Dict[str, Any]],
    dimensions: List[str],
    weights: Optional[Dict[str, float]] = None
) -> List[Dict[str, Any]]:
    """Calculate weighted scores for each competitor across dimensions."""
    if weights is None:
        weights = {d: 1.0 for d in dimensions}

    results = []
    for comp in competitors:
        scores = comp.get("scores", {})
        weighted_total = 0.0
        weight_sum = 0.0
        dimension_results = {}

        for dim in dimensions:
            raw = scores.get(dim, 0)
            w = weights.get(dim, 1.0)
            normalized = normalize_score(raw)
            weighted = normalized * w
            weighted_total += weighted
            weight_sum += w
            dimension_results[dim] = {
                "raw": raw,
                "normalized": round(normalized, 1),
                "weight": w,
                "weighted": round(weighted, 1)
            }

        overall = round(weighted_total / weight_sum, 1) if weight_sum > 0 else 0
        results.append({
            "name": comp["name"],
            "overall_score": overall,
            "dimensions": dimension_results,
            "tier": classify_tier(overall),
            "pricing": comp.get("pricing", {}),
            "strengths": comp.get("strengths", []),
            "weaknesses": comp.get("weaknesses", [])
        })

    results.sort(key=lambda x: x["overall_score"], reverse=True)
    return results


def classify_tier(score: float) -> str:
    """Classify competitor into tier based on overall score."""
    if score >= 80:
        return "Leader"
    elif score >= 60:
        return "Strong Competitor"
    elif score >= 40:
        return "Viable Alternative"
    elif score >= 20:
        return "Niche Player"
    else:
        return "Weak"


def gap_analysis(
    your_scores: Dict[str, float],
    competitor_scores: List[Dict[str, Any]],
    dimensions: List[str]
) -> Dict[str, Any]:
    """Identify gaps between your product and competitors."""
    gaps = {}
    for dim in dimensions:
        your_val = your_scores.get(dim, 0)
        comp_vals = [c["dimensions"][dim]["raw"] for c in competitor_scores if dim in c.get("dimensions", {})]
        if not comp_vals:
            continue

        avg_comp = mean(comp_vals)
        best_comp = max(comp_vals)
        gap_to_avg = round(your_val - avg_comp, 1)
        gap_to_best = round(your_val - best_comp, 1)

        gaps[dim] = {
            "your_score": your_val,
            "competitor_avg": round(avg_comp, 1),
            "competitor_best": best_comp,
            "gap_to_avg": gap_to_avg,
            "gap_to_best": gap_to_best,
            "status": "ahead" if gap_to_avg > 0.5 else ("behind" if gap_to_avg < -0.5 else "parity"),
            "priority": "high" if gap_to_best < -2 else ("medium" if gap_to_best < -1 else "low")
        }

    return {
        "gaps": gaps,
        "biggest_opportunities": sorted(
            [{"dimension": k, **v} for k, v in gaps.items() if v["status"] == "behind"],
            key=lambda x: x["gap_to_best"]
        )[:5],
        "competitive_advantages": sorted(
            [{"dimension": k, **v} for k, v in gaps.items() if v["status"] == "ahead"],
            key=lambda x: -x["gap_to_avg"]
        )[:5]
    }


def positioning_analysis(scored: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Generate positioning insights from scored competitors."""
    scores = [c["overall_score"] for c in scored]
    return {
        "market_leaders": [c["name"] for c in scored if c["tier"] == "Leader"],
        "your_rank": next((i + 1 for i, c in enumerate(scored) if c.get("is_you")), None),
        "total_competitors": len(scored),
        "score_distribution": {
            "mean": round(mean(scores), 1) if scores else 0,
            "stdev": round(stdev(scores), 1) if len(scores) > 1 else 0,
            "min": round(min(scores), 1) if scores else 0,
            "max": round(max(scores), 1) if scores else 0
        },
        "tier_distribution": {
            tier: len([c for c in scored if c["tier"] == tier])
            for tier in ["Leader", "Strong Competitor", "Viable Alternative", "Niche Player", "Weak"]
        }
    }


def format_text(result: Dict[str, Any]) -> str:
    """Format results as human-readable text."""
    lines = []
    lines.append("=" * 70)
    lines.append("COMPETITIVE MATRIX ANALYSIS")
    lines.append(f"Generated: {result['generated_at']}")
    lines.append("=" * 70)

    # Ranking table
    lines.append("\n## COMPETITIVE RANKING\n")
    lines.append(f"{'Rank':<6}{'Competitor':<25}{'Score':<10}{'Tier':<20}")
    lines.append("-" * 61)
    for i, c in enumerate(result["scored_competitors"], 1):
        marker = " ← YOU" if c.get("is_you") else ""
        lines.append(f"{i:<6}{c['name']:<25}{c['overall_score']:<10}{c['tier']:<20}{marker}")

    # Dimension breakdown
    lines.append("\n## DIMENSION BREAKDOWN\n")
    dims = result["dimensions"]
    header = f"{'Dimension':<20}" + "".join(f"{c['name'][:12]:<14}" for c in result["scored_competitors"])
    lines.append(header)
    lines.append("-" * len(header))
    for dim in dims:
        row = f"{dim:<20}"
        for c in result["scored_competitors"]:
            val = c["dimensions"].get(dim, {}).get("raw", "N/A")
            row += f"{val:<14}"
        lines.append(row)

    # Gap analysis
    if result.get("gap_analysis"):
        ga = result["gap_analysis"]
        if ga["biggest_opportunities"]:
            lines.append("\n## BIGGEST OPPORTUNITIES (where you're behind)\n")
            for opp in ga["biggest_opportunities"]:
                lines.append(f"  • {opp['dimension']}: You={opp['your_score']}, "
                           f"Best={opp['competitor_best']}, Gap={opp['gap_to_best']} "
                           f"[{opp['priority'].upper()} priority]")

        if ga["competitive_advantages"]:
            lines.append("\n## COMPETITIVE ADVANTAGES (where you lead)\n")
            for adv in ga["competitive_advantages"]:
                lines.append(f"  • {adv['dimension']}: You={adv['your_score']}, "
                           f"Avg={adv['competitor_avg']}, Lead=+{adv['gap_to_avg']}")

    # Positioning
    pos = result.get("positioning", {})
    if pos:
        lines.append("\n## MARKET POSITIONING\n")
        lines.append(f"  Market Leaders: {', '.join(pos.get('market_leaders', ['None']))}")
        if pos.get("your_rank"):
            lines.append(f"  Your Rank: #{pos['your_rank']} of {pos['total_competitors']}")
        dist = pos.get("score_distribution", {})
        lines.append(f"  Score Range: {dist.get('min', 0)} - {dist.get('max', 0)} "
                    f"(avg: {dist.get('mean', 0)}, stdev: {dist.get('stdev', 0)})")

    lines.append("\n" + "=" * 70)
    return "\n".join(lines)


def build_matrix(data: Dict[str, Any], weight_overrides: Optional[Dict[str, float]] = None) -> Dict[str, Any]:
    """Main entry: build competitive matrix from input data."""
    competitors = data.get("competitors", [])
    dimensions = data.get("dimensions", [])
    your_product = data.get("your_product", {})

    if not competitors:
        return {"error": "No competitors provided"}
    if not dimensions:
        # Auto-detect from first competitor's scores
        dimensions = list(competitors[0].get("scores", {}).keys())

    weights = data.get("weights", {})
    if weight_overrides:
        weights.update(weight_overrides)

    # Include your product in scoring if provided
    all_entries = list(competitors)
    if your_product:
        your_product["is_you"] = True
        all_entries.insert(0, your_product)

    scored = calculate_weighted_scores(all_entries, dimensions, weights)

    # Mark your product
    for s in scored:
        if any(c.get("is_you") and c["name"] == s["name"] for c in all_entries):
            s["is_you"] = True

    result = {
        "generated_at": datetime.now().isoformat(),
        "dimensions": dimensions,
        "weights": weights if weights else {d: 1.0 for d in dimensions},
        "scored_competitors": scored,
        "positioning": positioning_analysis(scored)
    }

    if your_product:
        result["gap_analysis"] = gap_analysis(
            your_product.get("scores", {}), scored, dimensions
        )

    return result


def parse_weights(weight_str: str) -> Dict[str, float]:
    """Parse weight string like 'pricing=2,ux=1.5' into dict."""
    weights = {}
    for pair in weight_str.split(","):
        if "=" in pair:
            k, v = pair.split("=", 1)
            weights[k.strip()] = float(v.strip())
    return weights


def main():
    parser = argparse.ArgumentParser(
        description="Build competitive matrix with scoring and gap analysis"
    )
    parser.add_argument("input", help="Path to competitors JSON file")
    parser.add_argument("--format", choices=["json", "text"], default="text",
                       help="Output format (default: text)")
    parser.add_argument("--weights", type=str, default=None,
                       help="Weight overrides: 'dim1=2.0,dim2=1.5'")
    parser.add_argument("--output", type=str, default=None,
                       help="Output file path (default: stdout)")

    args = parser.parse_args()

    data = load_competitors(args.input)
    weight_overrides = parse_weights(args.weights) if args.weights else None
    result = build_matrix(data, weight_overrides)

    if args.format == "json":
        output = json.dumps(result, indent=2)
    else:
        output = format_text(result)

    if args.output:
        with open(args.output, "w") as f:
            f.write(output)
        print(f"Output written to {args.output}")
    else:
        print(output)


if __name__ == "__main__":
    main()
