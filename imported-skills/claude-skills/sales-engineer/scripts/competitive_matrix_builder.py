#!/usr/bin/env python3
"""Competitive Matrix Builder - Generate feature comparison matrices and positioning analysis.

Builds feature-by-feature comparison matrices, calculates weighted competitive
scores, identifies differentiators and vulnerabilities, and generates win themes.

Usage:
    python competitive_matrix_builder.py competitive_data.json
    python competitive_matrix_builder.py competitive_data.json --format json
    python competitive_matrix_builder.py competitive_data.json --format text
"""

import argparse
import json
import sys
from typing import Any


# Feature scoring levels
FEATURE_SCORES: dict[str, int] = {
    "full": 3,
    "partial": 2,
    "limited": 1,
    "none": 0,
}

FEATURE_LABELS: dict[int, str] = {
    3: "Full",
    2: "Partial",
    1: "Limited",
    0: "None",
}


def safe_divide(numerator: float, denominator: float, default: float = 0.0) -> float:
    """Safely divide two numbers, returning default if denominator is zero."""
    if denominator == 0:
        return default
    return numerator / denominator


def load_competitive_data(filepath: str) -> dict[str, Any]:
    """Load and validate competitive data from a JSON file.

    Args:
        filepath: Path to the JSON file containing competitive data.

    Returns:
        Parsed competitive data dictionary.

    Raises:
        SystemExit: If the file cannot be read or parsed.
    """
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            data = json.load(f)
    except FileNotFoundError:
        print(f"Error: File not found: {filepath}", file=sys.stderr)
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in {filepath}: {e}", file=sys.stderr)
        sys.exit(1)

    if "categories" not in data:
        print("Error: JSON must contain a 'categories' array.", file=sys.stderr)
        sys.exit(1)

    if "our_product" not in data:
        print("Error: JSON must contain 'our_product' name.", file=sys.stderr)
        sys.exit(1)

    if "competitors" not in data or not data["competitors"]:
        print("Error: JSON must contain a non-empty 'competitors' array.", file=sys.stderr)
        sys.exit(1)

    return data


def normalize_score(score_value: Any) -> int:
    """Normalize a score value to an integer.

    Args:
        score_value: Score as string label or integer.

    Returns:
        Normalized integer score (0-3).
    """
    if isinstance(score_value, str):
        return FEATURE_SCORES.get(score_value.lower(), 0)
    if isinstance(score_value, (int, float)):
        return max(0, min(3, int(score_value)))
    return 0


def build_comparison_matrix(data: dict[str, Any]) -> dict[str, Any]:
    """Build the feature comparison matrix from input data.

    Args:
        data: Competitive data with categories, features, and scores.

    Returns:
        Comparison matrix with per-feature and per-category scores.
    """
    our_product = data["our_product"]
    competitors = data["competitors"]
    all_products = [our_product] + competitors

    matrix: list[dict[str, Any]] = []
    category_summaries: dict[str, dict[str, Any]] = {}

    for category in data["categories"]:
        cat_name = category["name"]
        cat_weight = category.get("weight", 1.0)
        cat_features = category.get("features", [])

        cat_scores: dict[str, list[int]] = {p: [] for p in all_products}

        for feature in cat_features:
            feature_name = feature["name"]
            scores: dict[str, int] = {}

            for product in all_products:
                raw_score = feature.get("scores", {}).get(product, 0)
                scores[product] = normalize_score(raw_score)
                cat_scores[product].append(scores[product])

            # Determine leader for this feature
            max_score = max(scores.values())
            leaders = [p for p, s in scores.items() if s == max_score]

            matrix.append({
                "category": cat_name,
                "feature": feature_name,
                "scores": scores,
                "leaders": leaders,
                "our_score": scores[our_product],
                "max_score": max_score,
                "we_lead": our_product in leaders and len(leaders) == 1,
                "we_trail": scores[our_product] < max_score,
            })

        # Category summary
        cat_product_scores = {}
        for product in all_products:
            product_scores = cat_scores[product]
            total = sum(product_scores)
            max_possible = len(product_scores) * 3
            pct = safe_divide(total, max_possible) * 100
            cat_product_scores[product] = {
                "total_score": total,
                "max_possible": max_possible,
                "percentage": round(pct, 1),
            }

        category_summaries[cat_name] = {
            "weight": cat_weight,
            "feature_count": len(cat_features),
            "product_scores": cat_product_scores,
        }

    return {
        "our_product": our_product,
        "competitors": competitors,
        "all_products": all_products,
        "matrix": matrix,
        "category_summaries": category_summaries,
    }


def compute_competitive_scores(
    comparison: dict[str, Any],
) -> dict[str, dict[str, Any]]:
    """Compute weighted competitive scores for each product.

    Args:
        comparison: Comparison matrix data.

    Returns:
        Product scores with weighted and unweighted totals.
    """
    all_products = comparison["all_products"]
    category_summaries = comparison["category_summaries"]

    product_scores: dict[str, dict[str, float]] = {
        p: {"weighted_total": 0.0, "max_weighted": 0.0, "unweighted_total": 0, "max_unweighted": 0}
        for p in all_products
    }

    for cat_name, cat_data in category_summaries.items():
        weight = cat_data["weight"]
        for product in all_products:
            p_data = cat_data["product_scores"][product]
            product_scores[product]["weighted_total"] += p_data["total_score"] * weight
            product_scores[product]["max_weighted"] += p_data["max_possible"] * weight
            product_scores[product]["unweighted_total"] += p_data["total_score"]
            product_scores[product]["max_unweighted"] += p_data["max_possible"]

    result = {}
    for product in all_products:
        ps = product_scores[product]
        weighted_pct = safe_divide(ps["weighted_total"], ps["max_weighted"]) * 100
        unweighted_pct = safe_divide(ps["unweighted_total"], ps["max_unweighted"]) * 100
        result[product] = {
            "weighted_score": round(weighted_pct, 1),
            "unweighted_score": round(unweighted_pct, 1),
            "weighted_total": round(ps["weighted_total"], 2),
            "max_weighted": round(ps["max_weighted"], 2),
        }

    return result


def identify_differentiators(comparison: dict[str, Any]) -> list[dict[str, Any]]:
    """Identify features where our product leads all competitors.

    Args:
        comparison: Comparison matrix data.

    Returns:
        List of differentiator features with details.
    """
    differentiators = []
    for entry in comparison["matrix"]:
        if entry["we_lead"] and entry["our_score"] >= 2:
            # Calculate gap from nearest competitor
            competitor_scores = [
                entry["scores"][c] for c in comparison["competitors"]
            ]
            max_competitor = max(competitor_scores) if competitor_scores else 0
            gap = entry["our_score"] - max_competitor

            differentiators.append({
                "feature": entry["feature"],
                "category": entry["category"],
                "our_score": entry["our_score"],
                "our_label": FEATURE_LABELS.get(entry["our_score"], "Unknown"),
                "best_competitor_score": max_competitor,
                "gap": gap,
            })

    # Sort by gap size descending
    differentiators.sort(key=lambda d: d["gap"], reverse=True)
    return differentiators


def identify_vulnerabilities(comparison: dict[str, Any]) -> list[dict[str, Any]]:
    """Identify features where competitors lead our product.

    Args:
        comparison: Comparison matrix data.

    Returns:
        List of vulnerability features with details.
    """
    vulnerabilities = []
    for entry in comparison["matrix"]:
        if entry["we_trail"]:
            # Find which competitor leads
            leader_scores = {
                p: entry["scores"][p]
                for p in comparison["competitors"]
                if entry["scores"][p] == entry["max_score"]
            }
            gap = entry["max_score"] - entry["our_score"]

            vulnerabilities.append({
                "feature": entry["feature"],
                "category": entry["category"],
                "our_score": entry["our_score"],
                "our_label": FEATURE_LABELS.get(entry["our_score"], "Unknown"),
                "leading_competitors": leader_scores,
                "gap": gap,
            })

    # Sort by gap size descending
    vulnerabilities.sort(key=lambda v: v["gap"], reverse=True)
    return vulnerabilities


def generate_win_themes(
    differentiators: list[dict[str, Any]],
    competitive_scores: dict[str, dict[str, Any]],
    our_product: str,
) -> list[str]:
    """Generate win themes based on differentiators and competitive position.

    Args:
        differentiators: List of differentiator features.
        competitive_scores: Product competitive scores.
        our_product: Our product name.

    Returns:
        List of win theme strings.
    """
    themes = []

    # Theme from top differentiators
    if differentiators:
        top_diff_categories = list({d["category"] for d in differentiators[:5]})
        for cat in top_diff_categories[:3]:
            cat_diffs = [d for d in differentiators if d["category"] == cat]
            feature_names = [d["feature"] for d in cat_diffs[:3]]
            themes.append(
                f"Superior {cat} capabilities: {', '.join(feature_names)}"
            )

    # Theme from overall competitive position
    our_score = competitive_scores.get(our_product, {}).get("weighted_score", 0)
    competitor_scores = [
        (p, s["weighted_score"])
        for p, s in competitive_scores.items()
        if p != our_product
    ]
    if competitor_scores:
        best_competitor_name, best_competitor_score = max(
            competitor_scores, key=lambda x: x[1]
        )
        if our_score > best_competitor_score:
            themes.append(
                f"Overall strongest solution ({our_score:.1f}% vs {best_competitor_name} at {best_competitor_score:.1f}%)"
            )

    # Theme from breadth of coverage
    strong_diffs = [d for d in differentiators if d["gap"] >= 2]
    if len(strong_diffs) >= 3:
        themes.append(
            f"Clear technical leadership across {len(strong_diffs)} key features with significant competitive gaps"
        )

    if not themes:
        themes.append("Competitive parity - emphasize implementation quality, support, and total cost of ownership")

    return themes


def analyze_competitive(data: dict[str, Any]) -> dict[str, Any]:
    """Run the complete competitive analysis pipeline.

    Args:
        data: Parsed competitive data dictionary.

    Returns:
        Complete analysis results dictionary.
    """
    comparison = build_comparison_matrix(data)
    competitive_scores = compute_competitive_scores(comparison)
    differentiators = identify_differentiators(comparison)
    vulnerabilities = identify_vulnerabilities(comparison)
    win_themes = generate_win_themes(
        differentiators, competitive_scores, comparison["our_product"]
    )

    return {
        "analysis_info": {
            "our_product": comparison["our_product"],
            "competitors": comparison["competitors"],
            "total_features": len(comparison["matrix"]),
            "total_categories": len(comparison["category_summaries"]),
        },
        "competitive_scores": competitive_scores,
        "category_breakdown": comparison["category_summaries"],
        "comparison_matrix": comparison["matrix"],
        "differentiators": differentiators,
        "vulnerabilities": vulnerabilities,
        "win_themes": win_themes,
    }


def format_text(result: dict[str, Any]) -> str:
    """Format analysis results as human-readable text.

    Args:
        result: Complete analysis results dictionary.

    Returns:
        Formatted text string.
    """
    lines = []
    info = result["analysis_info"]
    all_products = [info["our_product"]] + info["competitors"]

    lines.append("=" * 80)
    lines.append("COMPETITIVE MATRIX ANALYSIS")
    lines.append("=" * 80)
    lines.append(f"Our Product:   {info['our_product']}")
    lines.append(f"Competitors:   {', '.join(info['competitors'])}")
    lines.append(f"Features:      {info['total_features']}")
    lines.append(f"Categories:    {info['total_categories']}")
    lines.append("")

    # Competitive scores
    lines.append("-" * 80)
    lines.append("COMPETITIVE SCORES")
    lines.append("-" * 80)
    lines.append(f"{'Product':<25} {'Weighted':>10} {'Unweighted':>12}")
    lines.append("-" * 80)

    # Sort by weighted score descending
    sorted_scores = sorted(
        result["competitive_scores"].items(),
        key=lambda x: x[1]["weighted_score"],
        reverse=True,
    )
    for product, scores in sorted_scores:
        marker = " <-- US" if product == info["our_product"] else ""
        lines.append(
            f"{product:<25} {scores['weighted_score']:>9.1f}% {scores['unweighted_score']:>11.1f}%{marker}"
        )
    lines.append("")

    # Feature matrix
    lines.append("-" * 80)
    lines.append("FEATURE COMPARISON MATRIX")
    lines.append("-" * 80)

    # Build header
    product_cols = "  ".join(f"{p[:10]:>10}" for p in all_products)
    lines.append(f"{'Feature':<30} {product_cols}")
    lines.append("-" * 80)

    current_category = ""
    for entry in result["comparison_matrix"]:
        if entry["category"] != current_category:
            current_category = entry["category"]
            cat_data = result["category_breakdown"].get(current_category, {})
            weight = cat_data.get("weight", 1.0)
            lines.append(f"\n  [{current_category}] (weight: {weight}x)")

        score_cols = "  ".join(
            f"{FEATURE_LABELS.get(entry['scores'].get(p, 0), 'N/A'):>10}"
            for p in all_products
        )
        lead_marker = " *" if entry["we_lead"] else (" !" if entry["we_trail"] else "")
        feature_display = entry["feature"][:28]
        lines.append(f"    {feature_display:<28} {score_cols}{lead_marker}")
    lines.append("")
    lines.append("  * = We lead  |  ! = We trail")
    lines.append("")

    # Differentiators
    diffs = result["differentiators"]
    if diffs:
        lines.append("-" * 80)
        lines.append(f"DIFFERENTIATORS ({len(diffs)} features where we lead)")
        lines.append("-" * 80)
        for d in diffs:
            lines.append(
                f"  + {d['feature']} [{d['category']}] "
                f"- Us: {d['our_label']} vs Best Competitor: {FEATURE_LABELS.get(d['best_competitor_score'], 'N/A')} "
                f"(gap: +{d['gap']})"
            )
        lines.append("")

    # Vulnerabilities
    vulns = result["vulnerabilities"]
    if vulns:
        lines.append("-" * 80)
        lines.append(f"VULNERABILITIES ({len(vulns)} features where competitors lead)")
        lines.append("-" * 80)
        for v in vulns:
            leaders = ", ".join(
                f"{p}: {FEATURE_LABELS.get(s, 'N/A')}"
                for p, s in v["leading_competitors"].items()
            )
            lines.append(
                f"  - {v['feature']} [{v['category']}] "
                f"- Us: {v['our_label']} vs {leaders} "
                f"(gap: -{v['gap']})"
            )
        lines.append("")

    # Win themes
    themes = result["win_themes"]
    lines.append("-" * 80)
    lines.append("WIN THEMES")
    lines.append("-" * 80)
    for i, theme in enumerate(themes, 1):
        lines.append(f"  {i}. {theme}")
    lines.append("")
    lines.append("=" * 80)

    return "\n".join(lines)


def main() -> None:
    """Main entry point for the Competitive Matrix Builder."""
    parser = argparse.ArgumentParser(
        description="Build competitive feature comparison matrices and positioning analysis.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Feature Scoring:\n"
            "  Full (3)    - Complete feature support\n"
            "  Partial (2) - Partial or limited support\n"
            "  Limited (1) - Minimal or basic support\n"
            "  None (0)    - Feature not available\n"
            "\n"
            "Example:\n"
            "  python competitive_matrix_builder.py competitive_data.json --format json\n"
        ),
    )
    parser.add_argument(
        "input_file",
        help="Path to JSON file containing competitive data",
    )
    parser.add_argument(
        "--format",
        choices=["json", "text"],
        default="text",
        dest="output_format",
        help="Output format: json or text (default: text)",
    )

    args = parser.parse_args()

    data = load_competitive_data(args.input_file)
    result = analyze_competitive(data)

    if args.output_format == "json":
        print(json.dumps(result, indent=2))
    else:
        print(format_text(result))


if __name__ == "__main__":
    main()
