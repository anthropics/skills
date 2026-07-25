#!/usr/bin/env python3
"""
Decision Matrix Scorer — Executive Mentor Tool

Weighted multi-criteria decision analysis with sensitivity testing.
Answers: Which option wins? How fragile is that result? Where are the close calls?

Usage:
    python decision_matrix_scorer.py                    # Run with sample data
    python decision_matrix_scorer.py --interactive      # Interactive mode
    python decision_matrix_scorer.py --file data.json   # Load from JSON file

JSON format:
    {
        "decision": "Description of the decision",
        "criteria": [
            {"name": "Criterion Name", "weight": 0.3, "description": "Optional"},
            ...
        ],
        "options": [
            {
                "name": "Option Name",
                "description": "Optional description",
                "scores": {"Criterion Name": 8, "Another": 6, ...}
            },
            ...
        ]
    }

Scores: 1–10 scale. Weights: must sum to 1.0 (or will be normalized).
"""

import json
import sys
import argparse
from typing import List, Dict, Tuple

# ─────────────────────────────────────────────────────
# Core data structures
# ─────────────────────────────────────────────────────

def normalize_weights(criteria: List[Dict]) -> List[Dict]:
    """Ensure weights sum to 1.0."""
    total = sum(c["weight"] for c in criteria)
    if abs(total - 1.0) > 0.001:
        for c in criteria:
            c["weight"] = c["weight"] / total
    return criteria

def score_option(option: Dict, criteria: List[Dict]) -> float:
    """Calculate weighted score for an option."""
    total = 0.0
    for c in criteria:
        score = option["scores"].get(c["name"], 5)  # Default to 5 if missing
        total += score * c["weight"]
    return round(total, 3)

def score_all(options: List[Dict], criteria: List[Dict]) -> List[Tuple[str, float]]:
    """Return sorted list of (option_name, weighted_score)."""
    results = []
    for opt in options:
        s = score_option(opt, criteria)
        results.append((opt["name"], s))
    return sorted(results, key=lambda x: x[1], reverse=True)

# ─────────────────────────────────────────────────────
# Sensitivity analysis
# ─────────────────────────────────────────────────────

def sensitivity_analysis(options: List[Dict], criteria: List[Dict]) -> Dict:
    """
    Test how result changes when each criterion's weight is varied ±30%.
    Returns dict: criterion → {stable: bool, risk_of_flip: bool, details: str}
    """
    baseline = score_all(options, criteria)
    winner = baseline[0][0]
    results = {}

    for i, c in enumerate(criteria):
        flips = []
        for delta in [-0.30, -0.20, -0.10, +0.10, +0.20, +0.30]:
            # Adjust weight of criterion i, redistribute remainder proportionally
            test_criteria = [dict(cr) for cr in criteria]
            new_weight = max(0.01, test_criteria[i]["weight"] + delta)
            old_weight = test_criteria[i]["weight"]
            diff = new_weight - old_weight
            
            # Redistribute diff across other criteria
            others = [j for j in range(len(test_criteria)) if j != i]
            total_other = sum(test_criteria[j]["weight"] for j in others)
            
            if total_other > 0:
                for j in others:
                    proportion = test_criteria[j]["weight"] / total_other
                    test_criteria[j]["weight"] -= diff * proportion
                    test_criteria[j]["weight"] = max(0.01, test_criteria[j]["weight"])
            
            test_criteria[i]["weight"] = new_weight
            test_criteria = normalize_weights(test_criteria)
            
            test_results = score_all(options, test_criteria)
            if test_results[0][0] != winner:
                flips.append((delta, test_results[0][0]))
        
        if flips:
            smallest_delta = min(abs(delta) for delta, _name in flips)
            results[c["name"]] = {
                "stable": False,
                "flip_at": f"±{int(smallest_delta*100)}% weight change",
                "flip_to": flips[0][1],
                "importance": "HIGH — result depends heavily on this weight"
            }
        else:
            results[c["name"]] = {
                "stable": True,
                "flip_at": None,
                "flip_to": None,
                "importance": "LOW — winner holds even with significant weight changes"
            }
    
    return results

def close_call_analysis(results: List[Tuple[str, float]]) -> List[Dict]:
    """Find options within 10% of winner score — these are close calls."""
    if not results:
        return []
    winner_score = results[0][1]
    close = []
    for name, score in results[1:]:
        gap = winner_score - score
        gap_pct = (gap / winner_score * 100) if winner_score > 0 else 0
        if gap_pct <= 15:
            close.append({
                "name": name,
                "score": score,
                "gap": round(gap, 3),
                "gap_pct": round(gap_pct, 1),
                "verdict": "Very close — recheck assumptions" if gap_pct <= 5 else "Close — worth a second look"
            })
    return close

def criterion_breakdown(options: List[Dict], criteria: List[Dict]) -> Dict:
    """Show per-criterion scores for each option."""
    breakdown = {}
    for opt in options:
        breakdown[opt["name"]] = {}
        for c in criteria:
            raw = opt["scores"].get(c["name"], 5)
            weighted = raw * c["weight"]
            breakdown[opt["name"]][c["name"]] = {
                "raw": raw,
                "weighted": round(weighted, 3),
                "weight": f"{round(c['weight']*100)}%"
            }
    return breakdown

# ─────────────────────────────────────────────────────
# Output formatting
# ─────────────────────────────────────────────────────

def hr(char="─", width=65):
    return char * width

def print_report(data: Dict):
    """Print the full decision analysis report."""
    decision = data.get("decision", "Unnamed Decision")
    criteria = normalize_weights(data["criteria"])
    options = data["options"]
    
    print()
    print(hr("═"))
    print(f"  DECISION MATRIX ANALYSIS")
    print(f"  {decision}")
    print(hr("═"))
    
    # ── Criteria summary
    print()
    print("CRITERIA & WEIGHTS")
    print(hr())
    for c in sorted(criteria, key=lambda x: x["weight"], reverse=True):
        bar_len = int(c["weight"] * 30)
        bar = "█" * bar_len
        desc = f"  — {c['description']}" if c.get("description") else ""
        print(f"  {c['name']:<25} {c['weight']*100:>5.1f}%  {bar}{desc}")
    
    # ── Scoring results
    print()
    print("RESULTS (ranked)")
    print(hr())
    results = score_all(options, criteria)
    max_score = 10.0  # max possible weighted score
    for rank, (name, score) in enumerate(results, 1):
        pct = score / 10.0
        bar_len = int(pct * 40)
        bar = "█" * bar_len
        medal = ["🥇", "🥈", "🥉"][rank-1] if rank <= 3 else f"#{rank} "
        print(f"  {medal} {name:<25} {score:>5.2f}/10  {bar}")
    
    winner = results[0][0]
    print()
    print(f"  ► Winner: {winner}  (score: {results[0][1]:.2f})")
    
    # ── Close calls
    close = close_call_analysis(results)
    if close:
        print()
        print("CLOSE CALLS")
        print(hr())
        for c in close:
            print(f"  ⚠  {c['name']}: {c['score']:.2f}  (gap: {c['gap_pct']}% — {c['verdict']})")
    
    # ── Per-criterion breakdown
    print()
    print("SCORE BREAKDOWN BY CRITERION")
    print(hr())
    breakdown = criterion_breakdown(options, criteria)
    
    # Header
    opt_names = [opt["name"][:16] for opt in options]
    header = f"  {'Criterion':<22}"
    for n in opt_names:
        header += f"  {n:>10}"
    print(header)
    print("  " + hr("-", 63))
    
    for c in criteria:
        row = f"  {c['name']:<22}"
        for opt in options:
            raw = opt["scores"].get(c["name"], 5)
            row += f"  {raw:>10}"
        row += f"  (weight {c['weight']*100:.0f}%)"
        print(row)
    
    # Weighted row
    print("  " + hr("-", 63))
    weighted_row = f"  {'Weighted Total':<22}"
    for name, score in results:
        # Re-order by options list order
        weighted_row += f"  {score:>10.2f}"
    # Actually print in options order
    print(f"  {'Weighted Total':<22}", end="")
    for opt in options:
        s = score_option(opt, criteria)
        print(f"  {s:>10.2f}", end="")
    print()
    
    # ── Sensitivity analysis
    print()
    print("SENSITIVITY ANALYSIS")
    print(hr())
    print("  How much does the winner change if we adjust criterion weights?")
    print()
    sensitivity = sensitivity_analysis(options, criteria)
    for crit_name, result in sensitivity.items():
        if result["stable"]:
            print(f"  ✓ {crit_name:<28} STABLE — winner holds at ±30% weight change")
        else:
            print(f"  ⚠ {crit_name:<28} FRAGILE — flips to '{result['flip_to']}' at {result['flip_at']}")
    
    # ── Recommendation
    print()
    print("RECOMMENDATION")
    print(hr())
    unstable = [k for k, v in sensitivity.items() if not v["stable"]]
    if unstable:
        print(f"  Winner: {winner}")
        print(f"  Confidence: MEDIUM — result is sensitive to weights on: {', '.join(unstable)}")
        print()
        print("  Before committing:")
        print(f"  • Validate that your weighting of [{', '.join(unstable)}] is correct")
        print("  • Consider whether the weight differences reflect genuine priorities")
        print("  • If uncertain, run scenario with alternative weights")
    else:
        print(f"  Winner: {winner}")
        print(f"  Confidence: HIGH — winner is stable across all weight scenarios")
        print()
        print("  The decision is clear. The main risk is whether your scoring")
        print("  of each option on each criterion is accurate.")
    
    print()
    print(hr("═"))
    print()

# ─────────────────────────────────────────────────────
# Interactive mode
# ─────────────────────────────────────────────────────

def interactive_mode():
    """Guided interactive data entry."""
    print()
    print(hr("═"))
    print("  DECISION MATRIX — Interactive Mode")
    print(hr("═"))
    
    data = {}
    data["decision"] = input("\nWhat decision are you making?\n> ").strip()
    
    # Criteria
    print("\nDefine criteria (what matters in this decision).")
    print("Enter criteria one at a time. Empty line to finish.")
    print("Weight: importance 0–10 (will be normalized to %).")
    print()
    
    criteria = []
    while True:
        name = input(f"Criterion {len(criteria)+1} name (or ENTER to finish): ").strip()
        if not name:
            if len(criteria) < 2:
                print("  Need at least 2 criteria.")
                continue
            break
        weight_str = input(f"  Weight for '{name}' (0–10): ").strip()
        try:
            weight = float(weight_str)
        except ValueError:
            weight = 5.0
        criteria.append({"name": name, "weight": weight})
    
    data["criteria"] = criteria
    
    # Options
    print("\nDefine options (what you're choosing between).")
    print("Enter options one at a time. Empty line to finish.")
    print()
    
    options = []
    while True:
        name = input(f"Option {len(options)+1} name (or ENTER to finish): ").strip()
        if not name:
            if len(options) < 2:
                print("  Need at least 2 options.")
                continue
            break
        
        print(f"\n  Score each criterion for '{name}' (1=poor, 10=excellent):")
        scores = {}
        for c in criteria:
            while True:
                s = input(f"    {c['name']}: ").strip()
                try:
                    score = float(s)
                    if 1 <= score <= 10:
                        scores[c["name"]] = score
                        break
                    else:
                        print("    Score must be 1–10")
                except ValueError:
                    print("    Enter a number 1–10")
        
        options.append({"name": name, "scores": scores})
        print()
    
    data["options"] = options
    print_report(data)

# ─────────────────────────────────────────────────────
# Sample data
# ─────────────────────────────────────────────────────

SAMPLE_DATA = {
    "decision": "How to extend runway: Cut costs vs. Raise bridge vs. Accelerate revenue",
    "criteria": [
        {
            "name": "Speed to impact",
            "weight": 0.25,
            "description": "How quickly does this improve our situation?"
        },
        {
            "name": "Execution risk",
            "weight": 0.30,
            "description": "How likely is this to actually work? (10=low risk)"
        },
        {
            "name": "Team morale impact",
            "weight": 0.20,
            "description": "Effect on team (10=positive, 1=very negative)"
        },
        {
            "name": "Runway extension",
            "weight": 0.15,
            "description": "How much runway does this actually buy?"
        },
        {
            "name": "Strategic fit",
            "weight": 0.10,
            "description": "Does this align with where we want to go?"
        }
    ],
    "options": [
        {
            "name": "Cost cut 25%",
            "description": "Reduce headcount and discretionary spend by 25%",
            "scores": {
                "Speed to impact": 9,
                "Execution risk": 8,
                "Team morale impact": 2,
                "Runway extension": 8,
                "Strategic fit": 5
            }
        },
        {
            "name": "Bridge from investors",
            "description": "Raise $500K bridge from existing investors to hit next milestone",
            "scores": {
                "Speed to impact": 6,
                "Execution risk": 5,
                "Team morale impact": 7,
                "Runway extension": 6,
                "Strategic fit": 7
            }
        },
        {
            "name": "Accelerate revenue",
            "description": "Push 3 enterprise deals hard, offer incentives for Q4 close",
            "scores": {
                "Speed to impact": 4,
                "Execution risk": 3,
                "Team morale impact": 9,
                "Runway extension": 9,
                "Strategic fit": 10
            }
        },
        {
            "name": "Hybrid: cut 15% + bridge",
            "description": "Smaller cuts combined with a modest bridge round",
            "scores": {
                "Speed to impact": 7,
                "Execution risk": 6,
                "Team morale impact": 5,
                "Runway extension": 7,
                "Strategic fit": 6
            }
        }
    ]
}

# ─────────────────────────────────────────────────────
# Main
# ─────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Decision Matrix Scorer — weighted analysis with sensitivity testing"
    )
    parser.add_argument(
        "--interactive", "-i",
        action="store_true",
        help="Interactive mode: enter decision data manually"
    )
    parser.add_argument(
        "--file", "-f",
        type=str,
        help="Load decision data from JSON file"
    )
    parser.add_argument(
        "--sample",
        action="store_true",
        help="Show sample data structure and exit"
    )
    
    args = parser.parse_args()
    
    if args.sample:
        print(json.dumps(SAMPLE_DATA, indent=2))
        return
    
    if args.interactive:
        interactive_mode()
        return
    
    if args.file:
        try:
            with open(args.file) as f:
                data = json.load(f)
            print_report(data)
        except FileNotFoundError:
            print(f"Error: File '{args.file}' not found.")
            sys.exit(1)
        except json.JSONDecodeError as e:
            print(f"Error: Invalid JSON in '{args.file}': {e}")
            sys.exit(1)
        return
    
    # Default: run sample data
    print()
    print("Running with sample data. Use --interactive for custom input or --file for JSON.")
    print_report(SAMPLE_DATA)


if __name__ == "__main__":
    main()
