#!/usr/bin/env python3
"""
Stakeholder Mapper — Executive Mentor Tool

Maps stakeholders by influence and alignment.
Identifies: champions, blockers, swing votes, and hidden risks.
Outputs: stakeholder grid with engagement strategy per quadrant.

Usage:
    python stakeholder_mapper.py                    # Run with sample data
    python stakeholder_mapper.py --interactive      # Interactive mode
    python stakeholder_mapper.py --file data.json   # Load from JSON file

JSON format:
    {
        "initiative": "Name of the decision or initiative",
        "stakeholders": [
            {
                "name": "Person/Group Name",
                "role": "Their role or title",
                "influence": 8,          // 1–10: how much power they have over outcome
                "alignment": 3,          // 1–10: how supportive they are (10=champion, 1=blocker)
                "interest": 7,           // 1–10: how interested/engaged they are
                "notes": "Optional context — what drives them, hidden concerns, relationships"
            }
        ]
    }
"""

import json
import sys
import argparse
from typing import List, Dict, Tuple, Optional

# ─────────────────────────────────────────────────────
# Quadrant classification
# ─────────────────────────────────────────────────────

def classify_stakeholder(influence: float, alignment: float) -> Dict:
    """
    Classify into strategic quadrant based on influence and alignment.
    
    Quadrants:
    - Champions (high influence, high alignment): Your most valuable assets
    - Blockers (high influence, low alignment): Your biggest risks
    - Supporters (low influence, high alignment): Useful but less critical
    - Bystanders (low influence, low alignment): Monitor, low priority
    - Swing Votes (medium influence, medium alignment): Key to persuade
    """
    mid_influence = 5.5
    mid_alignment = 5.5
    
    # Special case: swing votes — medium on both dimensions
    if 4 <= influence <= 7 and 4 <= alignment <= 7:
        return {
            "quadrant": "Swing Vote",
            "symbol": "⚡",
            "priority": "HIGH",
            "strategy": "Persuade — understand concerns, address directly, build relationship"
        }
    
    if influence >= mid_influence and alignment >= mid_alignment:
        return {
            "quadrant": "Champion",
            "symbol": "★",
            "priority": "HIGH",
            "strategy": "Leverage — activate them as advocates, give them a role in the initiative"
        }
    elif influence >= mid_influence and alignment < mid_alignment:
        return {
            "quadrant": "Blocker",
            "symbol": "✖",
            "priority": "CRITICAL",
            "strategy": "Address — understand their specific objections, find common ground or neutralize"
        }
    elif influence < mid_influence and alignment >= mid_alignment:
        return {
            "quadrant": "Supporter",
            "symbol": "○",
            "priority": "MEDIUM",
            "strategy": "Maintain — keep informed and engaged, potentially increase their influence"
        }
    else:
        return {
            "quadrant": "Bystander",
            "symbol": "·",
            "priority": "LOW",
            "strategy": "Monitor — minimal investment, keep informed with standard comms"
        }

def risk_flags(stakeholder: Dict) -> List[str]:
    """Identify specific risk signals for a stakeholder."""
    flags = []
    influence = stakeholder["influence"]
    alignment = stakeholder["alignment"]
    interest = stakeholder.get("interest", 5)
    
    if influence >= 7 and alignment <= 3:
        flags.append("🔴 HIGH-POWER BLOCKER — can kill this initiative")
    
    if influence >= 7 and alignment <= 5 and interest >= 7:
        flags.append("🟡 ENGAGED SKEPTIC — high influence, paying close attention, not convinced")
    
    if alignment <= 4 and interest >= 8:
        flags.append("🟡 ACTIVE OPPOSITION — low alignment but highly engaged — may mobilize others")
    
    if influence >= 6 and alignment >= 7 and interest <= 3:
        flags.append("🟡 DISENGAGED CHAMPION — strong supporter but not paying attention — needs activation")
    
    if influence >= 5 and 4 <= alignment <= 6:
        flags.append("⚡ PERSUADABLE — medium influence, genuinely undecided — high ROI to engage")
    
    return flags

# ─────────────────────────────────────────────────────
# Analysis
# ─────────────────────────────────────────────────────

def calculate_overall_alignment(stakeholders: List[Dict]) -> Dict:
    """Calculate weighted average alignment (weighted by influence)."""
    if not stakeholders:
        return {"score": 0, "verdict": "No data"}
    
    total_influence = sum(s["influence"] for s in stakeholders)
    if total_influence == 0:
        return {"score": 0, "verdict": "No influence"}
    
    weighted_alignment = sum(
        s["alignment"] * s["influence"] for s in stakeholders
    ) / total_influence
    
    if weighted_alignment >= 7:
        verdict = "FAVORABLE — strong support among influential stakeholders"
    elif weighted_alignment >= 5:
        verdict = "MIXED — significant opposition needs to be addressed"
    else:
        verdict = "UNFAVORABLE — initiative faces significant headwinds"
    
    return {
        "score": round(weighted_alignment, 2),
        "verdict": verdict
    }

def find_critical_path(stakeholders: List[Dict]) -> List[Dict]:
    """
    Identify the minimal set of stakeholders whose alignment is critical.
    These are high-influence stakeholders — their position determines the outcome.
    """
    high_influence = [s for s in stakeholders if s["influence"] >= 7]
    return sorted(high_influence, key=lambda x: x["influence"], reverse=True)

def engagement_sequencing(stakeholders: List[Dict]) -> List[Dict]:
    """
    Recommend engagement sequence.
    Order: Fix blockers → Activate champions → Persuade swing votes → Maintain rest.
    """
    classified = []
    for s in stakeholders:
        cls = classify_stakeholder(s["influence"], s["alignment"])
        classified.append({**s, **cls})
    
    # Sort by engagement priority
    priority_order = {"CRITICAL": 0, "HIGH": 1, "MEDIUM": 2, "LOW": 3}
    classified.sort(key=lambda x: (priority_order[x["priority"]], -x["influence"]))
    
    return classified

# ─────────────────────────────────────────────────────
# ASCII grid visualization
# ─────────────────────────────────────────────────────

def render_grid(stakeholders: List[Dict], width: int = 60) -> str:
    """
    Render a 2D influence vs alignment grid with stakeholder positions.
    Y-axis: Influence (top = high)
    X-axis: Alignment (left = low, right = high)
    """
    rows = 10
    cols = 20
    
    grid = [[' ' for _ in range(cols)] for _ in range(rows)]
    
    for s in stakeholders:
        influence = s["influence"]
        alignment = s["alignment"]
        
        # Map scores 1–10 to grid coordinates
        col = int((alignment - 1) / 9 * (cols - 1))
        row = rows - 1 - int((influence - 1) / 9 * (rows - 1))
        
        col = max(0, min(cols - 1, col))
        row = max(0, min(rows - 1, row))
        
        initial = s["name"][0].upper()
        if grid[row][col] == ' ':
            grid[row][col] = initial
        else:
            grid[row][col] = '+'  # Overlap
    
    lines = []
    lines.append("  STAKEHOLDER MAP  (Influence ↑  |  Alignment →)")
    lines.append("")
    lines.append(f"  HIGH  ┌{'─'*cols}┐")
    
    for i, row in enumerate(grid):
        if i == rows // 2:
            prefix = "  INFL "
        else:
            prefix = "       "
        lines.append(f"{prefix}│{''.join(row)}│")
    
    lines.append(f"   LOW  └{'─'*cols}┘")
    lines.append(f"         {'BLOCKER':<12}  {'SWING':<8}   CHAMPION")
    lines.append(f"         Low alignment              High alignment")
    lines.append("")
    
    # Legend
    lines.append("  Legend (initials):")
    for s in stakeholders:
        cls = classify_stakeholder(s["influence"], s["alignment"])
        lines.append(f"    {s['name'][0].upper()} = {s['name']} ({cls['symbol']} {cls['quadrant']})")
    
    return "\n".join(lines)

# ─────────────────────────────────────────────────────
# Output formatting
# ─────────────────────────────────────────────────────

def hr(char="─", width=65):
    return char * width

def print_report(data: Dict):
    initiative = data.get("initiative", "Unnamed Initiative")
    stakeholders = data["stakeholders"]
    
    # Validate and fill defaults
    for s in stakeholders:
        s.setdefault("interest", 5)
        s.setdefault("notes", "")
        s["influence"] = max(1, min(10, float(s["influence"])))
        s["alignment"] = max(1, min(10, float(s["alignment"])))
        s["interest"] = max(1, min(10, float(s["interest"])))
    
    print()
    print(hr("═"))
    print(f"  STAKEHOLDER ANALYSIS")
    print(f"  {initiative}")
    print(hr("═"))
    
    # Overall assessment
    overall = calculate_overall_alignment(stakeholders)
    print()
    print("OVERALL ASSESSMENT")
    print(hr())
    print(f"  Weighted alignment score: {overall['score']}/10")
    print(f"  Verdict: {overall['verdict']}")
    
    # Grid visualization
    print()
    print(hr())
    print(render_grid(stakeholders))
    
    # Stakeholder profiles by quadrant
    sequenced = engagement_sequencing(stakeholders)
    
    # Group by quadrant
    quadrants = {}
    for s in sequenced:
        q = s["quadrant"]
        if q not in quadrants:
            quadrants[q] = []
        quadrants[q].append(s)
    
    quadrant_order = ["Blocker", "Swing Vote", "Champion", "Supporter", "Bystander"]
    
    print()
    print("STAKEHOLDER PROFILES")
    print(hr())
    
    for q_name in quadrant_order:
        if q_name not in quadrants:
            continue
        group = quadrants[q_name]
        first = group[0]
        print()
        print(f"  {first['symbol']} {q_name.upper()}S  ({len(group)} stakeholder{'s' if len(group)>1 else ''})")
        print(f"  Strategy: {first['strategy']}")
        print()
        
        for s in group:
            cls = classify_stakeholder(s["influence"], s["alignment"])
            flags = risk_flags(s)
            
            print(f"    {s['name']}")
            print(f"    Role: {s.get('role', 'Not specified')}")
            print(f"    Influence: {'█'*int(s['influence']//2)}{'░'*(5-int(s['influence']//2))} {s['influence']:.0f}/10  "
                  f"Alignment: {'█'*int(s['alignment']//2)}{'░'*(5-int(s['alignment']//2))} {s['alignment']:.0f}/10  "
                  f"Interest: {'█'*int(s['interest']//2)}{'░'*(5-int(s['interest']//2))} {s['interest']:.0f}/10")
            
            if flags:
                for flag in flags:
                    print(f"    {flag}")
            
            if s.get("notes"):
                print(f"    Notes: {s['notes']}")
            
            print()
    
    # Engagement plan
    print()
    print("ENGAGEMENT PLAN (sequenced by priority)")
    print(hr())
    print()
    print(f"  {'#':<3} {'Name':<22} {'Quadrant':<14} {'Priority':<10} {'First Action'}")
    print(f"  {hr('-', 63)}")
    
    actions = {
        "Blocker": "Schedule 1:1 — understand specific objections",
        "Swing Vote": "Coffee or informal conversation — listen first",
        "Champion": "Brief them on the initiative — give them a role",
        "Supporter": "Keep informed — monthly update or email",
        "Bystander": "Include in standard comms only"
    }
    
    for i, s in enumerate(sequenced, 1):
        action = actions.get(s["quadrant"], "Maintain standard communication")
        print(f"  {i:<3} {s['name']:<22} {s['quadrant']:<14} {s['priority']:<10} {action}")
    
    # Risk summary
    print()
    print("RISK SUMMARY")
    print(hr())
    
    critical_path = find_critical_path(stakeholders)
    if critical_path:
        print()
        print("  High-influence stakeholders (outcome depends on these):")
        for s in critical_path:
            cls = classify_stakeholder(s["influence"], s["alignment"])
            alignment_label = "CHAMPION" if s["alignment"] >= 7 else "BLOCKER" if s["alignment"] <= 4 else "UNDECIDED"
            print(f"  {cls['symbol']} {s['name']:<25} influence {s['influence']:.0f}/10  → {alignment_label}")
    
    # All risk flags
    all_flags = []
    for s in stakeholders:
        flags = risk_flags(s)
        for flag in flags:
            all_flags.append((s["name"], flag))
    
    if all_flags:
        print()
        print("  Risk flags:")
        for name, flag in all_flags:
            print(f"  [{name}] {flag}")
    
    print()
    print(hr("═"))
    print()

# ─────────────────────────────────────────────────────
# Interactive mode
# ─────────────────────────────────────────────────────

def interactive_mode():
    print()
    print(hr("═"))
    print("  STAKEHOLDER MAPPER — Interactive Mode")
    print(hr("═"))
    
    data = {}
    data["initiative"] = input("\nWhat initiative or decision are you mapping?\n> ").strip()
    
    print("\nAdd stakeholders one at a time. Empty name to finish.")
    print("Scores: 1=low, 10=high")
    print()
    
    stakeholders = []
    while True:
        name = input(f"Stakeholder {len(stakeholders)+1} name (or ENTER to finish): ").strip()
        if not name:
            if len(stakeholders) < 1:
                print("  Need at least 1 stakeholder.")
                continue
            break
        
        role = input(f"  Role/title: ").strip()
        
        def get_score(prompt, default=5):
            while True:
                s = input(f"  {prompt} (1–10, default {default}): ").strip()
                if not s:
                    return float(default)
                try:
                    v = float(s)
                    if 1 <= v <= 10:
                        return v
                    print("  Must be 1–10")
                except ValueError:
                    print("  Enter a number")
        
        influence = get_score("Influence (power over this decision)")
        alignment = get_score("Alignment (1=opposed, 10=champion)")
        interest = get_score("Interest level (how engaged are they)")
        notes = input(f"  Notes (optional): ").strip()
        
        stakeholders.append({
            "name": name,
            "role": role,
            "influence": influence,
            "alignment": alignment,
            "interest": interest,
            "notes": notes
        })
        print()
    
    data["stakeholders"] = stakeholders
    print_report(data)

# ─────────────────────────────────────────────────────
# Sample data
# ─────────────────────────────────────────────────────

SAMPLE_DATA = {
    "initiative": "Migrate from monolith to microservices (18-month program)",
    "stakeholders": [
        {
            "name": "Sarah Chen (CTO)",
            "role": "Chief Technology Officer",
            "influence": 10,
            "alignment": 9,
            "interest": 9,
            "notes": "Driving force behind the initiative. Will fund and protect the team."
        },
        {
            "name": "Marcus Webb (CFO)",
            "role": "Chief Financial Officer",
            "influence": 9,
            "alignment": 3,
            "interest": 6,
            "notes": "Concerned about 18-month cost with no visible revenue return. Has budget veto."
        },
        {
            "name": "Priya Agarwal (VP Eng)",
            "role": "VP Engineering",
            "influence": 8,
            "alignment": 7,
            "interest": 8,
            "notes": "Supportive in principle, worried about team bandwidth alongside feature delivery."
        },
        {
            "name": "Tom Briggs (VP Product)",
            "role": "VP Product",
            "influence": 7,
            "alignment": 4,
            "interest": 5,
            "notes": "Concerned about roadmap slowdown. Hasn't been in the architecture discussions."
        },
        {
            "name": "Elena Park (CEO)",
            "role": "Chief Executive Officer",
            "influence": 10,
            "alignment": 6,
            "interest": 4,
            "notes": "Trusts the CTO but will back out if CFO and VP Product both push back hard."
        },
        {
            "name": "Raj Patel (Lead Arch)",
            "role": "Lead Architect",
            "influence": 6,
            "alignment": 10,
            "interest": 10,
            "notes": "Deep technical champion. Has proposed detailed migration plan."
        },
        {
            "name": "Dev Team Leads (x4)",
            "role": "Team Leads",
            "influence": 5,
            "alignment": 6,
            "interest": 7,
            "notes": "Mixed. Some excited, some worried about learning curve. Middle ground."
        },
        {
            "name": "Board (investor reps)",
            "role": "Board Directors",
            "influence": 9,
            "alignment": 5,
            "interest": 3,
            "notes": "Not paying attention unless CFO raises flags. Could become blockers if CFO escalates."
        }
    ]
}

# ─────────────────────────────────────────────────────
# Main
# ─────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Stakeholder Mapper — influence, alignment, and engagement strategy"
    )
    parser.add_argument(
        "--interactive", "-i",
        action="store_true",
        help="Interactive mode: enter stakeholder data manually"
    )
    parser.add_argument(
        "--file", "-f",
        type=str,
        help="Load stakeholder data from JSON file"
    )
    parser.add_argument(
        "--sample",
        action="store_true",
        help="Print sample JSON structure and exit"
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
    
    # Default: sample data
    print()
    print("Running with sample data. Use --interactive for custom input or --file for JSON.")
    print_report(SAMPLE_DATA)


if __name__ == "__main__":
    main()
