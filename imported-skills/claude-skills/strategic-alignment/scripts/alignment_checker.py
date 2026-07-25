#!/usr/bin/env python3
"""
Strategic Alignment Checker

Detects misalignment in OKR structures:
- Orphan OKRs: team goals with no connection to company goals
- Conflicting OKRs: team goals that may work against each other
- Coverage gaps: company goals with insufficient team support

Input: JSON file with company and team OKRs
Output: Alignment score, gap report, conflict map

Usage:
    python alignment_checker.py                    # Run with sample data
    python alignment_checker.py --file my_okrs.json  # Run with your data
    python alignment_checker.py --sample            # Print sample JSON format
"""

import json
import sys
import argparse
from collections import defaultdict


# ─────────────────────────────────────────────
# Sample data
# ─────────────────────────────────────────────

SAMPLE_DATA = {
    "quarter": "Q2 2026",
    "company": {
        "name": "Acme Corp",
        "okrs": [
            {
                "id": "C1",
                "objective": "Win mid-market DACH healthcare segment",
                "key_results": [
                    "Reach 50 paying customers in DACH by EoQ",
                    "Achieve €800K ARR in DACH",
                    "Net Revenue Retention > 110%"
                ]
            },
            {
                "id": "C2",
                "objective": "Ship the platform API to unlock partner integrations",
                "key_results": [
                    "API v1 launched with 3 partner integrations",
                    "API documentation coverage: 100% of endpoints",
                    "< 200ms P95 response time under load"
                ]
            },
            {
                "id": "C3",
                "objective": "Build a capital-efficient growth engine",
                "key_results": [
                    "CAC payback period < 12 months",
                    "Burn multiple < 1.5x",
                    "Revenue per employee up 20% vs Q1"
                ]
            }
        ]
    },
    "teams": [
        {
            "name": "Sales",
            "okrs": [
                {
                    "id": "S1",
                    "objective": "Hit DACH new business targets",
                    "parent_company_okr_id": "C1",
                    "key_results": [
                        "Close 15 new DACH logos",
                        "Pipeline coverage: 3x of target",
                        "Average deal size > €18K ARR"
                    ],
                    "potential_conflicts": ["C3", "CS2"]
                },
                {
                    "id": "S2",
                    "objective": "Expand into Austria market",
                    "parent_company_okr_id": None,  # ORPHAN — no company OKR parent
                    "key_results": [
                        "5 qualified meetings with Austrian prospects",
                        "1 pilot signed in Austria"
                    ],
                    "potential_conflicts": []
                }
            ]
        },
        {
            "name": "Engineering",
            "okrs": [
                {
                    "id": "E1",
                    "objective": "Deliver API v1 on schedule",
                    "parent_company_okr_id": "C2",
                    "key_results": [
                        "API v1 feature complete by Week 8",
                        "Zero critical bugs at launch",
                        "P95 latency < 200ms under 500 RPS"
                    ],
                    "potential_conflicts": []
                },
                {
                    "id": "E2",
                    "objective": "Reduce infrastructure cost by 30%",
                    "parent_company_okr_id": "C3",
                    "key_results": [
                        "Migrate 3 services to spot instances",
                        "Decommission legacy DB cluster",
                        "Monthly infra cost < €12K"
                    ],
                    "potential_conflicts": []
                },
                {
                    "id": "E3",
                    "objective": "Achieve zero-downtime deployments",
                    "parent_company_okr_id": None,  # ORPHAN
                    "key_results": [
                        "Implement blue-green deployment pipeline",
                        "Deployment success rate > 99.5%"
                    ],
                    "potential_conflicts": []
                }
            ]
        },
        {
            "name": "Customer Success",
            "okrs": [
                {
                    "id": "CS1",
                    "objective": "Drive retention and expansion in DACH",
                    "parent_company_okr_id": "C1",
                    "key_results": [
                        "NRR > 110% for DACH cohort",
                        "Churn < 2% gross monthly",
                        "CSAT score > 4.5/5"
                    ],
                    "potential_conflicts": []
                },
                {
                    "id": "CS2",
                    "objective": "Reduce support ticket volume by 40%",
                    "parent_company_okr_id": "C3",
                    "key_results": [
                        "Launch self-serve knowledge base",
                        "Ticket deflection rate > 35%",
                        "Time-to-first-response < 2 hours"
                    ],
                    "potential_conflicts": ["S1"]  # Volume close pressure → more bad-fit customers → more tickets
                }
            ]
        },
        {
            "name": "Marketing",
            "okrs": [
                {
                    "id": "M1",
                    "objective": "Generate DACH pipeline to support sales targets",
                    "parent_company_okr_id": "C1",
                    "key_results": [
                        "€2.4M qualified pipeline from DACH",
                        "30 qualified demo requests from target ICP",
                        "CAC from inbound < €4K"
                    ],
                    "potential_conflicts": []
                }
            ]
        }
    ],
    "known_conflicts": [
        {
            "team_a": "Sales",
            "okr_a": "S1",
            "team_b": "Customer Success",
            "okr_b": "CS2",
            "description": "Sales closing volume deals to hit number may include poor-fit customers, increasing CS ticket load and reducing CSAT — directly conflicting with CS ticket reduction target."
        }
    ]
}


# ─────────────────────────────────────────────
# Analysis functions
# ─────────────────────────────────────────────

def get_all_company_okr_ids(data):
    return {okr["id"] for okr in data["company"]["okrs"]}


def detect_orphans(data, company_ids):
    """Find team OKRs with no parent company OKR."""
    orphans = []
    for team in data["teams"]:
        for okr in team["okrs"]:
            if okr.get("parent_company_okr_id") is None:
                orphans.append({
                    "team": team["name"],
                    "okr_id": okr["id"],
                    "objective": okr["objective"]
                })
            elif okr["parent_company_okr_id"] not in company_ids:
                orphans.append({
                    "team": team["name"],
                    "okr_id": okr["id"],
                    "objective": okr["objective"],
                    "note": f"References non-existent company OKR: {okr['parent_company_okr_id']}"
                })
    return orphans


def detect_coverage_gaps(data, company_ids):
    """Find company OKRs with no team support."""
    coverage = defaultdict(list)
    for team in data["teams"]:
        for okr in team["okrs"]:
            parent = okr.get("parent_company_okr_id")
            if parent and parent in company_ids:
                coverage[parent].append({
                    "team": team["name"],
                    "okr_id": okr["id"],
                    "objective": okr["objective"]
                })

    gaps = []
    over_indexed = []
    for company_okr in data["company"]["okrs"]:
        cid = company_okr["id"]
        supporting = coverage.get(cid, [])
        entry = {
            "company_okr_id": cid,
            "objective": company_okr["objective"],
            "supporting_team_count": len(supporting),
            "supporting_teams": [s["team"] for s in supporting]
        }
        if len(supporting) == 0:
            gaps.append(entry)
        elif len(supporting) >= 4:
            over_indexed.append(entry)

    return gaps, over_indexed, coverage


def detect_conflicts(data):
    """Surface declared and potential OKR conflicts."""
    conflicts = []

    # Use declared known_conflicts
    for conflict in data.get("known_conflicts", []):
        conflicts.append({
            "type": "declared",
            "team_a": conflict["team_a"],
            "okr_a": conflict["okr_a"],
            "team_b": conflict["team_b"],
            "okr_b": conflict["okr_b"],
            "description": conflict["description"]
        })

    # Use potential_conflicts fields on OKRs for cross-reference
    okr_index = {}
    for team in data["teams"]:
        for okr in team["okrs"]:
            okr_index[okr["id"]] = {"team": team["name"], "objective": okr["objective"]}

    for team in data["teams"]:
        for okr in team["okrs"]:
            for conflict_id in okr.get("potential_conflicts", []):
                if conflict_id in okr_index:
                    target = okr_index[conflict_id]
                    # Avoid duplicate (A→B and B→A)
                    already_declared = any(
                        (c["okr_a"] == okr["id"] and c["okr_b"] == conflict_id) or
                        (c["okr_a"] == conflict_id and c["okr_b"] == okr["id"])
                        for c in conflicts
                    )
                    if not already_declared:
                        conflicts.append({
                            "type": "potential",
                            "team_a": team["name"],
                            "okr_a": okr["id"],
                            "team_b": target["team"],
                            "okr_b": conflict_id,
                            "description": f"Potential conflict between '{okr['objective']}' and '{target['objective']}' — review recommended"
                        })

    return conflicts


def compute_alignment_score(data, orphans, gaps, conflicts, coverage):
    """Score overall alignment from 0–100."""
    total_team_okrs = sum(len(t["okrs"]) for t in data["teams"])
    total_company_okrs = len(data["company"]["okrs"])

    orphan_penalty = (len(orphans) / max(total_team_okrs, 1)) * 30
    gap_penalty = (len(gaps) / max(total_company_okrs, 1)) * 30
    conflict_penalty = min(len(conflicts) * 10, 30)

    score = max(0, 100 - orphan_penalty - gap_penalty - conflict_penalty)
    return round(score)


def score_label(score):
    if score >= 85:
        return "✅ Excellent"
    elif score >= 70:
        return "🟡 Moderate misalignment"
    elif score >= 50:
        return "🟠 Significant misalignment"
    else:
        return "🔴 Critical misalignment"


# ─────────────────────────────────────────────
# Report generation
# ─────────────────────────────────────────────

def print_report(data, orphans, gaps, over_indexed, conflicts, coverage, score):
    sep = "─" * 60

    print(f"\n{'═' * 60}")
    print(f"  STRATEGIC ALIGNMENT REPORT — {data.get('quarter', 'Unknown Quarter')}")
    print(f"  Company: {data['company']['name']}")
    print(f"{'═' * 60}\n")

    print(f"  ALIGNMENT SCORE: {score}/100  {score_label(score)}\n")
    print(sep)

    # Company OKRs summary
    print("\n📋 COMPANY OKRs\n")
    for okr in data["company"]["okrs"]:
        supporting = coverage.get(okr["id"], [])
        teams_str = ", ".join(s["team"] for s in supporting) if supporting else "⚠️  NONE"
        print(f"  [{okr['id']}] {okr['objective']}")
        print(f"       Supported by: {teams_str}")
    print()
    print(sep)

    # Orphan OKRs
    print(f"\n🔍 ORPHAN OKRs ({len(orphans)} found)\n")
    if orphans:
        for o in orphans:
            note = f" — {o.get('note', 'No parent company OKR assigned')}"
            print(f"  ⚠️  [{o['okr_id']}] {o['team']}: {o['objective']}")
            print(f"       Issue: {note}")
        print()
        print("  → Action: Connect each orphan to a company OKR, or deprioritize it.")
    else:
        print("  ✅ None found. All team OKRs connect to company OKRs.")
    print()
    print(sep)

    # Coverage gaps
    print(f"\n🕳️  COVERAGE GAPS ({len(gaps)} company OKRs with zero team support)\n")
    if gaps:
        for g in gaps:
            print(f"  🔴 [{g['company_okr_id']}] {g['objective']}")
            print(f"       No team is working on this. It will not be achieved.")
        print()
        print("  → Action: Assign at least one team owner to each unowned company OKR.")
    else:
        print("  ✅ All company OKRs have at least one team supporting them.")
    print()

    if over_indexed:
        print(f"  📊 OVER-INDEXED OKRs ({len(over_indexed)} company OKRs with 4+ teams)\n")
        for o in over_indexed:
            print(f"  [{o['company_okr_id']}] {o['objective']}")
            print(f"       {o['supporting_team_count']} teams: {', '.join(o['supporting_teams'])}")
        print()
        print("  → Note: High coverage isn't necessarily bad, but check if under-covered OKRs are being neglected.")
    print(sep)

    # Conflicts
    print(f"\n⚡ CONFLICTING OKRs ({len(conflicts)} found)\n")
    if conflicts:
        for i, c in enumerate(conflicts, 1):
            label = "🔴 Declared" if c["type"] == "declared" else "🟡 Potential"
            print(f"  {label} Conflict #{i}")
            print(f"    {c['team_a']} [{c['okr_a']}] ↔ {c['team_b']} [{c['okr_b']}]")
            print(f"    {c['description']}")
            print()
        print("  → Action: For each conflict, design a shared metric or shared constraint that prevents local optimization at company expense.")
    else:
        print("  ✅ No declared or potential conflicts detected.")
    print()
    print(sep)

    # Summary
    print("\n📊 SUMMARY\n")
    total_team_okrs = sum(len(t["okrs"]) for t in data["teams"])
    total_company_okrs = len(data["company"]["okrs"])
    print(f"  Company OKRs:       {total_company_okrs}")
    print(f"  Team OKRs:          {total_team_okrs}")
    print(f"  Orphan OKRs:        {len(orphans)}")
    print(f"  Coverage gaps:      {len(gaps)} of {total_company_okrs} company OKRs have no team support")
    print(f"  Conflicts:          {len(conflicts)}")
    print(f"  Alignment score:    {score}/100  {score_label(score)}")
    print()

    if score < 70:
        print("  ⚠️  RECOMMENDED ACTIONS:")
        if orphans:
            print(f"    1. Resolve {len(orphans)} orphan OKR(s) — connect to company goals or cut")
        if gaps:
            print(f"    2. Assign team owners to {len(gaps)} uncovered company OKR(s)")
        if conflicts:
            print(f"    3. Address {len(conflicts)} conflict(s) with shared metrics or constraints")
        print("    4. Run a cross-functional OKR review before next quarter begins")
    print()
    print(f"{'═' * 60}\n")


# ─────────────────────────────────────────────
# Main
# ─────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="Strategic OKR Alignment Checker")
    parser.add_argument("--file", help="Path to JSON file with OKR data")
    parser.add_argument("--sample", action="store_true", help="Print sample JSON format and exit")
    args = parser.parse_args()

    if args.sample:
        print(json.dumps(SAMPLE_DATA, indent=2))
        return

    if args.file:
        try:
            with open(args.file, "r") as f:
                data = json.load(f)
        except FileNotFoundError:
            print(f"Error: File '{args.file}' not found.")
            sys.exit(1)
        except json.JSONDecodeError as e:
            print(f"Error: Invalid JSON in '{args.file}': {e}")
            sys.exit(1)
    else:
        print("No file provided. Running with sample data.\n")
        print("To use your own data: python alignment_checker.py --file your_okrs.json")
        print("To see the expected JSON format: python alignment_checker.py --sample\n")
        data = SAMPLE_DATA

    # Run analysis
    company_ids = get_all_company_okr_ids(data)
    orphans = detect_orphans(data, company_ids)
    gaps, over_indexed, coverage = detect_coverage_gaps(data, company_ids)
    conflicts = detect_conflicts(data)
    score = compute_alignment_score(data, orphans, gaps, conflicts, coverage)

    # Print report
    print_report(data, orphans, gaps, over_indexed, conflicts, coverage, score)


if __name__ == "__main__":
    main()
