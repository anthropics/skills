#!/usr/bin/env python3
"""eng_team_structure_designer.py — Squad/tribe structure + manager-trigger.

Stdlib-only. Takes team profile and outputs:
  - Recommended structure (informal pods / squads only / squads + chapters / squads + tribes)
  - Number of squads needed (5-9 ICs per squad as the heuristic)
  - Manager-trigger (do you need to hire/promote an EM now?)
  - Director-trigger (3+ EMs without a director)
  - Span-of-control assessment

Deterministic logic based on headcount + IC/manager distribution.

Input schema (JSON):
{
  "total_engineers": 25,
  "ic_count": 22,
  "em_count": 3,
  "director_count": 0,
  "vpe_or_cto_count": 1,
  "current_squads": 3,
  "work_streams_count": 4,
  "data_culture_supports_chapters": false
}

Usage:
    python eng_team_structure_designer.py                       # uses embedded 25-eng sample
    python eng_team_structure_designer.py path/to/team.json
    python eng_team_structure_designer.py team.json --output json
"""

import argparse
import json
import math
import sys
from typing import Any, Dict, List


SAMPLE: Dict[str, Any] = {
    "total_engineers": 25,
    "ic_count": 22,
    "em_count": 3,
    "director_count": 0,
    "vpe_or_cto_count": 1,
    "current_squads": 3,
    "work_streams_count": 4,
    "data_culture_supports_chapters": False,
}


def recommend_structure(total: int, ics: int, ems: int, work_streams: int) -> Dict[str, Any]:
    if total <= 5:
        return {
            "structure": "One team, no formal structure",
            "rationale": "Sub-6 engineers: structure adds overhead with no benefit. Everyone works directly together.",
            "kill_criteria": "Grow past 5 engineers AND specialization emerges → move to informal pods.",
        }
    if total <= 15:
        return {
            "structure": "2-3 informal pods (no chapters yet)",
            "rationale": f"{total} engineers across {work_streams} work streams. Informal pods around work streams. Founder-CTO can still know everyone personally.",
            "kill_criteria": "Reach 15 engineers OR hire first dedicated EM → formalize squads.",
        }
    if total <= 40:
        suggested_squads = max(2, math.ceil(ics / 7))  # 5-9 per squad, target 7
        return {
            "structure": f"Formal squads ({suggested_squads} squads of ~5-9 ICs each)",
            "rationale": f"{total} engineers — squad model with EMs leading each squad. Chapters emerge informally for skill sharing.",
            "kill_criteria": "Reach 40+ engineers OR 3+ EMs without a director → add director layer + tribes.",
        }
    if total <= 100:
        suggested_squads = max(4, math.ceil(ics / 7))
        suggested_tribes = max(2, math.ceil(suggested_squads / 4))
        return {
            "structure": f"Squads + tribes ({suggested_squads} squads grouped into {suggested_tribes} tribes)",
            "rationale": f"{total} engineers — tribes cluster related squads. Director per tribe. Formal chapters for cross-squad skill alignment.",
            "kill_criteria": "Reach 100+ engineers → add VPE + multiple directors.",
        }
    # 100+
    suggested_squads = math.ceil(ics / 7)
    suggested_tribes = max(3, math.ceil(suggested_squads / 4))
    return {
        "structure": f"Multi-tribe ({suggested_squads} squads in {suggested_tribes} tribes; VPE + directors per tribe)",
        "rationale": f"{total} engineers at scale — VPE owns operating model; directors run tribes; EMs run squads; tech leads on each squad.",
        "kill_criteria": "Federated model emerging — group EMs / staff EMs / senior directors layer needed.",
    }


def manager_trigger(ics: int, ems: int) -> Dict[str, Any]:
    if ems == 0 and ics >= 6:
        return {
            "trigger_fired": True,
            "trigger": "First EM hire",
            "rationale": f"{ics} ICs with no EM. Above 5-7 ICs, a non-coding manager is needed to handle 1:1s, hiring, performance — work that's blocking IC time today.",
            "recommendation": "Internal promote preferred (knows the team + product); external hire if no senior IC ready for management.",
        }
    if ems > 0:
        per_em = ics / ems
        if per_em > 10:
            return {
                "trigger_fired": True,
                "trigger": "Add EM",
                "rationale": f"{ics} ICs across {ems} EMs = {per_em:.1f} per EM (above healthy 5-8 range).",
                "recommendation": "Add an EM OR split squads to reduce span.",
            }
        if per_em < 4:
            return {
                "trigger_fired": True,
                "trigger": "Span-of-control too small",
                "rationale": f"{per_em:.1f} ICs per EM (below 4). EMs become over-involved in IC work.",
                "recommendation": "Combine squads OR have an EM also tech-lead a squad (player-coach role at smaller scale).",
            }
    return {
        "trigger_fired": False,
        "trigger": "No EM trigger fired",
        "rationale": f"{ics} ICs across {ems} EMs — span of control healthy.",
        "recommendation": "Continue at current structure.",
    }


def director_trigger(ems: int, directors: int) -> Dict[str, Any]:
    if directors == 0 and ems >= 3:
        return {
            "trigger_fired": True,
            "trigger": "First director hire",
            "rationale": f"{ems} EMs reporting directly to VPE/CTO. Above 3 EMs, the CTO/VPE loses time on individual EM coaching.",
            "recommendation": "Hire or promote a director to manage EMs. CTO/VPE retains strategic role.",
        }
    if directors > 0 and ems > 0:
        per_director = ems / directors
        if per_director > 6:
            return {
                "trigger_fired": True,
                "trigger": "Add director",
                "rationale": f"{ems} EMs across {directors} directors = {per_director:.1f} per director (above 4-6 range).",
                "recommendation": "Add a director OR consolidate tribes.",
            }
    return {
        "trigger_fired": False,
        "trigger": "No director trigger fired",
        "rationale": f"{ems} EMs across {directors} directors — span healthy.",
        "recommendation": "Continue at current structure.",
    }


def analyze(team: Dict[str, Any]) -> Dict[str, Any]:
    total = team.get("total_engineers", 0)
    ics = team.get("ic_count", 0)
    ems = team.get("em_count", 0)
    directors = team.get("director_count", 0)
    work_streams = team.get("work_streams_count", 0)
    current_squads = team.get("current_squads", 0)

    structure = recommend_structure(total, ics, ems, work_streams)
    mgr_trigger = manager_trigger(ics, ems)
    dir_trigger = director_trigger(ems, directors)

    # Squad sizing assessment
    if current_squads > 0 and ics > 0:
        avg_squad_size = ics / current_squads
        squad_warnings = []
        if avg_squad_size < 5:
            squad_warnings.append(f"Average squad size {avg_squad_size:.1f} ICs (below 5-9 healthy range): squads too small, consolidate")
        elif avg_squad_size > 9:
            squad_warnings.append(f"Average squad size {avg_squad_size:.1f} ICs (above 5-9 healthy range): squads too large, split")
        squad_assessment = {
            "current_squads": current_squads,
            "ics_per_squad_avg": round(avg_squad_size, 1),
            "warnings": squad_warnings,
        }
    else:
        squad_assessment = {
            "current_squads": current_squads,
            "ics_per_squad_avg": None,
            "warnings": [],
        }

    return {
        "team_size": total,
        "ic_count": ics,
        "em_count": ems,
        "director_count": directors,
        "structure_recommendation": structure,
        "manager_trigger": mgr_trigger,
        "director_trigger": dir_trigger,
        "squad_assessment": squad_assessment,
    }


def render_text(result: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("ENGINEERING TEAM STRUCTURE")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Team: {result['team_size']} total ({result['ic_count']} ICs + {result['em_count']} EMs + {result['director_count']} directors)")
    lines.append("")
    lines.append("-" * 72)

    s = result["structure_recommendation"]
    lines.append(f"RECOMMENDED STRUCTURE: {s['structure']}")
    lines.append("")
    lines.append(f"  Rationale: {s['rationale']}")
    lines.append("")
    lines.append(f"  Kill criteria (when to evolve): {s['kill_criteria']}")
    lines.append("")
    lines.append("-" * 72)

    sa = result["squad_assessment"]
    lines.append(f"SQUAD ASSESSMENT:")
    lines.append(f"  Current squads: {sa['current_squads']}")
    if sa["ics_per_squad_avg"] is not None:
        lines.append(f"  Average ICs per squad: {sa['ics_per_squad_avg']}  (healthy: 5-9)")
    if sa["warnings"]:
        for w in sa["warnings"]:
            lines.append(f"  ⚠️  {w}")
    else:
        lines.append("  ✓ Squad sizing within healthy range")
    lines.append("")
    lines.append("-" * 72)

    mt = result["manager_trigger"]
    marker = "🔴" if mt["trigger_fired"] else "🟢"
    lines.append(f"MANAGER TRIGGER: {marker} {mt['trigger']}")
    lines.append(f"  {mt['rationale']}")
    lines.append(f"  Recommendation: {mt['recommendation']}")
    lines.append("")

    dt = result["director_trigger"]
    marker = "🔴" if dt["trigger_fired"] else "🟢"
    lines.append(f"DIRECTOR TRIGGER: {marker} {dt['trigger']}")
    lines.append(f"  {dt['rationale']}")
    lines.append(f"  Recommendation: {dt['recommendation']}")
    lines.append("")
    lines.append("-" * 72)
    lines.append("REMINDER: Structure follows headcount, but Conway's Law cuts both ways: the structure")
    lines.append("you design will shape the systems you build. Pair this with cs-cto-advisor for")
    lines.append("architecture alignment, and with cs-chro-advisor for comp + leveling.")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Eng team structure recommendation + manager/director triggers + squad sizing.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to team JSON (uses embedded sample if omitted)")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    args = parser.parse_args()

    if args.path:
        try:
            with open(args.path, "r", encoding="utf-8") as f:
                team = json.load(f)
            source = args.path
        except (IOError, OSError) as e:
            print(f"error: could not read {args.path}: {e}", file=sys.stderr)
            return 1
        except json.JSONDecodeError as e:
            print(f"error: invalid JSON in {args.path}: {e}", file=sys.stderr)
            return 1
    else:
        team = SAMPLE
        source = "<embedded sample: 25-engineer team, 22 ICs / 3 EMs / 1 CTO>"

    result = analyze(team)

    if args.output == "json":
        print(json.dumps({"source": source, **result}, indent=2))
    else:
        print(render_text(result, source))

    return 0


if __name__ == "__main__":
    sys.exit(main())
