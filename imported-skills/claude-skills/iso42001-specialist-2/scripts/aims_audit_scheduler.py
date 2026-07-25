#!/usr/bin/env python3
"""aims_audit_scheduler.py — ISO/IEC 42001 Clause 9.2 internal audit plan generator.

Stdlib-only. Produces a 12-month internal audit schedule for an AIMS with:
  - quarterly audit slots
  - clause + Annex A control coverage per slot
  - auditor assignments with independence checks (no self-audit)
  - rolling 3-year coverage to ensure every clause + applicable control is audited
  - prior-year nonconformity follow-up scheduled in Q1

Deterministic logic. No LLM calls. Stdlib only.

Input schema (JSON):
{
  "organization": "Acme AI Inc.",
  "audit_year": 2026,
  "certification_cycle_phase": "year_2",   # year_1 | year_2 | year_3 | surveillance
  "ai_systems_in_scope": ["recommendation_engine", "internal_llm_tools", "vendor_ai_chatbot"],
  "applicable_annex_a_controls": ["A.2.2", "A.3.2", "A.5.2", "A.6.2.4", "A.7.3", "A.8.4", "A.9.3", "A.10.2"],
  "auditors": [
    {"id": "alice", "name": "Alice Chen", "role": "quality_engineer", "owns_clauses": ["8.3"]},
    {"id": "bob", "name": "Bob Singh", "role": "ml_engineer", "owns_clauses": ["8.3", "A.6.2.4"]},
    {"id": "carol", "name": "Carol Diaz", "role": "external_auditor", "owns_clauses": []},
    {"id": "dave", "name": "Dave Park", "role": "ciso", "owns_clauses": ["A.10.2"]}
  ],
  "prior_year_findings": [
    {"clause": "9.2", "severity": "major", "status": "open"},
    {"clause": "A.7.3", "severity": "minor", "status": "closed"}
  ]
}

Usage:
    python aims_audit_scheduler.py
    python aims_audit_scheduler.py path/to/scope.json
    python aims_audit_scheduler.py scope.json --output json
"""

import argparse
import json
import sys
from typing import Any, Dict, List


SAMPLE: Dict[str, Any] = {
    "organization": "Acme AI Inc.",
    "audit_year": 2026,
    "certification_cycle_phase": "year_2",
    "ai_systems_in_scope": ["recommendation_engine", "internal_llm_tools", "vendor_ai_chatbot"],
    "applicable_annex_a_controls": [
        "A.2.2", "A.3.2", "A.5.2", "A.6.2.4", "A.7.3", "A.8.4", "A.9.3", "A.10.2"
    ],
    "auditors": [
        {"id": "alice", "name": "Alice Chen", "role": "quality_engineer", "owns_clauses": ["8.3"]},
        {"id": "bob", "name": "Bob Singh", "role": "ml_engineer", "owns_clauses": ["8.3", "A.6.2.4"]},
        {"id": "carol", "name": "Carol Diaz", "role": "external_auditor", "owns_clauses": []},
        {"id": "dave", "name": "Dave Park", "role": "ciso", "owns_clauses": ["A.10.2"]},
    ],
    "prior_year_findings": [
        {"clause": "9.2", "severity": "major", "status": "open"},
        {"clause": "A.7.3", "severity": "minor", "status": "closed"},
    ],
}


# Always-audit clauses (full coverage every year)
ANNUAL_CLAUSES = ["4.3", "5.1", "5.2", "5.3", "9.3", "10.2"]

# 3-year rotation for deep-dive clauses
ROTATION_Q2 = ["6.1.2", "6.1.3", "6.1.4", "6.2"]
ROTATION_Q3 = ["7.1", "7.2", "7.3", "7.4", "7.5", "8.1", "8.2", "8.3", "8.4"]
ROTATION_Q4 = ["9.1", "9.2", "10.1"]


def assign_auditor(scope_items: List[str], auditors: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Pick the auditor with the fewest independence conflicts in this scope."""
    best_auditor = None
    best_conflicts = 999
    for a in auditors:
        owns = set(a.get("owns_clauses", []))
        conflicts = sum(1 for s in scope_items if s in owns)
        if conflicts < best_conflicts:
            best_conflicts = conflicts
            best_auditor = a
    if best_auditor is None:
        return {"id": None, "name": "UNASSIGNED", "independent": False, "conflicts": []}

    owns = set(best_auditor.get("owns_clauses", []))
    conflicts = [s for s in scope_items if s in owns]
    return {
        "id": best_auditor["id"],
        "name": best_auditor["name"],
        "role": best_auditor["role"],
        "independent": len(conflicts) == 0,
        "conflicts": conflicts,
    }


def build_quarter(label: str, scope_clauses: List[str], scope_controls: List[str],
                  auditors: List[Dict[str, Any]], extra_notes: str = "") -> Dict[str, Any]:
    all_scope = scope_clauses + scope_controls
    auditor = assign_auditor(all_scope, auditors)
    return {
        "quarter": label,
        "scope_clauses": scope_clauses,
        "scope_annex_a_controls": scope_controls,
        "auditor": auditor,
        "notes": extra_notes,
    }


def plan(payload: Dict[str, Any]) -> Dict[str, Any]:
    year = int(payload.get("audit_year", 2026))
    phase = payload.get("certification_cycle_phase", "year_2")
    systems = payload.get("ai_systems_in_scope", [])
    controls = payload.get("applicable_annex_a_controls", [])
    auditors = payload.get("auditors", [])
    prior_findings = payload.get("prior_year_findings", [])
    open_priors = [f for f in prior_findings if f.get("status") != "closed"]

    # 3-year control rotation: split applicable controls into thirds
    third = max(1, len(controls) // 3)
    controls_y1 = controls[0:third]
    controls_y2 = controls[third:2 * third]
    controls_y3 = controls[2 * third:]
    phase_to_controls = {
        "year_1": controls_y1, "year_2": controls_y2,
        "year_3": controls_y3, "surveillance": controls_y3,
    }
    this_year_controls = phase_to_controls.get(phase, controls_y2)

    # Q1: leadership + scope + prior-year follow-up
    q1_clauses = ["4.3", "5.1", "5.2", "5.3"]
    q1_notes = f"Follow up {len(open_priors)} open prior-year finding(s)." if open_priors else "No open priors."
    q1 = build_quarter(f"Q1 {year}", q1_clauses, [], auditors, q1_notes)

    # Q2: planning + objectives + risk
    q2 = build_quarter(f"Q2 {year}", ROTATION_Q2, this_year_controls[:max(1, len(this_year_controls) // 2)], auditors)

    # Q3: support + operation
    q3_controls = this_year_controls[max(1, len(this_year_controls) // 2):]
    q3_notes = f"Deep-dive across {len(systems)} AI systems: {', '.join(systems)}."
    q3 = build_quarter(f"Q3 {year}", ROTATION_Q3, q3_controls, auditors, q3_notes)

    # Q4: performance + improvement + management review
    q4_notes = "Management review inputs prepared per Clause 9.3."
    q4 = build_quarter(f"Q4 {year}", ROTATION_Q4 + ANNUAL_CLAUSES[-2:], [], auditors, q4_notes)

    # Independence audit
    quarters = [q1, q2, q3, q4]
    independence_issues = [{
        "quarter": q["quarter"], "auditor": q["auditor"]["name"], "conflicts": q["auditor"]["conflicts"]
    } for q in quarters if not q["auditor"]["independent"]]

    # Coverage check
    audited_clauses = set()
    audited_controls = set()
    for q in quarters:
        audited_clauses.update(q["scope_clauses"])
        audited_controls.update(q["scope_annex_a_controls"])

    return {
        "organization": payload.get("organization"),
        "audit_year": year,
        "certification_cycle_phase": phase,
        "ai_systems_in_scope": systems,
        "open_prior_findings": len(open_priors),
        "quarters": quarters,
        "independence_issues": independence_issues,
        "coverage_summary": {
            "clauses_audited_this_year": sorted(audited_clauses),
            "controls_audited_this_year": sorted(audited_controls),
            "controls_deferred_to_future_years": sorted(
                set(controls) - audited_controls
            ),
        },
    }


def render_text(p: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("ISO/IEC 42001 — CLAUSE 9.2 INTERNAL AUDIT PLAN")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Organization: {p['organization']}")
    lines.append(f"Year: {p['audit_year']}  |  Cert cycle phase: {p['certification_cycle_phase']}")
    lines.append(f"AI systems in scope: {', '.join(p['ai_systems_in_scope'])}")
    lines.append(f"Open prior-year findings: {p['open_prior_findings']}")
    lines.append("")
    lines.append("-" * 72)
    lines.append("QUARTERLY SCHEDULE:")
    lines.append("")

    for q in p["quarters"]:
        a = q["auditor"]
        flag = "" if a["independent"] else "  ⚠️ INDEPENDENCE CONFLICT"
        lines.append(f"  {q['quarter']}  →  Auditor: {a['name']} ({a['role']}){flag}")
        if q["scope_clauses"]:
            lines.append(f"      Clauses: {', '.join(q['scope_clauses'])}")
        if q["scope_annex_a_controls"]:
            lines.append(f"      Annex A: {', '.join(q['scope_annex_a_controls'])}")
        if a["conflicts"]:
            lines.append(f"      ⚠️ Conflicts on: {', '.join(a['conflicts'])} — reassign or use external auditor")
        if q["notes"]:
            lines.append(f"      Notes: {q['notes']}")
        lines.append("")

    if p["independence_issues"]:
        lines.append("-" * 72)
        lines.append(f"INDEPENDENCE ISSUES ({len(p['independence_issues'])}):")
        for issue in p["independence_issues"]:
            lines.append(f"  - {issue['quarter']}: {issue['auditor']} owns {', '.join(issue['conflicts'])}")
        lines.append("")

    c = p["coverage_summary"]
    lines.append("-" * 72)
    lines.append("3-YEAR COVERAGE STATUS:")
    lines.append(f"  Clauses audited this year ({len(c['clauses_audited_this_year'])}): {', '.join(c['clauses_audited_this_year'])}")
    lines.append(f"  Annex A controls audited this year ({len(c['controls_audited_this_year'])}): {', '.join(c['controls_audited_this_year']) or 'none'}")
    lines.append(f"  Controls deferred to future years ({len(c['controls_deferred_to_future_years'])}): {', '.join(c['controls_deferred_to_future_years']) or 'none'}")
    lines.append("")
    lines.append("RULES: every clause + every applicable Annex A control must be audited at least once per 3-year cert cycle.")
    lines.append("       Same auditor cannot audit work they own (Clause 9.2 independence).")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="ISO/IEC 42001 Clause 9.2 internal audit 12-month plan generator.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to audit scope JSON (uses embedded sample if omitted)")
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
        source = "<embedded sample: year-2 cert cycle, 3 systems, 8 controls applicable>"

    result = plan(payload)
    if args.output == "json":
        print(json.dumps({"source": source, **result}, indent=2))
    else:
        print(render_text(result, source))
    return 0


if __name__ == "__main__":
    sys.exit(main())
