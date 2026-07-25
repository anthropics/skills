#!/usr/bin/env python3
"""ost_linter.py — structural linter for Opportunity Solution Trees.

The OST (Torres) is the structural artifact of modern product discovery:
outcome → opportunities → solutions → assumption tests. Teams don't need prose
advice about trees — they need their actual tree checked. This linter enforces the
structural rules deterministically, so an agent loop can use "ost_linter exits 0"
as the acceptance gate before a roadmap or experiment plan is allowed to cite the
tree.

Rules:
  O1 exactly one outcome root, phrased measurably (contains a number, or a
     `metric` field is present)
  O2 opportunities are needs/pains/desires, not features — flag statements that
     start with build-verbs (add/build/implement/create/integrate/launch/ship)
  O3 every opportunity marked "target": true has >= 2 solutions under
     consideration (compare-and-contrast, never a single pet solution)
  O4 every solution carries >= 1 assumption test
  O5 no orphan solutions attached directly to the outcome — a solution without an
     opportunity is the feature-factory anti-pattern

Input JSON (see --sample):
  {"outcome": {"statement": str, "metric": str?},
   "opportunities": [{"statement": str, "target": bool?,
                      "children": [<nested opportunities>]?,
                      "solutions": [{"statement": str,
                                     "tests": [{"assumption": str, "type": str}]}]}],
   "solutions": [ ... ]   # anything here is an O5 violation by definition
  }

Exit codes: 0 clean (warnings allowed) · 2 violations found · 3 unreadable input.
Exception: `--sample` always exits 0 — it is a smoke test, and the bundled tree
deliberately contains one O2 and one O4 violation so the report output is visible.
Stdlib only, deterministic.
"""

import argparse
import json
import re
import sys

BUILD_VERBS = re.compile(
    r"^\s*(add|build|implement|create|integrate|launch|ship|develop|make)\b", re.I)

SAMPLE_TREE = {
    "outcome": {"statement": "Increase week-4 retention from 22% to 30%",
                "metric": "week-4 retention"},
    "opportunities": [
        {"statement": "New users can't tell whether setup worked",
         "target": True,
         "solutions": [
             {"statement": "Post-setup verification checklist",
              "tests": [{"assumption": "users abandon because they doubt setup succeeded",
                         "type": "interview"}]},
             {"statement": "Live sample-data preview after connect",
              "tests": [{"assumption": "a working preview reduces first-week drop-off",
                         "type": "prototype"}]},
         ]},
        {"statement": "Add an onboarding wizard",
         "solutions": [
             {"statement": "Onboarding wizard v2", "tests": []},
         ]},
    ],
    "solutions": [],
}


def walk_opportunities(nodes, path="opportunities"):
    for idx, node in enumerate(nodes or []):
        here = f"{path}[{idx}]"
        yield here, node
        yield from walk_opportunities(node.get("children"), here + ".children")


def lint(tree: dict):
    violations, warnings = [], []
    outcome = tree.get("outcome")
    if not isinstance(outcome, dict) or not str(outcome.get("statement", "")).strip():
        violations.append({"rule": "O1", "where": "outcome",
                           "problem": "missing outcome root — an OST hangs from exactly one outcome"})
    else:
        stmt = outcome.get("statement", "")
        if not (re.search(r"\d", stmt) or str(outcome.get("metric", "")).strip()):
            violations.append({"rule": "O1", "where": "outcome",
                               "problem": f"outcome is not measurable: '{stmt[:80]}' — "
                                          "state a metric and a target number"})

    opp_count = 0
    for where, opp in walk_opportunities(tree.get("opportunities")):
        opp_count += 1
        stmt = str(opp.get("statement", ""))
        if BUILD_VERBS.match(stmt):
            violations.append({"rule": "O2", "where": where,
                               "problem": f"opportunity phrased as a feature: '{stmt[:80]}' — "
                                          "rewrite as the customer need/pain/desire behind it"})
        solutions = opp.get("solutions") or []
        if opp.get("target") and len(solutions) < 2:
            violations.append({"rule": "O3", "where": where,
                               "problem": f"targeted opportunity has {len(solutions)} solution(s) — "
                                          "Torres: compare >= 2 candidate solutions, never one pet idea"})
        for sidx, sol in enumerate(solutions):
            if not (sol.get("tests") or []):
                violations.append({"rule": "O4", "where": f"{where}.solutions[{sidx}]",
                                   "problem": f"solution '{str(sol.get('statement', ''))[:60]}' has no "
                                              "assumption test — untested solutions are opinions"})

    orphans = tree.get("solutions") or []
    for sidx, sol in enumerate(orphans):
        violations.append({"rule": "O5", "where": f"solutions[{sidx}]",
                           "problem": f"orphan solution '{str(sol.get('statement', ''))[:60]}' attached to "
                                      "no opportunity — the feature-factory anti-pattern"})

    if opp_count == 0 and not violations:
        warnings.append("tree has an outcome but zero opportunities — map the opportunity "
                        "space before jumping to solutions")
    return violations, warnings, opp_count


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Lint an Opportunity Solution Tree for structural discipline (Torres canon).")
    ap.add_argument("--input", help="Path to the OST JSON ('-' for stdin).")
    ap.add_argument("--output", choices=["json", "human"], default="json")
    ap.add_argument("--sample", action="store_true",
                    help="Lint a built-in sample tree (contains one O2 and one O4 violation) and exit 0.")
    args = ap.parse_args()

    if args.sample:
        tree = SAMPLE_TREE
    elif args.input:
        try:
            tree = json.load(sys.stdin if args.input == "-"
                             else open(args.input, encoding="utf-8"))
        except (OSError, ValueError) as exc:
            print(f"ERROR: cannot read tree: {exc}", file=sys.stderr)
            return 3
    else:
        ap.error("--input is required (or use --sample)")

    violations, warnings, opp_count = lint(tree)
    result = {
        "opportunities": opp_count,
        "violations": violations,
        "warnings": warnings,
        "verdict": "STRUCTURALLY-SOUND" if not violations else "NEEDS-REWORK",
    }
    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(f"Verdict: {result['verdict']} ({opp_count} opportunities, "
              f"{len(violations)} violation(s))")
        for v in violations:
            print(f"  [{v['rule']}] {v['where']}: {v['problem']}")
        for w in warnings:
            print(f"  (warn) {w}")
    if args.sample:
        return 0
    return 0 if not violations else 2


if __name__ == "__main__":
    sys.exit(main())
