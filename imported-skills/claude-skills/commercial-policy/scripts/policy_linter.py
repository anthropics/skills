#!/usr/bin/env python3
"""policy_linter.py - Lint a discount matrix for governance defects.

Stdlib-only. Reads the JSON output of discount_matrix_builder.py (or a
hand-authored matrix in the same shape). Returns a ranked findings report:
  BLOCKER  — policy is internally contradictory or unsignable
  MAJOR    — discoverable gaming surface or missing data backing in a critical cell
  MINOR    — stylistic / completeness issue

Lint rules (deterministic):
  L01 BLOCKER  approver_hierarchy_inversion   — lower-tier approves more than higher-tier
  L02 BLOCKER  cell_band_inverted             — min > max in a cell band
  L03 BLOCKER  margin_floor_below_constraint  — cell margin floor < 50%
  L04 MAJOR    coverage_gap                   — cell missing approver_tier
  L05 MAJOR    cliff_edge                     — adjacent ARR/term/payment cells differ by > 10 pts
  L06 MAJOR    strategic_value_undefined      — strategic tier present but no verifiable definition supplied
  L07 MAJOR    inconsistent_margin_floor      — same arr_band has > 5pt floor variance across cells
  L08 MAJOR    thin_data_in_critical_cell     — critical cell (enterprise/strategic) flagged THIN
  L09 MINOR    cell_unreviewed                — n_observed_deals == 0
  L10 MINOR    missing_exception_marker       — high discount cell without exception flag

Usage:
    python policy_linter.py --sample
    python policy_linter.py --input matrix.json
    python policy_linter.py --input matrix.json --output json
"""

from __future__ import annotations

import argparse
import json
import sys
from typing import Any


SAMPLE_INPUT: dict[str, Any] = {
    "profile": "saas",
    "constraints": {
        "min_margin_pct": 70.0,
        "max_discount_pct_without_exception": 35.0,
        "target_nrr": 1.10,
    },
    "strategic_value_definitions_supplied": False,
    "cells": [
        # A clean cell
        {
            "arr_band": "smb", "term_band": "annual", "payment_band": "net30_prepay", "strategic_tier": "standard",
            "approved_discount_min_pct": 0, "approved_discount_max_pct": 15,
            "approver_tier": "AE", "margin_floor_pct": 70,
            "data_backing": {"n_observed_deals": 8, "win_rate": 0.62, "nrr_12mo_observed": 1.05, "thin_data_flag": False},
            "exception_required": False,
        },
        # Approver inversion — Manager allows 25%, Director below allows only 20%
        {
            "arr_band": "mid", "term_band": "annual", "payment_band": "net30_prepay", "strategic_tier": "standard",
            "approved_discount_min_pct": 8, "approved_discount_max_pct": 25,
            "approver_tier": "Sales Manager", "margin_floor_pct": 70,
            "data_backing": {"n_observed_deals": 6, "win_rate": 0.5, "nrr_12mo_observed": 1.10, "thin_data_flag": False},
            "exception_required": False,
        },
        {
            "arr_band": "mid", "term_band": "two_year", "payment_band": "net30_prepay", "strategic_tier": "standard",
            "approved_discount_min_pct": 5, "approved_discount_max_pct": 20,
            "approver_tier": "Director", "margin_floor_pct": 70,
            "data_backing": {"n_observed_deals": 3, "win_rate": 0.4, "nrr_12mo_observed": 1.12, "thin_data_flag": True},
            "exception_required": False,
        },
        # Inverted band (BLOCKER)
        {
            "arr_band": "enterprise", "term_band": "two_year", "payment_band": "net30_prepay", "strategic_tier": "logo",
            "approved_discount_min_pct": 25, "approved_discount_max_pct": 20,
            "approver_tier": "Director", "margin_floor_pct": 65,
            "data_backing": {"n_observed_deals": 2, "win_rate": 0.5, "nrr_12mo_observed": 1.18, "thin_data_flag": True},
            "exception_required": False,
        },
        # Margin floor below constraint (BLOCKER)
        {
            "arr_band": "strategic", "term_band": "multi_year", "payment_band": "net60_plus", "strategic_tier": "lighthouse",
            "approved_discount_min_pct": 25, "approved_discount_max_pct": 48,
            "approver_tier": "CFO + CRO", "margin_floor_pct": 45,
            "data_backing": {"n_observed_deals": 1, "win_rate": 1.0, "nrr_12mo_observed": 1.30, "thin_data_flag": True},
            "exception_required": True,
        },
        # Coverage gap (no approver)
        {
            "arr_band": "enterprise", "term_band": "multi_year", "payment_band": "net45", "strategic_tier": "expansion",
            "approved_discount_min_pct": 15, "approved_discount_max_pct": 36,
            "approver_tier": None, "margin_floor_pct": 64,
            "data_backing": {"n_observed_deals": 0, "win_rate": None, "nrr_12mo_observed": None, "thin_data_flag": True},
            "exception_required": True,
        },
        # High discount with no exception flag (MINOR)
        {
            "arr_band": "enterprise", "term_band": "two_year", "payment_band": "net30_prepay", "strategic_tier": "logo",
            "approved_discount_min_pct": 18, "approved_discount_max_pct": 40,
            "approver_tier": "VP Sales", "margin_floor_pct": 66,
            "data_backing": {"n_observed_deals": 4, "win_rate": 0.5, "nrr_12mo_observed": 1.12, "thin_data_flag": True},
            "exception_required": False,
        },
    ],
}


APPROVER_RANK = {
    "AE": 1, "Sales Manager": 2, "Director": 3, "Director of Sales": 3,
    "VP Sales": 4, "VP": 4, "VP Services": 4, "CFO + CRO": 5, "CFO + COO": 5,
}


def _rank(approver: str | None) -> int:
    return APPROVER_RANK.get(approver or "", 0)


def lint(matrix: dict[str, Any]) -> dict[str, Any]:
    cells = matrix.get("cells", [])
    constraints = matrix.get("constraints", {})
    max_without = float(constraints.get("max_discount_pct_without_exception", 35.0))
    findings: list[dict[str, Any]] = []

    # L01: approver hierarchy inversion across all cells
    # For each pair, if approver_A rank > approver_B rank but approved_max_A < approved_max_B
    # => the lower-rank approver authorizes a higher discount than the higher-rank approver.
    for i, ci in enumerate(cells):
        for cj in cells[i + 1:]:
            ri, rj = _rank(ci.get("approver_tier")), _rank(cj.get("approver_tier"))
            if ri == 0 or rj == 0 or ri == rj:
                continue
            mi, mj = ci["approved_discount_max_pct"], cj["approved_discount_max_pct"]
            # Identify the higher-rank and lower-rank cell, then check inversion.
            if ri > rj:
                higher, lower, mh, ml = ci, cj, mi, mj
            else:
                higher, lower, mh, ml = cj, ci, mj, mi
            if mh < ml:
                findings.append({
                    "rule_id": "L01", "severity": "BLOCKER",
                    "name": "approver_hierarchy_inversion",
                    "detail": (
                        f"{lower['approver_tier']} approves up to {ml}% in "
                        f"({lower['arr_band']}/{lower['term_band']}/{lower['strategic_tier']}), but "
                        f"{higher['approver_tier']} approves only up to {mh}% in "
                        f"({higher['arr_band']}/{higher['term_band']}/{higher['strategic_tier']})."
                    ),
                    "fix": "Raise the higher-rank approver's cap above the lower-rank cap, or demote the lower-rank cap.",
                })

    # L02: inverted bands
    for c in cells:
        if c["approved_discount_min_pct"] > c["approved_discount_max_pct"]:
            findings.append({
                "rule_id": "L02", "severity": "BLOCKER",
                "name": "cell_band_inverted",
                "detail": f"Cell ({c['arr_band']}/{c['term_band']}/{c['payment_band']}/{c['strategic_tier']}) has min {c['approved_discount_min_pct']}% > max {c['approved_discount_max_pct']}%.",
                "fix": "Recompute the band — min must be <= max.",
            })

    # L03: margin floor below sanity (<50%)
    for c in cells:
        if c["margin_floor_pct"] < 50.0:
            findings.append({
                "rule_id": "L03", "severity": "BLOCKER",
                "name": "margin_floor_below_constraint",
                "detail": f"Cell ({c['arr_band']}/{c['term_band']}/{c['strategic_tier']}) margin floor is {c['margin_floor_pct']}% (< 50%).",
                "fix": "Raise the floor, or carve out this cell as an explicit exception band requiring CFO sign.",
            })

    # L04: coverage gap (no approver)
    for c in cells:
        if not c.get("approver_tier"):
            findings.append({
                "rule_id": "L04", "severity": "MAJOR",
                "name": "coverage_gap",
                "detail": f"Cell ({c['arr_band']}/{c['term_band']}/{c['payment_band']}/{c['strategic_tier']}) has no approver_tier assigned.",
                "fix": "Assign a named approver tier per the approver_thresholds table.",
            })

    # L05: cliff edges — same dim differing by > 10 pts on adjacent bands.
    # Compare cells differing only in arr_band (adjacent), then only in term_band, then only in payment.
    ARR_ORDER = ["smb", "mid", "enterprise", "strategic"]
    TERM_ORDER = ["annual", "two_year", "multi_year"]
    PAY_ORDER = ["net30_prepay", "net45", "net60_plus"]

    by_key: dict[tuple, dict[str, Any]] = {}
    for c in cells:
        key = (c["arr_band"], c["term_band"], c["payment_band"], c["strategic_tier"])
        by_key[key] = c

    def _adj(order: list[str], v: str) -> str | None:
        try:
            idx = order.index(v)
            return order[idx + 1] if idx + 1 < len(order) else None
        except ValueError:
            return None

    for key, c in by_key.items():
        arr, term, pay, strat = key
        for dim, order, axis in [(arr, ARR_ORDER, "arr"), (term, TERM_ORDER, "term"), (pay, PAY_ORDER, "payment")]:
            nxt = _adj(order, dim)
            if not nxt:
                continue
            adj_key = (
                nxt if axis == "arr" else arr,
                nxt if axis == "term" else term,
                nxt if axis == "payment" else pay,
                strat,
            )
            adj = by_key.get(adj_key)
            if not adj:
                continue
            delta = abs(adj["approved_discount_max_pct"] - c["approved_discount_max_pct"])
            if delta > 10:
                findings.append({
                    "rule_id": "L05", "severity": "MAJOR",
                    "name": "cliff_edge",
                    "detail": (
                        f"{axis} cliff between ({c['arr_band']}/{c['term_band']}/{c['payment_band']}/{c['strategic_tier']}) "
                        f"max {c['approved_discount_max_pct']}% and ({adj['arr_band']}/{adj['term_band']}/{adj['payment_band']}/{adj['strategic_tier']}) "
                        f"max {adj['approved_discount_max_pct']}% — {delta} pts apart."
                    ),
                    "fix": "Smooth the gradient — large jumps create gaming surfaces (e.g., AE splits a $101K deal into 2x $50.5K to dodge the band).",
                })

    # L06: strategic_value_undefined — if any strategic tier > 'standard' is used and definitions absent
    used_strategic = {c["strategic_tier"] for c in cells if c["strategic_tier"] != "standard"}
    if used_strategic and not matrix.get("strategic_value_definitions_supplied", False):
        findings.append({
            "rule_id": "L06", "severity": "MAJOR",
            "name": "strategic_value_undefined",
            "detail": f"Strategic tiers used ({sorted(used_strategic)}) but no verifiable definition supplied in the matrix.",
            "fix": "Add strategic_value_definitions_supplied=true plus a definitions section: e.g., 'logo = top-20 enterprise in named target list; expansion = signed MSA with named BU expansion path'.",
        })

    # L07: inconsistent margin floor within an arr_band
    by_arr: dict[str, list[float]] = {}
    for c in cells:
        by_arr.setdefault(c["arr_band"], []).append(c["margin_floor_pct"])
    for arr_band, floors in by_arr.items():
        if floors and (max(floors) - min(floors)) > 5:
            findings.append({
                "rule_id": "L07", "severity": "MAJOR",
                "name": "inconsistent_margin_floor",
                "detail": f"Margin floor in arr_band={arr_band} varies by {max(floors) - min(floors):.1f} pts (min {min(floors)}, max {max(floors)}).",
                "fix": "Pick one floor per arr_band — variance > 5 pts suggests the strategic-tier allowance is undisciplined.",
            })

    # L08: thin data in critical cell
    for c in cells:
        if c["arr_band"] in ("enterprise", "strategic") and c.get("data_backing", {}).get("thin_data_flag"):
            findings.append({
                "rule_id": "L08", "severity": "MAJOR",
                "name": "thin_data_in_critical_cell",
                "detail": f"Critical cell ({c['arr_band']}/{c['term_band']}/{c['strategic_tier']}) flagged THIN (n={c['data_backing'].get('n_observed_deals')}).",
                "fix": "Treat band as directional until n>=5; do not publish to AEs as binding without flagging directional.",
            })

    # L09: cell unreviewed (n=0)
    for c in cells:
        if (c.get("data_backing", {}) or {}).get("n_observed_deals", 0) == 0:
            findings.append({
                "rule_id": "L09", "severity": "MINOR",
                "name": "cell_unreviewed",
                "detail": f"Cell ({c['arr_band']}/{c['term_band']}/{c['payment_band']}/{c['strategic_tier']}) has zero observed deals.",
                "fix": "Mark as PROVISIONAL in the matrix doc; revisit at the next quarterly review.",
            })

    # L10: high discount cell w/o exception flag
    for c in cells:
        if c["approved_discount_max_pct"] > max_without and not c.get("exception_required"):
            findings.append({
                "rule_id": "L10", "severity": "MINOR",
                "name": "missing_exception_marker",
                "detail": (
                    f"Cell ({c['arr_band']}/{c['term_band']}/{c['strategic_tier']}) max {c['approved_discount_max_pct']}% "
                    f"exceeds max_without_exception ({max_without}%) but exception_required is False."
                ),
                "fix": "Set exception_required=True so deal-desk routes through exception_router.py.",
            })

    severity_rank = {"BLOCKER": 0, "MAJOR": 1, "MINOR": 2}
    findings.sort(key=lambda f: (severity_rank[f["severity"]], f["rule_id"]))

    counts = {"BLOCKER": 0, "MAJOR": 0, "MINOR": 0}
    for f in findings:
        counts[f["severity"]] += 1

    return {
        "n_cells_linted": len(cells),
        "n_findings": len(findings),
        "counts": counts,
        "verdict": (
            "PASS" if counts["BLOCKER"] == 0 and counts["MAJOR"] == 0
            else "FAIL" if counts["BLOCKER"] > 0
            else "PASS_WITH_WARNINGS"
        ),
        "findings": findings,
    }


def render_markdown(report: dict[str, Any]) -> str:
    out = []
    out.append("# Policy Lint Report")
    out.append("")
    out.append(f"- Cells linted: **{report['n_cells_linted']}**")
    out.append(f"- Findings: **{report['n_findings']}** "
               f"(BLOCKER: {report['counts']['BLOCKER']}, MAJOR: {report['counts']['MAJOR']}, MINOR: {report['counts']['MINOR']})")
    out.append(f"- Verdict: **{report['verdict']}**")
    out.append("")
    if not report["findings"]:
        out.append("No findings. Matrix passes lint.")
        return "\n".join(out)
    out.append("## Findings (ranked)")
    out.append("")
    out.append("| # | Severity | Rule | Detail | Suggested fix |")
    out.append("|---|---|---|---|---|")
    for i, f in enumerate(report["findings"], 1):
        out.append(
            f"| {i} | **{f['severity']}** | `{f['rule_id']}` {f['name']} | {f['detail']} | {f['fix']} |"
        )
    out.append("")
    out.append("## Next steps")
    if report["counts"]["BLOCKER"] > 0:
        out.append("- Resolve every BLOCKER before publishing the matrix to AEs. Blockers indicate the policy is unsignable as written.")
    if report["counts"]["MAJOR"] > 0:
        out.append("- Address MAJOR findings within one policy-review cycle. They surface gaming risk or coverage holes.")
    if report["counts"]["MINOR"] > 0:
        out.append("- Track MINOR findings in the quarterly policy review.")
    return "\n".join(out)


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description="Lint a discount matrix for governance defects.")
    ap.add_argument("--input", help="Path to matrix JSON (output of discount_matrix_builder.py).")
    ap.add_argument("--output", default="markdown", choices=["markdown", "json"],
                    help="Output format (default: markdown).")
    ap.add_argument("--sample", action="store_true", help="Run with the built-in sample matrix.")
    args = ap.parse_args(argv)

    if args.sample:
        matrix = SAMPLE_INPUT
    elif args.input:
        try:
            with open(args.input, "r", encoding="utf-8") as f:
                matrix = json.load(f)
        except Exception as e:
            print(f"ERROR: could not read {args.input}: {e}", file=sys.stderr)
            return 1
    else:
        ap.print_help()
        return 0

    report = lint(matrix)

    if args.output == "json":
        print(json.dumps(report, indent=2))
    else:
        print(render_markdown(report))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
