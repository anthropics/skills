#!/usr/bin/env python3
"""exception_router.py - Route a discount exception through the policy.

Stdlib-only. Takes an exception request and a matrix path. Decides:
  - IN_POLICY → no exception needed; surface the standard approver
  - EXCEPTION → produces:
      * required approver chain (AE -> ... -> CFO/CRO)
      * required compensating commitments (multi-year prepay, named
        expansion path, reference commitment, MSA tightening, etc.)
      * audit-trail metadata block (timestamp, requested_by, justification,
        compensating_commitments_text, approver_chain)
  - PRECEDENT_RISK → flagged if recent_exceptions[] shows 3+ similar
    asks in the trailing quarter. Signals the matrix may be wrong, not
    the deal.

Usage:
    python exception_router.py --sample
    python exception_router.py --input request.json
    python exception_router.py --input request.json --output json
"""

from __future__ import annotations

import argparse
import json
import sys
import datetime
from typing import Any


SAMPLE_INPUT: dict[str, Any] = {
    "exception_request": {
        "deal_id": "ACME-2026-Q3-204",
        "requested_by": "Jordan Smith, AE",
        "deal_arr": 320000,
        "requested_discount": 42.0,
        "term_months": 36,
        "payment_terms_days": 30,
        "justification": "Customer is a logo competitor displacement; CFO sponsor; pipeline expansion to 3 BU committed verbally.",
        "strategic_value": "logo",
        "customer_threats": ["competitor_proposal", "fy_close_pressure"],
        "submitted_at": "2026-05-19T10:00:00Z",
    },
    "policy_matrix": {
        "profile": "saas",
        "max_discount_pct_without_exception": 35.0,
        "approver_thresholds": [
            [15, "AE"], [25, "Sales Manager"], [35, "Director"], [50, "VP Sales"], [100.1, "CFO + CRO"]
        ],
    },
    "recent_exceptions": [
        {"deal_id": "BETA-2026-Q2-188", "discount": 40, "arr": 280000, "strategic": "logo"},
        {"deal_id": "GAMMA-2026-Q2-192", "discount": 41, "arr": 310000, "strategic": "logo"},
        {"deal_id": "DELTA-2026-Q2-201", "discount": 43, "arr": 350000, "strategic": "expansion"},
    ],
}


# Compensating commitments are NON-NEGOTIABLE per band of exception severity.
# Severity = (requested_discount - max_without_exception).
COMPENSATING_LIBRARY: list[dict[str, Any]] = [
    {
        "severity_floor": 0.0, "severity_ceiling": 5.0,
        "commitments": [
            "multi_year_term (>= 24 months)",
            "annual_prepay (NET-30 or shorter)",
        ],
    },
    {
        "severity_floor": 5.0, "severity_ceiling": 10.0,
        "commitments": [
            "multi_year_term (>= 36 months)",
            "annual_prepay (NET-30 or shorter)",
            "named_expansion_path (BU or product, in writing)",
        ],
    },
    {
        "severity_floor": 10.0, "severity_ceiling": 20.0,
        "commitments": [
            "multi_year_term (>= 36 months) with prepay of years 1+2",
            "named_expansion_path (BU or product, in writing)",
            "reference_commitment (case study + 2 customer-reference calls per year)",
            "msa_tightening (auto-renewal, MFN-protection, indemnity-cap)",
        ],
    },
    {
        "severity_floor": 20.0, "severity_ceiling": 1000.0,
        "commitments": [
            "multi_year_term (>= 36 months) with prepay of years 1+2",
            "named_expansion_path with quantified expansion ARR target",
            "reference_commitment + co-marketing agreement",
            "msa_tightening (auto-renewal, MFN-protection, indemnity-cap)",
            "executive_sponsor_signoff (customer C-level on the contract)",
            "kill_switch: if expansion ARR target missed by end of year 2, renewal reverts to list",
        ],
    },
]


def _approver_chain_for(discount: float, thresholds: list[tuple[float, str]]) -> list[str]:
    """Build cumulative approver chain up to the named human who must sign."""
    chain: list[str] = []
    for cutoff, name in thresholds:
        chain.append(name)
        if discount <= cutoff:
            return chain
    return chain


def _compensating_for(severity: float) -> list[str]:
    for band in COMPENSATING_LIBRARY:
        if band["severity_floor"] <= severity < band["severity_ceiling"]:
            return list(band["commitments"])
    return list(COMPENSATING_LIBRARY[-1]["commitments"])


def _precedent_risk(recent: list[dict[str, Any]], requested_discount: float, strategic_value: str) -> dict[str, Any]:
    similar = [
        r for r in recent
        if abs(r.get("discount", 0) - requested_discount) <= 5
        and r.get("strategic") == strategic_value
    ]
    flag = len(similar) >= 3
    return {
        "similar_recent_count": len(similar),
        "trigger_threshold": 3,
        "flag": flag,
        "matrix_review_recommended": flag,
        "rationale": (
            "3+ similar exceptions in trailing quarter — the policy band may be set wrong; "
            "rebuild the matrix with discount_matrix_builder.py before approving another."
            if flag else "Pattern within tolerance; treat as individual exception."
        ),
    }


def route_exception(payload: dict[str, Any]) -> dict[str, Any]:
    req = payload["exception_request"]
    matrix = payload.get("policy_matrix", {})
    recent = payload.get("recent_exceptions", [])

    max_without = float(matrix.get("max_discount_pct_without_exception", 35.0))
    thresholds: list[tuple[float, str]] = [
        (float(c), n) for c, n in matrix.get("approver_thresholds", [(15, "AE"), (35, "Director"), (100.1, "CFO + CRO")])
    ]

    requested = float(req["requested_discount"])
    in_policy = requested <= max_without
    severity = max(0.0, requested - max_without)

    chain = _approver_chain_for(requested, thresholds)
    if not in_policy:
        # Exceptions always escalate to at least Director — never stop at AE/Manager.
        promoted = []
        seen_director_or_above = False
        for hop in chain:
            promoted.append(hop)
            if hop in ("Director", "Director of Sales", "VP Sales", "VP", "VP Services", "CFO + CRO", "CFO + COO"):
                seen_director_or_above = True
        if not seen_director_or_above:
            promoted.append("Director")
            promoted.append("VP Sales")
        chain = promoted

    compensating = _compensating_for(severity) if not in_policy else []
    precedent = _precedent_risk(recent, requested, req.get("strategic_value", "standard"))

    audit_trail = {
        "deal_id": req.get("deal_id"),
        "requested_by": req.get("requested_by"),
        "requested_discount_pct": requested,
        "deal_arr": req.get("deal_arr"),
        "term_months": req.get("term_months"),
        "justification": req.get("justification"),
        "strategic_value": req.get("strategic_value"),
        "customer_threats": req.get("customer_threats", []),
        "submitted_at": req.get("submitted_at") or datetime.datetime.utcnow().isoformat() + "Z",
        "compensating_commitments_required": compensating,
        "approver_chain": chain,
        "verdict": "IN_POLICY" if in_policy else "EXCEPTION",
    }

    return {
        "verdict": "IN_POLICY" if in_policy else "EXCEPTION",
        "severity_pct_over_threshold": round(severity, 2),
        "approver_chain": chain,
        "required_compensating_commitments": compensating,
        "precedent_risk": precedent,
        "audit_trail": audit_trail,
        "notes": [
            ("In-policy request — route to standard approver; no compensating commitments required."
             if in_policy else
             "EXCEPTION — the chain must capture each compensating commitment in writing before sign."),
            ("Precedent risk FLAGGED — rebuild the matrix before approving."
             if precedent["flag"] else
             "No precedent flag."),
        ],
    }


def render_markdown(result: dict[str, Any]) -> str:
    out = []
    audit = result["audit_trail"]
    out.append(f"# Exception Routing — {audit['deal_id']}")
    out.append("")
    out.append(f"**Verdict:** `{result['verdict']}` "
               f"(severity: {result['severity_pct_over_threshold']} pts over threshold)")
    out.append("")
    out.append("## Approver chain")
    for i, hop in enumerate(result["approver_chain"], 1):
        out.append(f"{i}. {hop}")
    out.append("")
    if result["required_compensating_commitments"]:
        out.append("## Required compensating commitments (NON-NEGOTIABLE)")
        for c in result["required_compensating_commitments"]:
            out.append(f"- {c}")
        out.append("")
    out.append("## Precedent risk")
    pr = result["precedent_risk"]
    out.append(f"- Similar recent exceptions: **{pr['similar_recent_count']}** (trigger: {pr['trigger_threshold']})")
    out.append(f"- Flag: **{'YES' if pr['flag'] else 'no'}**")
    out.append(f"- Rationale: {pr['rationale']}")
    out.append("")
    out.append("## Audit trail")
    out.append("```json")
    out.append(json.dumps(audit, indent=2))
    out.append("```")
    out.append("")
    out.append("## Notes")
    for n in result["notes"]:
        out.append(f"- {n}")
    return "\n".join(out)


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description="Route a discount exception through the policy.")
    ap.add_argument("--input", help="Path to exception request JSON (with policy_matrix + recent_exceptions).")
    ap.add_argument("--output", default="markdown", choices=["markdown", "json"],
                    help="Output format (default: markdown).")
    ap.add_argument("--sample", action="store_true", help="Run with the built-in sample request.")
    args = ap.parse_args(argv)

    if args.sample:
        payload = SAMPLE_INPUT
    elif args.input:
        try:
            with open(args.input, "r", encoding="utf-8") as f:
                payload = json.load(f)
        except Exception as e:
            print(f"ERROR: could not read {args.input}: {e}", file=sys.stderr)
            return 1
    else:
        ap.print_help()
        return 0

    result = route_exception(payload)

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_markdown(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
