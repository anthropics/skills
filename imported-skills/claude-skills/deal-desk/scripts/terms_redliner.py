#!/usr/bin/env python3
"""terms_redliner.py - Detect commercial-contract landmines in a deal's terms.

Stdlib-only. Takes a JSON description of the deal's terms (NOT the full contract
text — for full text scanning, see c-level-advisor/skills/general-counsel-advisor/
scripts/contract_risk_scanner.py).

Detects 10 founder/seller-killer patterns and emits a RANKED REDLINE LIST with:
  - severity        CRITICAL | HIGH | MEDIUM | LOW
  - the standard counter-language
  - the NAMED legal/commercial approver (no auto-approval; everything routes)

The skill never says the deal is fine on terms; it only outputs which clauses
need human sign-off and by whom.

Usage:
    python terms_redliner.py --sample
    python terms_redliner.py --input deal_terms.json
    python terms_redliner.py --input deal_terms.json --output json
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, asdict, field


SAMPLE_TERMS = {
    "deal_id": "ACME-2026-Q2-117",
    "payment_terms_days": 75,
    "auto_renew": True,
    "auto_renew_notice_days": 90,
    "indemnity_cap": None,            # None = uncapped
    "liability_cap": 1.0,             # multiplier on annual fees (1x = standard)
    "dpa_present": False,
    "eu_data_involved": True,
    "ip_assignment": "ambiguous",     # "customer" | "vendor" | "ambiguous" | "perpetual_license_back"
    "mfn_clause_present": True,
    "exclusivity_clause_present": False,
    "exclusivity_compensated": False,
    "non_solicit_years": 3,
    "governing_law": "Delaware",
    "vendor_home_jurisdiction": "Delaware",
}


SEVERITY_RANK = {"CRITICAL": 0, "HIGH": 1, "MEDIUM": 2, "LOW": 3}


@dataclass
class Redline:
    rule_id: str
    severity: str
    title: str
    why_it_matters: str
    standard_counter: str
    approver: str


def _rules() -> list[dict]:
    """Each rule: id, severity, title, predicate(terms), why, counter, approver."""
    return [
        {
            "id": "UNCAPPED_INDEMNITY",
            "severity": "CRITICAL",
            "title": "Uncapped indemnity exposure",
            "predicate": lambda t: t.get("indemnity_cap") is None,
            "why": (
                "Uncapped indemnity is the single biggest founder-killer in commercial "
                "contracts. A breach claim can wipe out the company."
            ),
            "counter": (
                "Cap indemnity at 12x monthly fees OR mutual cap; carve out only IP "
                "infringement and gross-negligence/willful-misconduct."
            ),
            "approver": "General Counsel + CFO",
        },
        {
            "id": "MISSING_DPA_EU_DATA",
            "severity": "CRITICAL",
            "title": "EU personal data flows but no DPA",
            "predicate": lambda t: t.get("eu_data_involved") and not t.get("dpa_present"),
            "why": (
                "GDPR Art. 28 requires a DPA when personal data of EU residents is "
                "processed. Missing DPA = regulatory exposure + customer audit fail."
            ),
            "counter": (
                "Attach standard DPA (SCC 2021/914 or your template) and confirm "
                "sub-processor list. Block close until DPA is countersigned."
            ),
            "approver": "General Counsel + DPO",
        },
        {
            "id": "MFN_PRICING",
            "severity": "HIGH",
            "title": "Most-Favored-Nation pricing clause present",
            "predicate": lambda t: bool(t.get("mfn_clause_present")),
            "why": (
                "MFN binds you to refund any customer whose price drops below this one. "
                "Limits future flexibility on bundles, segments, and competitive deals."
            ),
            "counter": (
                "Strike MFN entirely. If counterparty insists, narrow to 'same SKU, "
                "same volume, same term, same geography' and time-bound to 12 months."
            ),
            "approver": "VP Sales + CFO",
        },
        {
            "id": "AUTORENEW_LONG_NOTICE",
            "severity": "HIGH",
            "title": "Auto-renew with notice window > 30 days",
            "predicate": lambda t: (
                t.get("auto_renew") and int(t.get("auto_renew_notice_days") or 0) > 30
            ),
            "why": (
                "Long notice windows on auto-renew are a classic trap: easy to miss, "
                "and locks you into another full term. Especially painful on multi-year."
            ),
            "counter": (
                "Reduce notice to 30 days OR require affirmative re-signature each term."
            ),
            "approver": "Deal Desk + General Counsel",
        },
        {
            "id": "PERPETUAL_LICENSE_BACK",
            "severity": "CRITICAL",
            "title": "Perpetual license-back of IP to customer",
            "predicate": lambda t: t.get("ip_assignment") == "perpetual_license_back",
            "why": (
                "Perpetual license-back gives the customer rights to use your IP "
                "forever, often royalty-free, surviving termination. Kills moat."
            ),
            "counter": (
                "Convert to time-bounded license tied to subscription term, "
                "field-of-use restricted, no transferability."
            ),
            "approver": "General Counsel + CEO",
        },
        {
            "id": "AMBIGUOUS_IP",
            "severity": "HIGH",
            "title": "IP ownership ambiguous",
            "predicate": lambda t: t.get("ip_assignment") == "ambiguous",
            "why": (
                "Ambiguous IP becomes a dispute at acquisition diligence. Costs "
                "weeks of legal review and can break a deal."
            ),
            "counter": (
                "Clarify: vendor retains all pre-existing IP and IP developed in "
                "delivery; customer owns its data and outputs derived solely from it."
            ),
            "approver": "General Counsel",
        },
        {
            "id": "EXCLUSIVITY_UNCOMPENSATED",
            "severity": "CRITICAL",
            "title": "Exclusivity clause without compensation",
            "predicate": lambda t: (
                t.get("exclusivity_clause_present") and not t.get("exclusivity_compensated")
            ),
            "why": (
                "Free exclusivity removes addressable market for no economic benefit. "
                "Even paid exclusivity needs a kill switch on missed quarterly minimums."
            ),
            "counter": (
                "Either strike exclusivity OR price it (minimum guaranteed spend) AND "
                "add an exit ramp if MGS isn't hit two consecutive quarters."
            ),
            "approver": "CRO + General Counsel",
        },
        {
            "id": "LONG_PAYMENT_TERMS",
            "severity": "HIGH",
            "title": "Payment terms longer than NET-45",
            "predicate": lambda t: int(t.get("payment_terms_days") or 0) > 45,
            "why": (
                "NET-60/75/90 inflates DSO, ties up working capital, and is a classic "
                "buyer ploy. Material on any deal > 10% of cash balance."
            ),
            "counter": (
                "Counter to NET-30; offer 1-2% discount for NET-15 prepay if customer "
                "won't move. Add late-payment interest of 1.5% / mo on any overdue."
            ),
            "approver": "CFO + Deal Desk",
        },
        {
            "id": "LOW_LIABILITY_CAP",
            "severity": "MEDIUM",
            "title": "Liability cap below 1x annual fees",
            "predicate": lambda t: float(t.get("liability_cap") or 0.0) < 1.0,
            "why": (
                "Customer pushing for sub-1x cap usually indicates they expect "
                "outsized claims. Don't accept without symmetric protection."
            ),
            "counter": (
                "Hold liability cap at 1x annual fees (12-month look-back), mutual; "
                "super-cap (3x) on IP and confidentiality breaches if needed."
            ),
            "approver": "General Counsel",
        },
        {
            "id": "BROAD_NON_SOLICIT",
            "severity": "MEDIUM",
            "title": "Non-solicit longer than 12 months",
            "predicate": lambda t: int(t.get("non_solicit_years") or 0) >= 2,
            "why": (
                "Multi-year non-solicit limits hiring and is increasingly unenforceable "
                "in many US jurisdictions (e.g. California). Negotiate down."
            ),
            "counter": (
                "Cap non-solicit at 12 months post-termination, scoped to employees "
                "directly engaged on the project, with exception for general advertising."
            ),
            "approver": "General Counsel + CHRO",
        },
    ]


def scan_terms(terms: dict) -> list[Redline]:
    findings: list[Redline] = []
    for rule in _rules():
        try:
            if rule["predicate"](terms):
                findings.append(
                    Redline(
                        rule_id=rule["id"],
                        severity=rule["severity"],
                        title=rule["title"],
                        why_it_matters=rule["why"],
                        standard_counter=rule["counter"],
                        approver=rule["approver"],
                    )
                )
        except (KeyError, TypeError, ValueError):
            # Missing or malformed field for this rule -> skip silently
            continue
    findings.sort(key=lambda r: (SEVERITY_RANK[r.severity], r.rule_id))
    return findings


def _render_human(deal_id: str, findings: list[Redline]) -> str:
    lines = []
    lines.append(f"Terms Redline Report: {deal_id}")
    lines.append(f"{len(findings)} landmine(s) detected.")
    lines.append("")
    if not findings:
        lines.append("No flagged terms. STILL route to General Counsel for sign-off — ")
        lines.append("this scanner only catches the 10 most common patterns.")
        return "\n".join(lines)
    for i, f in enumerate(findings, start=1):
        lines.append(f"{i}. [{f.severity}] {f.title}")
        lines.append(f"   why: {f.why_it_matters}")
        lines.append(f"   counter: {f.standard_counter}")
        lines.append(f"   approver: {f.approver}")
        lines.append("")
    lines.append("note: This is a triage tool, not legal advice. All HIGH/CRITICAL")
    lines.append("      findings must be reviewed by named approver before signing.")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Scan deal terms JSON for commercial-contract landmines.",
    )
    parser.add_argument("--input", help="Path to JSON terms")
    parser.add_argument("--output", default="human", choices=["human", "json"])
    parser.add_argument("--sample", action="store_true")
    args = parser.parse_args(argv)

    if args.sample or not args.input:
        terms = SAMPLE_TERMS
    else:
        with open(args.input) as f:
            terms = json.load(f)

    findings = scan_terms(terms)
    deal_id = str(terms.get("deal_id", "UNSPECIFIED"))
    if args.output == "json":
        print(json.dumps({
            "deal_id": deal_id,
            "finding_count": len(findings),
            "findings": [asdict(f) for f in findings],
        }, indent=2))
    else:
        print(_render_human(deal_id, findings))
    return 0


if __name__ == "__main__":
    sys.exit(main())
