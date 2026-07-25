#!/usr/bin/env python3
"""contract_risk_scanner.py — Scan a contract for founder-killer clauses.

Stdlib-only. Outputs human-readable or JSON. Detects 12 common risk patterns:
  1. Unilateral termination favoring the counterparty
  2. Auto-renewal with long notice (60+ days)
  3. Uncapped liability or exclusion of standard caps
  4. Broad indemnification flowing one direction
  5. Non-mutual confidentiality
  6. Missing or vague IP ownership clauses
  7. Aggressive non-compete / non-solicit
  8. Choice of law/venue in counterparty's home jurisdiction (one-sided)
  9. Force majeure favoring only the counterparty
 10. Missing DPA reference when personal data flows
 11. Most-favored-nation pricing clauses
 12. Audit rights without reciprocity

NOT legal advice. Use this to triage; bring findings to qualified counsel.

Usage:
    python contract_risk_scanner.py                       # uses embedded sample
    python contract_risk_scanner.py path/to/contract.txt
    python contract_risk_scanner.py contract.txt --output json
    python contract_risk_scanner.py --help
"""

import argparse
import json
import re
import sys
from dataclasses import dataclass, asdict
from typing import List


SAMPLE_CONTRACT = """\
MASTER SERVICES AGREEMENT

This Agreement shall automatically renew for successive one (1) year terms
unless either party provides ninety (90) days written notice of non-renewal.

LIMITATION OF LIABILITY. In no event shall Provider's aggregate liability
arising out of this Agreement exceed the fees paid by Customer in the
twelve (12) months preceding the claim. Notwithstanding the foregoing,
Customer's indemnification obligations under Section 8 shall be uncapped.

INDEMNIFICATION. Customer shall defend, indemnify and hold harmless
Provider, its affiliates, officers, directors and employees from and against
any and all claims, damages, losses and expenses arising out of or relating
to Customer's use of the Services.

INTELLECTUAL PROPERTY. The parties agree that intellectual property created
during the engagement shall belong to the party who develops it.

NON-COMPETE. For a period of three (3) years following termination, Customer
shall not engage with any competitor of Provider in any capacity, in any
geography.

GOVERNING LAW. This Agreement shall be governed by the laws of Delaware,
and any disputes shall be resolved exclusively in the state and federal
courts located in Wilmington, Delaware.

FORCE MAJEURE. Provider shall not be liable for any failure to perform due
to causes beyond its reasonable control.
"""


@dataclass
class Finding:
    rule_id: str
    severity: str           # CRITICAL | HIGH | MEDIUM | LOW
    title: str
    excerpt: str
    why_it_matters: str
    suggested_redline: str


RULES = [
    {
        "id": "AUTO_RENEW_LONG_NOTICE",
        "severity": "HIGH",
        "title": "Auto-renewal with long notice period",
        "pattern": re.compile(
            r"automatically renew.{0,200}?(\d+|sixty|ninety|one hundred|180)\s*(\(\d+\))?\s*day",
            re.IGNORECASE | re.DOTALL,
        ),
        "why_it_matters": (
            "Auto-renewal with >30 day notice is a classic vendor trap: founders forget the "
            "deadline and get locked into another full term. Especially painful on multi-year contracts."
        ),
        "redline": (
            "Counter: '...unless either party provides thirty (30) days written notice of non-renewal' "
            "OR remove auto-renewal entirely and require affirmative re-signature."
        ),
    },
    {
        "id": "UNCAPPED_CUSTOMER_INDEMNITY",
        "severity": "CRITICAL",
        "title": "Customer indemnity carved out from liability cap (uncapped)",
        "pattern": re.compile(
            r"(customer'?s|your)\s+indemnification.{0,200}?(uncapped|shall be uncapped|excluded from)",
            re.IGNORECASE | re.DOTALL,
        ),
        "why_it_matters": (
            "Uncapped customer indemnity means a single bad claim can exceed all fees ever paid. "
            "Standard practice: mutual indemnity, both sides capped at fees, with narrow carve-outs "
            "(IP infringement, data breach, gross negligence)."
        ),
        "redline": (
            "Counter: cap customer indemnity at 12 months of fees, mutual indemnity, carve-outs only "
            "for willful misconduct and breach of confidentiality."
        ),
    },
    {
        "id": "ONE_SIDED_INDEMNITY",
        "severity": "HIGH",
        "title": "Indemnification flows in one direction only",
        "pattern": re.compile(
            r"(customer|client)\s+shall\s+(defend|indemnify).{0,500}?(provider|company|vendor)",
            re.IGNORECASE | re.DOTALL,
        ),
        "why_it_matters": (
            "One-sided indemnity means you take on risk for the counterparty's actions without reciprocity. "
            "A balanced contract has mutual indemnification with mirrored carve-outs."
        ),
        "redline": (
            "Counter: 'Each party shall defend, indemnify and hold harmless the other party...' with "
            "mirrored scope and equal caps."
        ),
    },
    {
        "id": "VAGUE_IP",
        "severity": "CRITICAL",
        "title": "Vague IP ownership clause",
        "pattern": re.compile(
            r"intellectual property.{0,200}?(belong to the party who develops it|jointly owned|to be determined|as agreed)",
            re.IGNORECASE | re.DOTALL,
        ),
        "why_it_matters": (
            "Vague IP language is the #1 source of post-engagement disputes. Joint ownership often means "
            "neither party can license freely without the other's consent. 'As agreed' is unenforceable."
        ),
        "redline": (
            "Counter: 'All work product, deliverables, and derivative works created under this Agreement "
            "shall be the sole and exclusive property of Customer. Provider hereby assigns all right, title "
            "and interest...' Or explicitly carve out Provider's pre-existing IP and tools with a license back."
        ),
    },
    {
        "id": "AGGRESSIVE_NONCOMPETE",
        "severity": "HIGH",
        "title": "Aggressive non-compete (long duration or broad geography)",
        "pattern": re.compile(
            r"non.compete.{0,300}?(two|three|four|five|2|3|4|5)\s*\(?\d*\)?\s*year",
            re.IGNORECASE | re.DOTALL,
        ),
        "why_it_matters": (
            "Non-competes >12 months or with unbounded geography are often unenforceable (especially in "
            "California, and increasingly federally) but create chilling effects. They also signal the "
            "counterparty's overall negotiation posture."
        ),
        "redline": (
            "Counter: maximum 12 months, specific competitor list (not 'any competitor'), specific "
            "geography. For California-resident counterparties, remove entirely (California labor code "
            "voids most non-competes)."
        ),
    },
    {
        "id": "ONE_SIDED_VENUE",
        "severity": "MEDIUM",
        "title": "Choice of law/venue exclusively in counterparty jurisdiction",
        "pattern": re.compile(
            r"(exclusively in|exclusive jurisdiction).{0,300}?(courts? located in|state and federal courts of)",
            re.IGNORECASE | re.DOTALL,
        ),
        "why_it_matters": (
            "Exclusive venue in counterparty's jurisdiction means you bear travel cost and out-of-state "
            "counsel cost for any dispute. For startups this can effectively prevent enforcement."
        ),
        "redline": (
            "Counter: neutral venue (Delaware is common), or 'venue in the jurisdiction of the defendant' "
            "(forces plaintiff to travel), or arbitration in a neutral location with AAA/JAMS rules."
        ),
    },
    {
        "id": "ONE_SIDED_FORCE_MAJEURE",
        "severity": "MEDIUM",
        "title": "Force majeure clause favors one party",
        "pattern": re.compile(
            r"(provider|company|vendor)\s+shall not be liable.{0,200}?(force majeure|causes beyond)",
            re.IGNORECASE | re.DOTALL,
        ),
        "why_it_matters": (
            "If only the vendor gets force-majeure protection, you pay full price during a pandemic / "
            "outage / supply chain disruption but receive nothing. Mutual force majeure is standard."
        ),
        "redline": (
            "Counter: 'Neither party shall be liable...' with explicit list of qualifying events "
            "(pandemic, war, natural disaster, government action) and a termination right after 30 days."
        ),
    },
    {
        "id": "MISSING_DPA",
        "severity": "HIGH",
        "title": "Personal data appears to flow but no DPA referenced",
        "pattern": re.compile(
            r"(personal data|personally identifiable|user data|customer data|PII)(?!.{0,500}(DPA|data processing agreement|GDPR))",
            re.IGNORECASE | re.DOTALL,
        ),
        "why_it_matters": (
            "If personal data of EU residents (or California residents) flows, a DPA is legally required. "
            "Missing DPA = GDPR Article 28 violation, potential 4%-of-revenue fine, contract unenforceable "
            "with EU customers."
        ),
        "redline": (
            "Counter: 'The parties shall execute a Data Processing Agreement substantially in the form "
            "of Exhibit X prior to any processing of Personal Data.' Use IAPP or Vendor-friendly DPA template."
        ),
    },
    {
        "id": "MOST_FAVORED_NATION",
        "severity": "MEDIUM",
        "title": "Most-favored-nation (MFN) pricing clause",
        "pattern": re.compile(
            r"(most.favored.nation|MFN|best price|lowest price).{0,200}?(offered to|charged to)",
            re.IGNORECASE | re.DOTALL,
        ),
        "why_it_matters": (
            "MFN clauses prevent you from offering volume discounts or strategic pricing to anyone else. "
            "If you sign with one customer, every future customer can demand the same price."
        ),
        "redline": (
            "Counter: remove the MFN entirely. If kept, narrow to 'similarly situated customers, same "
            "tier and volume, excluding strategic / launch / migration discounts.'"
        ),
    },
    {
        "id": "ONE_SIDED_AUDIT",
        "severity": "MEDIUM",
        "title": "Audit rights without reciprocity",
        "pattern": re.compile(
            r"(customer|client).{0,100}?right to audit",
            re.IGNORECASE | re.DOTALL,
        ),
        "why_it_matters": (
            "One-sided audit rights mean the counterparty can demand records on demand, often at your "
            "expense. Reciprocity is standard for B2B agreements."
        ),
        "redline": (
            "Counter: mutual audit rights, max once per year, at requesting party's expense, with "
            "30-day notice, during business hours, narrowed to specific compliance categories."
        ),
    },
    {
        "id": "BROAD_NON_SOLICIT",
        "severity": "MEDIUM",
        "title": "Broad non-solicit (employees AND customers, long duration)",
        "pattern": re.compile(
            r"non.solicit.{0,300}?(employees? and customers?|customers? and employees?)",
            re.IGNORECASE | re.DOTALL,
        ),
        "why_it_matters": (
            "Combined employee + customer non-solicits, especially with long duration, can severely "
            "limit hiring and business development. Many states limit enforceability."
        ),
        "redline": (
            "Counter: split into employee-only (12 months max) and customer-only (12 months max) clauses, "
            "with carve-outs for general advertising / open job postings and for customers who initiate "
            "contact independently."
        ),
    },
    {
        "id": "PERPETUAL_LICENSE_BACK",
        "severity": "HIGH",
        "title": "Perpetual license-back to counterparty of your data or work",
        "pattern": re.compile(
            r"perpetual.{0,100}?(license|right).{0,300}?(customer data|user data|work product|deliverables)",
            re.IGNORECASE | re.DOTALL,
        ),
        "why_it_matters": (
            "A perpetual license-back lets the counterparty use your data or deliverables forever, even "
            "after termination. This is acceptable for usage analytics, NOT for customer data or core IP."
        ),
        "redline": (
            "Counter: time-limited license (for the term of the agreement only), specific purpose "
            "(service delivery only, not training AI models, not sharing with third parties), and "
            "post-termination return-or-destroy obligation."
        ),
    },
]


def scan(text: str) -> List[Finding]:
    findings: List[Finding] = []
    for rule in RULES:
        for match in rule["pattern"].finditer(text):
            excerpt = match.group(0).strip()
            # truncate long excerpts
            if len(excerpt) > 300:
                excerpt = excerpt[:297] + "..."
            findings.append(Finding(
                rule_id=rule["id"],
                severity=rule["severity"],
                title=rule["title"],
                excerpt=excerpt,
                why_it_matters=rule["why_it_matters"],
                suggested_redline=rule["redline"],
            ))
    # rank by severity then rule order
    severity_order = {"CRITICAL": 0, "HIGH": 1, "MEDIUM": 2, "LOW": 3}
    findings.sort(key=lambda f: (severity_order.get(f.severity, 9), f.rule_id))
    return findings


def render_text(findings: List[Finding], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("CONTRACT RISK SCAN")
    lines.append(f"Source: {source}")
    lines.append(f"Findings: {len(findings)}")
    lines.append("=" * 72)
    lines.append("")
    if not findings:
        lines.append("No risk patterns matched. (Absence of findings does not mean the contract is safe;")
        lines.append("it means the 12 common patterns this scanner checks did not trigger.)")
        lines.append("")
        lines.append("Always engage qualified counsel before signing.")
        return "\n".join(lines)

    severity_counts = {}
    for f in findings:
        severity_counts[f.severity] = severity_counts.get(f.severity, 0) + 1
    severity_summary = "  ".join(
        f"{sev}: {severity_counts.get(sev, 0)}"
        for sev in ("CRITICAL", "HIGH", "MEDIUM", "LOW")
        if severity_counts.get(sev, 0) > 0
    )
    lines.append(f"Severity: {severity_summary}")
    lines.append("")

    for i, f in enumerate(findings, 1):
        lines.append(f"[{i}] {f.severity} — {f.title}")
        lines.append(f"    Rule: {f.rule_id}")
        lines.append(f"    Excerpt: \"{f.excerpt}\"")
        lines.append("")
        lines.append(f"    Why it matters:")
        for line in _wrap(f.why_it_matters, 4):
            lines.append(line)
        lines.append("")
        lines.append(f"    Suggested redline:")
        for line in _wrap(f.suggested_redline, 4):
            lines.append(line)
        lines.append("")
        lines.append("-" * 72)

    lines.append("")
    lines.append("REMINDER: This scanner triages obvious traps. Always bring redlines to qualified counsel.")
    return "\n".join(lines)


def _wrap(text: str, indent: int, width: int = 68) -> List[str]:
    import textwrap
    return textwrap.wrap(text, width=width, initial_indent=" " * indent, subsequent_indent=" " * indent) or [" " * indent + text]


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Scan a contract for the 12 most common founder-killer clauses.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to contract text file (uses embedded sample if omitted)")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    args = parser.parse_args()

    if args.path:
        try:
            with open(args.path, "r", encoding="utf-8") as f:
                text = f.read()
            source = args.path
        except (IOError, OSError) as e:
            print(f"error: could not read {args.path}: {e}", file=sys.stderr)
            return 1
    else:
        text = SAMPLE_CONTRACT
        source = "<embedded sample MSA>"

    findings = scan(text)

    if args.output == "json":
        payload = {
            "source": source,
            "findings_count": len(findings),
            "findings": [asdict(f) for f in findings],
        }
        print(json.dumps(payload, indent=2))
    else:
        print(render_text(findings, source))

    return 0


if __name__ == "__main__":
    sys.exit(main())
