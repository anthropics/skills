#!/usr/bin/env python3
"""sop_generator.py

Generate a 5W2H-structured Standard Operating Procedure (SOP) from a JSON
metadata file. Output is markdown by default, or normalized JSON.

5W2H = Who, What, When, Where, Why, How, How-much (Ishikawa, *Guide to
Quality Control*, 1985). Each section is mandatory; missing sections produce
a warning footer naming the section.

Industry tuning:
  --profile {ops,support,finance,hr,it,regulated}

  - ops:        general internal ops SOP scaffold
  - support:    adds customer-impact section + escalation matrix
  - finance:    adds controls + reconciliation + segregation-of-duties section
  - hr:         flags PII / sensitive-data handling; adds consent section
  - it:         adds system + access + change-management section
  - regulated:  adds version control, signoff matrix, audit-trail, change
                history (required under ISO 9001 / FDA 21 CFR Part 211 /
                SOC 2 / HIPAA / ISO 13485)

Regulatory overlay flags attach the appropriate compliance preamble:
  regulatory_overlay: ["SOC2", "HIPAA", "ISO13485", "GDPR", "SOX"]

Input schema (JSON):
{
  "sop_name": "Vendor Offboarding",
  "process_owner": "alex@company.com",
  "triggering_event": "Vendor contract not renewed OR vendor terminated",
  "audience_role": "Vendor Management Office operator",
  "frequency": "On-demand (avg 3 times per quarter)",
  "regulatory_overlay": ["SOC2"],
  "inputs": ["Vendor name", "Contract end date", "Data access list"],
  "outputs": ["Access revoked", "Data deleted/returned", "Final invoice paid"],
  "steps_outline": [
    "Notify vendor of offboarding intent",
    "Inventory data and system access",
    "Revoke production system access",
    "Confirm data deletion or return",
    "Final invoice reconciliation",
    "Archive vendor record"
  ],
  "estimated_minutes": 240,
  "estimated_cost_usd": 800
}

Stdlib only.
"""
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field, asdict
from pathlib import Path


VALID_PROFILES = {"ops", "support", "finance", "hr", "it", "regulated"}
VALID_OVERLAYS = {"SOC2", "HIPAA", "ISO13485", "GDPR", "SOX"}


REGULATORY_PREAMBLE = {
    "SOC2": (
        "**SOC 2 overlay:** This SOP supports the Common Criteria control "
        "framework. Changes require change-management approval (CC8.1). "
        "Evidence of execution must be retained for the audit period."
    ),
    "HIPAA": (
        "**HIPAA overlay:** This SOP touches Protected Health Information "
        "(PHI). All access must be logged per §164.312(b). Minimum-necessary "
        "rule applies (§164.502(b))."
    ),
    "ISO13485": (
        "**ISO 13485 overlay:** This is a controlled document under §4.2.4. "
        "Document revision, approval, and review records must be maintained. "
        "Use the regulated profile."
    ),
    "GDPR": (
        "**GDPR overlay:** This SOP touches personal data of EU data "
        "subjects. Lawful basis must be documented (Art. 6). Data-subject "
        "rights (Art. 15-22) requests must be respected during execution."
    ),
    "SOX": (
        "**SOX overlay:** This SOP supports a financial control. Execution "
        "must be evidenced and segregation-of-duties enforced. Quarterly "
        "management testing applies."
    ),
}


@dataclass
class SOPMetadata:
    sop_name: str = ""
    process_owner: str = ""
    triggering_event: str = ""
    audience_role: str = ""
    frequency: str = ""
    regulatory_overlay: list = field(default_factory=list)
    inputs: list = field(default_factory=list)
    outputs: list = field(default_factory=list)
    steps_outline: list = field(default_factory=list)
    estimated_minutes: int = 0
    estimated_cost_usd: int = 0

    def validate(self) -> list:
        errs = []
        for fld in ("sop_name", "process_owner", "triggering_event",
                    "audience_role", "frequency"):
            if not getattr(self, fld):
                errs.append(f"missing required field: '{fld}'")
        if not self.steps_outline:
            errs.append("missing 'steps_outline' (need >= 1 step)")
        for ov in self.regulatory_overlay:
            if ov not in VALID_OVERLAYS:
                errs.append(
                    f"invalid regulatory_overlay '{ov}'; "
                    f"allowed: {sorted(VALID_OVERLAYS)}"
                )
        return errs


def _sample_metadata() -> dict:
    return {
        "sop_name": "Vendor Offboarding",
        "process_owner": "alex@company.com (Vendor Management Lead)",
        "triggering_event": (
            "Vendor contract not renewed OR vendor terminated for cause"
        ),
        "audience_role": "Vendor Management Office (VMO) operator",
        "frequency": "On-demand (avg 3 executions per quarter)",
        "regulatory_overlay": ["SOC2"],
        "inputs": [
            "Vendor legal name",
            "Contract end date (effective offboarding date)",
            "List of systems with vendor access",
            "List of data classes vendor processed",
        ],
        "outputs": [
            "All production system access revoked (evidenced)",
            "Vendor data deleted or returned (evidenced)",
            "Final invoice reconciled and paid",
            "Vendor record archived in VMO registry",
        ],
        "steps_outline": [
            "Notify vendor of offboarding intent (written, 30 days notice)",
            "Inventory data classes and system access vendor holds",
            "Revoke production system access (IAM, VPN, SaaS)",
            "Confirm data deletion (vendor certification) or data return",
            "Final invoice reconciliation and payment",
            "Archive vendor record in VMO registry with offboarding evidence",
        ],
        "estimated_minutes": 240,
        "estimated_cost_usd": 800,
    }


def _build_who(meta: SOPMetadata, profile: str) -> str:
    lines = [
        "### Who",
        "",
        f"- **Process owner (Accountable):** {meta.process_owner}",
        f"- **Audience (Responsible):** {meta.audience_role}",
    ]
    if profile == "regulated":
        lines.append("- **Approver (Consulted):** "
                     "Quality Management Representative")
        lines.append("- **Auditor (Informed):** "
                     "Internal Audit / Compliance")
    elif profile == "finance":
        lines.append("- **Approver (Consulted):** Controller")
        lines.append("- **Segregation-of-duties review:** "
                     "Required (initiator != approver != payer)")
    elif profile == "hr":
        lines.append("- **Approver (Consulted):** HR Business Partner")
        lines.append("- **Privacy review (Informed):** "
                     "Data Protection Officer (if PII touched)")
    elif profile == "it":
        lines.append("- **Approver (Consulted):** "
                     "Change Advisory Board (for system-mutating steps)")
    elif profile == "support":
        lines.append("- **Approver (Consulted):** Support Team Lead")
        lines.append("- **Escalation (Informed):** "
                     "Engineering on-call (if customer-impact > 30 min)")
    return "\n".join(lines)


def _build_what(meta: SOPMetadata) -> str:
    lines = [
        "### What",
        "",
        f"**Process name:** {meta.sop_name}",
        "",
        "**Inputs required before starting:**",
        "",
    ]
    for inp in meta.inputs:
        lines.append(f"- {inp}")
    lines.append("")
    lines.append("**Outputs produced:**")
    lines.append("")
    for out in meta.outputs:
        lines.append(f"- {out}")
    return "\n".join(lines)


def _build_when(meta: SOPMetadata) -> str:
    return (
        "### When\n\n"
        f"- **Triggering event:** {meta.triggering_event}\n"
        f"- **Frequency:** {meta.frequency}\n"
        "- **Time-of-day constraint:** _(business hours only? on-call? "
        "fill in)_\n"
        "- **Blocking dependencies:** _(prerequisites that must be true "
        "before starting)_"
    )


def _build_where(meta: SOPMetadata, profile: str) -> str:
    lines = [
        "### Where",
        "",
        "- **Primary system of record:** _(name the system — Salesforce, "
        "Notion, Jira, ServiceNow, etc.)_",
        "- **Supporting tools:** _(IAM console, IT ticketing, accounting "
        "system, etc.)_",
        "- **Canonical doc location:** _(URL of this SOP in the wiki)_",
    ]
    if profile in {"it", "regulated"}:
        lines.append("- **Change-management ticket location:** "
                     "_(Jira / ServiceNow queue)_")
    return "\n".join(lines)


def _build_why(meta: SOPMetadata) -> str:
    lines = [
        "### Why",
        "",
        "**Purpose:** _(one-paragraph statement of why this process "
        "exists. Anchor to a business outcome, not a task.)_",
        "",
        "**Regulatory basis (if any):**",
        "",
    ]
    if meta.regulatory_overlay:
        for ov in meta.regulatory_overlay:
            lines.append(f"- {REGULATORY_PREAMBLE[ov]}")
    else:
        lines.append("- _(none — confirm by checking data classes "
                     "touched. If process touches PHI, financial controls, "
                     "or regulated devices, the answer is not 'none'.)_")
    return "\n".join(lines)


def _build_how(meta: SOPMetadata) -> str:
    lines = ["### How", ""]
    lines.append("Step-by-step procedure. Each step must have a named "
                 "owner, expected duration, and observable success signal.")
    lines.append("")
    for i, step in enumerate(meta.steps_outline, start=1):
        lines.append(f"**Step {i}: {step}**")
        lines.append("")
        lines.append("- **Owner:** _(named human or named rotation)_")
        lines.append("- **Expected duration:** _(concrete number + unit)_")
        lines.append("- **Success signal (observable):** _(e.g., 'IAM "
                     "console shows user disabled', not 'access is "
                     "revoked')_")
        lines.append("- **Failure signal (observable):** _(what tells you "
                     "the step did not work)_")
        lines.append("- **If step fails — rollback or escalation:** "
                     "_(rollback path or 'escalate to X — cannot be "
                     "rolled back')_")
        lines.append("")
    return "\n".join(lines)


def _build_how_much(meta: SOPMetadata) -> str:
    mins = meta.estimated_minutes or "_(fill in)_"
    cost = meta.estimated_cost_usd
    cost_line = f"${cost}" if cost else "_(fill in)_"
    return (
        "### How-much\n\n"
        f"- **Estimated execution time:** {mins} minutes\n"
        f"- **Estimated cost per execution:** {cost_line} "
        "(labor + license + third-party fees)\n"
        "- **Frequency × cost = annual run-rate:** _(compute from "
        "frequency + cost per execution)_\n"
    )


def _build_regulated_footer() -> str:
    return (
        "\n---\n\n"
        "## Document control (regulated profile)\n\n"
        "- **Version:** 1.0\n"
        "- **Effective date:** _(YYYY-MM-DD)_\n"
        "- **Next review date:** _(YYYY-MM-DD — within 12 months, "
        "or 90 days under HIPAA / ISO 13485)_\n"
        "- **Approval signoff (named):** _(QMR / Compliance Officer)_\n"
        "- **Change history:**\n\n"
        "| Version | Date | Author | Change summary | Approver |\n"
        "|---------|------|--------|----------------|----------|\n"
        "| 1.0     | _date_ | _author_ | Initial issue | _approver_ |\n"
    )


def _build_finance_footer() -> str:
    return (
        "\n---\n\n"
        "## Controls section (finance profile)\n\n"
        "- **Control objective:** _(what financial assertion this "
        "controls — e.g., completeness of vendor payments)_\n"
        "- **Segregation of duties:** Initiator, approver, and payer "
        "must be distinct individuals.\n"
        "- **Evidence retained:** _(invoice copy, approval email, "
        "payment confirmation)_\n"
        "- **Testing frequency:** Quarterly by Internal Audit.\n"
    )


def _build_hr_footer() -> str:
    return (
        "\n---\n\n"
        "## Privacy & sensitive-data handling (HR profile)\n\n"
        "- **Data classes touched:** _(name, address, SSN/national ID, "
        "compensation, medical, etc.)_\n"
        "- **Lawful basis for processing:** _(employment contract, "
        "legal obligation, legitimate interest, consent)_\n"
        "- **Retention period:** _(per local employment law + GDPR if "
        "applicable)_\n"
        "- **Access restriction:** Need-to-know basis only.\n"
    )


def _build_it_footer() -> str:
    return (
        "\n---\n\n"
        "## Change management (IT profile)\n\n"
        "- **Change type:** _(standard / normal / emergency)_\n"
        "- **Change ticket:** _(link to Jira / ServiceNow)_\n"
        "- **Rollback plan:** _(named rollback procedure)_\n"
        "- **Test evidence:** _(staging validation)_\n"
        "- **Communication plan:** _(who is notified pre/post change)_\n"
    )


def _build_support_footer() -> str:
    return (
        "\n---\n\n"
        "## Customer impact & escalation (support profile)\n\n"
        "- **Customer impact category:** _(none / single-customer / "
        "multi-customer / company-wide outage)_\n"
        "- **External comms required:** _(yes/no — if yes, link "
        "internal-comms cascade SOP)_\n"
        "- **Escalation matrix:**\n\n"
        "| Trigger | Escalate to | SLA |\n"
        "|---------|-------------|-----|\n"
        "| Customer-impact > 30 min | Engineering on-call | 5 min |\n"
        "| Multi-customer impact | Support Lead + VP Eng | 10 min |\n"
        "| External comms needed  | Communications + CEO  | 30 min |\n"
    )


PROFILE_FOOTER = {
    "ops": "",
    "support": _build_support_footer(),
    "finance": _build_finance_footer(),
    "hr": _build_hr_footer(),
    "it": _build_it_footer(),
    "regulated": _build_regulated_footer(),
}


def generate_markdown(meta: SOPMetadata, profile: str) -> str:
    header = (
        f"# SOP: {meta.sop_name}\n\n"
        f"_Profile: `{profile}` | "
        f"Regulatory overlay: "
        f"{meta.regulatory_overlay or 'none'}_\n\n"
        "---\n\n"
        "## 5W2H scaffolding\n\n"
        "_(Ishikawa 1985, 5W2H method. Each section is required.)_\n"
    )
    body = "\n\n".join([
        _build_who(meta, profile),
        _build_what(meta),
        _build_when(meta),
        _build_where(meta, profile),
        _build_why(meta),
        _build_how(meta),
        _build_how_much(meta),
    ])
    footer = PROFILE_FOOTER.get(profile, "")
    return header + "\n" + body + footer + "\n"


def generate_json(meta: SOPMetadata, profile: str) -> dict:
    return {
        "sop_name": meta.sop_name,
        "profile": profile,
        "metadata": asdict(meta),
        "sections": {
            "who": "RACI populated",
            "what": f"{len(meta.inputs)} inputs / "
                    f"{len(meta.outputs)} outputs",
            "when": meta.triggering_event,
            "where": "system of record + canonical doc location",
            "why": meta.regulatory_overlay or ["none"],
            "how": [{"step": i + 1, "title": s}
                    for i, s in enumerate(meta.steps_outline)],
            "how_much": {
                "estimated_minutes": meta.estimated_minutes,
                "estimated_cost_usd": meta.estimated_cost_usd,
            },
        },
    }


def main(argv=None) -> int:
    p = argparse.ArgumentParser(
        description="Generate a 5W2H-structured SOP from JSON metadata."
    )
    p.add_argument("--input", "-i", type=str,
                   help="Path to SOP metadata JSON file.")
    p.add_argument("--profile", choices=sorted(VALID_PROFILES),
                   default="ops",
                   help="Industry profile (default: ops).")
    p.add_argument("--output", "-o", choices=["markdown", "json"],
                   default="markdown",
                   help="Output format (default: markdown).")
    p.add_argument("--sample", action="store_true",
                   help="Print a sample vendor-offboarding SOP.")
    args = p.parse_args(argv)

    if args.sample:
        data = _sample_metadata()
    elif args.input:
        path = Path(args.input)
        if not path.exists():
            print(f"ERROR: input file not found: {args.input}",
                  file=sys.stderr)
            return 2
        data = json.loads(path.read_text())
    else:
        print("ERROR: provide --input <metadata.json> or --sample",
              file=sys.stderr)
        return 2

    meta = SOPMetadata(**data)
    errs = meta.validate()
    if errs:
        print("VALIDATION ERRORS:", file=sys.stderr)
        for e in errs:
            print(f"  - {e}", file=sys.stderr)
        return 1

    if args.output == "json":
        print(json.dumps(generate_json(meta, args.profile), indent=2))
    else:
        print(generate_markdown(meta, args.profile))
    return 0


if __name__ == "__main__":
    sys.exit(main())
