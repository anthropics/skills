#!/usr/bin/env python3
"""ai_training_data_audit.py — Audit data sources for AI training eligibility.

Stdlib-only. Audits each data source on 3 dimensions:
  - Origin (1st-party-explicit-opt-in / 1st-party-tos-only / partner-licensed / scraped / synthetic)
  - Data class (anonymous-aggregate / behavioral / pii / third-party-content / regulated)
  - Use case (in-product-personalization / fine-tune-our-model / train-foundation-model / external-sharing)

Returns GO / MITIGATE / NO-GO per source with the specific risk and remediation.

NOT legal advice — surfaces decisions for qualified counsel.

Input schema (JSON):
{
  "sources": [
    {
      "name": "Product telemetry events",
      "origin": "1st-party-tos-only",
      "data_class": "behavioral",
      "use_case": "in-product-personalization"
    },
    ...
  ]
}

Usage:
    python ai_training_data_audit.py                       # uses embedded sample
    python ai_training_data_audit.py path/to/sources.json
    python ai_training_data_audit.py sources.json --output json
"""

import argparse
import json
import sys
from dataclasses import dataclass, asdict
from typing import Any, Dict, List, Optional, Tuple


SAMPLE: Dict[str, Any] = {
    "sources": [
        {
            "name": "Anonymous product telemetry (event aggregates)",
            "origin": "1st-party-tos-only",
            "data_class": "anonymous-aggregate",
            "use_case": "in-product-personalization",
        },
        {
            "name": "Customer support transcripts",
            "origin": "1st-party-tos-only",
            "data_class": "pii",
            "use_case": "fine-tune-our-model",
        },
        {
            "name": "Scraped LinkedIn profiles",
            "origin": "scraped",
            "data_class": "pii",
            "use_case": "fine-tune-our-model",
        },
        {
            "name": "Synthetic conversational data (LLM-generated)",
            "origin": "synthetic",
            "data_class": "third-party-content",
            "use_case": "train-foundation-model",
        },
        {
            "name": "User opt-in survey responses",
            "origin": "1st-party-explicit-opt-in",
            "data_class": "behavioral",
            "use_case": "external-sharing",
        },
        {
            "name": "Partner-licensed industry dataset",
            "origin": "partner-licensed",
            "data_class": "anonymous-aggregate",
            "use_case": "train-foundation-model",
        },
        {
            "name": "Anonymized health screening responses",
            "origin": "1st-party-explicit-opt-in",
            "data_class": "regulated",
            "use_case": "fine-tune-our-model",
        },
    ]
}


VALID_ORIGINS = {
    "1st-party-explicit-opt-in",
    "1st-party-tos-only",
    "partner-licensed",
    "scraped",
    "synthetic",
}
VALID_CLASSES = {
    "anonymous-aggregate",
    "behavioral",
    "pii",
    "third-party-content",
    "regulated",
}
VALID_USE_CASES = {
    "in-product-personalization",
    "fine-tune-our-model",
    "train-foundation-model",
    "external-sharing",
}


@dataclass
class AuditResult:
    name: str
    origin: str
    data_class: str
    use_case: str
    verdict: str           # GO | MITIGATE | NO-GO
    risk: str
    remediation: str
    citations: List[str]


# Verdict matrix: (origin, data_class, use_case) -> (verdict, risk, remediation, citations)
# Built by applying these rules in order; first match wins.
def _decide(origin: str, data_class: str, use_case: str) -> Tuple[str, str, str, List[str]]:

    # Rule 1: Scraped data is always NO-GO for training (hiQ v. LinkedIn, copyright, GDPR Art. 6).
    if origin == "scraped":
        return (
            "NO-GO",
            "Scraped data lacks lawful basis under GDPR Art. 6 (no consent, no legitimate interest "
            "balancing test); high copyright risk; hiQ v. LinkedIn left exposure for ToS-violation claims; "
            "many AI Act high-risk use cases require demonstrable provenance.",
            "Remove from training set. Either (a) procure licensed alternative from data broker, "
            "(b) replace with synthetic data, or (c) build 1st-party explicit opt-in pipeline.",
            ["GDPR Art. 6", "hiQ Labs v. LinkedIn", "EU AI Act Art. 10 (data governance)"],
        )

    # Rule 2: Regulated data (PHI, PCI, kids) requires explicit opt-in + specific compliance
    # framework; never train foundation model with raw regulated data.
    if data_class == "regulated":
        if origin == "1st-party-explicit-opt-in" and use_case in {"in-product-personalization", "fine-tune-our-model"}:
            return (
                "MITIGATE",
                "Regulated data (PHI / PCI / children) may be processed under explicit opt-in IF the "
                "framework permits (HIPAA Limited Data Set, COPPA verifiable parental consent). "
                "Fine-tuning increases re-identification risk vs in-product use.",
                "Required: (1) framework-specific consent flow, (2) DPIA/PIA on file, (3) k-anonymity "
                "≥ 5 audit before any training, (4) model output filters for regulated-content leakage, "
                "(5) DPA with any vendor in the pipeline.",
                ["HIPAA", "HITECH §13402", "COPPA", "GDPR Art. 9", "EU AI Act Annex III"],
            )
        return (
            "NO-GO",
            "Regulated data (PHI / PCI / children) cannot be used for foundation training or external "
            "sharing without specific framework authorization, and not at all without explicit opt-in.",
            "Either (a) restrict to in-product use under existing framework consent, (b) train on "
            "synthetic data modeled on the corpus, or (c) obtain new explicit opt-in covering the "
            "specific training purpose.",
            ["HIPAA", "GDPR Art. 9", "COPPA"],
        )

    # Rule 3: PII at any use case beyond in-product-personalization requires explicit opt-in,
    # specific lawful basis, AND anonymization/pseudonymization.
    if data_class == "pii":
        if use_case == "in-product-personalization":
            if origin == "1st-party-tos-only":
                return (
                    "MITIGATE",
                    "PII processing for in-product personalization can rest on GDPR Art. 6(1)(b) "
                    "(performance of contract) or 6(1)(f) (legitimate interest) IF the personalization "
                    "is reasonably expected. Train-once derived models retain risk.",
                    "Required: (1) Art. 6 lawful basis documented, (2) data minimization audit, "
                    "(3) deletion request honored for the source data even after model training "
                    "(implementation: filter-on-output OR retrain on deletion), (4) DPIA if scale > 5000 users.",
                    ["GDPR Art. 6", "GDPR Art. 17 (right to erasure)", "EDPB Guidelines on Art. 22"],
                )
            if origin == "1st-party-explicit-opt-in":
                return (
                    "GO",
                    "PII with explicit opt-in for in-product personalization is the strongest position. "
                    "Standard residual risks: opt-in revocation, deletion requests.",
                    "Maintain: (1) opt-in audit trail per user, (2) machinery to honor revocation/erasure "
                    "(filter-on-output or retrain), (3) clear notice on what model is trained.",
                    ["GDPR Art. 6(1)(a)", "GDPR Art. 17"],
                )

        # Fine-tune-our-model, train-foundation-model, external-sharing with PII
        if origin == "1st-party-explicit-opt-in":
            return (
                "MITIGATE",
                "PII for fine-tuning or beyond requires explicit opt-in covering THIS specific "
                "training purpose (not generic TOS). Risk: training-data extraction attacks, "
                "memorization, model-output leakage.",
                "Required: (1) purpose-specific opt-in (not bundled TOS), (2) differential privacy "
                "or k-anonymity audit, (3) memorization tests on the trained model, (4) DPIA, "
                "(5) DPA with infra/training vendor, (6) EU AI Act conformity assessment if "
                "high-risk use case.",
                ["GDPR Art. 6(1)(a)", "GDPR Art. 35 (DPIA)", "EU AI Act Art. 10"],
            )
        return (
            "NO-GO",
            "PII for fine-tuning or foundation training without explicit opt-in fails GDPR Art. 6. "
            "TOS-only consent is insufficient for materially different purpose.",
            "Either (a) restrict use case to in-product personalization under existing basis, "
            "(b) build explicit opt-in pipeline before training, or (c) anonymize/pseudonymize "
            "to k-anonymity ≥ 5 and re-classify as anonymous-aggregate.",
            ["GDPR Art. 6", "EDPB Opinion 28/2024"],
        )

    # Rule 4: 3rd-party content (e.g., user-uploaded files, customer support transcripts
    # quoting other systems, scraped public documents within user submissions).
    if data_class == "third-party-content":
        if origin in {"synthetic", "partner-licensed"}:
            return (
                "MITIGATE",
                "Synthetic or licensed 3rd-party-content carries content-license risk: even with a "
                "license, training a model may exceed the license scope (e.g., 'view' license vs "
                "'derivative work creation').",
                "Required: (1) license review by counsel for training-specific clauses, (2) carve-out "
                "for AI training in licensing agreement, (3) provenance log per source for AI Act compliance, "
                "(4) opt-out mechanism if license permits revocation.",
                ["NYT v. OpenAI (2024)", "EU AI Act Art. 53 (general-purpose models)"],
            )
        if origin == "1st-party-tos-only":
            return (
                "MITIGATE",
                "User-uploaded content under TOS-only license has uncertain training rights post-2024 "
                "lawsuits. Risk: copyright infringement if model output is substantially similar to "
                "training data.",
                "Required: (1) TOS explicitly grants training rights for the specific model class, "
                "(2) output similarity monitoring (de-duping / fuzzy match against training corpus), "
                "(3) opt-out mechanism in TOS update.",
                ["Authors Guild v. Google", "Andersen v. Stability AI", "NYT v. OpenAI"],
            )
        if origin == "1st-party-explicit-opt-in":
            return (
                "GO",
                "Explicit opt-in for training on user-uploaded content is the strongest position. "
                "Maintain output-similarity guardrails to catch unexpected memorization.",
                "Required: (1) opt-in audit trail, (2) revocation flow, (3) output similarity testing.",
                ["GDPR Art. 6(1)(a)"],
            )

    # Rule 5: Behavioral data — generally safer than PII, but external sharing still requires consent.
    if data_class == "behavioral":
        if use_case == "external-sharing":
            if origin == "1st-party-explicit-opt-in":
                return (
                    "GO",
                    "Behavioral data with explicit opt-in for external sharing — clean.",
                    "Maintain: (1) revocation flow, (2) anonymization audit before each external "
                    "share (k-anonymity ≥ 5), (3) recipient DPA.",
                    ["GDPR Art. 6(1)(a)"],
                )
            return (
                "MITIGATE",
                "Behavioral data without explicit opt-in for external sharing is borderline. TOS-only "
                "is weak basis; partner-licensed depends on partner's original consent flow.",
                "Required: (1) anonymization to k-anonymity ≥ 5, (2) recipient DPA with no-reidentification "
                "clause, (3) audit upstream consent if partner-licensed, (4) consider opt-in pipeline.",
                ["GDPR Art. 6", "Art. 22 (automated decision-making)"],
            )
        # Behavioral + training use cases
        if origin in {"1st-party-explicit-opt-in", "1st-party-tos-only", "partner-licensed"}:
            return (
                "GO",
                "Behavioral data from controlled origin for internal training is generally safe. "
                "Residual risk: model leakage if behavioral patterns are individually identifying.",
                "Maintain: (1) deletion handling on user request, (2) periodic memorization tests, "
                "(3) DPIA if scale > 50K users or sensitive inferences.",
                ["GDPR Art. 6", "GDPR Art. 35"],
            )

    # Rule 6: Anonymous aggregate — generally safe at all use cases.
    if data_class == "anonymous-aggregate":
        if origin == "scraped":
            # Already handled above
            pass
        return (
            "GO",
            "Anonymous aggregate data is the safest class. Residual risk: re-identification attacks "
            "if aggregate cells are small.",
            "Maintain: (1) k-anonymity ≥ 5 in all published aggregates, (2) differential privacy if "
            "shared externally, (3) provenance log for AI Act compliance.",
            ["EU AI Act Art. 10", "GDPR Recital 26"],
        )

    # Synthetic + non-3rd-party-content
    if origin == "synthetic":
        return (
            "GO",
            "Synthetic data is generally safe for training. Residual risk: synthetic data generated "
            "from a non-clean source inherits its risks.",
            "Maintain: (1) document the generation pipeline including any non-synthetic seed, "
            "(2) test for bias inherited from generator, (3) provenance log.",
            ["EU AI Act Art. 10"],
        )

    # Default conservative fallback
    return (
        "MITIGATE",
        "Configuration not matched by explicit rules — manual review required.",
        "Engage qualified data privacy counsel to assess this specific origin/class/use combination.",
        [],
    )


def audit(payload: Dict[str, Any]) -> List[AuditResult]:
    results: List[AuditResult] = []
    for src in payload.get("sources", []):
        name = src.get("name", "<unnamed>")
        origin = src.get("origin", "")
        data_class = src.get("data_class", "")
        use_case = src.get("use_case", "")

        # Validation
        errors = []
        if origin not in VALID_ORIGINS:
            errors.append(f"invalid origin '{origin}'")
        if data_class not in VALID_CLASSES:
            errors.append(f"invalid data_class '{data_class}'")
        if use_case not in VALID_USE_CASES:
            errors.append(f"invalid use_case '{use_case}'")
        if errors:
            results.append(AuditResult(
                name=name,
                origin=origin,
                data_class=data_class,
                use_case=use_case,
                verdict="NO-GO",
                risk=f"Schema error: {'; '.join(errors)}",
                remediation=(
                    f"Origin must be one of {sorted(VALID_ORIGINS)}; "
                    f"data_class one of {sorted(VALID_CLASSES)}; "
                    f"use_case one of {sorted(VALID_USE_CASES)}."
                ),
                citations=[],
            ))
            continue

        verdict, risk, remediation, citations = _decide(origin, data_class, use_case)
        results.append(AuditResult(
            name=name,
            origin=origin,
            data_class=data_class,
            use_case=use_case,
            verdict=verdict,
            risk=risk,
            remediation=remediation,
            citations=citations,
        ))

    # Sort: NO-GO first, then MITIGATE, then GO
    order = {"NO-GO": 0, "MITIGATE": 1, "GO": 2}
    results.sort(key=lambda r: order.get(r.verdict, 9))
    return results


def render_text(results: List[AuditResult], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("AI TRAINING DATA AUDIT")
    lines.append(f"Source: {source}")
    lines.append(f"Sources audited: {len(results)}")
    lines.append("=" * 72)
    lines.append("")

    counts = {"NO-GO": 0, "MITIGATE": 0, "GO": 0}
    for r in results:
        counts[r.verdict] = counts.get(r.verdict, 0) + 1
    lines.append(f"Verdicts: 🔴 NO-GO: {counts['NO-GO']}  🟡 MITIGATE: {counts['MITIGATE']}  🟢 GO: {counts['GO']}")
    lines.append("")
    lines.append("-" * 72)

    for i, r in enumerate(results, 1):
        marker = {"NO-GO": "🔴", "MITIGATE": "🟡", "GO": "🟢"}.get(r.verdict, "•")
        lines.append(f"[{i}] {marker} {r.verdict:<9} — {r.name}")
        lines.append(f"    Origin: {r.origin} | Class: {r.data_class} | Use case: {r.use_case}")
        lines.append("")
        lines.append(f"    Risk:")
        for line in _wrap(r.risk, 6):
            lines.append(line)
        lines.append("")
        lines.append(f"    Remediation:")
        for line in _wrap(r.remediation, 6):
            lines.append(line)
        if r.citations:
            lines.append(f"    Citations: {', '.join(r.citations)}")
        lines.append("")
        lines.append("-" * 72)

    lines.append("")
    lines.append("REMINDER: This audit applies rule-based triage to a 3-dimensional matrix. Always engage")
    lines.append("qualified data privacy / AI counsel for binding decisions.")
    return "\n".join(lines)


def _wrap(text: str, indent: int, width: int = 66) -> List[str]:
    import textwrap
    return textwrap.wrap(text, width=width, initial_indent=" " * indent, subsequent_indent=" " * indent) or [" " * indent + text]


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Audit data sources for AI training eligibility (origin × class × use-case matrix).",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to sources JSON (uses embedded sample if omitted)")
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
        source = "<embedded sample: 7 mixed sources>"

    results = audit(payload)

    if args.output == "json":
        print(json.dumps({
            "source": source,
            "count": len(results),
            "verdict_counts": {
                "NO-GO": sum(1 for r in results if r.verdict == "NO-GO"),
                "MITIGATE": sum(1 for r in results if r.verdict == "MITIGATE"),
                "GO": sum(1 for r in results if r.verdict == "GO"),
            },
            "results": [asdict(r) for r in results],
        }, indent=2))
    else:
        print(render_text(results, source))

    return 0


if __name__ == "__main__":
    sys.exit(main())
