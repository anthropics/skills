#!/usr/bin/env python3
"""data_product_strategy_picker.py — Pick data architecture + build-vs-buy + sequencing.

Stdlib-only. Takes a company profile and outputs:
  - Recommended architecture (warehouse / lakehouse / data mesh) with reasoning + kill criteria
  - Build-vs-buy decision per layer (storage, ELT, modeling, BI, feature store, ML platform)
  - 12-month sequencing roadmap

The recommendation is deterministic, derived from the profile, not pattern-matched.

Input schema (JSON):
{
  "stage": "series-a",            // seed | series-a | series-b | growth | late-stage
  "data_team_size": 3,
  "internal_consumers": 8,         // distinct people/teams consuming data weekly
  "data_volume_tb": 4.5,
  "ml_models_in_prod": 1,
  "company_type": "b2b-saas",     // b2b-saas | b2c-saas | consumer | marketplace | enterprise
  "has_data_culture": false,       // federated ownership culture in place? (mesh prerequisite)
  "near_term_priorities": [
    "self-serve-bi",
    "improve-pipeline-reliability"
  ]
}

Usage:
    python data_product_strategy_picker.py                       # uses embedded Series A SaaS
    python data_product_strategy_picker.py path/to/profile.json
    python data_product_strategy_picker.py profile.json --output json
"""

import argparse
import json
import sys
from typing import Any, Dict, List, Tuple


SAMPLE: Dict[str, Any] = {
    "stage": "series-a",
    "data_team_size": 3,
    "internal_consumers": 8,
    "data_volume_tb": 4.5,
    "ml_models_in_prod": 1,
    "company_type": "b2b-saas",
    "has_data_culture": False,
    "near_term_priorities": ["self-serve-bi", "improve-pipeline-reliability"],
}


def pick_architecture(profile: Dict[str, Any]) -> Tuple[str, str, List[str]]:
    """Returns (architecture, reasoning, kill_criteria)."""
    consumers = profile.get("internal_consumers", 0)
    volume = profile.get("data_volume_tb", 0)
    ml_models = profile.get("ml_models_in_prod", 0)
    culture = profile.get("has_data_culture", False)
    stage = profile.get("stage", "")

    # Data mesh: requires 25+ consumers across 4+ domains AND federated culture
    if consumers >= 25 and culture and stage in ("growth", "late-stage"):
        return (
            "DATA MESH",
            f"{consumers} data consumers across enough domains to justify federated ownership; "
            "stated data-culture maturity supports the operational overhead.",
            [
                "Stop and revert if 6 months in: producing teams haven't adopted ownership (typical failure mode)",
                "Stop if: central data platform team is still doing >50% of data product work",
                "Stop if: domain teams complain about platform onboarding (signals platform isn't truly self-serve)",
            ],
        )

    # Mesh ambition without prerequisites
    if consumers >= 25 and not culture:
        return (
            "LAKEHOUSE (defer mesh)",
            f"{consumers} consumers is mesh-sized BUT no federated ownership culture in place; mesh "
            "without culture fails. Run lakehouse with hub-and-spoke until ownership culture matures.",
            [
                "Revisit mesh in 18 months once 3+ domain teams own their own data products",
                "Stop hub-and-spoke if central team is bottleneck > 60% of requests",
            ],
        )

    # Lakehouse: 5+ consumers OR ML workloads OR >2TB
    if consumers >= 5 or ml_models >= 1 or volume >= 2:
        return (
            "LAKEHOUSE",
            (
                f"{consumers} data consumer(s), {ml_models} ML model(s) in prod, {volume}TB. "
                "Pure warehouse is too rigid for ML; pure data lake too unstructured for BI. "
                "Lakehouse (warehouse + object storage with table format like Iceberg/Delta) "
                "covers both with one substrate."
            ),
            [
                "Downgrade to warehouse-only if ML models retired and data shrinks below 2TB",
                "Upgrade to mesh only if 25+ consumers AND federated culture",
                "Stop investment if vendor lock-in becomes unacceptable (lakehouse table formats mitigate this)",
            ],
        )

    # Warehouse only
    return (
        "WAREHOUSE ONLY",
        (
            f"{consumers} consumer(s), {volume}TB, {ml_models} ML model(s). Sub-scale for lakehouse "
            "complexity. Single warehouse (Snowflake / BigQuery / Postgres) + dbt is the simplest viable "
            "stack at this stage."
        ),
        [
            "Upgrade to lakehouse when ANY of: 5+ consumers, 2TB+ data, 1+ ML model in prod",
            "Stop investment in custom modeling if SaaS BI vendor solves it (avoid premature dbt complexity)",
        ],
    )


def build_vs_buy(profile: Dict[str, Any], architecture: str) -> List[Dict[str, str]]:
    """Returns build-vs-buy decision per layer."""
    consumers = profile.get("internal_consumers", 0)
    ml_models = profile.get("ml_models_in_prod", 0)
    company_type = profile.get("company_type", "")

    decisions = []

    # Storage / warehouse
    decisions.append({
        "layer": "Storage / Warehouse",
        "decision": "BUY",
        "vendor_suggestion": "Snowflake / BigQuery / Databricks (lakehouse) or Postgres (warehouse-only)",
        "rationale": "Storage is commodity. Building distributed storage is a 50-engineer-year investment with no business return unless you are a data-infra company.",
    })

    # ELT / ingest
    decisions.append({
        "layer": "ELT / Ingest",
        "decision": "BUY",
        "vendor_suggestion": "Fivetran / Airbyte / Stitch",
        "rationale": "Connector maintenance is a moving target (200+ source APIs). Build only if your source isn't supported and is critical (then contribute upstream).",
    })

    # Modeling
    decisions.append({
        "layer": "Modeling / Transformations",
        "decision": "BUILD",
        "vendor_suggestion": "dbt + your domain logic (dbt itself is open source)",
        "rationale": "This is your IP. Your domain logic encodes how the business actually works — vendors cannot supply it.",
    })

    # BI
    if consumers < 100:
        decisions.append({
            "layer": "BI / Dashboards",
            "decision": "BUY",
            "vendor_suggestion": "Metabase (cheap) / Looker (enterprise) / Mode (analyst-friendly) / Hex (notebooks+BI)",
            "rationale": f"At {consumers} consumers, building BI is a distraction. SaaS BI is mature; pick one that matches your analyst skillset.",
        })
    else:
        decisions.append({
            "layer": "BI / Dashboards",
            "decision": "BUY + consider embedded for customer-facing analytics",
            "vendor_suggestion": "Looker / Sigma + (Cube.dev or Embeddable) for customer-facing",
            "rationale": f"At {consumers} consumers, BI is critical. If you're a B2B SaaS with customer-facing analytics, embedded BI is a real build-vs-buy decision; usually still buy.",
        })

    # Feature store
    if ml_models < 3:
        decisions.append({
            "layer": "Feature Store",
            "decision": "DEFER",
            "vendor_suggestion": "(none yet — use dbt + simple feature tables)",
            "rationale": f"{ml_models} model(s) in prod. Feature stores pay off at 3+ models sharing features. Premature investment is a maintenance burden.",
        })
    else:
        decisions.append({
            "layer": "Feature Store",
            "decision": "BUY (Tecton / Hopsworks) or BUILD (Feast)",
            "vendor_suggestion": "Tecton (managed) or Feast (open source)",
            "rationale": f"{ml_models} models is the threshold where feature reuse + governance matter more than simplicity.",
        })

    # ML platform
    if ml_models < 5:
        decisions.append({
            "layer": "ML Platform",
            "decision": "DEFER",
            "vendor_suggestion": "(none yet — use notebooks + scheduled training jobs)",
            "rationale": f"{ml_models} models. ML platforms (Databricks ML, Vertex AI, SageMaker) make sense at 5+ models with active retraining; before that, the platform overhead exceeds the value.",
        })
    else:
        decisions.append({
            "layer": "ML Platform",
            "decision": "BUY",
            "vendor_suggestion": "Databricks ML / Vertex AI / SageMaker",
            "rationale": f"{ml_models} models with active retraining. Platform handles experiment tracking, deployment, monitoring — all of which become painful to build at this scale.",
        })

    return decisions


def sequence_roadmap(profile: Dict[str, Any], architecture: str) -> List[Dict[str, str]]:
    """Returns 4-quarter sequencing roadmap based on priorities + architecture."""
    priorities = profile.get("near_term_priorities", [])
    ml_models = profile.get("ml_models_in_prod", 0)

    roadmap = []

    # Q1: always reliability first if pipeline issues exist
    if "improve-pipeline-reliability" in priorities or "reliability" in str(priorities):
        roadmap.append({
            "quarter": "Q1",
            "focus": "Pipeline reliability",
            "deliverables": "SLA on top-3 critical pipelines (freshness, completeness); on-call rotation; data quality tests in dbt",
        })
    else:
        roadmap.append({
            "quarter": "Q1",
            "focus": "Foundation",
            "deliverables": "Centralized ingest (Fivetran/Airbyte); dbt for top-5 marts; basic data quality tests",
        })

    # Q2
    if "self-serve-bi" in priorities:
        roadmap.append({
            "quarter": "Q2",
            "focus": "Self-serve BI",
            "deliverables": "BI tool rollout to non-data teams; semantic layer (dbt metrics or LookML); training program",
        })
    else:
        roadmap.append({
            "quarter": "Q2",
            "focus": "Coverage",
            "deliverables": "Extend dbt to top-10 marts; document data lineage; add domain-specific data quality tests",
        })

    # Q3
    if ml_models >= 1 or "ml" in str(priorities).lower():
        roadmap.append({
            "quarter": "Q3",
            "focus": "ML enablement",
            "deliverables": "First feature-store table for top-1 production model; experiment tracking (MLflow / W&B); model monitoring",
        })
    else:
        roadmap.append({
            "quarter": "Q3",
            "focus": "Embed analysts",
            "deliverables": "Embedded analysts in 2-3 functional teams; central team owns platform; SLAs renegotiated",
        })

    # Q4: evaluate + decide
    roadmap.append({
        "quarter": "Q4",
        "focus": "Evaluate and decide",
        "deliverables": "Re-run this picker with updated profile; decide on year-2 architecture (e.g., introduce feature store, evaluate mesh prereqs)",
    })

    return roadmap


def analyze(profile: Dict[str, Any]) -> Dict[str, Any]:
    architecture, reasoning, kill_criteria = pick_architecture(profile)
    decisions = build_vs_buy(profile, architecture)
    roadmap = sequence_roadmap(profile, architecture)
    return {
        "architecture": architecture,
        "reasoning": reasoning,
        "kill_criteria": kill_criteria,
        "build_vs_buy": decisions,
        "roadmap_12mo": roadmap,
    }


def render_text(result: Dict[str, Any], profile: Dict[str, Any], source: str) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("DATA PRODUCT STRATEGY")
    lines.append(f"Source: {source}")
    lines.append("=" * 72)
    lines.append("")
    lines.append("Profile:")
    lines.append(f"  Stage: {profile.get('stage')} | Team: {profile.get('data_team_size')} | Consumers: {profile.get('internal_consumers')}")
    lines.append(f"  Data volume: {profile.get('data_volume_tb')}TB | ML models in prod: {profile.get('ml_models_in_prod')}")
    lines.append(f"  Company type: {profile.get('company_type')} | Data culture in place: {profile.get('has_data_culture')}")
    lines.append("")
    lines.append("-" * 72)
    lines.append(f"RECOMMENDED ARCHITECTURE: {result['architecture']}")
    lines.append("")
    lines.append("Reasoning:")
    for line in _wrap(result["reasoning"], 2):
        lines.append(line)
    lines.append("")
    lines.append("Kill criteria (when to abandon this choice):")
    for k in result["kill_criteria"]:
        lines.append(f"  • {k}")
    lines.append("")
    lines.append("-" * 72)
    lines.append("BUILD vs BUY (per layer):")
    lines.append("")
    for d in result["build_vs_buy"]:
        lines.append(f"  {d['layer']:<32} {d['decision']}")
        lines.append(f"    Vendor: {d['vendor_suggestion']}")
        for line in _wrap(f"Rationale: {d['rationale']}", 4):
            lines.append(line)
        lines.append("")
    lines.append("-" * 72)
    lines.append("12-MONTH ROADMAP:")
    lines.append("")
    for r in result["roadmap_12mo"]:
        lines.append(f"  {r['quarter']}: {r['focus']}")
        for line in _wrap(r["deliverables"], 6):
            lines.append(line)
        lines.append("")
    lines.append("-" * 72)
    lines.append("REMINDER: Re-run this picker quarterly with updated profile. Architecture is not a once-")
    lines.append("and-done decision — kill criteria exist for a reason.")
    return "\n".join(lines)


def _wrap(text: str, indent: int, width: int = 68) -> List[str]:
    import textwrap
    return textwrap.wrap(text, width=width, initial_indent=" " * indent, subsequent_indent=" " * indent) or [" " * indent + text]


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Pick data architecture + build-vs-buy + sequencing roadmap from a company profile.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to profile JSON (uses embedded sample if omitted)")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    args = parser.parse_args()

    if args.path:
        try:
            with open(args.path, "r", encoding="utf-8") as f:
                profile = json.load(f)
            source = args.path
        except (IOError, OSError) as e:
            print(f"error: could not read {args.path}: {e}", file=sys.stderr)
            return 1
        except json.JSONDecodeError as e:
            print(f"error: invalid JSON in {args.path}: {e}", file=sys.stderr)
            return 1
    else:
        profile = SAMPLE
        source = "<embedded sample: Series A B2B SaaS, 3-person data team>"

    result = analyze(profile)

    if args.output == "json":
        print(json.dumps({"source": source, "profile": profile, **result}, indent=2))
    else:
        print(render_text(result, profile, source))

    return 0


if __name__ == "__main__":
    sys.exit(main())
