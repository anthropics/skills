#!/usr/bin/env python3
"""
Azure architecture design and service recommendation tool.
Generates architecture patterns based on application requirements.

Usage:
    python architecture_designer.py --app-type web_app --users 10000
    python architecture_designer.py --app-type microservices --users 50000 --requirements '{"compliance": ["HIPAA"]}'
    python architecture_designer.py --app-type serverless --users 5000 --json
"""

import argparse
import json
import sys
from typing import Dict, List, Any


# ---------------------------------------------------------------------------
# Azure service catalog used by the designer
# ---------------------------------------------------------------------------

ARCHITECTURE_PATTERNS = {
    "web_app": {
        "small": "app_service_web",
        "medium": "app_service_scaled",
        "large": "multi_region_web",
    },
    "saas_platform": {
        "small": "app_service_web",
        "medium": "aks_microservices",
        "large": "multi_region_web",
    },
    "mobile_backend": {
        "small": "serverless_functions",
        "medium": "app_service_web",
        "large": "aks_microservices",
    },
    "microservices": {
        "small": "container_apps",
        "medium": "aks_microservices",
        "large": "aks_microservices",
    },
    "data_pipeline": {
        "small": "serverless_data",
        "medium": "synapse_pipeline",
        "large": "synapse_pipeline",
    },
    "serverless": {
        "small": "serverless_functions",
        "medium": "serverless_functions",
        "large": "serverless_functions",
    },
}


def _size_bucket(users: int) -> str:
    if users < 10000:
        return "small"
    if users < 100000:
        return "medium"
    return "large"


# ---------------------------------------------------------------------------
# Pattern builders
# ---------------------------------------------------------------------------

def _app_service_web(users: int, reqs: Dict) -> Dict[str, Any]:
    budget = reqs.get("budget_monthly_usd", 500)
    return {
        "recommended_pattern": "app_service_web",
        "description": "Azure App Service with managed SQL and CDN",
        "use_case": "Web apps, SaaS platforms, startup MVPs",
        "service_stack": [
            "App Service (Linux P1v3)",
            "Azure SQL Database (Serverless GP_S_Gen5_2)",
            "Azure Front Door",
            "Azure Blob Storage",
            "Key Vault",
            "Entra ID + RBAC",
            "Application Insights",
        ],
        "estimated_monthly_cost_usd": min(280, budget),
        "cost_breakdown": {
            "App Service P1v3": "$70-95",
            "Azure SQL Serverless": "$40-120",
            "Front Door": "$35-55",
            "Blob Storage": "$5-15",
            "Key Vault": "$1-5",
            "Application Insights": "$5-20",
        },
        "pros": [
            "Managed platform — no OS patching",
            "Built-in autoscale and deployment slots",
            "Easy CI/CD with GitHub Actions or Azure DevOps",
            "Custom domains and TLS certificates included",
            "Integrated authentication (Easy Auth)",
        ],
        "cons": [
            "Less control than VMs or containers",
            "Platform constraints for exotic runtimes",
            "Cold start on lower-tier plans",
            "Outbound IP shared unless isolated tier",
        ],
        "scaling": {
            "users_supported": "1k - 100k",
            "requests_per_second": "100 - 10,000",
            "method": "App Service autoscale rules (CPU, memory, HTTP queue)",
        },
    }


def _aks_microservices(users: int, reqs: Dict) -> Dict[str, Any]:
    budget = reqs.get("budget_monthly_usd", 2000)
    return {
        "recommended_pattern": "aks_microservices",
        "description": "Microservices on AKS with API Management and Cosmos DB",
        "use_case": "Complex SaaS, multi-team microservices, high-scale platforms",
        "service_stack": [
            "AKS (3 node pools: system, app, jobs)",
            "API Management (Standard v2)",
            "Cosmos DB (multi-model)",
            "Service Bus (Standard)",
            "Azure Container Registry",
            "Azure Monitor + Application Insights",
            "Key Vault",
            "Entra ID workload identity",
        ],
        "estimated_monthly_cost_usd": min(1200, budget),
        "cost_breakdown": {
            "AKS node pools (D4s_v5 x3)": "$350-500",
            "API Management Standard v2": "$175",
            "Cosmos DB": "$100-400",
            "Service Bus Standard": "$10-50",
            "Container Registry Basic": "$5",
            "Azure Monitor": "$50-100",
            "Key Vault": "$1-5",
        },
        "pros": [
            "Full Kubernetes ecosystem",
            "Independent scaling per service",
            "Multi-language and multi-framework",
            "Mature ecosystem (Helm, Keda, Dapr)",
            "Workload identity — no credentials in pods",
        ],
        "cons": [
            "Kubernetes operational complexity",
            "Higher baseline cost",
            "Requires dedicated platform team",
            "Networking (CNI, ingress) configuration heavy",
        ],
        "scaling": {
            "users_supported": "10k - 10M",
            "requests_per_second": "1,000 - 1,000,000",
            "method": "Cluster autoscaler + KEDA event-driven autoscaling",
        },
    }


def _container_apps(users: int, reqs: Dict) -> Dict[str, Any]:
    budget = reqs.get("budget_monthly_usd", 500)
    return {
        "recommended_pattern": "container_apps",
        "description": "Serverless containers on Azure Container Apps",
        "use_case": "Microservices without Kubernetes management overhead",
        "service_stack": [
            "Azure Container Apps",
            "Azure Container Registry",
            "Cosmos DB",
            "Service Bus",
            "Key Vault",
            "Application Insights",
            "Entra ID managed identity",
        ],
        "estimated_monthly_cost_usd": min(350, budget),
        "cost_breakdown": {
            "Container Apps (consumption)": "$50-150",
            "Container Registry Basic": "$5",
            "Cosmos DB": "$50-150",
            "Service Bus Standard": "$10-30",
            "Key Vault": "$1-5",
            "Application Insights": "$5-20",
        },
        "pros": [
            "Serverless containers — scale to zero",
            "Built-in Dapr integration",
            "KEDA autoscaling included",
            "No cluster management",
            "Simpler networking than AKS",
        ],
        "cons": [
            "Less control than full AKS",
            "Limited to HTTP and event-driven workloads",
            "Smaller ecosystem than Kubernetes",
            "Some advanced features still in preview",
        ],
        "scaling": {
            "users_supported": "1k - 500k",
            "requests_per_second": "100 - 50,000",
            "method": "KEDA scalers (HTTP, queue length, CPU, custom)",
        },
    }


def _serverless_functions(users: int, reqs: Dict) -> Dict[str, Any]:
    budget = reqs.get("budget_monthly_usd", 300)
    return {
        "recommended_pattern": "serverless_functions",
        "description": "Azure Functions with Event Grid and Cosmos DB",
        "use_case": "Event-driven backends, APIs, scheduled jobs, webhooks",
        "service_stack": [
            "Azure Functions (Consumption plan)",
            "Event Grid",
            "Service Bus",
            "Cosmos DB (Serverless)",
            "Azure Blob Storage",
            "Application Insights",
            "Key Vault",
        ],
        "estimated_monthly_cost_usd": min(80, budget),
        "cost_breakdown": {
            "Functions (Consumption)": "$0-20 (1M free executions/month)",
            "Event Grid": "$0-5",
            "Service Bus Basic": "$0-10",
            "Cosmos DB Serverless": "$5-40",
            "Blob Storage": "$2-10",
            "Application Insights": "$5-15",
        },
        "pros": [
            "Pay-per-execution — true serverless",
            "Scale to zero, scale to millions",
            "Multiple trigger types (HTTP, queue, timer, blob, event)",
            "Durable Functions for orchestration",
            "Fast development cycle",
        ],
        "cons": [
            "Cold start latency (1-5s on consumption plan)",
            "10-minute execution timeout on consumption plan",
            "Limited local development experience",
            "Debugging distributed functions is complex",
        ],
        "scaling": {
            "users_supported": "1k - 1M",
            "requests_per_second": "100 - 100,000",
            "method": "Automatic (Azure Functions runtime scales instances)",
        },
    }


def _synapse_pipeline(users: int, reqs: Dict) -> Dict[str, Any]:
    budget = reqs.get("budget_monthly_usd", 1500)
    return {
        "recommended_pattern": "synapse_pipeline",
        "description": "Data pipeline with Event Hubs, Synapse, and Data Lake",
        "use_case": "Data warehousing, ETL, analytics, ML pipelines",
        "service_stack": [
            "Event Hubs (Standard)",
            "Data Factory / Synapse Pipelines",
            "Data Lake Storage Gen2",
            "Synapse Analytics (Serverless SQL pool)",
            "Azure Functions (processing)",
            "Power BI",
            "Azure Monitor",
        ],
        "estimated_monthly_cost_usd": min(800, budget),
        "cost_breakdown": {
            "Event Hubs Standard": "$20-80",
            "Data Factory": "$50-200",
            "Data Lake Storage Gen2": "$20-80",
            "Synapse Serverless SQL": "$50-300 (per TB scanned)",
            "Azure Functions": "$10-40",
            "Power BI Pro": "$10/user/month",
        },
        "pros": [
            "Unified analytics platform (Synapse)",
            "Serverless SQL — pay per query",
            "Native Spark integration",
            "Data Lake Gen2 — hierarchical namespace, cheap storage",
            "Built-in data integration (90+ connectors)",
        ],
        "cons": [
            "Synapse learning curve",
            "Cost unpredictable with serverless SQL at scale",
            "Complex permissions model (Synapse RBAC + storage ACLs)",
            "Spark pool startup time",
        ],
        "scaling": {
            "events_per_second": "1,000 - 10,000,000",
            "data_volume": "1 GB - 1 PB per day",
            "method": "Event Hubs throughput units + Synapse auto-scale",
        },
    }


def _serverless_data(users: int, reqs: Dict) -> Dict[str, Any]:
    budget = reqs.get("budget_monthly_usd", 300)
    return {
        "recommended_pattern": "serverless_data",
        "description": "Lightweight data pipeline with Functions and Data Lake",
        "use_case": "Small-scale ETL, event processing, log aggregation",
        "service_stack": [
            "Azure Functions",
            "Event Grid",
            "Data Lake Storage Gen2",
            "Azure SQL Serverless",
            "Application Insights",
        ],
        "estimated_monthly_cost_usd": min(120, budget),
        "cost_breakdown": {
            "Azure Functions": "$0-20",
            "Event Grid": "$0-5",
            "Data Lake Storage Gen2": "$5-20",
            "Azure SQL Serverless": "$20-60",
            "Application Insights": "$5-15",
        },
        "pros": [
            "Very low cost for small volumes",
            "Serverless end-to-end",
            "Simple to operate",
            "Scales automatically",
        ],
        "cons": [
            "Not suitable for high-volume analytics",
            "Limited transformation capabilities",
            "No built-in orchestration (use Durable Functions)",
        ],
        "scaling": {
            "events_per_second": "10 - 10,000",
            "data_volume": "1 MB - 100 GB per day",
            "method": "Azure Functions auto-scale",
        },
    }


def _multi_region_web(users: int, reqs: Dict) -> Dict[str, Any]:
    budget = reqs.get("budget_monthly_usd", 5000)
    return {
        "recommended_pattern": "multi_region_web",
        "description": "Multi-region active-active deployment with Front Door",
        "use_case": "Global applications, 99.99% uptime, data residency compliance",
        "service_stack": [
            "Azure Front Door (Premium)",
            "App Service (2+ regions) or AKS (2+ regions)",
            "Cosmos DB (multi-region writes)",
            "Azure SQL (geo-replication or failover groups)",
            "Traffic Manager (DNS failover)",
            "Azure Monitor + Log Analytics (centralized)",
            "Key Vault (per region)",
        ],
        "estimated_monthly_cost_usd": min(3000, budget),
        "cost_breakdown": {
            "Front Door Premium": "$100-200",
            "Compute (2 regions)": "$300-1000",
            "Cosmos DB (multi-region)": "$400-1500",
            "Azure SQL geo-replication": "$200-600",
            "Monitoring": "$50-150",
            "Data transfer (cross-region)": "$50-200",
        },
        "pros": [
            "Global low latency",
            "99.99% availability",
            "Automatic failover",
            "Data residency compliance",
            "Front Door WAF at the edge",
        ],
        "cons": [
            "1.5-2x cost vs single region",
            "Data consistency challenges (Cosmos DB conflict resolution)",
            "Complex deployment pipeline",
            "Cross-region data transfer costs",
        ],
        "scaling": {
            "users_supported": "100k - 100M",
            "requests_per_second": "10,000 - 10,000,000",
            "method": "Per-region autoscale + Front Door global routing",
        },
    }


PATTERN_DISPATCH = {
    "app_service_web": _app_service_web,
    "app_service_scaled": _app_service_web,  # same builder, cost adjusts
    "aks_microservices": _aks_microservices,
    "container_apps": _container_apps,
    "serverless_functions": _serverless_functions,
    "synapse_pipeline": _synapse_pipeline,
    "serverless_data": _serverless_data,
    "multi_region_web": _multi_region_web,
}


# ---------------------------------------------------------------------------
# Core recommendation logic
# ---------------------------------------------------------------------------

def recommend(app_type: str, users: int, requirements: Dict) -> Dict[str, Any]:
    """Return architecture recommendation for the given inputs."""
    bucket = _size_bucket(users)
    patterns = ARCHITECTURE_PATTERNS.get(app_type, ARCHITECTURE_PATTERNS["web_app"])
    pattern_key = patterns.get(bucket, "app_service_web")
    builder = PATTERN_DISPATCH.get(pattern_key, _app_service_web)
    result = builder(users, requirements)

    # Add compliance notes if relevant
    compliance = requirements.get("compliance", [])
    if compliance:
        result["compliance_notes"] = []
        if "HIPAA" in compliance:
            result["compliance_notes"].append(
                "Enable Microsoft Defender for Cloud, BAA agreement, audit logging, encryption at rest with CMK"
            )
        if "SOC2" in compliance:
            result["compliance_notes"].append(
                "Azure Policy SOC 2 initiative, Defender for Cloud regulatory compliance dashboard"
            )
        if "GDPR" in compliance:
            result["compliance_notes"].append(
                "Data residency in EU region, Purview for data classification, consent management"
            )
        if "ISO27001" in compliance or "ISO 27001" in compliance:
            result["compliance_notes"].append(
                "Azure Policy ISO 27001 initiative, audit logs to Log Analytics, access reviews in Entra ID"
            )

    return result


def generate_checklist(result: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Return an implementation checklist for the recommended architecture."""
    services = result.get("service_stack", [])
    return [
        {
            "phase": "Planning",
            "tasks": [
                "Review architecture pattern and Azure services",
                "Estimate costs with Azure Pricing Calculator",
                "Define environment strategy (dev, staging, production)",
                "Set up Azure subscription and resource groups",
                "Define tagging strategy (environment, owner, cost-center, app-name)",
            ],
        },
        {
            "phase": "Foundation",
            "tasks": [
                "Create VNet with subnets (app, data, management)",
                "Configure NSGs and Private Endpoints",
                "Set up Entra ID groups and RBAC assignments",
                "Create Key Vault and seed with initial secrets",
                "Enable Microsoft Defender for Cloud",
            ],
        },
        {
            "phase": "Core Services",
            "tasks": [f"Deploy {svc}" for svc in services],
        },
        {
            "phase": "Security",
            "tasks": [
                "Enable Managed Identity on all services",
                "Configure Private Endpoints for PaaS resources",
                "Set up Application Gateway or Front Door with WAF",
                "Assign Azure Policy initiatives (CIS, SOC 2, etc.)",
                "Enable diagnostic settings on all resources",
            ],
        },
        {
            "phase": "Monitoring",
            "tasks": [
                "Create Log Analytics workspace",
                "Enable Application Insights for all services",
                "Create Azure Monitor alert rules for critical metrics",
                "Set up Action Groups for notifications (email, Teams, PagerDuty)",
                "Create Azure Dashboard for operational visibility",
            ],
        },
        {
            "phase": "CI/CD",
            "tasks": [
                "Set up Azure DevOps or GitHub Actions pipeline",
                "Configure workload identity federation (no secrets in CI)",
                "Implement Bicep deployment pipeline with what-if preview",
                "Set up staging slots or blue-green deployment",
                "Document rollback procedures",
            ],
        },
    ]


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _format_text(result: Dict[str, Any]) -> str:
    lines = []
    lines.append(f"Pattern: {result['recommended_pattern']}")
    lines.append(f"Description: {result['description']}")
    lines.append(f"Use Case: {result['use_case']}")
    lines.append(f"Estimated Monthly Cost: ${result['estimated_monthly_cost_usd']}")
    lines.append("")
    lines.append("Service Stack:")
    for svc in result.get("service_stack", []):
        lines.append(f"  - {svc}")
    lines.append("")
    lines.append("Cost Breakdown:")
    for k, v in result.get("cost_breakdown", {}).items():
        lines.append(f"  {k}: {v}")
    lines.append("")
    lines.append("Pros:")
    for p in result.get("pros", []):
        lines.append(f"  + {p}")
    lines.append("")
    lines.append("Cons:")
    for c in result.get("cons", []):
        lines.append(f"  - {c}")
    if result.get("compliance_notes"):
        lines.append("")
        lines.append("Compliance Notes:")
        for note in result["compliance_notes"]:
            lines.append(f"  * {note}")
    lines.append("")
    lines.append("Scaling:")
    for k, v in result.get("scaling", {}).items():
        lines.append(f"  {k}: {v}")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Azure Architecture Designer — recommend Azure architecture patterns based on application requirements.",
        epilog="Examples:\n"
               "  python architecture_designer.py --app-type web_app --users 10000\n"
               "  python architecture_designer.py --app-type microservices --users 50000 --json\n"
               '  python architecture_designer.py --app-type serverless --users 5000 --requirements \'{"compliance":["HIPAA"]}\'',
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--app-type",
        required=True,
        choices=["web_app", "saas_platform", "mobile_backend", "microservices", "data_pipeline", "serverless"],
        help="Application type to design for",
    )
    parser.add_argument(
        "--users",
        type=int,
        default=1000,
        help="Expected number of users (default: 1000)",
    )
    parser.add_argument(
        "--requirements",
        type=str,
        default="{}",
        help="JSON string of additional requirements (budget_monthly_usd, compliance, etc.)",
    )
    parser.add_argument(
        "--checklist",
        action="store_true",
        help="Include implementation checklist in output",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        dest="json_output",
        help="Output as JSON instead of human-readable text",
    )

    args = parser.parse_args()

    try:
        reqs = json.loads(args.requirements)
    except json.JSONDecodeError as exc:
        print(f"Error: invalid --requirements JSON: {exc}", file=sys.stderr)
        sys.exit(1)

    result = recommend(args.app_type, args.users, reqs)

    if args.checklist:
        result["implementation_checklist"] = generate_checklist(result)

    if args.json_output:
        print(json.dumps(result, indent=2))
    else:
        print(_format_text(result))
        if args.checklist:
            print("\n--- Implementation Checklist ---")
            for phase in result["implementation_checklist"]:
                print(f"\n{phase['phase']}:")
                for task in phase["tasks"]:
                    print(f"  [ ] {task}")


if __name__ == "__main__":
    main()
