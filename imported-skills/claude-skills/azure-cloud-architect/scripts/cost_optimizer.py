#!/usr/bin/env python3
"""
Azure cost optimization analyzer.
Analyzes Azure resource configurations and provides cost-saving recommendations.

Usage:
    python cost_optimizer.py --config resources.json
    python cost_optimizer.py --config resources.json --json
    python cost_optimizer.py --help

Expected JSON config format:
{
  "virtual_machines": [
    {"name": "vm-web-01", "size": "Standard_D4s_v5", "cpu_utilization": 12, "pricing": "on-demand", "monthly_cost": 140}
  ],
  "sql_databases": [
    {"name": "sqldb-main", "tier": "GeneralPurpose", "vcores": 8, "utilization": 25, "monthly_cost": 400}
  ],
  "storage_accounts": [
    {"name": "stmyapp", "size_gb": 500, "tier": "Hot", "has_lifecycle_policy": false}
  ],
  "aks_clusters": [
    {"name": "aks-prod", "node_count": 6, "node_size": "Standard_D4s_v5", "avg_cpu_utilization": 35, "monthly_cost": 800}
  ],
  "cosmos_db": [
    {"name": "cosmos-orders", "ru_provisioned": 10000, "ru_used_avg": 2000, "monthly_cost": 580}
  ],
  "public_ips": [
    {"name": "pip-unused", "attached": false}
  ],
  "app_services": [
    {"name": "app-web", "tier": "PremiumV3", "instance_count": 3, "cpu_utilization": 15, "monthly_cost": 300}
  ],
  "has_budget_alerts": false,
  "has_advisor_enabled": false
}
"""

import argparse
import json
import sys
from typing import Dict, List, Any


class AzureCostOptimizer:
    """Analyze Azure resource configurations and recommend cost savings."""

    def __init__(self, resources: Dict[str, Any]):
        self.resources = resources
        self.recommendations: List[Dict[str, Any]] = []

    def analyze(self) -> Dict[str, Any]:
        """Run all analysis passes and return full report."""
        self.recommendations = []
        total_savings = 0.0

        total_savings += self._analyze_virtual_machines()
        total_savings += self._analyze_sql_databases()
        total_savings += self._analyze_storage()
        total_savings += self._analyze_aks()
        total_savings += self._analyze_cosmos_db()
        total_savings += self._analyze_app_services()
        total_savings += self._analyze_networking()
        total_savings += self._analyze_general()

        current_spend = self._estimate_current_spend()

        return {
            "current_monthly_usd": round(current_spend, 2),
            "potential_monthly_savings_usd": round(total_savings, 2),
            "optimized_monthly_usd": round(current_spend - total_savings, 2),
            "savings_percentage": round((total_savings / current_spend) * 100, 2) if current_spend > 0 else 0,
            "recommendations": self.recommendations,
            "priority_actions": self._top_priority(),
        }

    # ------------------------------------------------------------------
    # Analysis passes
    # ------------------------------------------------------------------

    def _analyze_virtual_machines(self) -> float:
        savings = 0.0
        vms = self.resources.get("virtual_machines", [])

        for vm in vms:
            cost = vm.get("monthly_cost", 140)
            cpu = vm.get("cpu_utilization", 100)
            pricing = vm.get("pricing", "on-demand")

            # Idle VMs
            if cpu < 5:
                savings += cost * 0.9
                self.recommendations.append({
                    "service": "Virtual Machines",
                    "type": "Idle Resource",
                    "issue": f"VM {vm.get('name', '?')} has <5% CPU utilization",
                    "recommendation": "Deallocate or delete the VM. Use Azure Automation auto-shutdown for dev/test VMs.",
                    "potential_savings_usd": round(cost * 0.9, 2),
                    "priority": "high",
                })
            elif cpu < 20:
                savings += cost * 0.4
                self.recommendations.append({
                    "service": "Virtual Machines",
                    "type": "Right-sizing",
                    "issue": f"VM {vm.get('name', '?')} is under-utilized ({cpu}% CPU)",
                    "recommendation": "Downsize to a smaller SKU. Use Azure Advisor right-sizing recommendations.",
                    "potential_savings_usd": round(cost * 0.4, 2),
                    "priority": "high",
                })

            # Reserved Instances
            if pricing == "on-demand" and cpu >= 20:
                ri_savings = cost * 0.35
                savings += ri_savings
                self.recommendations.append({
                    "service": "Virtual Machines",
                    "type": "Reserved Instances",
                    "issue": f"VM {vm.get('name', '?')} runs on-demand with steady utilization",
                    "recommendation": "Purchase 1-year Reserved Instance (up to 35% savings) or 3-year (up to 55% savings).",
                    "potential_savings_usd": round(ri_savings, 2),
                    "priority": "medium",
                })

        # Spot VMs for batch/fault-tolerant workloads
        spot_candidates = [vm for vm in vms if vm.get("workload_type") in ("batch", "dev", "test")]
        if spot_candidates:
            spot_savings = sum(vm.get("monthly_cost", 100) * 0.6 for vm in spot_candidates)
            savings += spot_savings
            self.recommendations.append({
                "service": "Virtual Machines",
                "type": "Spot VMs",
                "issue": f"{len(spot_candidates)} VMs running batch/dev/test workloads on regular instances",
                "recommendation": "Switch to Azure Spot VMs for up to 90% savings on interruptible workloads.",
                "potential_savings_usd": round(spot_savings, 2),
                "priority": "medium",
            })

        return savings

    def _analyze_sql_databases(self) -> float:
        savings = 0.0
        dbs = self.resources.get("sql_databases", [])

        for db in dbs:
            cost = db.get("monthly_cost", 200)
            utilization = db.get("utilization", 100)
            vcores = db.get("vcores", 2)
            tier = db.get("tier", "GeneralPurpose")

            # Idle databases
            if db.get("connections_per_day", 1000) < 10:
                savings += cost * 0.8
                self.recommendations.append({
                    "service": "Azure SQL",
                    "type": "Idle Resource",
                    "issue": f"Database {db.get('name', '?')} has <10 connections/day",
                    "recommendation": "Delete unused database or switch to serverless tier with auto-pause.",
                    "potential_savings_usd": round(cost * 0.8, 2),
                    "priority": "high",
                })

            # Serverless opportunity
            elif utilization < 30 and tier == "GeneralPurpose":
                serverless_savings = cost * 0.45
                savings += serverless_savings
                self.recommendations.append({
                    "service": "Azure SQL",
                    "type": "Serverless Migration",
                    "issue": f"Database {db.get('name', '?')} has low utilization ({utilization}%) on provisioned tier",
                    "recommendation": "Switch to Azure SQL Serverless tier with auto-pause (60-min delay). Pay only for active compute.",
                    "potential_savings_usd": round(serverless_savings, 2),
                    "priority": "high",
                })

            # Right-sizing
            elif utilization < 50 and vcores > 2:
                right_size_savings = cost * 0.3
                savings += right_size_savings
                self.recommendations.append({
                    "service": "Azure SQL",
                    "type": "Right-sizing",
                    "issue": f"Database {db.get('name', '?')} uses {vcores} vCores at {utilization}% utilization",
                    "recommendation": f"Reduce to {max(2, vcores // 2)} vCores. Monitor DTU/vCore usage after change.",
                    "potential_savings_usd": round(right_size_savings, 2),
                    "priority": "medium",
                })

        return savings

    def _analyze_storage(self) -> float:
        savings = 0.0
        accounts = self.resources.get("storage_accounts", [])

        for acct in accounts:
            size_gb = acct.get("size_gb", 0)
            tier = acct.get("tier", "Hot")

            # Lifecycle policy missing
            if not acct.get("has_lifecycle_policy", False) and size_gb > 50:
                lifecycle_savings = size_gb * 0.01  # ~$0.01/GB moving hot to cool
                savings += lifecycle_savings
                self.recommendations.append({
                    "service": "Blob Storage",
                    "type": "Lifecycle Policy",
                    "issue": f"Account {acct.get('name', '?')} ({size_gb} GB) has no lifecycle policy",
                    "recommendation": "Add lifecycle management: move to Cool after 30 days, Archive after 90 days.",
                    "potential_savings_usd": round(lifecycle_savings, 2),
                    "priority": "medium",
                })

            # Hot tier for large, infrequently accessed data
            if tier == "Hot" and size_gb > 500:
                tier_savings = size_gb * 0.008
                savings += tier_savings
                self.recommendations.append({
                    "service": "Blob Storage",
                    "type": "Storage Tier",
                    "issue": f"Account {acct.get('name', '?')} ({size_gb} GB) on Hot tier",
                    "recommendation": "Evaluate Cool or Cold tier for infrequently accessed data. Hot=$0.018/GB, Cool=$0.01/GB, Cold=$0.0036/GB.",
                    "potential_savings_usd": round(tier_savings, 2),
                    "priority": "high",
                })

        return savings

    def _analyze_aks(self) -> float:
        savings = 0.0
        clusters = self.resources.get("aks_clusters", [])

        for cluster in clusters:
            cost = cluster.get("monthly_cost", 500)
            cpu = cluster.get("avg_cpu_utilization", 100)
            node_count = cluster.get("node_count", 3)

            # Over-provisioned cluster
            if cpu < 30 and node_count > 3:
                aks_savings = cost * 0.3
                savings += aks_savings
                self.recommendations.append({
                    "service": "AKS",
                    "type": "Right-sizing",
                    "issue": f"Cluster {cluster.get('name', '?')} has {node_count} nodes at {cpu}% CPU",
                    "recommendation": "Enable cluster autoscaler. Set min nodes to 2 (or 1 for dev). Use node auto-provisioning.",
                    "potential_savings_usd": round(aks_savings, 2),
                    "priority": "high",
                })

            # Spot node pools for non-critical workloads
            if not cluster.get("has_spot_pool", False):
                spot_savings = cost * 0.15
                savings += spot_savings
                self.recommendations.append({
                    "service": "AKS",
                    "type": "Spot Node Pools",
                    "issue": f"Cluster {cluster.get('name', '?')} has no spot node pools",
                    "recommendation": "Add a spot node pool for batch jobs, CI runners, and dev workloads (up to 90% savings).",
                    "potential_savings_usd": round(spot_savings, 2),
                    "priority": "medium",
                })

        return savings

    def _analyze_cosmos_db(self) -> float:
        savings = 0.0
        dbs = self.resources.get("cosmos_db", [])

        for db in dbs:
            cost = db.get("monthly_cost", 200)
            ru_provisioned = db.get("ru_provisioned", 400)
            ru_used = db.get("ru_used_avg", 400)

            # Massive over-provisioning
            if ru_provisioned > 0 and ru_used / ru_provisioned < 0.2:
                cosmos_savings = cost * 0.5
                savings += cosmos_savings
                self.recommendations.append({
                    "service": "Cosmos DB",
                    "type": "Right-sizing",
                    "issue": f"Container {db.get('name', '?')} uses {ru_used}/{ru_provisioned} RU/s ({int(ru_used/ru_provisioned*100)}% utilization)",
                    "recommendation": "Switch to autoscale throughput or serverless mode. Autoscale adjusts RU/s between 10%-100% of max.",
                    "potential_savings_usd": round(cosmos_savings, 2),
                    "priority": "high",
                })
            elif ru_provisioned > 0 and ru_used / ru_provisioned < 0.5:
                cosmos_savings = cost * 0.25
                savings += cosmos_savings
                self.recommendations.append({
                    "service": "Cosmos DB",
                    "type": "Autoscale",
                    "issue": f"Container {db.get('name', '?')} uses {ru_used}/{ru_provisioned} RU/s — variable workload",
                    "recommendation": "Enable autoscale throughput. Set max RU/s to current provisioned value.",
                    "potential_savings_usd": round(cosmos_savings, 2),
                    "priority": "medium",
                })

        return savings

    def _analyze_app_services(self) -> float:
        savings = 0.0
        apps = self.resources.get("app_services", [])

        for app in apps:
            cost = app.get("monthly_cost", 100)
            cpu = app.get("cpu_utilization", 100)
            instances = app.get("instance_count", 1)
            tier = app.get("tier", "Basic")

            # Over-provisioned instances
            if cpu < 20 and instances > 1:
                app_savings = cost * 0.4
                savings += app_savings
                self.recommendations.append({
                    "service": "App Service",
                    "type": "Right-sizing",
                    "issue": f"App {app.get('name', '?')} runs {instances} instances at {cpu}% CPU",
                    "recommendation": "Reduce instance count or enable autoscale with min=1. Consider downgrading plan tier.",
                    "potential_savings_usd": round(app_savings, 2),
                    "priority": "high",
                })

            # Premium tier for dev/test
            if tier in ("PremiumV3", "PremiumV2") and app.get("environment") in ("dev", "test"):
                tier_savings = cost * 0.5
                savings += tier_savings
                self.recommendations.append({
                    "service": "App Service",
                    "type": "Plan Tier",
                    "issue": f"App {app.get('name', '?')} uses {tier} in {app.get('environment', 'unknown')} environment",
                    "recommendation": "Use Basic (B1) or Free tier for dev/test environments.",
                    "potential_savings_usd": round(tier_savings, 2),
                    "priority": "high",
                })

        return savings

    def _analyze_networking(self) -> float:
        savings = 0.0

        # Unattached public IPs
        pips = self.resources.get("public_ips", [])
        unattached = [p for p in pips if not p.get("attached", True)]
        if unattached:
            pip_savings = len(unattached) * 3.65  # ~$0.005/hr = $3.65/month
            savings += pip_savings
            self.recommendations.append({
                "service": "Public IP",
                "type": "Unused Resource",
                "issue": f"{len(unattached)} unattached public IPs incurring hourly charges",
                "recommendation": "Delete unused public IPs. Unattached Standard SKU IPs cost ~$3.65/month each.",
                "potential_savings_usd": round(pip_savings, 2),
                "priority": "high",
            })

        # NAT Gateway in dev environments
        nat_gateways = self.resources.get("nat_gateways", [])
        dev_nats = [n for n in nat_gateways if n.get("environment") in ("dev", "test")]
        if dev_nats:
            nat_savings = len(dev_nats) * 32  # ~$32/month per NAT Gateway
            savings += nat_savings
            self.recommendations.append({
                "service": "NAT Gateway",
                "type": "Environment Optimization",
                "issue": f"{len(dev_nats)} NAT Gateways in dev/test environments",
                "recommendation": "Remove NAT Gateways in dev/test. Use Azure Firewall or service tags for outbound instead.",
                "potential_savings_usd": round(nat_savings, 2),
                "priority": "medium",
            })

        return savings

    def _analyze_general(self) -> float:
        savings = 0.0

        if not self.resources.get("has_budget_alerts", False):
            self.recommendations.append({
                "service": "Cost Management",
                "type": "Budget Alerts",
                "issue": "No budget alerts configured",
                "recommendation": "Create Azure Budget with alerts at 50%, 80%, and 100% of monthly target.",
                "potential_savings_usd": 0,
                "priority": "high",
            })

        if not self.resources.get("has_advisor_enabled", True):
            self.recommendations.append({
                "service": "Azure Advisor",
                "type": "Visibility",
                "issue": "Azure Advisor cost recommendations not reviewed",
                "recommendation": "Review Azure Advisor cost recommendations weekly. Enable Advisor alerts for new findings.",
                "potential_savings_usd": 0,
                "priority": "medium",
            })

        return savings

    # ------------------------------------------------------------------
    # Helpers
    # ------------------------------------------------------------------

    def _estimate_current_spend(self) -> float:
        total = 0.0
        for key in ("virtual_machines", "sql_databases", "aks_clusters", "cosmos_db", "app_services"):
            for item in self.resources.get(key, []):
                total += item.get("monthly_cost", 0)
        # Storage estimate
        for acct in self.resources.get("storage_accounts", []):
            total += acct.get("size_gb", 0) * 0.018  # Hot tier default
        # Public IPs
        for pip in self.resources.get("public_ips", []):
            total += 3.65
        return total if total > 0 else 1000  # Default if no cost data

    def _top_priority(self) -> List[Dict[str, Any]]:
        high = [r for r in self.recommendations if r["priority"] == "high"]
        high.sort(key=lambda x: x.get("potential_savings_usd", 0), reverse=True)
        return high[:5]


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _format_text(report: Dict[str, Any]) -> str:
    lines = []
    lines.append(f"Current Monthly Spend: ${report['current_monthly_usd']}")
    lines.append(f"Potential Savings:     ${report['potential_monthly_savings_usd']} ({report['savings_percentage']}%)")
    lines.append(f"Optimized Spend:       ${report['optimized_monthly_usd']}")
    lines.append("")

    lines.append("=== Priority Actions ===")
    for i, action in enumerate(report.get("priority_actions", []), 1):
        lines.append(f"  {i}. [{action['service']}] {action['recommendation']}")
        lines.append(f"     Savings: ${action.get('potential_savings_usd', 0)}")
    lines.append("")

    lines.append("=== All Recommendations ===")
    for rec in report.get("recommendations", []):
        lines.append(f"  [{rec['priority'].upper()}] {rec['service']} — {rec['type']}")
        lines.append(f"    Issue: {rec['issue']}")
        lines.append(f"    Action: {rec['recommendation']}")
        savings = rec.get("potential_savings_usd", 0)
        if savings:
            lines.append(f"    Savings: ${savings}")
        lines.append("")

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Azure Cost Optimizer — analyze Azure resources and recommend cost savings.",
        epilog="Examples:\n"
               "  python cost_optimizer.py --config resources.json\n"
               "  python cost_optimizer.py --config resources.json --json",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--config",
        required=True,
        help="Path to JSON file with current Azure resource inventory",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        dest="json_output",
        help="Output as JSON instead of human-readable text",
    )

    args = parser.parse_args()

    try:
        with open(args.config, "r") as f:
            resources = json.load(f)
    except FileNotFoundError:
        print(f"Error: file not found: {args.config}", file=sys.stderr)
        sys.exit(1)
    except json.JSONDecodeError as exc:
        print(f"Error: invalid JSON in {args.config}: {exc}", file=sys.stderr)
        sys.exit(1)

    optimizer = AzureCostOptimizer(resources)
    report = optimizer.analyze()

    if args.json_output:
        print(json.dumps(report, indent=2))
    else:
        print(_format_text(report))


if __name__ == "__main__":
    main()
