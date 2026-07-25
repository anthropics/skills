"""
GCP cost optimization analyzer.
Provides cost-saving recommendations for GCP resources.
"""

import argparse
import json
import sys
from typing import Dict, List, Any


class CostOptimizer:
    """Analyze GCP costs and provide optimization recommendations."""

    def __init__(self, current_resources: Dict[str, Any], monthly_spend: float):
        """
        Initialize with current GCP resources and spending.

        Args:
            current_resources: Dictionary of current GCP resources
            monthly_spend: Current monthly GCP spend in USD
        """
        self.resources = current_resources
        self.monthly_spend = monthly_spend
        self.recommendations = []

    def analyze_and_optimize(self) -> Dict[str, Any]:
        """
        Analyze current setup and generate cost optimization recommendations.

        Returns:
            Dictionary with recommendations and potential savings
        """
        self.recommendations = []
        potential_savings = 0.0

        compute_savings = self._analyze_compute()
        potential_savings += compute_savings

        storage_savings = self._analyze_storage()
        potential_savings += storage_savings

        database_savings = self._analyze_database()
        potential_savings += database_savings

        network_savings = self._analyze_networking()
        potential_savings += network_savings

        general_savings = self._analyze_general_optimizations()
        potential_savings += general_savings

        return {
            'current_monthly_spend': self.monthly_spend,
            'potential_monthly_savings': round(potential_savings, 2),
            'optimized_monthly_spend': round(self.monthly_spend - potential_savings, 2),
            'savings_percentage': round((potential_savings / self.monthly_spend) * 100, 2) if self.monthly_spend > 0 else 0,
            'recommendations': self.recommendations,
            'priority_actions': self._prioritize_recommendations()
        }

    def _analyze_compute(self) -> float:
        """Analyze compute resources (GCE, GKE, Cloud Run)."""
        savings = 0.0

        gce_instances = self.resources.get('gce_instances', [])
        if gce_instances:
            idle_count = sum(1 for inst in gce_instances if inst.get('cpu_utilization', 100) < 10)
            if idle_count > 0:
                idle_cost = idle_count * 50
                savings += idle_cost
                self.recommendations.append({
                    'service': 'Compute Engine',
                    'type': 'Idle Resources',
                    'issue': f'{idle_count} GCE instances with <10% CPU utilization',
                    'recommendation': 'Stop or delete idle instances, or downsize to smaller machine types',
                    'potential_savings': idle_cost,
                    'priority': 'high'
                })

            # Check for committed use discounts
            on_demand_count = sum(1 for inst in gce_instances if inst.get('pricing', 'on-demand') == 'on-demand')
            if on_demand_count >= 2:
                cud_savings = on_demand_count * 50 * 0.37  # 37% savings with 1-yr CUD
                savings += cud_savings
                self.recommendations.append({
                    'service': 'Compute Engine',
                    'type': 'Committed Use Discounts',
                    'issue': f'{on_demand_count} instances on on-demand pricing',
                    'recommendation': 'Purchase 1-year committed use discounts for predictable workloads (37% savings) or 3-year (55% savings)',
                    'potential_savings': cud_savings,
                    'priority': 'medium'
                })

            # Check for sustained use discounts awareness
            short_lived = sum(1 for inst in gce_instances if inst.get('uptime_hours_month', 730) < 200)
            if short_lived > 0:
                self.recommendations.append({
                    'service': 'Compute Engine',
                    'type': 'Scheduling',
                    'issue': f'{short_lived} instances running <200 hours/month',
                    'recommendation': 'Use Instance Scheduler to stop dev/test instances outside business hours',
                    'potential_savings': short_lived * 20,
                    'priority': 'medium'
                })
                savings += short_lived * 20

        # GKE optimization
        gke_clusters = self.resources.get('gke_clusters', [])
        for cluster in gke_clusters:
            if cluster.get('mode', 'standard') == 'standard':
                node_utilization = cluster.get('avg_node_utilization', 100)
                if node_utilization < 40:
                    autopilot_savings = cluster.get('monthly_cost', 500) * 0.30
                    savings += autopilot_savings
                    self.recommendations.append({
                        'service': 'GKE',
                        'type': 'Cluster Mode',
                        'issue': f'Standard GKE cluster with <40% node utilization',
                        'recommendation': 'Migrate to GKE Autopilot to pay only for pod resources, or enable cluster autoscaler',
                        'potential_savings': autopilot_savings,
                        'priority': 'high'
                    })

        # Cloud Run optimization
        cloud_run_services = self.resources.get('cloud_run_services', [])
        for svc in cloud_run_services:
            if svc.get('min_instances', 0) > 0 and svc.get('avg_rps', 100) < 1:
                min_inst_savings = svc.get('min_instances', 1) * 15
                savings += min_inst_savings
                self.recommendations.append({
                    'service': 'Cloud Run',
                    'type': 'Min Instances',
                    'issue': f'Service {svc.get("name", "unknown")} has min instances but very low traffic',
                    'recommendation': 'Set min-instances to 0 for low-traffic services to enable scale-to-zero',
                    'potential_savings': min_inst_savings,
                    'priority': 'medium'
                })

        return savings

    def _analyze_storage(self) -> float:
        """Analyze Cloud Storage resources."""
        savings = 0.0

        gcs_buckets = self.resources.get('gcs_buckets', [])
        for bucket in gcs_buckets:
            size_gb = bucket.get('size_gb', 0)
            storage_class = bucket.get('storage_class', 'STANDARD')

            if not bucket.get('has_lifecycle_policy', False) and size_gb > 100:
                lifecycle_savings = size_gb * 0.012
                savings += lifecycle_savings
                self.recommendations.append({
                    'service': 'Cloud Storage',
                    'type': 'Lifecycle Policy',
                    'issue': f'Bucket {bucket.get("name", "unknown")} ({size_gb} GB) has no lifecycle policy',
                    'recommendation': 'Add lifecycle rule: Transition to Nearline after 30 days, Coldline after 90 days, Archive after 365 days',
                    'potential_savings': lifecycle_savings,
                    'priority': 'medium'
                })

            if storage_class == 'STANDARD' and size_gb > 500:
                class_savings = size_gb * 0.006
                savings += class_savings
                self.recommendations.append({
                    'service': 'Cloud Storage',
                    'type': 'Storage Class',
                    'issue': f'Large bucket ({size_gb} GB) using Standard class',
                    'recommendation': 'Enable Autoclass for automatic storage class management based on access patterns',
                    'potential_savings': class_savings,
                    'priority': 'high'
                })

        return savings

    def _analyze_database(self) -> float:
        """Analyze Cloud SQL, Firestore, and BigQuery costs."""
        savings = 0.0

        cloud_sql_instances = self.resources.get('cloud_sql_instances', [])
        for db in cloud_sql_instances:
            if db.get('connections_per_day', 1000) < 10:
                db_cost = db.get('monthly_cost', 100)
                savings += db_cost * 0.8
                self.recommendations.append({
                    'service': 'Cloud SQL',
                    'type': 'Idle Resource',
                    'issue': f'Database {db.get("name", "unknown")} has <10 connections/day',
                    'recommendation': 'Stop database if not needed, or take a backup and delete',
                    'potential_savings': db_cost * 0.8,
                    'priority': 'high'
                })

            if db.get('utilization', 100) < 30 and not db.get('has_ha', False):
                rightsize_savings = db.get('monthly_cost', 200) * 0.35
                savings += rightsize_savings
                self.recommendations.append({
                    'service': 'Cloud SQL',
                    'type': 'Right-sizing',
                    'issue': f'Cloud SQL instance {db.get("name", "unknown")} has low utilization (<30%)',
                    'recommendation': 'Downsize to a smaller machine type (e.g., db-custom-2-8192 to db-f1-micro for dev)',
                    'potential_savings': rightsize_savings,
                    'priority': 'medium'
                })

        # BigQuery optimization
        bigquery_datasets = self.resources.get('bigquery_datasets', [])
        for dataset in bigquery_datasets:
            if dataset.get('pricing_model', 'on_demand') == 'on_demand':
                monthly_tb_scanned = dataset.get('monthly_tb_scanned', 0)
                if monthly_tb_scanned > 10:
                    slot_savings = (monthly_tb_scanned * 6.25) * 0.30
                    savings += slot_savings
                    self.recommendations.append({
                        'service': 'BigQuery',
                        'type': 'Pricing Model',
                        'issue': f'Scanning {monthly_tb_scanned} TB/month on on-demand pricing',
                        'recommendation': 'Switch to BigQuery editions with slots for predictable costs (30%+ savings at this volume)',
                        'potential_savings': slot_savings,
                        'priority': 'high'
                    })

            if not dataset.get('has_partitioning', False):
                partition_savings = dataset.get('monthly_query_cost', 50) * 0.50
                savings += partition_savings
                self.recommendations.append({
                    'service': 'BigQuery',
                    'type': 'Table Partitioning',
                    'issue': f'Tables in {dataset.get("name", "unknown")} lack partitioning',
                    'recommendation': 'Partition tables by date and add clustering columns to reduce bytes scanned',
                    'potential_savings': partition_savings,
                    'priority': 'medium'
                })

        return savings

    def _analyze_networking(self) -> float:
        """Analyze networking costs (egress, Cloud NAT, etc.)."""
        savings = 0.0

        cloud_nat_gateways = self.resources.get('cloud_nat_gateways', [])
        if len(cloud_nat_gateways) > 1:
            extra_nats = len(cloud_nat_gateways) - 1
            nat_savings = extra_nats * 45
            savings += nat_savings
            self.recommendations.append({
                'service': 'Cloud NAT',
                'type': 'Resource Consolidation',
                'issue': f'{len(cloud_nat_gateways)} Cloud NAT gateways deployed',
                'recommendation': 'Consolidate NAT gateways in dev/staging, or use Private Google Access for GCP services',
                'potential_savings': nat_savings,
                'priority': 'high'
            })

        egress_gb = self.resources.get('monthly_egress_gb', 0)
        if egress_gb > 1000:
            cdn_savings = egress_gb * 0.04  # CDN is cheaper than direct egress
            savings += cdn_savings
            self.recommendations.append({
                'service': 'Networking',
                'type': 'CDN Optimization',
                'issue': f'High egress volume ({egress_gb} GB/month)',
                'recommendation': 'Enable Cloud CDN to serve cached content at lower egress rates',
                'potential_savings': cdn_savings,
                'priority': 'medium'
            })

        return savings

    def _analyze_general_optimizations(self) -> float:
        """General GCP cost optimizations."""
        savings = 0.0

        # Log retention
        log_sinks = self.resources.get('log_sinks', [])
        if not log_sinks:
            log_volume_gb = self.resources.get('monthly_log_volume_gb', 0)
            if log_volume_gb > 50:
                log_savings = log_volume_gb * 0.50 * 0.6
                savings += log_savings
                self.recommendations.append({
                    'service': 'Cloud Logging',
                    'type': 'Log Exclusion',
                    'issue': f'{log_volume_gb} GB/month of logs without exclusion filters',
                    'recommendation': 'Create log exclusion filters for verbose/debug logs and route remaining to Cloud Storage via log sinks',
                    'potential_savings': log_savings,
                    'priority': 'medium'
                })

        # Unattached persistent disks
        persistent_disks = self.resources.get('persistent_disks', [])
        unattached = sum(1 for disk in persistent_disks if not disk.get('attached', True))
        if unattached > 0:
            disk_savings = unattached * 10  # ~$10/month per 100 GB disk
            savings += disk_savings
            self.recommendations.append({
                'service': 'Compute Engine',
                'type': 'Unused Resources',
                'issue': f'{unattached} unattached persistent disks',
                'recommendation': 'Snapshot and delete unused persistent disks',
                'potential_savings': disk_savings,
                'priority': 'high'
            })

        # Static external IPs
        static_ips = self.resources.get('static_ips', [])
        unused_ips = sum(1 for ip in static_ips if not ip.get('in_use', True))
        if unused_ips > 0:
            ip_savings = unused_ips * 7.30  # $0.01/hour = $7.30/month
            savings += ip_savings
            self.recommendations.append({
                'service': 'Networking',
                'type': 'Unused Resources',
                'issue': f'{unused_ips} unused static external IP addresses',
                'recommendation': 'Release unused static IPs to avoid hourly charges',
                'potential_savings': ip_savings,
                'priority': 'high'
            })

        # Budget alerts
        if not self.resources.get('has_budget_alerts', False):
            self.recommendations.append({
                'service': 'Cloud Billing',
                'type': 'Cost Monitoring',
                'issue': 'No budget alerts configured',
                'recommendation': 'Set up Cloud Billing budgets with alerts at 50%, 80%, 100% of monthly budget',
                'potential_savings': 0,
                'priority': 'high'
            })

        # Recommender API
        if not self.resources.get('uses_recommender', False):
            self.recommendations.append({
                'service': 'Active Assist',
                'type': 'Visibility',
                'issue': 'GCP Recommender not reviewed',
                'recommendation': 'Review Active Assist recommendations for right-sizing, idle resources, and committed use discounts',
                'potential_savings': 0,
                'priority': 'medium'
            })

        return savings

    def _prioritize_recommendations(self) -> List[Dict[str, Any]]:
        """Get top priority recommendations."""
        high_priority = [r for r in self.recommendations if r['priority'] == 'high']
        high_priority.sort(key=lambda x: x.get('potential_savings', 0), reverse=True)
        return high_priority[:5]

    def generate_optimization_checklist(self) -> List[Dict[str, Any]]:
        """Generate actionable checklist for cost optimization."""
        return [
            {
                'category': 'Immediate Actions (Today)',
                'items': [
                    'Release unused static IPs',
                    'Delete unattached persistent disks',
                    'Stop idle Compute Engine instances',
                    'Set up billing budget alerts'
                ]
            },
            {
                'category': 'This Week',
                'items': [
                    'Add Cloud Storage lifecycle policies',
                    'Create log exclusion filters for verbose logs',
                    'Right-size Cloud SQL instances',
                    'Review Active Assist recommendations'
                ]
            },
            {
                'category': 'This Month',
                'items': [
                    'Evaluate committed use discounts',
                    'Migrate GKE Standard to Autopilot where applicable',
                    'Partition and cluster BigQuery tables',
                    'Enable Cloud CDN for high-egress services'
                ]
            },
            {
                'category': 'Ongoing',
                'items': [
                    'Review billing reports weekly',
                    'Label all resources for cost allocation',
                    'Monitor Active Assist recommendations monthly',
                    'Conduct quarterly cost optimization reviews'
                ]
            }
        ]


def main():
    parser = argparse.ArgumentParser(
        description='GCP Cost Optimizer - Analyzes GCP resources and recommends cost savings'
    )
    parser.add_argument(
        '--resources', '-r',
        type=str,
        help='Path to JSON file with current GCP resource inventory'
    )
    parser.add_argument(
        '--monthly-spend', '-s',
        type=float,
        default=1000,
        help='Current monthly GCP spend in USD (default: 1000)'
    )
    parser.add_argument(
        '--output', '-o',
        type=str,
        help='Path to write optimization report JSON'
    )
    parser.add_argument(
        '--json',
        action='store_true',
        help='Output as JSON format'
    )
    parser.add_argument(
        '--checklist',
        action='store_true',
        help='Generate optimization checklist'
    )

    args = parser.parse_args()

    if args.resources:
        try:
            with open(args.resources, 'r') as f:
                resources = json.load(f)
        except FileNotFoundError:
            print(f"Error: File '{args.resources}' not found.", file=sys.stderr)
            sys.exit(1)
        except json.JSONDecodeError:
            print(f"Error: File '{args.resources}' is not valid JSON.", file=sys.stderr)
            sys.exit(1)
    else:
        resources = {}

    optimizer = CostOptimizer(resources, args.monthly_spend)
    result = optimizer.analyze_and_optimize()

    if args.checklist:
        result['checklist'] = optimizer.generate_optimization_checklist()

    if args.output:
        with open(args.output, 'w') as f:
            json.dump(result, f, indent=2)
        print(f"Report written to {args.output}")
    elif args.json:
        print(json.dumps(result, indent=2))
    else:
        print(f"\nGCP Cost Optimization Report")
        print(f"{'=' * 40}")
        print(f"Current Monthly Spend: ${result['current_monthly_spend']:.2f}")
        print(f"Potential Savings:     ${result['potential_monthly_savings']:.2f}")
        print(f"Optimized Spend:       ${result['optimized_monthly_spend']:.2f}")
        print(f"Savings Percentage:    {result['savings_percentage']}%")
        print(f"\nTop Priority Actions:")
        for i, action in enumerate(result['priority_actions'], 1):
            print(f"  {i}. [{action['service']}] {action['recommendation']}")
            print(f"     Savings: ${action['potential_savings']:.2f}/month")
        print(f"\nTotal Recommendations: {len(result['recommendations'])}")


if __name__ == '__main__':
    main()
