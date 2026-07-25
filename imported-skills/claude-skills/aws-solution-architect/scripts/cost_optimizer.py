"""
AWS cost optimization analyzer.
Provides cost-saving recommendations for startup budgets.
"""

from typing import Dict, List, Any, Optional


class CostOptimizer:
    """Analyze AWS costs and provide optimization recommendations."""

    def __init__(self, current_resources: Dict[str, Any], monthly_spend: float):
        """
        Initialize with current AWS resources and spending.

        Args:
            current_resources: Dictionary of current AWS resources
            monthly_spend: Current monthly AWS spend in USD
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

        # Analyze compute resources
        compute_savings = self._analyze_compute()
        potential_savings += compute_savings

        # Analyze storage
        storage_savings = self._analyze_storage()
        potential_savings += storage_savings

        # Analyze database
        database_savings = self._analyze_database()
        potential_savings += database_savings

        # Analyze networking
        network_savings = self._analyze_networking()
        potential_savings += network_savings

        # General AWS optimizations
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
        """Analyze compute resources (EC2, Lambda, Fargate)."""
        savings = 0.0

        ec2_instances = self.resources.get('ec2_instances', [])
        if ec2_instances:
            # Check for idle instances
            idle_count = sum(1 for inst in ec2_instances if inst.get('cpu_utilization', 100) < 10)
            if idle_count > 0:
                idle_cost = idle_count * 50  # Assume $50/month per idle instance
                savings += idle_cost
                self.recommendations.append({
                    'service': 'EC2',
                    'type': 'Idle Resources',
                    'issue': f'{idle_count} EC2 instances with <10% CPU utilization',
                    'recommendation': 'Stop or terminate idle instances, or downsize to smaller instance types',
                    'potential_savings': idle_cost,
                    'priority': 'high'
                })

            # Check for Savings Plans / Reserved Instances
            on_demand_count = sum(1 for inst in ec2_instances if inst.get('pricing', 'on-demand') == 'on-demand')
            if on_demand_count >= 2:
                ri_savings = on_demand_count * 50 * 0.30  # 30% savings with RIs
                savings += ri_savings
                self.recommendations.append({
                    'service': 'EC2',
                    'type': 'Pricing Optimization',
                    'issue': f'{on_demand_count} instances on On-Demand pricing',
                    'recommendation': 'Purchase Compute Savings Plan or Reserved Instances for predictable workloads (1-year commitment)',
                    'potential_savings': ri_savings,
                    'priority': 'medium'
                })

        # Lambda optimization
        lambda_functions = self.resources.get('lambda_functions', [])
        if lambda_functions:
            oversized = sum(1 for fn in lambda_functions if fn.get('memory_mb', 128) > 512 and fn.get('avg_memory_used_mb', 0) < 256)
            if oversized > 0:
                lambda_savings = oversized * 5  # Assume $5/month per oversized function
                savings += lambda_savings
                self.recommendations.append({
                    'service': 'Lambda',
                    'type': 'Right-sizing',
                    'issue': f'{oversized} Lambda functions over-provisioned (memory too high)',
                    'recommendation': 'Use AWS Lambda Power Tuning tool to optimize memory settings',
                    'potential_savings': lambda_savings,
                    'priority': 'low'
                })

        return savings

    def _analyze_storage(self) -> float:
        """Analyze S3 and other storage resources."""
        savings = 0.0

        s3_buckets = self.resources.get('s3_buckets', [])
        for bucket in s3_buckets:
            size_gb = bucket.get('size_gb', 0)
            storage_class = bucket.get('storage_class', 'STANDARD')

            # Check for lifecycle policies
            if not bucket.get('has_lifecycle_policy', False) and size_gb > 100:
                lifecycle_savings = size_gb * 0.015  # $0.015/GB savings with IA transition
                savings += lifecycle_savings
                self.recommendations.append({
                    'service': 'S3',
                    'type': 'Lifecycle Policy',
                    'issue': f'Bucket {bucket.get("name", "unknown")} ({size_gb} GB) has no lifecycle policy',
                    'recommendation': 'Implement lifecycle policy: Transition to IA after 30 days, Glacier after 90 days',
                    'potential_savings': lifecycle_savings,
                    'priority': 'medium'
                })

            # Check for Intelligent-Tiering
            if storage_class == 'STANDARD' and size_gb > 500:
                tiering_savings = size_gb * 0.005
                savings += tiering_savings
                self.recommendations.append({
                    'service': 'S3',
                    'type': 'Storage Class',
                    'issue': f'Large bucket ({size_gb} GB) using STANDARD storage',
                    'recommendation': 'Enable S3 Intelligent-Tiering for automatic cost optimization',
                    'potential_savings': tiering_savings,
                    'priority': 'high'
                })

        return savings

    def _analyze_database(self) -> float:
        """Analyze RDS, DynamoDB, and other database costs."""
        savings = 0.0

        rds_instances = self.resources.get('rds_instances', [])
        for db in rds_instances:
            # Check for idle databases
            if db.get('connections_per_day', 1000) < 10:
                db_cost = db.get('monthly_cost', 100)
                savings += db_cost * 0.8  # Can save 80% by stopping
                self.recommendations.append({
                    'service': 'RDS',
                    'type': 'Idle Resource',
                    'issue': f'Database {db.get("name", "unknown")} has <10 connections/day',
                    'recommendation': 'Stop database if not needed, or take final snapshot and delete',
                    'potential_savings': db_cost * 0.8,
                    'priority': 'high'
                })

            # Check for Aurora Serverless opportunity
            if db.get('engine', '').startswith('aurora') and db.get('utilization', 100) < 30:
                serverless_savings = db.get('monthly_cost', 200) * 0.40
                savings += serverless_savings
                self.recommendations.append({
                    'service': 'RDS Aurora',
                    'type': 'Serverless Migration',
                    'issue': f'Aurora instance {db.get("name", "unknown")} has low utilization (<30%)',
                    'recommendation': 'Migrate to Aurora Serverless v2 for auto-scaling and pay-per-use',
                    'potential_savings': serverless_savings,
                    'priority': 'medium'
                })

        # DynamoDB optimization
        dynamodb_tables = self.resources.get('dynamodb_tables', [])
        for table in dynamodb_tables:
            if table.get('billing_mode', 'PROVISIONED') == 'PROVISIONED':
                read_capacity = table.get('read_capacity_units', 0)
                write_capacity = table.get('write_capacity_units', 0)
                utilization = table.get('utilization_percentage', 100)

                if utilization < 20:
                    on_demand_savings = (read_capacity * 0.00013 + write_capacity * 0.00065) * 730 * 0.3
                    savings += on_demand_savings
                    self.recommendations.append({
                        'service': 'DynamoDB',
                        'type': 'Billing Mode',
                        'issue': f'Table {table.get("name", "unknown")} has low utilization with provisioned capacity',
                        'recommendation': 'Switch to On-Demand billing mode for variable workloads',
                        'potential_savings': on_demand_savings,
                        'priority': 'medium'
                    })

        return savings

    def _analyze_networking(self) -> float:
        """Analyze networking costs (data transfer, NAT Gateway, etc.)."""
        savings = 0.0

        nat_gateways = self.resources.get('nat_gateways', [])
        if len(nat_gateways) > 1:
            multi_az = self.resources.get('multi_az_required', False)
            if not multi_az:
                nat_savings = (len(nat_gateways) - 1) * 45  # $45/month per NAT Gateway
                savings += nat_savings
                self.recommendations.append({
                    'service': 'NAT Gateway',
                    'type': 'Resource Consolidation',
                    'issue': f'{len(nat_gateways)} NAT Gateways deployed (multi-AZ not required)',
                    'recommendation': 'Use single NAT Gateway in dev/staging, or consider VPC endpoints for AWS services',
                    'potential_savings': nat_savings,
                    'priority': 'high'
                })

        # Check for VPC endpoints opportunity
        if not self.resources.get('vpc_endpoints', []):
            s3_data_transfer = self.resources.get('s3_data_transfer_gb', 0)
            if s3_data_transfer > 100:
                endpoint_savings = s3_data_transfer * 0.09 * 0.5  # Save 50% of data transfer costs
                savings += endpoint_savings
                self.recommendations.append({
                    'service': 'VPC',
                    'type': 'VPC Endpoints',
                    'issue': 'High S3 data transfer without VPC endpoints',
                    'recommendation': 'Create VPC endpoints for S3 and DynamoDB to avoid NAT Gateway costs',
                    'potential_savings': endpoint_savings,
                    'priority': 'medium'
                })

        return savings

    def _analyze_general_optimizations(self) -> float:
        """General AWS cost optimizations."""
        savings = 0.0

        # Check for CloudWatch Logs retention
        log_groups = self.resources.get('cloudwatch_log_groups', [])
        for log in log_groups:
            if log.get('retention_days', 1) == -1:  # Never expire
                log_size_gb = log.get('size_gb', 1)
                retention_savings = log_size_gb * 0.50 * 0.7  # 70% savings with 7-day retention
                savings += retention_savings
                self.recommendations.append({
                    'service': 'CloudWatch Logs',
                    'type': 'Retention Policy',
                    'issue': f'Log group {log.get("name", "unknown")} has infinite retention',
                    'recommendation': 'Set retention to 7 days for non-compliance logs, 30 days for production',
                    'potential_savings': retention_savings,
                    'priority': 'low'
                })

        # Check for unused Elastic IPs
        elastic_ips = self.resources.get('elastic_ips', [])
        unattached = sum(1 for eip in elastic_ips if not eip.get('attached', True))
        if unattached > 0:
            eip_savings = unattached * 3.65  # $0.005/hour = $3.65/month
            savings += eip_savings
            self.recommendations.append({
                'service': 'EC2',
                'type': 'Unused Resources',
                'issue': f'{unattached} unattached Elastic IPs',
                'recommendation': 'Release unused Elastic IPs to avoid hourly charges',
                'potential_savings': eip_savings,
                'priority': 'high'
            })

        # Budget alerts
        if not self.resources.get('has_budget_alerts', False):
            self.recommendations.append({
                'service': 'AWS Budgets',
                'type': 'Cost Monitoring',
                'issue': 'No budget alerts configured',
                'recommendation': 'Set up AWS Budgets with alerts at 50%, 80%, 100% of monthly budget',
                'potential_savings': 0,
                'priority': 'high'
            })

        # Cost Explorer recommendations
        if not self.resources.get('has_cost_explorer', False):
            self.recommendations.append({
                'service': 'Cost Management',
                'type': 'Visibility',
                'issue': 'Cost Explorer not enabled',
                'recommendation': 'Enable AWS Cost Explorer to track spending patterns and identify anomalies',
                'potential_savings': 0,
                'priority': 'medium'
            })

        return savings

    def _prioritize_recommendations(self) -> List[Dict[str, Any]]:
        """Get top priority recommendations."""
        high_priority = [r for r in self.recommendations if r['priority'] == 'high']
        high_priority.sort(key=lambda x: x.get('potential_savings', 0), reverse=True)
        return high_priority[:5]  # Top 5 high-priority recommendations

    def generate_optimization_checklist(self) -> List[Dict[str, Any]]:
        """Generate actionable checklist for cost optimization."""
        return [
            {
                'category': 'Immediate Actions (Today)',
                'items': [
                    'Release unattached Elastic IPs',
                    'Stop idle EC2 instances',
                    'Delete unused EBS volumes',
                    'Set up budget alerts'
                ]
            },
            {
                'category': 'This Week',
                'items': [
                    'Implement S3 lifecycle policies',
                    'Consolidate NAT Gateways in non-prod',
                    'Set CloudWatch Logs retention to 7 days',
                    'Review and rightsize EC2/RDS instances'
                ]
            },
            {
                'category': 'This Month',
                'items': [
                    'Evaluate Savings Plans or Reserved Instances',
                    'Migrate to Aurora Serverless where applicable',
                    'Implement VPC endpoints for S3/DynamoDB',
                    'Switch DynamoDB tables to On-Demand if variable load'
                ]
            },
            {
                'category': 'Ongoing',
                'items': [
                    'Review Cost Explorer weekly',
                    'Tag all resources for cost allocation',
                    'Monitor Trusted Advisor recommendations',
                    'Conduct monthly cost review meetings'
                ]
            }
        ]
