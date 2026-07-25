#!/usr/bin/env python3
"""
SLO Designer - Generate comprehensive SLI/SLO frameworks for services

This script analyzes service descriptions and generates complete SLO frameworks including:
- SLI definitions based on service characteristics
- SLO targets based on criticality and user impact
- Error budget calculations and policies
- Multi-window burn rate alerts
- SLA recommendations for customer-facing services

Usage:
    python slo_designer.py --input service_definition.json --output slo_framework.json
    python slo_designer.py --service-type api --criticality high --user-facing true
"""

import json
import argparse
import sys
import math
from typing import Dict, List, Any, Tuple
from datetime import datetime, timedelta


class SLODesigner:
    """Design and generate SLO frameworks for services."""
    
    # SLO target recommendations based on service criticality
    SLO_TARGETS = {
        'critical': {
            'availability': 0.9999,  # 99.99% - 4.38 minutes downtime/month
            'latency_p95': 100,      # 95th percentile latency in ms
            'latency_p99': 500,      # 99th percentile latency in ms
            'error_rate': 0.001      # 0.1% error rate
        },
        'high': {
            'availability': 0.999,   # 99.9% - 43.8 minutes downtime/month
            'latency_p95': 200,      # 95th percentile latency in ms
            'latency_p99': 1000,     # 99th percentile latency in ms
            'error_rate': 0.005      # 0.5% error rate
        },
        'medium': {
            'availability': 0.995,   # 99.5% - 3.65 hours downtime/month
            'latency_p95': 500,      # 95th percentile latency in ms
            'latency_p99': 2000,     # 99th percentile latency in ms
            'error_rate': 0.01       # 1% error rate
        },
        'low': {
            'availability': 0.99,    # 99% - 7.3 hours downtime/month
            'latency_p95': 1000,     # 95th percentile latency in ms
            'latency_p99': 5000,     # 99th percentile latency in ms
            'error_rate': 0.02       # 2% error rate
        }
    }
    
    # Burn rate windows for multi-window alerting
    BURN_RATE_WINDOWS = [
        {'short': '5m', 'long': '1h', 'burn_rate': 14.4, 'budget_consumed': '2%'},
        {'short': '30m', 'long': '6h', 'burn_rate': 6, 'budget_consumed': '5%'},
        {'short': '2h', 'long': '1d', 'burn_rate': 3, 'budget_consumed': '10%'},
        {'short': '6h', 'long': '3d', 'burn_rate': 1, 'budget_consumed': '10%'}
    ]
    
    # Service type specific SLI recommendations
    SERVICE_TYPE_SLIS = {
        'api': ['availability', 'latency', 'error_rate', 'throughput'],
        'web': ['availability', 'latency', 'error_rate', 'page_load_time'],
        'database': ['availability', 'query_latency', 'connection_success_rate', 'replication_lag'],
        'queue': ['availability', 'message_processing_time', 'queue_depth', 'message_loss_rate'],
        'batch': ['job_success_rate', 'job_duration', 'data_freshness', 'resource_utilization'],
        'ml': ['model_accuracy', 'prediction_latency', 'training_success_rate', 'feature_freshness']
    }

    def __init__(self):
        """Initialize the SLO Designer."""
        self.service_config = {}
        self.slo_framework = {}

    def load_service_definition(self, file_path: str) -> Dict[str, Any]:
        """Load service definition from JSON file."""
        try:
            with open(file_path, 'r') as f:
                return json.load(f)
        except FileNotFoundError:
            raise ValueError(f"Service definition file not found: {file_path}")
        except json.JSONDecodeError as e:
            raise ValueError(f"Invalid JSON in service definition: {e}")

    def create_service_definition(self, service_type: str, criticality: str, 
                                user_facing: bool, name: str = None) -> Dict[str, Any]:
        """Create a service definition from parameters."""
        return {
            'name': name or f'{service_type}_service',
            'type': service_type,
            'criticality': criticality,
            'user_facing': user_facing,
            'description': f'A {criticality} criticality {service_type} service',
            'dependencies': [],
            'team': 'platform',
            'environment': 'production'
        }

    def generate_slis(self, service_def: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Generate Service Level Indicators based on service characteristics."""
        service_type = service_def.get('type', 'api')
        base_slis = self.SERVICE_TYPE_SLIS.get(service_type, ['availability', 'latency', 'error_rate'])
        
        slis = []
        
        for sli_name in base_slis:
            sli = self._create_sli_definition(sli_name, service_def)
            if sli:
                slis.append(sli)
        
        # Add user-facing specific SLIs
        if service_def.get('user_facing', False):
            user_slis = self._generate_user_facing_slis(service_def)
            slis.extend(user_slis)
            
        return slis

    def _create_sli_definition(self, sli_name: str, service_def: Dict[str, Any]) -> Dict[str, Any]:
        """Create detailed SLI definition."""
        service_name = service_def.get('name', 'service')
        
        sli_definitions = {
            'availability': {
                'name': 'Availability',
                'description': 'Percentage of successful requests',
                'type': 'ratio',
                'good_events': f'sum(rate(http_requests_total{{service="{service_name}",code!~"5.."}}))',
                'total_events': f'sum(rate(http_requests_total{{service="{service_name}"}}))',
                'unit': 'percentage'
            },
            'latency': {
                'name': 'Request Latency P95',
                'description': '95th percentile of request latency',
                'type': 'threshold',
                'query': f'histogram_quantile(0.95, rate(http_request_duration_seconds_bucket{{service="{service_name}"}}[5m]))',
                'unit': 'seconds'
            },
            'error_rate': {
                'name': 'Error Rate',
                'description': 'Rate of 5xx errors',
                'type': 'ratio',
                'good_events': f'sum(rate(http_requests_total{{service="{service_name}",code!~"5.."}}))',
                'total_events': f'sum(rate(http_requests_total{{service="{service_name}"}}))',
                'unit': 'percentage'
            },
            'throughput': {
                'name': 'Request Throughput',
                'description': 'Requests per second',
                'type': 'gauge',
                'query': f'sum(rate(http_requests_total{{service="{service_name}"}}[5m]))',
                'unit': 'requests/sec'
            },
            'page_load_time': {
                'name': 'Page Load Time P95',
                'description': '95th percentile of page load time',
                'type': 'threshold',
                'query': f'histogram_quantile(0.95, rate(page_load_duration_seconds_bucket{{service="{service_name}"}}[5m]))',
                'unit': 'seconds'
            },
            'query_latency': {
                'name': 'Database Query Latency P95',
                'description': '95th percentile of database query latency',
                'type': 'threshold',
                'query': f'histogram_quantile(0.95, rate(db_query_duration_seconds_bucket{{service="{service_name}"}}[5m]))',
                'unit': 'seconds'
            },
            'connection_success_rate': {
                'name': 'Database Connection Success Rate',
                'description': 'Percentage of successful database connections',
                'type': 'ratio',
                'good_events': f'sum(rate(db_connections_total{{service="{service_name}",status="success"}}[5m]))',
                'total_events': f'sum(rate(db_connections_total{{service="{service_name}"}}[5m]))',
                'unit': 'percentage'
            }
        }
        
        return sli_definitions.get(sli_name)

    def _generate_user_facing_slis(self, service_def: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Generate additional SLIs for user-facing services."""
        service_name = service_def.get('name', 'service')
        
        return [
            {
                'name': 'User Journey Success Rate',
                'description': 'Percentage of successful complete user journeys',
                'type': 'ratio',
                'good_events': f'sum(rate(user_journey_total{{service="{service_name}",status="success"}}[5m]))',
                'total_events': f'sum(rate(user_journey_total{{service="{service_name}"}}[5m]))',
                'unit': 'percentage'
            },
            {
                'name': 'Feature Availability',
                'description': 'Percentage of time key features are available',
                'type': 'ratio',
                'good_events': f'sum(rate(feature_checks_total{{service="{service_name}",status="available"}}[5m]))',
                'total_events': f'sum(rate(feature_checks_total{{service="{service_name}"}}[5m]))',
                'unit': 'percentage'
            }
        ]

    def generate_slos(self, service_def: Dict[str, Any], slis: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """Generate Service Level Objectives based on service criticality."""
        criticality = service_def.get('criticality', 'medium')
        targets = self.SLO_TARGETS.get(criticality, self.SLO_TARGETS['medium'])
        
        slos = []
        
        for sli in slis:
            slo = self._create_slo_from_sli(sli, targets, service_def)
            if slo:
                slos.append(slo)
                
        return slos

    def _create_slo_from_sli(self, sli: Dict[str, Any], targets: Dict[str, float], 
                           service_def: Dict[str, Any]) -> Dict[str, Any]:
        """Create SLO definition from SLI."""
        sli_name = sli['name'].lower().replace(' ', '_')
        
        # Map SLI names to target keys
        target_mapping = {
            'availability': 'availability',
            'request_latency_p95': 'latency_p95',
            'error_rate': 'error_rate',
            'user_journey_success_rate': 'availability',
            'feature_availability': 'availability',
            'page_load_time_p95': 'latency_p95',
            'database_query_latency_p95': 'latency_p95',
            'database_connection_success_rate': 'availability'
        }
        
        target_key = target_mapping.get(sli_name)
        if not target_key:
            return None
            
        target_value = targets.get(target_key)
        if target_value is None:
            return None
            
        # Determine comparison operator and format target
        if 'latency' in sli_name or 'duration' in sli_name:
            operator = '<='
            target_display = f"{target_value}ms" if target_value < 10 else f"{target_value/1000}s"
        elif 'rate' in sli_name and 'error' in sli_name:
            operator = '<='
            target_display = f"{target_value * 100}%"
            target_value = target_value  # Keep as decimal
        else:
            operator = '>='
            target_display = f"{target_value * 100}%"
        
        # Calculate time windows
        time_windows = ['1h', '1d', '7d', '30d']
        
        slo = {
            'name': f"{sli['name']} SLO",
            'description': f"Service level objective for {sli['description'].lower()}",
            'sli_name': sli['name'],
            'target_value': target_value,
            'target_display': target_display,
            'operator': operator,
            'time_windows': time_windows,
            'measurement_window': '30d',
            'service': service_def.get('name', 'service'),
            'criticality': service_def.get('criticality', 'medium')
        }
        
        return slo

    def calculate_error_budgets(self, slos: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """Calculate error budgets for SLOs."""
        error_budgets = []
        
        for slo in slos:
            if slo['operator'] == '>=':  # Availability-type SLOs
                target = slo['target_value']
                error_budget_rate = 1 - target
                
                # Calculate budget for different time windows
                time_windows = {
                    '1h': 3600,
                    '1d': 86400,
                    '7d': 604800,
                    '30d': 2592000
                }
                
                budgets = {}
                for window, seconds in time_windows.items():
                    budget_seconds = seconds * error_budget_rate
                    if budget_seconds < 60:
                        budgets[window] = f"{budget_seconds:.1f} seconds"
                    elif budget_seconds < 3600:
                        budgets[window] = f"{budget_seconds/60:.1f} minutes"
                    else:
                        budgets[window] = f"{budget_seconds/3600:.1f} hours"
                
                error_budget = {
                    'slo_name': slo['name'],
                    'error_budget_rate': error_budget_rate,
                    'error_budget_percentage': f"{error_budget_rate * 100:.3f}%",
                    'budgets_by_window': budgets,
                    'burn_rate_alerts': self._generate_burn_rate_alerts(slo, error_budget_rate)
                }
                
                error_budgets.append(error_budget)
                
        return error_budgets

    def _generate_burn_rate_alerts(self, slo: Dict[str, Any], error_budget_rate: float) -> List[Dict[str, Any]]:
        """Generate multi-window burn rate alerts."""
        alerts = []
        service_name = slo['service']
        sli_query = self._get_sli_query_for_burn_rate(slo)
        
        for window_config in self.BURN_RATE_WINDOWS:
            alert = {
                'name': f"{slo['sli_name']} Burn Rate {window_config['budget_consumed']} Alert",
                'description': f"Alert when {slo['sli_name']} is consuming error budget at {window_config['burn_rate']}x rate",
                'severity': self._determine_alert_severity(float(window_config['budget_consumed'].rstrip('%'))),
                'short_window': window_config['short'],
                'long_window': window_config['long'],
                'burn_rate_threshold': window_config['burn_rate'],
                'budget_consumed': window_config['budget_consumed'],
                'condition': f"({sli_query}_short > {window_config['burn_rate']}) and ({sli_query}_long > {window_config['burn_rate']})",
                'annotations': {
                    'summary': f"High burn rate detected for {slo['sli_name']}",
                    'description': f"Error budget consumption rate is {window_config['burn_rate']}x normal, will exhaust {window_config['budget_consumed']} of monthly budget"
                }
            }
            alerts.append(alert)
            
        return alerts

    def _get_sli_query_for_burn_rate(self, slo: Dict[str, Any]) -> str:
        """Generate SLI query fragment for burn rate calculation."""
        service_name = slo['service']
        sli_name = slo['sli_name'].lower().replace(' ', '_')
        
        if 'availability' in sli_name or 'success' in sli_name:
            return f"(1 - (sum(rate(http_requests_total{{service='{service_name}',code!~'5..'}})) / sum(rate(http_requests_total{{service='{service_name}'}}))))"
        elif 'error' in sli_name:
            return f"(sum(rate(http_requests_total{{service='{service_name}',code=~'5..'}})) / sum(rate(http_requests_total{{service='{service_name}'}})))"
        else:
            return f"sli_burn_rate_{sli_name}"

    def _determine_alert_severity(self, budget_consumed_percent: float) -> str:
        """Determine alert severity based on budget consumption rate."""
        if budget_consumed_percent <= 2:
            return 'critical'
        elif budget_consumed_percent <= 5:
            return 'warning'
        else:
            return 'info'

    def generate_sla_recommendations(self, service_def: Dict[str, Any], 
                                   slos: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Generate SLA recommendations for customer-facing services."""
        if not service_def.get('user_facing', False):
            return {
                'applicable': False,
                'reason': 'SLA not recommended for non-user-facing services'
            }
        
        criticality = service_def.get('criticality', 'medium')
        
        # SLA targets should be more conservative than SLO targets
        sla_buffer = 0.001  # 0.1% buffer below SLO
        
        sla_recommendations = {
            'applicable': True,
            'service': service_def.get('name'),
            'commitments': [],
            'penalties': self._generate_penalty_structure(criticality),
            'measurement_methodology': 'External synthetic monitoring from multiple geographic locations',
            'exclusions': [
                'Planned maintenance windows (with 72h advance notice)',
                'Customer-side network or infrastructure issues',
                'Force majeure events',
                'Third-party service dependencies beyond our control'
            ]
        }
        
        for slo in slos:
            if slo['operator'] == '>=' and 'availability' in slo['sli_name'].lower():
                sla_target = max(0.9, slo['target_value'] - sla_buffer)
                commitment = {
                    'metric': slo['sli_name'],
                    'target': sla_target,
                    'target_display': f"{sla_target * 100:.2f}%",
                    'measurement_window': 'monthly',
                    'measurement_method': 'Uptime monitoring with 1-minute granularity'
                }
                sla_recommendations['commitments'].append(commitment)
        
        return sla_recommendations

    def _generate_penalty_structure(self, criticality: str) -> List[Dict[str, Any]]:
        """Generate penalty structure based on service criticality."""
        penalty_structures = {
            'critical': [
                {'breach_threshold': '< 99.99%', 'credit_percentage': 10},
                {'breach_threshold': '< 99.9%', 'credit_percentage': 25},
                {'breach_threshold': '< 99%', 'credit_percentage': 50}
            ],
            'high': [
                {'breach_threshold': '< 99.9%', 'credit_percentage': 10},
                {'breach_threshold': '< 99.5%', 'credit_percentage': 25}
            ],
            'medium': [
                {'breach_threshold': '< 99.5%', 'credit_percentage': 10}
            ],
            'low': []
        }
        
        return penalty_structures.get(criticality, [])

    def generate_framework(self, service_def: Dict[str, Any]) -> Dict[str, Any]:
        """Generate complete SLO framework."""
        # Generate SLIs
        slis = self.generate_slis(service_def)
        
        # Generate SLOs
        slos = self.generate_slos(service_def, slis)
        
        # Calculate error budgets
        error_budgets = self.calculate_error_budgets(slos)
        
        # Generate SLA recommendations
        sla_recommendations = self.generate_sla_recommendations(service_def, slos)
        
        # Create comprehensive framework
        framework = {
            'metadata': {
                'service': service_def,
                'generated_at': datetime.utcnow().isoformat() + 'Z',
                'framework_version': '1.0'
            },
            'slis': slis,
            'slos': slos,
            'error_budgets': error_budgets,
            'sla_recommendations': sla_recommendations,
            'monitoring_recommendations': self._generate_monitoring_recommendations(service_def),
            'implementation_guide': self._generate_implementation_guide(service_def, slis, slos)
        }
        
        return framework

    def _generate_monitoring_recommendations(self, service_def: Dict[str, Any]) -> Dict[str, Any]:
        """Generate monitoring tool recommendations."""
        service_type = service_def.get('type', 'api')
        
        recommendations = {
            'metrics': {
                'collection': 'Prometheus with service discovery',
                'retention': '90 days for raw metrics, 1 year for aggregated',
                'alerting': 'Prometheus Alertmanager with multi-window burn rate alerts'
            },
            'logging': {
                'format': 'Structured JSON logs with correlation IDs',
                'aggregation': 'ELK stack or equivalent with proper indexing',
                'retention': '30 days for debug logs, 90 days for error logs'
            },
            'tracing': {
                'sampling': 'Adaptive sampling with 1% base rate',
                'storage': 'Jaeger or Zipkin with 7-day retention',
                'integration': 'OpenTelemetry instrumentation'
            }
        }
        
        if service_type == 'web':
            recommendations['synthetic_monitoring'] = {
                'frequency': 'Every 1 minute from 3+ geographic locations',
                'checks': 'Full user journey simulation',
                'tools': 'Pingdom, DataDog Synthetics, or equivalent'
            }
        
        return recommendations

    def _generate_implementation_guide(self, service_def: Dict[str, Any], 
                                     slis: List[Dict[str, Any]], 
                                     slos: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Generate implementation guide for the SLO framework."""
        return {
            'prerequisites': [
                'Service instrumented with metrics collection (Prometheus format)',
                'Structured logging with correlation IDs',
                'Monitoring infrastructure (Prometheus, Grafana, Alertmanager)',
                'Incident response processes and escalation policies'
            ],
            'implementation_steps': [
                {
                    'step': 1,
                    'title': 'Instrument Service',
                    'description': 'Add metrics collection for all defined SLIs',
                    'estimated_effort': '1-2 days'
                },
                {
                    'step': 2,
                    'title': 'Configure Recording Rules',
                    'description': 'Set up Prometheus recording rules for SLI calculations',
                    'estimated_effort': '4-8 hours'
                },
                {
                    'step': 3,
                    'title': 'Implement Burn Rate Alerts',
                    'description': 'Configure multi-window burn rate alerting rules',
                    'estimated_effort': '1 day'
                },
                {
                    'step': 4,
                    'title': 'Create SLO Dashboard',
                    'description': 'Build Grafana dashboard for SLO tracking and error budget monitoring',
                    'estimated_effort': '4-6 hours'
                },
                {
                    'step': 5,
                    'title': 'Test and Validate',
                    'description': 'Test alerting and validate SLI measurements against expectations',
                    'estimated_effort': '1-2 days'
                },
                {
                    'step': 6,
                    'title': 'Documentation and Training',
                    'description': 'Document runbooks and train team on SLO monitoring',
                    'estimated_effort': '1 day'
                }
            ],
            'validation_checklist': [
                'All SLIs produce expected metric values',
                'Burn rate alerts fire correctly during simulated outages',
                'Error budget calculations match manual verification',
                'Dashboard displays accurate SLO achievement rates',
                'Alert routing reaches correct escalation paths',
                'Runbooks are complete and tested'
            ]
        }

    def export_json(self, framework: Dict[str, Any], output_file: str):
        """Export framework as JSON."""
        with open(output_file, 'w') as f:
            json.dump(framework, f, indent=2)

    def print_summary(self, framework: Dict[str, Any]):
        """Print human-readable summary of the SLO framework."""
        service = framework['metadata']['service']
        slis = framework['slis']
        slos = framework['slos']
        error_budgets = framework['error_budgets']
        
        print(f"\n{'='*60}")
        print(f"SLO FRAMEWORK SUMMARY FOR {service['name'].upper()}")
        print(f"{'='*60}")
        
        print(f"\nService Details:")
        print(f"  Type: {service['type']}")
        print(f"  Criticality: {service['criticality']}")
        print(f"  User Facing: {'Yes' if service.get('user_facing') else 'No'}")
        print(f"  Team: {service.get('team', 'Unknown')}")
        
        print(f"\nService Level Indicators ({len(slis)}):")
        for i, sli in enumerate(slis, 1):
            print(f"  {i}. {sli['name']}")
            print(f"     Description: {sli['description']}")
            print(f"     Type: {sli['type']}")
            print()
        
        print(f"Service Level Objectives ({len(slos)}):")
        for i, slo in enumerate(slos, 1):
            print(f"  {i}. {slo['name']}")
            print(f"     Target: {slo['target_display']}")
            print(f"     Measurement Window: {slo['measurement_window']}")
            print()
        
        print(f"Error Budget Summary:")
        for budget in error_budgets:
            print(f"  {budget['slo_name']}:")
            print(f"    Monthly Budget: {budget['error_budget_percentage']}")
            print(f"    Burn Rate Alerts: {len(budget['burn_rate_alerts'])}")
            print()
        
        sla = framework['sla_recommendations']
        if sla['applicable']:
            print(f"SLA Recommendations:")
            print(f"  Commitments: {len(sla['commitments'])}")
            print(f"  Penalty Tiers: {len(sla['penalties'])}")
        else:
            print(f"SLA Recommendations: {sla['reason']}")
        
        print(f"\nImplementation Timeline: 1-2 weeks")
        print(f"Framework generated at: {framework['metadata']['generated_at']}")
        print(f"{'='*60}\n")


def main():
    """Main function for CLI usage."""
    parser = argparse.ArgumentParser(
        description='Generate comprehensive SLO frameworks for services',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    # Generate from service definition file
    python slo_designer.py --input service.json --output framework.json
    
    # Generate from command line parameters
    python slo_designer.py --service-type api --criticality high --user-facing true --output framework.json
    
    # Generate and display summary only
    python slo_designer.py --service-type web --criticality critical --user-facing true --summary-only
        """
    )
    
    parser.add_argument('--input', '-i', 
                       help='Input service definition JSON file')
    parser.add_argument('--output', '-o', 
                       help='Output framework JSON file')
    parser.add_argument('--service-type', 
                       choices=['api', 'web', 'database', 'queue', 'batch', 'ml'],
                       help='Service type')
    parser.add_argument('--criticality',
                       choices=['critical', 'high', 'medium', 'low'],
                       help='Service criticality level')
    parser.add_argument('--user-facing',
                       choices=['true', 'false'],
                       help='Whether service is user-facing')
    parser.add_argument('--service-name',
                       help='Service name')
    parser.add_argument('--summary-only', action='store_true',
                       help='Only display summary, do not save JSON')
    
    args = parser.parse_args()
    
    if not args.input and not (args.service_type and args.criticality and args.user_facing):
        parser.error("Must provide either --input file or --service-type, --criticality, and --user-facing")
    
    designer = SLODesigner()
    
    try:
        # Load or create service definition
        if args.input:
            service_def = designer.load_service_definition(args.input)
        else:
            user_facing = args.user_facing.lower() == 'true'
            service_def = designer.create_service_definition(
                args.service_type, args.criticality, user_facing, args.service_name
            )
        
        # Generate framework
        framework = designer.generate_framework(service_def)
        
        # Output results
        if not args.summary_only:
            output_file = args.output or f"{service_def['name']}_slo_framework.json"
            designer.export_json(framework, output_file)
            print(f"SLO framework saved to: {output_file}")
        
        # Always show summary
        designer.print_summary(framework)
        
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()