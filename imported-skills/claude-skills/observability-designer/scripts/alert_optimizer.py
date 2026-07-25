#!/usr/bin/env python3
"""
Alert Optimizer - Analyze and optimize alert configurations

This script analyzes existing alert configurations and identifies optimization opportunities:
- Noisy alerts with high false positive rates
- Missing coverage gaps in monitoring
- Duplicate or redundant alerts
- Poor threshold settings and alert fatigue risks
- Missing runbooks and documentation
- Routing and escalation policy improvements

Usage:
    python alert_optimizer.py --input alert_config.json --output optimized_config.json
    python alert_optimizer.py --input alerts.json --analyze-only --report report.html
"""

import json
import argparse
import sys
import re
import math
from typing import Dict, List, Any, Tuple, Set
from datetime import datetime, timedelta
from collections import defaultdict, Counter


class AlertOptimizer:
    """Analyze and optimize alert configurations."""
    
    # Alert severity priority mapping
    SEVERITY_PRIORITY = {
        'critical': 1,
        'high': 2,
        'warning': 3,
        'info': 4
    }
    
    # Common noisy alert patterns
    NOISY_PATTERNS = [
        r'disk.*usage.*>.*[89]\d%',  # Disk usage > 80% often noisy
        r'memory.*>.*[89]\d%',       # Memory > 80% often noisy
        r'cpu.*>.*[789]\d%',         # CPU > 70% can be noisy
        r'response.*time.*>.*\d+ms', # Low latency thresholds
        r'error.*rate.*>.*0\.[01]%'  # Very low error rate thresholds
    ]
    
    # Essential monitoring categories
    COVERAGE_CATEGORIES = [
        'availability',
        'latency', 
        'error_rate',
        'resource_utilization',
        'security',
        'business_metrics'
    ]
    
    # Golden signals that should always be monitored
    GOLDEN_SIGNALS = [
        'latency',
        'traffic',
        'errors', 
        'saturation'
    ]

    def __init__(self):
        """Initialize the Alert Optimizer."""
        self.alert_config = {}
        self.optimization_results = {}
        self.alert_analysis = {}

    def load_alert_config(self, file_path: str) -> Dict[str, Any]:
        """Load alert configuration from JSON file."""
        try:
            with open(file_path, 'r') as f:
                return json.load(f)
        except FileNotFoundError:
            raise ValueError(f"Alert configuration file not found: {file_path}")
        except json.JSONDecodeError as e:
            raise ValueError(f"Invalid JSON in alert configuration: {e}")

    def analyze_alert_noise(self, alerts: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """Identify potentially noisy alerts."""
        noisy_alerts = []
        
        for alert in alerts:
            noise_score = 0
            noise_reasons = []
            
            alert_rule = alert.get('expr', alert.get('condition', ''))
            alert_name = alert.get('alert', alert.get('name', 'Unknown'))
            
            # Check for common noisy patterns
            for pattern in self.NOISY_PATTERNS:
                if re.search(pattern, alert_rule, re.IGNORECASE):
                    noise_score += 3
                    noise_reasons.append(f"Matches noisy pattern: {pattern}")
            
            # Check for very frequent evaluation intervals
            evaluation_interval = alert.get('for', '0s')
            if self._parse_duration(evaluation_interval) < 60:  # Less than 1 minute
                noise_score += 2
                noise_reasons.append("Very short evaluation interval")
            
            # Check for lack of 'for' clause
            if not alert.get('for') or alert.get('for') == '0s':
                noise_score += 2
                noise_reasons.append("No 'for' clause - may cause alert flapping")
            
            # Check for overly sensitive thresholds
            if self._has_sensitive_threshold(alert_rule):
                noise_score += 2
                noise_reasons.append("Potentially sensitive threshold")
            
            # Check historical firing rate if available
            historical_data = alert.get('historical_data', {})
            if historical_data:
                firing_rate = historical_data.get('fires_per_day', 0)
                if firing_rate > 10:  # More than 10 fires per day
                    noise_score += 3
                    noise_reasons.append(f"High firing rate: {firing_rate} times/day")
                
                false_positive_rate = historical_data.get('false_positive_rate', 0)
                if false_positive_rate > 0.3:  # > 30% false positives
                    noise_score += 4
                    noise_reasons.append(f"High false positive rate: {false_positive_rate*100:.1f}%")
            
            if noise_score >= 3:  # Threshold for considering an alert noisy
                noisy_alert = {
                    'alert_name': alert_name,
                    'noise_score': noise_score,
                    'reasons': noise_reasons,
                    'current_rule': alert_rule,
                    'recommendations': self._generate_noise_reduction_recommendations(alert, noise_reasons)
                }
                noisy_alerts.append(noisy_alert)
        
        return sorted(noisy_alerts, key=lambda x: x['noise_score'], reverse=True)

    def _parse_duration(self, duration_str: str) -> int:
        """Parse duration string to seconds."""
        if not duration_str or duration_str == '0s':
            return 0
        
        duration_map = {'s': 1, 'm': 60, 'h': 3600, 'd': 86400}
        match = re.match(r'(\d+)([smhd])', duration_str)
        if match:
            value, unit = match.groups()
            return int(value) * duration_map.get(unit, 1)
        return 0

    def _has_sensitive_threshold(self, rule: str) -> bool:
        """Check if alert rule has potentially sensitive thresholds."""
        # Look for very low error rates or very tight latency thresholds
        sensitive_patterns = [
            r'error.*rate.*>.*0\.0[01]',     # Error rate > 0.01% or 0.001%
            r'latency.*>.*[12]\d\d?ms',      # Latency > 100-299ms
            r'response.*time.*>.*0\.[12]',   # Response time > 0.1-0.2s
            r'cpu.*>.*[456]\d%'              # CPU > 40-69% (too sensitive for most cases)
        ]
        
        for pattern in sensitive_patterns:
            if re.search(pattern, rule, re.IGNORECASE):
                return True
        return False

    def _generate_noise_reduction_recommendations(self, alert: Dict[str, Any], 
                                                 reasons: List[str]) -> List[str]:
        """Generate recommendations to reduce alert noise."""
        recommendations = []
        
        if "No 'for' clause" in str(reasons):
            recommendations.append("Add 'for: 5m' clause to prevent flapping")
        
        if "Very short evaluation interval" in str(reasons):
            recommendations.append("Increase evaluation interval to at least 1 minute")
        
        if "sensitive threshold" in str(reasons):
            recommendations.append("Review and increase threshold based on historical data")
        
        if "High firing rate" in str(reasons):
            recommendations.append("Analyze historical firing patterns and adjust thresholds")
        
        if "High false positive rate" in str(reasons):
            recommendations.append("Implement more specific conditions to reduce false positives")
        
        if "noisy pattern" in str(reasons):
            recommendations.append("Consider using percentile-based thresholds instead of absolute values")
        
        return recommendations

    def identify_coverage_gaps(self, alerts: List[Dict[str, Any]], 
                             services: List[Dict[str, Any]] = None) -> Dict[str, Any]:
        """Identify gaps in monitoring coverage."""
        coverage_analysis = {
            'missing_categories': [],
            'missing_golden_signals': [],
            'service_coverage_gaps': [],
            'critical_gaps': [],
            'recommendations': []
        }
        
        # Analyze coverage by category
        covered_categories = set()
        alert_categories = []
        
        for alert in alerts:
            alert_rule = alert.get('expr', alert.get('condition', ''))
            alert_name = alert.get('alert', alert.get('name', ''))
            
            category = self._classify_alert_category(alert_rule, alert_name)
            if category:
                covered_categories.add(category)
                alert_categories.append(category)
        
        # Check for missing essential categories
        missing_categories = set(self.COVERAGE_CATEGORIES) - covered_categories
        coverage_analysis['missing_categories'] = list(missing_categories)
        
        # Check for missing golden signals
        covered_signals = set()
        for alert in alerts:
            alert_rule = alert.get('expr', alert.get('condition', ''))
            signal = self._identify_golden_signal(alert_rule)
            if signal:
                covered_signals.add(signal)
        
        missing_signals = set(self.GOLDEN_SIGNALS) - covered_signals
        coverage_analysis['missing_golden_signals'] = list(missing_signals)
        
        # Analyze service-specific coverage if service list provided
        if services:
            service_coverage = self._analyze_service_coverage(alerts, services)
            coverage_analysis['service_coverage_gaps'] = service_coverage
        
        # Identify critical gaps
        critical_gaps = []
        if 'availability' in missing_categories:
            critical_gaps.append("Missing availability monitoring")
        if 'error_rate' in missing_categories:
            critical_gaps.append("Missing error rate monitoring")
        if 'errors' in missing_signals:
            critical_gaps.append("Missing error signal monitoring")
        
        coverage_analysis['critical_gaps'] = critical_gaps
        
        # Generate recommendations
        recommendations = self._generate_coverage_recommendations(coverage_analysis)
        coverage_analysis['recommendations'] = recommendations
        
        return coverage_analysis

    def _classify_alert_category(self, rule: str, alert_name: str) -> str:
        """Classify alert into monitoring category."""
        rule_lower = rule.lower()
        name_lower = alert_name.lower()
        
        if any(keyword in rule_lower or keyword in name_lower 
               for keyword in ['up', 'down', 'available', 'reachable']):
            return 'availability'
        
        if any(keyword in rule_lower or keyword in name_lower 
               for keyword in ['latency', 'response_time', 'duration']):
            return 'latency'
        
        if any(keyword in rule_lower or keyword in name_lower 
               for keyword in ['error', 'fail', '5xx', '4xx']):
            return 'error_rate'
        
        if any(keyword in rule_lower or keyword in name_lower 
               for keyword in ['cpu', 'memory', 'disk', 'network', 'utilization']):
            return 'resource_utilization'
        
        if any(keyword in rule_lower or keyword in name_lower 
               for keyword in ['security', 'auth', 'login', 'breach']):
            return 'security'
        
        if any(keyword in rule_lower or keyword in name_lower 
               for keyword in ['revenue', 'conversion', 'user', 'business']):
            return 'business_metrics'
        
        return 'other'

    def _identify_golden_signal(self, rule: str) -> str:
        """Identify which golden signal an alert covers."""
        rule_lower = rule.lower()
        
        if any(keyword in rule_lower for keyword in ['latency', 'response_time', 'duration']):
            return 'latency'
        
        if any(keyword in rule_lower for keyword in ['rate', 'rps', 'qps', 'throughput']):
            return 'traffic'
        
        if any(keyword in rule_lower for keyword in ['error', 'fail', '5xx']):
            return 'errors'
        
        if any(keyword in rule_lower for keyword in ['cpu', 'memory', 'disk', 'utilization']):
            return 'saturation'
        
        return None

    def _analyze_service_coverage(self, alerts: List[Dict[str, Any]], 
                                services: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """Analyze monitoring coverage per service."""
        service_coverage = []
        
        for service in services:
            service_name = service.get('name', '')
            service_alerts = [alert for alert in alerts 
                            if service_name in alert.get('expr', '') or 
                               service_name in alert.get('labels', {}).get('service', '')]
            
            covered_signals = set()
            for alert in service_alerts:
                signal = self._identify_golden_signal(alert.get('expr', ''))
                if signal:
                    covered_signals.add(signal)
            
            missing_signals = set(self.GOLDEN_SIGNALS) - covered_signals
            
            if missing_signals or len(service_alerts) < 3:  # Less than 3 alerts per service
                coverage_gap = {
                    'service': service_name,
                    'alert_count': len(service_alerts),
                    'covered_signals': list(covered_signals),
                    'missing_signals': list(missing_signals),
                    'criticality': service.get('criticality', 'medium'),
                    'recommendations': []
                }
                
                if len(service_alerts) == 0:
                    coverage_gap['recommendations'].append("Add basic availability monitoring")
                if 'errors' in missing_signals:
                    coverage_gap['recommendations'].append("Add error rate monitoring")
                if 'latency' in missing_signals:
                    coverage_gap['recommendations'].append("Add latency monitoring")
                    
                service_coverage.append(coverage_gap)
        
        return service_coverage

    def _generate_coverage_recommendations(self, coverage_analysis: Dict[str, Any]) -> List[str]:
        """Generate recommendations to improve monitoring coverage."""
        recommendations = []
        
        for missing_category in coverage_analysis['missing_categories']:
            if missing_category == 'availability':
                recommendations.append("Add service availability/uptime monitoring")
            elif missing_category == 'latency':
                recommendations.append("Add response time and latency monitoring")
            elif missing_category == 'error_rate':
                recommendations.append("Add error rate and HTTP status code monitoring")
            elif missing_category == 'resource_utilization':
                recommendations.append("Add CPU, memory, and disk utilization monitoring")
            elif missing_category == 'security':
                recommendations.append("Add security monitoring (auth failures, suspicious activity)")
            elif missing_category == 'business_metrics':
                recommendations.append("Add business KPI monitoring")
        
        for missing_signal in coverage_analysis['missing_golden_signals']:
            recommendations.append(f"Implement {missing_signal} monitoring (Golden Signal)")
        
        if coverage_analysis['critical_gaps']:
            recommendations.append("Address critical monitoring gaps as highest priority")
        
        return recommendations

    def find_duplicate_alerts(self, alerts: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """Identify duplicate or redundant alerts."""
        duplicates = []
        alert_signatures = defaultdict(list)
        
        # Group alerts by signature
        for i, alert in enumerate(alerts):
            signature = self._generate_alert_signature(alert)
            alert_signatures[signature].append((i, alert))
        
        # Find exact duplicates
        for signature, alert_group in alert_signatures.items():
            if len(alert_group) > 1:
                duplicate_group = {
                    'type': 'exact_duplicate',
                    'signature': signature,
                    'alerts': [{'index': i, 'name': alert.get('alert', alert.get('name', f'Alert_{i}'))} 
                             for i, alert in alert_group],
                    'recommendation': 'Remove duplicate alerts, keep the most comprehensive one'
                }
                duplicates.append(duplicate_group)
        
        # Find semantic duplicates (similar but not identical)
        semantic_duplicates = self._find_semantic_duplicates(alerts)
        duplicates.extend(semantic_duplicates)
        
        return duplicates

    def _generate_alert_signature(self, alert: Dict[str, Any]) -> str:
        """Generate a signature for alert comparison."""
        expr = alert.get('expr', alert.get('condition', ''))
        labels = alert.get('labels', {})
        
        # Normalize the expression by removing whitespace and standardizing
        normalized_expr = re.sub(r'\s+', ' ', expr).strip()
        
        # Create signature from expression and key labels
        key_labels = {k: v for k, v in labels.items() 
                     if k in ['service', 'severity', 'team']}
        
        return f"{normalized_expr}::{json.dumps(key_labels, sort_keys=True)}"

    def _find_semantic_duplicates(self, alerts: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """Find semantically similar alerts."""
        semantic_duplicates = []
        
        # Group alerts by service and metric type
        service_groups = defaultdict(list)
        
        for i, alert in enumerate(alerts):
            service = self._extract_service_from_alert(alert)
            metric_type = self._extract_metric_type_from_alert(alert)
            key = f"{service}::{metric_type}"
            service_groups[key].append((i, alert))
        
        # Look for similar alerts within each group
        for key, alert_group in service_groups.items():
            if len(alert_group) > 1:
                similar_alerts = self._identify_similar_alerts(alert_group)
                if similar_alerts:
                    semantic_duplicates.extend(similar_alerts)
        
        return semantic_duplicates

    def _extract_service_from_alert(self, alert: Dict[str, Any]) -> str:
        """Extract service name from alert."""
        labels = alert.get('labels', {})
        if 'service' in labels:
            return labels['service']
        
        expr = alert.get('expr', alert.get('condition', ''))
        # Try to extract service from metric labels
        service_match = re.search(r'service="([^"]+)"', expr)
        if service_match:
            return service_match.group(1)
        
        return 'unknown'

    def _extract_metric_type_from_alert(self, alert: Dict[str, Any]) -> str:
        """Extract metric type from alert."""
        expr = alert.get('expr', alert.get('condition', ''))
        
        # Common metric patterns
        if 'up' in expr.lower():
            return 'availability'
        elif any(keyword in expr.lower() for keyword in ['latency', 'duration', 'response_time']):
            return 'latency'
        elif any(keyword in expr.lower() for keyword in ['error', 'fail', '5xx']):
            return 'error_rate'
        elif any(keyword in expr.lower() for keyword in ['cpu', 'memory', 'disk']):
            return 'resource'
        
        return 'other'

    def _identify_similar_alerts(self, alert_group: List[Tuple[int, Dict[str, Any]]]) -> List[Dict[str, Any]]:
        """Identify similar alerts within a group."""
        similar_groups = []
        
        # Simple similarity check based on threshold values and conditions
        threshold_groups = defaultdict(list)
        
        for index, alert in alert_group:
            expr = alert.get('expr', alert.get('condition', ''))
            threshold = self._extract_threshold_from_expression(expr)
            severity = alert.get('labels', {}).get('severity', 'unknown')
            
            similarity_key = f"{threshold}::{severity}"
            threshold_groups[similarity_key].append((index, alert))
        
        # If multiple alerts have very similar thresholds, they might be redundant
        for similarity_key, similar_alerts in threshold_groups.items():
            if len(similar_alerts) > 1:
                similar_group = {
                    'type': 'semantic_duplicate',
                    'similarity_key': similarity_key,
                    'alerts': [{'index': i, 'name': alert.get('alert', alert.get('name', f'Alert_{i}'))} 
                             for i, alert in similar_alerts],
                    'recommendation': 'Review for potential consolidation - similar thresholds and conditions'
                }
                similar_groups.append(similar_group)
        
        return similar_groups

    def _extract_threshold_from_expression(self, expr: str) -> str:
        """Extract threshold value from alert expression."""
        # Look for common threshold patterns
        threshold_patterns = [
            r'>[\s]*([0-9.]+)',
            r'<[\s]*([0-9.]+)',
            r'>=[\s]*([0-9.]+)',
            r'<=[\s]*([0-9.]+)',
            r'==[\s]*([0-9.]+)'
        ]
        
        for pattern in threshold_patterns:
            match = re.search(pattern, expr)
            if match:
                return match.group(1)
        
        return 'unknown'

    def analyze_thresholds(self, alerts: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """Analyze alert thresholds for optimization opportunities."""
        threshold_analysis = []
        
        for alert in alerts:
            alert_name = alert.get('alert', alert.get('name', 'Unknown'))
            expr = alert.get('expr', alert.get('condition', ''))
            
            analysis = {
                'alert_name': alert_name,
                'current_expression': expr,
                'threshold_issues': [],
                'recommendations': []
            }
            
            # Check for hard-coded thresholds
            if re.search(r'[><=]\s*[0-9.]+', expr):
                analysis['threshold_issues'].append('Hard-coded threshold value')
                analysis['recommendations'].append('Consider parameterizing thresholds')
            
            # Check for percentage-based thresholds that might be too strict
            percentage_match = re.search(r'([><=])\s*0?\.\d+', expr)
            if percentage_match:
                operator = percentage_match.group(1)
                if operator in ['>', '>='] and 'error' in expr.lower():
                    analysis['threshold_issues'].append('Very low error rate threshold')
                    analysis['recommendations'].append('Consider increasing error rate threshold based on SLO')
            
            # Check for missing hysteresis
            if '>' in expr and 'for:' not in str(alert):
                analysis['threshold_issues'].append('No hysteresis (for clause)')
                analysis['recommendations'].append('Add "for" clause to prevent alert flapping')
            
            # Check for resource utilization thresholds
            if any(resource in expr.lower() for resource in ['cpu', 'memory', 'disk']):
                threshold_value = self._extract_threshold_from_expression(expr)
                if threshold_value and threshold_value.replace('.', '').isdigit():
                    threshold_num = float(threshold_value)
                    if threshold_num < 0.7:  # Less than 70%
                        analysis['threshold_issues'].append('Low resource utilization threshold')
                        analysis['recommendations'].append('Consider increasing threshold to reduce noise')
            
            # Add historical data analysis if available
            historical_data = alert.get('historical_data', {})
            if historical_data:
                false_positive_rate = historical_data.get('false_positive_rate', 0)
                if false_positive_rate > 0.2:
                    analysis['threshold_issues'].append(f'High false positive rate: {false_positive_rate*100:.1f}%')
                    analysis['recommendations'].append('Analyze historical data and adjust threshold')
            
            if analysis['threshold_issues']:
                threshold_analysis.append(analysis)
        
        return threshold_analysis

    def assess_alert_fatigue_risk(self, alerts: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Assess risk of alert fatigue."""
        fatigue_assessment = {
            'total_alerts': len(alerts),
            'risk_level': 'low',
            'risk_factors': [],
            'metrics': {},
            'recommendations': []
        }
        
        # Count alerts by severity
        severity_counts = Counter()
        for alert in alerts:
            severity = alert.get('labels', {}).get('severity', 'unknown')
            severity_counts[severity] += 1
        
        fatigue_assessment['metrics']['severity_distribution'] = dict(severity_counts)
        
        # Calculate risk factors
        critical_count = severity_counts.get('critical', 0)
        warning_count = severity_counts.get('warning', 0) + severity_counts.get('high', 0)
        total_high_priority = critical_count + warning_count
        
        # Too many high-priority alerts
        if total_high_priority > 50:
            fatigue_assessment['risk_factors'].append('High number of critical/warning alerts')
            fatigue_assessment['recommendations'].append('Review and reduce number of high-priority alerts')
        
        # Poor critical to warning ratio
        if critical_count > 0 and warning_count > 0:
            critical_ratio = critical_count / (critical_count + warning_count)
            if critical_ratio > 0.3:  # More than 30% critical
                fatigue_assessment['risk_factors'].append('High ratio of critical alerts')
                fatigue_assessment['recommendations'].append('Review critical alert criteria - not everything should be critical')
        
        # Estimate daily alert volume
        daily_estimate = self._estimate_daily_alert_volume(alerts)
        fatigue_assessment['metrics']['estimated_daily_alerts'] = daily_estimate
        
        if daily_estimate > 100:
            fatigue_assessment['risk_factors'].append('High estimated daily alert volume')
            fatigue_assessment['recommendations'].append('Implement alert grouping and suppression rules')
        
        # Check for missing runbooks
        alerts_without_runbooks = [alert for alert in alerts 
                                 if not alert.get('annotations', {}).get('runbook_url')]
        runbook_ratio = len(alerts_without_runbooks) / len(alerts) if alerts else 0
        
        if runbook_ratio > 0.5:
            fatigue_assessment['risk_factors'].append('Many alerts lack runbooks')
            fatigue_assessment['recommendations'].append('Create runbooks for alerts to improve response efficiency')
        
        # Determine overall risk level
        risk_score = len(fatigue_assessment['risk_factors'])
        if risk_score >= 3:
            fatigue_assessment['risk_level'] = 'high'
        elif risk_score >= 1:
            fatigue_assessment['risk_level'] = 'medium'
        
        return fatigue_assessment

    def _estimate_daily_alert_volume(self, alerts: List[Dict[str, Any]]) -> int:
        """Estimate daily alert volume."""
        total_estimated = 0
        
        for alert in alerts:
            # Use historical data if available
            historical_data = alert.get('historical_data', {})
            if historical_data and 'fires_per_day' in historical_data:
                total_estimated += historical_data['fires_per_day']
                continue
            
            # Otherwise estimate based on alert characteristics
            expr = alert.get('expr', alert.get('condition', ''))
            severity = alert.get('labels', {}).get('severity', 'warning')
            
            # Base estimate by severity
            base_estimates = {
                'critical': 0.1,  # Critical should rarely fire
                'high': 0.5,
                'warning': 2,
                'info': 5
            }
            
            estimate = base_estimates.get(severity, 1)
            
            # Adjust based on alert type
            if 'error_rate' in expr.lower():
                estimate *= 1.5  # Error rate alerts tend to be more frequent
            elif 'availability' in expr.lower() or 'up' in expr.lower():
                estimate *= 0.5  # Availability alerts should be rare
            
            total_estimated += estimate
        
        return int(total_estimated)

    def generate_optimized_config(self, alerts: List[Dict[str, Any]], 
                                analysis_results: Dict[str, Any]) -> Dict[str, Any]:
        """Generate optimized alert configuration."""
        optimized_alerts = []
        
        for i, alert in enumerate(alerts):
            optimized_alert = alert.copy()
            alert_name = alert.get('alert', alert.get('name', f'Alert_{i}'))
            
            # Apply noise reduction optimizations
            noisy_alerts = analysis_results.get('noisy_alerts', [])
            for noisy_alert in noisy_alerts:
                if noisy_alert['alert_name'] == alert_name:
                    optimized_alert = self._apply_noise_reduction(optimized_alert, noisy_alert)
                    break
            
            # Apply threshold optimizations
            threshold_issues = analysis_results.get('threshold_analysis', [])
            for threshold_issue in threshold_issues:
                if threshold_issue['alert_name'] == alert_name:
                    optimized_alert = self._apply_threshold_optimization(optimized_alert, threshold_issue)
                    break
            
            # Ensure proper alert metadata
            optimized_alert = self._ensure_alert_metadata(optimized_alert)
            
            optimized_alerts.append(optimized_alert)
        
        # Remove duplicates based on analysis
        if 'duplicate_alerts' in analysis_results:
            optimized_alerts = self._remove_duplicate_alerts(optimized_alerts, 
                                                           analysis_results['duplicate_alerts'])
        
        # Add missing alerts for coverage gaps
        if 'coverage_gaps' in analysis_results:
            new_alerts = self._generate_missing_alerts(analysis_results['coverage_gaps'])
            optimized_alerts.extend(new_alerts)
        
        optimized_config = {
            'alerts': optimized_alerts,
            'optimization_metadata': {
                'optimized_at': datetime.utcnow().isoformat() + 'Z',
                'original_count': len(alerts),
                'optimized_count': len(optimized_alerts),
                'changes_applied': analysis_results.get('optimizations_applied', [])
            }
        }
        
        return optimized_config

    def _apply_noise_reduction(self, alert: Dict[str, Any], 
                             noise_analysis: Dict[str, Any]) -> Dict[str, Any]:
        """Apply noise reduction optimizations to an alert."""
        optimized_alert = alert.copy()
        
        for recommendation in noise_analysis['recommendations']:
            if 'for:' in recommendation and not alert.get('for'):
                optimized_alert['for'] = '5m'
            elif 'threshold' in recommendation.lower():
                # This would require more sophisticated threshold adjustment
                # For now, add annotation for manual review
                if 'annotations' not in optimized_alert:
                    optimized_alert['annotations'] = {}
                optimized_alert['annotations']['optimization_note'] = 'Review threshold - potentially too sensitive'
        
        return optimized_alert

    def _apply_threshold_optimization(self, alert: Dict[str, Any], 
                                    threshold_analysis: Dict[str, Any]) -> Dict[str, Any]:
        """Apply threshold optimizations to an alert."""
        optimized_alert = alert.copy()
        
        # Add 'for' clause if missing
        if 'No hysteresis' in str(threshold_analysis['threshold_issues']):
            if not alert.get('for'):
                optimized_alert['for'] = '5m'
        
        # Add optimization annotations
        if threshold_analysis['recommendations']:
            if 'annotations' not in optimized_alert:
                optimized_alert['annotations'] = {}
            optimized_alert['annotations']['threshold_recommendations'] = '; '.join(threshold_analysis['recommendations'])
        
        return optimized_alert

    def _ensure_alert_metadata(self, alert: Dict[str, Any]) -> Dict[str, Any]:
        """Ensure alert has proper metadata."""
        optimized_alert = alert.copy()
        
        # Ensure annotations exist
        if 'annotations' not in optimized_alert:
            optimized_alert['annotations'] = {}
        
        # Add summary if missing
        if 'summary' not in optimized_alert['annotations']:
            alert_name = alert.get('alert', alert.get('name', 'Alert'))
            optimized_alert['annotations']['summary'] = f"Alert: {alert_name}"
        
        # Add description if missing
        if 'description' not in optimized_alert['annotations']:
            optimized_alert['annotations']['description'] = 'This alert requires a description. Please update with specific details about the condition and impact.'
        
        # Ensure proper labels
        if 'labels' not in optimized_alert:
            optimized_alert['labels'] = {}
        
        if 'severity' not in optimized_alert['labels']:
            optimized_alert['labels']['severity'] = 'warning'
        
        return optimized_alert

    def _remove_duplicate_alerts(self, alerts: List[Dict[str, Any]], 
                               duplicates: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """Remove duplicate alerts from the list."""
        indices_to_remove = set()
        
        for duplicate_group in duplicates:
            if duplicate_group['type'] == 'exact_duplicate':
                # Keep the first alert, remove the rest
                alert_indices = [alert_info['index'] for alert_info in duplicate_group['alerts']]
                indices_to_remove.update(alert_indices[1:])  # Remove all but first
        
        return [alert for i, alert in enumerate(alerts) if i not in indices_to_remove]

    def _generate_missing_alerts(self, coverage_gaps: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Generate alerts for missing coverage."""
        new_alerts = []
        
        for missing_signal in coverage_gaps.get('missing_golden_signals', []):
            if missing_signal == 'latency':
                new_alert = {
                    'alert': 'HighLatency',
                    'expr': 'histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m])) > 0.5',
                    'for': '5m',
                    'labels': {
                        'severity': 'warning'
                    },
                    'annotations': {
                        'summary': 'High request latency detected',
                        'description': 'The 95th percentile latency is above 500ms for 5 minutes.',
                        'generated': 'true'
                    }
                }
                new_alerts.append(new_alert)
            
            elif missing_signal == 'errors':
                new_alert = {
                    'alert': 'HighErrorRate',
                    'expr': 'sum(rate(http_requests_total{code=~"5.."}[5m])) / sum(rate(http_requests_total[5m])) > 0.01',
                    'for': '5m',
                    'labels': {
                        'severity': 'warning'
                    },
                    'annotations': {
                        'summary': 'High error rate detected',
                        'description': 'Error rate is above 1% for 5 minutes.',
                        'generated': 'true'
                    }
                }
                new_alerts.append(new_alert)
        
        return new_alerts

    def analyze_configuration(self, alert_config: Dict[str, Any]) -> Dict[str, Any]:
        """Perform comprehensive analysis of alert configuration."""
        alerts = alert_config.get('alerts', alert_config.get('rules', []))
        services = alert_config.get('services', [])
        
        analysis_results = {
            'summary': {
                'total_alerts': len(alerts),
                'analysis_timestamp': datetime.utcnow().isoformat() + 'Z'
            },
            'noisy_alerts': self.analyze_alert_noise(alerts),
            'coverage_gaps': self.identify_coverage_gaps(alerts, services),
            'duplicate_alerts': self.find_duplicate_alerts(alerts),
            'threshold_analysis': self.analyze_thresholds(alerts),
            'alert_fatigue_assessment': self.assess_alert_fatigue_risk(alerts)
        }
        
        # Generate overall recommendations
        analysis_results['overall_recommendations'] = self._generate_overall_recommendations(analysis_results)
        
        return analysis_results

    def _generate_overall_recommendations(self, analysis_results: Dict[str, Any]) -> List[str]:
        """Generate overall recommendations based on complete analysis."""
        recommendations = []
        
        # High-priority recommendations
        if analysis_results['alert_fatigue_assessment']['risk_level'] == 'high':
            recommendations.append("HIGH PRIORITY: Address alert fatigue risk by reducing alert volume")
        
        if len(analysis_results['coverage_gaps']['critical_gaps']) > 0:
            recommendations.append("HIGH PRIORITY: Address critical monitoring gaps")
        
        # Medium-priority recommendations
        if len(analysis_results['noisy_alerts']) > 0:
            recommendations.append(f"Optimize {len(analysis_results['noisy_alerts'])} noisy alerts to reduce false positives")
        
        if len(analysis_results['duplicate_alerts']) > 0:
            recommendations.append(f"Remove or consolidate {len(analysis_results['duplicate_alerts'])} duplicate alert groups")
        
        # General recommendations
        recommendations.append("Implement proper alert routing and escalation policies")
        recommendations.append("Create runbooks for all production alerts")
        recommendations.append("Set up alert effectiveness monitoring and regular reviews")
        
        return recommendations

    def export_analysis(self, analysis_results: Dict[str, Any], output_file: str, 
                       format_type: str = 'json'):
        """Export analysis results."""
        if format_type.lower() == 'json':
            with open(output_file, 'w') as f:
                json.dump(analysis_results, f, indent=2)
        elif format_type.lower() == 'html':
            self._export_html_report(analysis_results, output_file)
        else:
            raise ValueError(f"Unsupported format: {format_type}")

    def _export_html_report(self, analysis_results: Dict[str, Any], output_file: str):
        """Export analysis as HTML report."""
        html_content = self._generate_html_report(analysis_results)
        with open(output_file, 'w') as f:
            f.write(html_content)

    def _generate_html_report(self, analysis_results: Dict[str, Any]) -> str:
        """Generate HTML report of analysis results."""
        html = f"""
<!DOCTYPE html>
<html>
<head>
    <title>Alert Configuration Analysis Report</title>
    <style>
        body {{ font-family: Arial, sans-serif; margin: 20px; }}
        .header {{ background: #f4f4f4; padding: 20px; border-radius: 5px; }}
        .section {{ margin: 20px 0; padding: 15px; border: 1px solid #ddd; border-radius: 5px; }}
        .critical {{ border-left: 5px solid #ff0000; }}
        .warning {{ border-left: 5px solid #ff9900; }}
        .info {{ border-left: 5px solid #0066cc; }}
        .success {{ border-left: 5px solid #00aa00; }}
        ul {{ margin: 10px 0; }}
        li {{ margin: 5px 0; }}
    </style>
</head>
<body>
    <div class="header">
        <h1>Alert Configuration Analysis Report</h1>
        <p>Generated: {analysis_results['summary']['analysis_timestamp']}</p>
        <p>Total Alerts Analyzed: {analysis_results['summary']['total_alerts']}</p>
    </div>
    
    <div class="section critical">
        <h2>Overall Recommendations</h2>
        <ul>
        {''.join(f'<li>{rec}</li>' for rec in analysis_results['overall_recommendations'])}
        </ul>
    </div>
    
    <div class="section warning">
        <h2>Alert Fatigue Assessment</h2>
        <p><strong>Risk Level:</strong> {analysis_results['alert_fatigue_assessment']['risk_level'].upper()}</p>
        <p><strong>Risk Factors:</strong></p>
        <ul>
        {''.join(f'<li>{factor}</li>' for factor in analysis_results['alert_fatigue_assessment']['risk_factors'])}
        </ul>
    </div>
    
    <div class="section info">
        <h2>Noisy Alerts ({len(analysis_results['noisy_alerts'])})</h2>
        {''.join(f'<div><strong>{alert["alert_name"]}</strong> (Score: {alert["noise_score"]})<ul>{"".join(f"<li>{reason}</li>" for reason in alert["reasons"])}</ul></div>' 
                for alert in analysis_results['noisy_alerts'][:5])}
    </div>
    
    <div class="section info">
        <h2>Coverage Gaps</h2>
        <p><strong>Missing Categories:</strong> {', '.join(analysis_results['coverage_gaps']['missing_categories']) or 'None'}</p>
        <p><strong>Missing Golden Signals:</strong> {', '.join(analysis_results['coverage_gaps']['missing_golden_signals']) or 'None'}</p>
        <p><strong>Critical Gaps:</strong> {len(analysis_results['coverage_gaps']['critical_gaps'])}</p>
    </div>
    
</body>
</html>
        """
        return html

    def print_summary(self, analysis_results: Dict[str, Any]):
        """Print human-readable summary of analysis."""
        print(f"\n{'='*60}")
        print(f"ALERT CONFIGURATION ANALYSIS SUMMARY")
        print(f"{'='*60}")
        
        summary = analysis_results['summary']
        print(f"\nOverall Statistics:")
        print(f"  Total Alerts: {summary['total_alerts']}")
        print(f"  Analysis Date: {summary['analysis_timestamp']}")
        
        # Alert fatigue assessment
        fatigue = analysis_results['alert_fatigue_assessment']
        print(f"\nAlert Fatigue Risk: {fatigue['risk_level'].upper()}")
        if fatigue['risk_factors']:
            print(f"  Risk Factors:")
            for factor in fatigue['risk_factors']:
                print(f"    • {factor}")
        
        # Noisy alerts
        noisy = analysis_results['noisy_alerts']
        print(f"\nNoisy Alerts: {len(noisy)}")
        if noisy:
            print(f"  Top 3 Noisiest:")
            for alert in noisy[:3]:
                print(f"    • {alert['alert_name']} (Score: {alert['noise_score']})")
        
        # Coverage gaps
        gaps = analysis_results['coverage_gaps']
        print(f"\nMonitoring Coverage:")
        print(f"  Missing Categories: {len(gaps['missing_categories'])}")
        print(f"  Missing Golden Signals: {len(gaps['missing_golden_signals'])}")
        print(f"  Critical Gaps: {len(gaps['critical_gaps'])}")
        
        # Duplicates
        duplicates = analysis_results['duplicate_alerts']
        print(f"\nDuplicate Alerts: {len(duplicates)} groups")
        
        # Overall recommendations
        recommendations = analysis_results['overall_recommendations']
        print(f"\nTop Recommendations:")
        for i, rec in enumerate(recommendations[:5], 1):
            print(f"  {i}. {rec}")
        
        print(f"\n{'='*60}\n")


def main():
    """Main function for CLI usage."""
    parser = argparse.ArgumentParser(
        description='Analyze and optimize alert configurations',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    # Analyze alert configuration
    python alert_optimizer.py --input alerts.json --analyze-only
    
    # Generate optimized configuration
    python alert_optimizer.py --input alerts.json --output optimized_alerts.json
    
    # Generate HTML report
    python alert_optimizer.py --input alerts.json --report report.html --format html
        """
    )
    
    parser.add_argument('--input', '-i', required=True,
                       help='Input alert configuration JSON file')
    parser.add_argument('--output', '-o',
                       help='Output optimized configuration JSON file')
    parser.add_argument('--report', '-r',
                       help='Generate analysis report file')
    parser.add_argument('--format', choices=['json', 'html'], default='json',
                       help='Report format (json or html)')
    parser.add_argument('--analyze-only', action='store_true',
                       help='Only perform analysis, do not generate optimized config')
    
    args = parser.parse_args()
    
    optimizer = AlertOptimizer()
    
    try:
        # Load alert configuration
        alert_config = optimizer.load_alert_config(args.input)
        
        # Perform analysis
        analysis_results = optimizer.analyze_configuration(alert_config)
        
        # Generate optimized configuration if requested
        if not args.analyze_only:
            optimized_config = optimizer.generate_optimized_config(
                alert_config.get('alerts', alert_config.get('rules', [])),
                analysis_results
            )
            
            output_file = args.output or 'optimized_alerts.json'
            optimizer.export_analysis(optimized_config, output_file, 'json')
            print(f"Optimized configuration saved to: {output_file}")
        
        # Generate report if requested
        if args.report:
            optimizer.export_analysis(analysis_results, args.report, args.format)
            print(f"Analysis report saved to: {args.report}")
        
        # Always show summary
        optimizer.print_summary(analysis_results)
        
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()