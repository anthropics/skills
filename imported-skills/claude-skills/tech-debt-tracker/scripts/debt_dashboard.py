#!/usr/bin/env python3
"""
Tech Debt Dashboard

Takes historical debt inventories (multiple scans over time) and generates trend analysis,
debt velocity (accruing vs paying down), health score, and executive summary.

Usage:
    python debt_dashboard.py historical_data.json
    python debt_dashboard.py data1.json data2.json data3.json
    python debt_dashboard.py --input-dir ./debt_scans/ --output dashboard_report.json
    python debt_dashboard.py historical_data.json --period quarterly --team-size 8
"""

import json
import argparse
import sys
import os
from collections import defaultdict, Counter
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple
from dataclasses import dataclass, asdict
from statistics import mean, median, stdev
import re


@dataclass
class HealthMetrics:
    """Health metrics for a specific time period."""
    overall_score: float  # 0-100
    debt_density: float  # debt items per file
    velocity_impact: float  # estimated velocity reduction %
    quality_score: float  # 0-100
    maintainability_score: float  # 0-100
    technical_risk_score: float  # 0-100


@dataclass
class TrendAnalysis:
    """Trend analysis for debt metrics over time."""
    metric_name: str
    trend_direction: str  # "improving", "declining", "stable"
    change_rate: float  # rate of change per period
    correlation_strength: float  # -1 to 1
    forecast_next_period: float
    confidence_interval: Tuple[float, float]


@dataclass
class DebtVelocity:
    """Debt velocity tracking - how fast debt is being created vs resolved."""
    period: str
    new_debt_items: int
    resolved_debt_items: int
    net_change: int
    velocity_ratio: float  # resolved/new, >1 is good
    effort_hours_added: float
    effort_hours_resolved: float
    net_effort_change: float


class DebtDashboard:
    """Main dashboard class for debt trend analysis and reporting."""
    
    def __init__(self, team_size: int = 5):
        self.team_size = team_size
        self.historical_data = []
        self.processed_snapshots = []
        self.trend_analyses = {}
        self.health_history = []
        self.velocity_history = []
        
        # Configuration for health scoring
        self.health_weights = {
            "debt_density": 0.25,
            "complexity_score": 0.20,
            "test_coverage_proxy": 0.15,
            "documentation_proxy": 0.10,
            "security_score": 0.15,
            "maintainability": 0.15
        }
        
        # Thresholds for categorization
        self.thresholds = {
            "excellent": 85,
            "good": 70,
            "fair": 55,
            "poor": 40
        }
    
    def load_historical_data(self, file_paths: List[str]) -> bool:
        """Load multiple debt inventory files for historical analysis."""
        self.historical_data = []
        
        for file_path in file_paths:
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                
                # Normalize data format
                if isinstance(data, dict) and 'debt_items' in data:
                    # Scanner output format
                    snapshot = {
                        "file_path": file_path,
                        "scan_date": data.get("scan_metadata", {}).get("scan_date", 
                                               self._extract_date_from_filename(file_path)),
                        "debt_items": data["debt_items"],
                        "summary": data.get("summary", {}),
                        "file_statistics": data.get("file_statistics", {})
                    }
                elif isinstance(data, dict) and 'prioritized_backlog' in data:
                    # Prioritizer output format
                    snapshot = {
                        "file_path": file_path,
                        "scan_date": data.get("metadata", {}).get("analysis_date",
                                               self._extract_date_from_filename(file_path)),
                        "debt_items": data["prioritized_backlog"],
                        "summary": data.get("insights", {}),
                        "file_statistics": {}
                    }
                elif isinstance(data, list):
                    # Raw debt items array
                    snapshot = {
                        "file_path": file_path,
                        "scan_date": self._extract_date_from_filename(file_path),
                        "debt_items": data,
                        "summary": {},
                        "file_statistics": {}
                    }
                else:
                    raise ValueError(f"Unrecognized data format in {file_path}")
                
                self.historical_data.append(snapshot)
                
            except Exception as e:
                print(f"Error loading {file_path}: {e}")
                continue
        
        if not self.historical_data:
            print("No valid data files loaded.")
            return False
        
        # Sort by date
        self.historical_data.sort(key=lambda x: x["scan_date"])
        print(f"Loaded {len(self.historical_data)} historical snapshots")
        return True
    
    def load_from_directory(self, directory_path: str, pattern: str = "*.json") -> bool:
        """Load all JSON files from a directory."""
        directory = Path(directory_path)
        if not directory.exists():
            print(f"Directory does not exist: {directory_path}")
            return False
        
        file_paths = []
        for file_path in directory.glob(pattern):
            if file_path.is_file():
                file_paths.append(str(file_path))
        
        if not file_paths:
            print(f"No matching files found in {directory_path}")
            return False
        
        return self.load_historical_data(file_paths)
    
    def _extract_date_from_filename(self, file_path: str) -> str:
        """Extract date from filename if possible, otherwise use current date."""
        filename = Path(file_path).name
        
        # Try to find date patterns in filename
        date_patterns = [
            r"(\d{4}-\d{2}-\d{2})",  # YYYY-MM-DD
            r"(\d{4}\d{2}\d{2})",    # YYYYMMDD
            r"(\d{2}-\d{2}-\d{4})",  # MM-DD-YYYY
        ]
        
        for pattern in date_patterns:
            match = re.search(pattern, filename)
            if match:
                date_str = match.group(1)
                try:
                    if len(date_str) == 8:  # YYYYMMDD
                        date_str = f"{date_str[:4]}-{date_str[4:6]}-{date_str[6:]}"
                    datetime.strptime(date_str, "%Y-%m-%d")
                    return date_str + "T12:00:00"
                except ValueError:
                    continue
        
        # Fallback to file modification time
        try:
            mtime = os.path.getmtime(file_path)
            return datetime.fromtimestamp(mtime).isoformat()
        except:
            return datetime.now().isoformat()
    
    def generate_dashboard(self, period: str = "monthly") -> Dict[str, Any]:
        """
        Generate comprehensive debt dashboard.
        
        Args:
            period: Analysis period ("weekly", "monthly", "quarterly")
            
        Returns:
            Dictionary containing dashboard data and analysis
        """
        print(f"Generating debt dashboard for {len(self.historical_data)} snapshots...")
        print(f"Analysis period: {period}")
        print("=" * 50)
        
        # Step 1: Process historical snapshots
        self._process_snapshots()
        
        # Step 2: Calculate health metrics for each snapshot
        self._calculate_health_metrics()
        
        # Step 3: Analyze trends
        self._analyze_trends(period)
        
        # Step 4: Calculate debt velocity
        self._calculate_debt_velocity(period)
        
        # Step 5: Generate forecasts
        forecasts = self._generate_forecasts()
        
        # Step 6: Create executive summary
        executive_summary = self._generate_executive_summary()
        
        # Step 7: Generate recommendations
        recommendations = self._generate_strategic_recommendations()
        
        # Step 8: Create visualizations data
        visualizations = self._generate_visualization_data()
        
        dashboard_data = {
            "metadata": {
                "generated_date": datetime.now().isoformat(),
                "analysis_period": period,
                "snapshots_analyzed": len(self.historical_data),
                "date_range": {
                    "start": self.historical_data[0]["scan_date"] if self.historical_data else None,
                    "end": self.historical_data[-1]["scan_date"] if self.historical_data else None
                },
                "team_size": self.team_size
            },
            "executive_summary": executive_summary,
            "current_health": self.health_history[-1] if self.health_history else None,
            "trend_analysis": {name: asdict(trend) for name, trend in self.trend_analyses.items()},
            "debt_velocity": [asdict(v) for v in self.velocity_history],
            "forecasts": forecasts,
            "recommendations": recommendations,
            "visualizations": visualizations,
            "detailed_metrics": self._get_detailed_metrics()
        }
        
        return dashboard_data
    
    def _process_snapshots(self):
        """Process raw snapshots into standardized format."""
        self.processed_snapshots = []
        
        for snapshot in self.historical_data:
            processed = {
                "date": snapshot["scan_date"],
                "total_debt_items": len(snapshot["debt_items"]),
                "debt_by_type": Counter(item.get("type", "unknown") for item in snapshot["debt_items"]),
                "debt_by_severity": Counter(item.get("severity", "medium") for item in snapshot["debt_items"]),
                "debt_by_category": Counter(self._categorize_debt_item(item) for item in snapshot["debt_items"]),
                "total_files": snapshot["summary"].get("total_files_scanned", 
                                                     len(snapshot["file_statistics"])),
                "total_effort_estimate": self._calculate_total_effort(snapshot["debt_items"]),
                "high_priority_count": len([item for item in snapshot["debt_items"] 
                                          if self._is_high_priority(item)]),
                "security_debt_count": len([item for item in snapshot["debt_items"]
                                          if self._is_security_related(item)]),
                "raw_data": snapshot
            }
            self.processed_snapshots.append(processed)
    
    def _categorize_debt_item(self, item: Dict[str, Any]) -> str:
        """Categorize debt item into high-level categories."""
        debt_type = item.get("type", "unknown")
        
        categories = {
            "code_quality": ["large_function", "high_complexity", "duplicate_code", 
                           "long_line", "missing_docstring"],
            "architecture": ["architecture_debt", "large_file"],
            "security": ["security_risk", "hardcoded_secrets", "sql_injection_risk"],
            "testing": ["test_debt", "missing_tests", "low_coverage"],
            "maintenance": ["todo_comment", "commented_code"],
            "dependencies": ["dependency_debt", "outdated_packages"],
            "infrastructure": ["deployment_debt", "monitoring_gaps"],
            "documentation": ["missing_docstring", "outdated_docs"]
        }
        
        for category, types in categories.items():
            if debt_type in types:
                return category
        
        return "other"
    
    def _calculate_total_effort(self, debt_items: List[Dict[str, Any]]) -> float:
        """Calculate total estimated effort for debt items."""
        total_effort = 0.0
        
        for item in debt_items:
            # Try to get effort from existing analysis
            if "effort_estimate" in item:
                total_effort += item["effort_estimate"].get("hours_estimate", 0)
            else:
                # Estimate based on debt type and severity
                effort = self._estimate_item_effort(item)
                total_effort += effort
        
        return total_effort
    
    def _estimate_item_effort(self, item: Dict[str, Any]) -> float:
        """Estimate effort for a debt item."""
        debt_type = item.get("type", "unknown")
        severity = item.get("severity", "medium")
        
        base_efforts = {
            "todo_comment": 2,
            "missing_docstring": 2,
            "long_line": 1,
            "large_function": 8,
            "high_complexity": 16,
            "duplicate_code": 12,
            "large_file": 32,
            "syntax_error": 4,
            "security_risk": 20,
            "architecture_debt": 80,
            "test_debt": 16
        }
        
        base_effort = base_efforts.get(debt_type, 8)
        
        severity_multipliers = {
            "low": 0.5,
            "medium": 1.0,
            "high": 1.5,
            "critical": 2.0
        }
        
        return base_effort * severity_multipliers.get(severity, 1.0)
    
    def _is_high_priority(self, item: Dict[str, Any]) -> bool:
        """Determine if debt item is high priority."""
        severity = item.get("severity", "medium")
        priority_score = item.get("priority_score", 0)
        debt_type = item.get("type", "")
        
        return (severity in ["high", "critical"] or 
                priority_score >= 7 or
                debt_type in ["security_risk", "syntax_error", "architecture_debt"])
    
    def _is_security_related(self, item: Dict[str, Any]) -> bool:
        """Determine if debt item is security-related."""
        debt_type = item.get("type", "")
        description = item.get("description", "").lower()
        
        security_types = ["security_risk", "hardcoded_secrets", "sql_injection_risk"]
        security_keywords = ["password", "token", "key", "secret", "auth", "security"]
        
        return (debt_type in security_types or 
                any(keyword in description for keyword in security_keywords))
    
    def _calculate_health_metrics(self):
        """Calculate health metrics for each snapshot."""
        self.health_history = []
        
        for snapshot in self.processed_snapshots:
            # Debt density (lower is better)
            debt_density = snapshot["total_debt_items"] / max(1, snapshot["total_files"])
            debt_density_score = max(0, 100 - (debt_density * 20))  # Scale to 0-100
            
            # Complexity score (based on high complexity debt)
            complex_debt_ratio = (snapshot["debt_by_type"].get("high_complexity", 0) + 
                                snapshot["debt_by_type"].get("large_function", 0)) / max(1, snapshot["total_debt_items"])
            complexity_score = max(0, 100 - (complex_debt_ratio * 100))
            
            # Test coverage proxy (based on test debt)
            test_debt_ratio = snapshot["debt_by_category"].get("testing", 0) / max(1, snapshot["total_debt_items"])
            test_coverage_proxy = max(0, 100 - (test_debt_ratio * 150))
            
            # Documentation proxy (based on documentation debt)
            doc_debt_ratio = snapshot["debt_by_category"].get("documentation", 0) / max(1, snapshot["total_debt_items"])
            documentation_proxy = max(0, 100 - (doc_debt_ratio * 100))
            
            # Security score (based on security debt)
            security_debt_ratio = snapshot["security_debt_count"] / max(1, snapshot["total_debt_items"])
            security_score = max(0, 100 - (security_debt_ratio * 200))
            
            # Maintainability (based on architecture and code quality debt)
            maint_debt_count = (snapshot["debt_by_category"].get("architecture", 0) + 
                              snapshot["debt_by_category"].get("code_quality", 0))
            maint_debt_ratio = maint_debt_count / max(1, snapshot["total_debt_items"])
            maintainability = max(0, 100 - (maint_debt_ratio * 120))
            
            # Calculate weighted overall score
            weights = self.health_weights
            overall_score = (
                debt_density_score * weights["debt_density"] +
                complexity_score * weights["complexity_score"] +
                test_coverage_proxy * weights["test_coverage_proxy"] +
                documentation_proxy * weights["documentation_proxy"] +
                security_score * weights["security_score"] +
                maintainability * weights["maintainability"]
            )
            
            # Velocity impact (estimated percentage reduction in team velocity)
            high_impact_ratio = snapshot["high_priority_count"] / max(1, snapshot["total_debt_items"])
            velocity_impact = min(50, high_impact_ratio * 30 + debt_density * 5)
            
            # Technical risk (0-100, higher is more risky)
            risk_factors = snapshot["security_debt_count"] + snapshot["debt_by_type"].get("architecture_debt", 0)
            technical_risk = min(100, risk_factors * 10 + (100 - security_score))
            
            health_metrics = HealthMetrics(
                overall_score=round(overall_score, 1),
                debt_density=round(debt_density, 2),
                velocity_impact=round(velocity_impact, 1),
                quality_score=round((complexity_score + maintainability) / 2, 1),
                maintainability_score=round(maintainability, 1),
                technical_risk_score=round(technical_risk, 1)
            )
            
            # Add timestamp
            health_entry = asdict(health_metrics)
            health_entry["date"] = snapshot["date"]
            self.health_history.append(health_entry)
    
    def _analyze_trends(self, period: str):
        """Analyze trends in various metrics."""
        self.trend_analyses = {}
        
        if len(self.health_history) < 2:
            return
        
        # Define metrics to analyze
        metrics_to_analyze = [
            "overall_score",
            "debt_density", 
            "velocity_impact",
            "quality_score",
            "technical_risk_score"
        ]
        
        for metric in metrics_to_analyze:
            values = [entry[metric] for entry in self.health_history]
            dates = [datetime.fromisoformat(entry["date"].replace('Z', '+00:00')) 
                    for entry in self.health_history]
            
            trend = self._calculate_trend(values, dates, metric)
            self.trend_analyses[metric] = trend
    
    def _calculate_trend(self, values: List[float], dates: List[datetime], metric_name: str) -> TrendAnalysis:
        """Calculate trend analysis for a specific metric."""
        if len(values) < 2:
            return TrendAnalysis(metric_name, "stable", 0.0, 0.0, values[-1], (values[-1], values[-1]))
        
        # Calculate simple linear trend
        n = len(values)
        x = list(range(n))  # Time periods as numbers
        
        # Linear regression
        x_mean = mean(x)
        y_mean = mean(values)
        
        numerator = sum((x[i] - x_mean) * (values[i] - y_mean) for i in range(n))
        denominator = sum((x[i] - x_mean) ** 2 for i in range(n))
        
        if denominator == 0:
            slope = 0
        else:
            slope = numerator / denominator
        
        # Correlation strength
        if n > 2 and len(set(values)) > 1:
            try:
                correlation = numerator / (
                    (sum((x[i] - x_mean) ** 2 for i in range(n)) * 
                     sum((values[i] - y_mean) ** 2 for i in range(n))) ** 0.5
                )
            except ZeroDivisionError:
                correlation = 0.0
        else:
            correlation = 0.0
        
        # Determine trend direction
        if abs(slope) < 0.1:
            trend_direction = "stable"
        elif slope > 0:
            if metric_name in ["overall_score", "quality_score"]:
                trend_direction = "improving"  # Higher is better
            else:
                trend_direction = "declining"  # Higher is worse
        else:
            if metric_name in ["overall_score", "quality_score"]:
                trend_direction = "declining"
            else:
                trend_direction = "improving"
        
        # Forecast next period
        forecast = values[-1] + slope
        
        # Confidence interval (simple approach)
        if n > 2:
            residuals = [values[i] - (y_mean + slope * (x[i] - x_mean)) for i in range(n)]
            std_error = (sum(r**2 for r in residuals) / (n - 2)) ** 0.5
            confidence_interval = (forecast - std_error, forecast + std_error)
        else:
            confidence_interval = (forecast, forecast)
        
        return TrendAnalysis(
            metric_name=metric_name,
            trend_direction=trend_direction,
            change_rate=round(slope, 3),
            correlation_strength=round(correlation, 3),
            forecast_next_period=round(forecast, 2),
            confidence_interval=(round(confidence_interval[0], 2), round(confidence_interval[1], 2))
        )
    
    def _calculate_debt_velocity(self, period: str):
        """Calculate debt velocity between snapshots."""
        self.velocity_history = []
        
        if len(self.processed_snapshots) < 2:
            return
        
        for i in range(1, len(self.processed_snapshots)):
            current = self.processed_snapshots[i]
            previous = self.processed_snapshots[i-1]
            
            # Track debt by unique identifiers when possible
            current_debt_ids = set()
            previous_debt_ids = set()
            
            current_effort = current["total_effort_estimate"]
            previous_effort = previous["total_effort_estimate"]
            
            # Simple approach: compare total counts and effort
            debt_change = current["total_debt_items"] - previous["total_debt_items"]
            effort_change = current_effort - previous_effort
            
            # Estimate new vs resolved (rough approximation)
            if debt_change >= 0:
                new_debt_items = debt_change
                resolved_debt_items = 0
            else:
                new_debt_items = 0
                resolved_debt_items = abs(debt_change)
            
            # Calculate velocity ratio
            if new_debt_items > 0:
                velocity_ratio = resolved_debt_items / new_debt_items
            else:
                velocity_ratio = float('inf') if resolved_debt_items > 0 else 1.0
            
            velocity = DebtVelocity(
                period=f"{previous['date'][:10]} to {current['date'][:10]}",
                new_debt_items=new_debt_items,
                resolved_debt_items=resolved_debt_items,
                net_change=debt_change,
                velocity_ratio=min(10.0, velocity_ratio),  # Cap at 10 for display
                effort_hours_added=max(0, effort_change),
                effort_hours_resolved=max(0, -effort_change),
                net_effort_change=effort_change
            )
            
            self.velocity_history.append(velocity)
    
    def _generate_forecasts(self) -> Dict[str, Any]:
        """Generate forecasts based on trend analysis."""
        if not self.trend_analyses:
            return {}
        
        forecasts = {}
        
        # Overall health forecast
        health_trend = self.trend_analyses.get("overall_score")
        if health_trend:
            current_score = self.health_history[-1]["overall_score"]
            forecasts["health_score_3_months"] = max(0, min(100, 
                current_score + (health_trend.change_rate * 3)))
            forecasts["health_score_6_months"] = max(0, min(100,
                current_score + (health_trend.change_rate * 6)))
        
        # Debt accumulation forecast
        if self.velocity_history:
            avg_net_change = mean([v.net_change for v in self.velocity_history[-3:]])  # Last 3 periods
            current_debt = self.processed_snapshots[-1]["total_debt_items"]
            
            forecasts["debt_count_3_months"] = max(0, current_debt + (avg_net_change * 3))
            forecasts["debt_count_6_months"] = max(0, current_debt + (avg_net_change * 6))
        
        # Risk forecast
        risk_trend = self.trend_analyses.get("technical_risk_score")
        if risk_trend:
            current_risk = self.health_history[-1]["technical_risk_score"]
            forecasts["risk_score_3_months"] = max(0, min(100,
                current_risk + (risk_trend.change_rate * 3)))
        
        return forecasts
    
    def _generate_executive_summary(self) -> Dict[str, Any]:
        """Generate executive summary of debt status."""
        if not self.health_history:
            return {}
        
        current_health = self.health_history[-1]
        
        # Determine overall status
        score = current_health["overall_score"]
        if score >= self.thresholds["excellent"]:
            status = "excellent"
            status_message = "Code quality is excellent with minimal technical debt."
        elif score >= self.thresholds["good"]:
            status = "good" 
            status_message = "Code quality is good with manageable technical debt."
        elif score >= self.thresholds["fair"]:
            status = "fair"
            status_message = "Code quality needs attention. Technical debt is accumulating."
        else:
            status = "poor"
            status_message = "Critical: High levels of technical debt requiring immediate action."
        
        # Key insights
        insights = []
        
        if len(self.health_history) > 1:
            prev_health = self.health_history[-2]
            score_change = current_health["overall_score"] - prev_health["overall_score"]
            
            if score_change > 5:
                insights.append("Health score improving significantly")
            elif score_change < -5:
                insights.append("Health score declining - attention needed")
        
        if current_health["velocity_impact"] > 20:
            insights.append("High velocity impact detected - development speed affected")
        
        if current_health["technical_risk_score"] > 70:
            insights.append("High technical risk - security and stability concerns")
        
        # Debt velocity insight
        if self.velocity_history:
            recent_velocity = self.velocity_history[-1]
            if recent_velocity.velocity_ratio < 0.5:
                insights.append("Debt accumulating faster than resolution")
            elif recent_velocity.velocity_ratio > 1.5:
                insights.append("Good progress on debt reduction")
        
        return {
            "overall_status": status,
            "health_score": current_health["overall_score"],
            "status_message": status_message,
            "key_insights": insights,
            "total_debt_items": self.processed_snapshots[-1]["total_debt_items"] if self.processed_snapshots else 0,
            "estimated_effort_hours": self.processed_snapshots[-1]["total_effort_estimate"] if self.processed_snapshots else 0,
            "high_priority_items": self.processed_snapshots[-1]["high_priority_count"] if self.processed_snapshots else 0,
            "velocity_impact_percent": current_health["velocity_impact"]
        }
    
    def _generate_strategic_recommendations(self) -> List[Dict[str, Any]]:
        """Generate strategic recommendations for debt management."""
        recommendations = []
        
        if not self.health_history:
            return recommendations
        
        current_health = self.health_history[-1]
        current_snapshot = self.processed_snapshots[-1] if self.processed_snapshots else {}
        
        # Health-based recommendations
        if current_health["overall_score"] < 50:
            recommendations.append({
                "priority": "critical",
                "category": "immediate_action",
                "title": "Initiate Emergency Debt Reduction",
                "description": "Current health score is critically low. Consider dedicating 50%+ of development capacity to debt reduction.",
                "impact": "high",
                "effort": "high"
            })
        
        # Velocity impact recommendations
        if current_health["velocity_impact"] > 25:
            recommendations.append({
                "priority": "high",
                "category": "productivity",
                "title": "Address Velocity Blockers",
                "description": f"Technical debt is reducing team velocity by {current_health['velocity_impact']:.1f}%. Focus on high-impact debt items first.",
                "impact": "high",
                "effort": "medium"
            })
        
        # Security recommendations
        if current_health["technical_risk_score"] > 70:
            recommendations.append({
                "priority": "high",
                "category": "security",
                "title": "Security Debt Review Required",
                "description": "High technical risk score indicates security vulnerabilities. Conduct immediate security debt audit.",
                "impact": "high",
                "effort": "medium"
            })
        
        # Trend-based recommendations
        health_trend = self.trend_analyses.get("overall_score")
        if health_trend and health_trend.trend_direction == "declining":
            recommendations.append({
                "priority": "medium",
                "category": "process",
                "title": "Implement Debt Prevention Measures",
                "description": "Health score is declining over time. Establish coding standards, automated quality gates, and regular debt reviews.",
                "impact": "medium",
                "effort": "medium"
            })
        
        # Category-specific recommendations
        if current_snapshot:
            debt_by_category = current_snapshot["debt_by_category"]
            top_category = debt_by_category.most_common(1)[0] if debt_by_category else None
            
            if top_category and top_category[1] > 10:
                category, count = top_category
                recommendations.append({
                    "priority": "medium",
                    "category": "focus_area",
                    "title": f"Focus on {category.replace('_', ' ').title()} Debt",
                    "description": f"{category.replace('_', ' ').title()} represents the largest debt category ({count} items). Consider targeted initiatives.",
                    "impact": "medium",
                    "effort": "medium"
                })
        
        # Velocity-based recommendations
        if self.velocity_history:
            recent_velocities = self.velocity_history[-3:] if len(self.velocity_history) >= 3 else self.velocity_history
            avg_velocity_ratio = mean([v.velocity_ratio for v in recent_velocities])
            
            if avg_velocity_ratio < 0.8:
                recommendations.append({
                    "priority": "medium",
                    "category": "capacity",
                    "title": "Increase Debt Resolution Capacity",
                    "description": "Debt is accumulating faster than resolution. Consider increasing debt budget or improving resolution efficiency.",
                    "impact": "medium",
                    "effort": "low"
                })
        
        return recommendations
    
    def _generate_visualization_data(self) -> Dict[str, Any]:
        """Generate data for dashboard visualizations."""
        visualizations = {}
        
        # Health score timeline
        visualizations["health_timeline"] = [
            {
                "date": entry["date"][:10],  # Date only
                "overall_score": entry["overall_score"],
                "quality_score": entry["quality_score"],
                "technical_risk": entry["technical_risk_score"]
            }
            for entry in self.health_history
        ]
        
        # Debt accumulation trend
        visualizations["debt_accumulation"] = [
            {
                "date": snapshot["date"][:10],
                "total_debt": snapshot["total_debt_items"],
                "high_priority": snapshot["high_priority_count"],
                "security_debt": snapshot["security_debt_count"]
            }
            for snapshot in self.processed_snapshots
        ]
        
        # Category distribution (latest snapshot)
        if self.processed_snapshots:
            latest_categories = self.processed_snapshots[-1]["debt_by_category"]
            visualizations["category_distribution"] = [
                {"category": category, "count": count}
                for category, count in latest_categories.items()
            ]
        
        # Velocity chart
        visualizations["debt_velocity"] = [
            {
                "period": velocity.period,
                "new_items": velocity.new_debt_items,
                "resolved_items": velocity.resolved_debt_items,
                "net_change": velocity.net_change,
                "velocity_ratio": velocity.velocity_ratio
            }
            for velocity in self.velocity_history
        ]
        
        # Effort estimation trend
        visualizations["effort_trend"] = [
            {
                "date": snapshot["date"][:10],
                "total_effort": snapshot["total_effort_estimate"]
            }
            for snapshot in self.processed_snapshots
        ]
        
        return visualizations
    
    def _get_detailed_metrics(self) -> Dict[str, Any]:
        """Get detailed metrics for the current state."""
        if not self.processed_snapshots:
            return {}
        
        current = self.processed_snapshots[-1]
        
        return {
            "debt_breakdown": dict(current["debt_by_type"]),
            "severity_breakdown": dict(current["debt_by_severity"]),
            "category_breakdown": dict(current["debt_by_category"]),
            "files_analyzed": current["total_files"],
            "debt_density": current["total_debt_items"] / max(1, current["total_files"]),
            "average_effort_per_item": current["total_effort_estimate"] / max(1, current["total_debt_items"])
        }


def format_dashboard_report(dashboard_data: Dict[str, Any]) -> str:
    """Format dashboard data into human-readable report."""
    output = []
    
    # Header
    output.append("=" * 60)
    output.append("TECHNICAL DEBT DASHBOARD")
    output.append("=" * 60)
    metadata = dashboard_data["metadata"]
    output.append(f"Generated: {metadata['generated_date'][:19]}")
    output.append(f"Analysis Period: {metadata['analysis_period']}")
    output.append(f"Snapshots Analyzed: {metadata['snapshots_analyzed']}")
    if metadata["date_range"]["start"]:
        output.append(f"Date Range: {metadata['date_range']['start'][:10]} to {metadata['date_range']['end'][:10]}")
    output.append("")
    
    # Executive Summary
    exec_summary = dashboard_data["executive_summary"]
    output.append("EXECUTIVE SUMMARY")
    output.append("-" * 30)
    output.append(f"Overall Status: {exec_summary['overall_status'].upper()}")
    output.append(f"Health Score: {exec_summary['health_score']:.1f}/100")
    output.append(f"Status: {exec_summary['status_message']}")
    output.append("")
    output.append("Key Metrics:")
    output.append(f"  • Total Debt Items: {exec_summary['total_debt_items']}")
    output.append(f"  • High Priority Items: {exec_summary['high_priority_items']}")
    output.append(f"  • Estimated Effort: {exec_summary['estimated_effort_hours']:.1f} hours")
    output.append(f"  • Velocity Impact: {exec_summary['velocity_impact_percent']:.1f}%")
    output.append("")
    
    if exec_summary["key_insights"]:
        output.append("Key Insights:")
        for insight in exec_summary["key_insights"]:
            output.append(f"  • {insight}")
        output.append("")
    
    # Current Health
    if dashboard_data["current_health"]:
        health = dashboard_data["current_health"]
        output.append("CURRENT HEALTH METRICS")
        output.append("-" * 30)
        output.append(f"Overall Score: {health['overall_score']:.1f}/100")
        output.append(f"Quality Score: {health['quality_score']:.1f}/100")
        output.append(f"Maintainability: {health['maintainability_score']:.1f}/100")
        output.append(f"Technical Risk: {health['technical_risk_score']:.1f}/100")
        output.append(f"Debt Density: {health['debt_density']:.2f} items/file")
        output.append("")
    
    # Trend Analysis
    trends = dashboard_data["trend_analysis"]
    if trends:
        output.append("TREND ANALYSIS")
        output.append("-" * 30)
        for metric, trend in trends.items():
            direction_symbol = {
                "improving": "↑",
                "declining": "↓", 
                "stable": "→"
            }.get(trend["trend_direction"], "→")
            
            output.append(f"{metric.replace('_', ' ').title()}: {direction_symbol} {trend['trend_direction']}")
            output.append(f"  Change Rate: {trend['change_rate']:.3f} per period")
            output.append(f"  Forecast: {trend['forecast_next_period']:.1f}")
        output.append("")
    
    # Top Recommendations
    recommendations = dashboard_data["recommendations"]
    if recommendations:
        output.append("TOP RECOMMENDATIONS")
        output.append("-" * 30)
        for i, rec in enumerate(recommendations[:5], 1):
            output.append(f"{i}. [{rec['priority'].upper()}] {rec['title']}")
            output.append(f"   {rec['description']}")
            output.append(f"   Impact: {rec['impact']}, Effort: {rec['effort']}")
            output.append("")
    
    return "\n".join(output)


def main():
    """Main entry point for the debt dashboard."""
    parser = argparse.ArgumentParser(description="Generate technical debt dashboard")
    parser.add_argument("files", nargs="*", help="Debt inventory files")
    parser.add_argument("--input-dir", help="Directory containing debt inventory files")
    parser.add_argument("--output", help="Output file path")
    parser.add_argument("--format", choices=["json", "text", "both"], 
                       default="both", help="Output format")
    parser.add_argument("--period", choices=["weekly", "monthly", "quarterly"],
                       default="monthly", help="Analysis period")
    parser.add_argument("--team-size", type=int, default=5, help="Team size")
    
    args = parser.parse_args()
    
    # Initialize dashboard
    dashboard = DebtDashboard(args.team_size)
    
    # Load data
    if args.input_dir:
        success = dashboard.load_from_directory(args.input_dir)
    elif args.files:
        success = dashboard.load_historical_data(args.files)
    else:
        print("Error: Must specify either files or --input-dir")
        sys.exit(1)
    
    if not success:
        sys.exit(1)
    
    # Generate dashboard
    try:
        dashboard_data = dashboard.generate_dashboard(args.period)
    except Exception as e:
        print(f"Dashboard generation failed: {e}")
        sys.exit(1)
    
    # Output results
    if args.format in ["json", "both"]:
        json_output = json.dumps(dashboard_data, indent=2, default=str)
        if args.output:
            output_path = args.output if args.output.endswith('.json') else f"{args.output}.json"
            with open(output_path, 'w') as f:
                f.write(json_output)
            print(f"JSON dashboard written to: {output_path}")
        else:
            print("JSON DASHBOARD:")
            print("=" * 50)
            print(json_output)
    
    if args.format in ["text", "both"]:
        text_output = format_dashboard_report(dashboard_data)
        if args.output:
            output_path = args.output if args.output.endswith('.txt') else f"{args.output}.txt"
            with open(output_path, 'w') as f:
                f.write(text_output)
            print(f"Text dashboard written to: {output_path}")
        else:
            print("\nTEXT DASHBOARD:")
            print("=" * 50)
            print(text_output)


if __name__ == "__main__":
    main()