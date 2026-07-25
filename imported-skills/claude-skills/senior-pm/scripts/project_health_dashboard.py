#!/usr/bin/env python3
"""
Project Health Dashboard

Aggregates project metrics across timeline, budget, scope, and quality dimensions.
Calculates composite health scores, generates RAG (Red/Amber/Green) status reports,
and identifies projects needing intervention for portfolio management.

Usage:
    python project_health_dashboard.py portfolio_data.json
    python project_health_dashboard.py portfolio_data.json --format json
"""

import argparse
import json
import statistics
import sys
from datetime import datetime, timedelta
from typing import Any, Dict, List, Optional, Tuple, Union


# ---------------------------------------------------------------------------
# Health Assessment Configuration
# ---------------------------------------------------------------------------

HEALTH_DIMENSIONS = {
    "timeline": {
        "weight": 0.25,
        "thresholds": {
            "green": {"min": 0.0, "max": 0.05},      # ≤5% delay
            "amber": {"min": 0.05, "max": 0.15},     # 5-15% delay  
            "red": {"min": 0.15, "max": 1.0}         # >15% delay
        }
    },
    "budget": {
        "weight": 0.25,
        "thresholds": {
            "green": {"min": 0.0, "max": 0.05},      # ≤5% over budget
            "amber": {"min": 0.05, "max": 0.15},     # 5-15% over budget
            "red": {"min": 0.15, "max": 1.0}         # >15% over budget
        }
    },
    "scope": {
        "weight": 0.20,
        "thresholds": {
            "green": {"min": 0.90, "max": 1.0},      # 90-100% scope delivered
            "amber": {"min": 0.75, "max": 0.90},     # 75-90% scope delivered
            "red": {"min": 0.0, "max": 0.75}         # <75% scope delivered
        }
    },
    "quality": {
        "weight": 0.20,
        "thresholds": {
            "green": {"min": 0.95, "max": 1.0},      # ≤5% defect rate
            "amber": {"min": 0.85, "max": 0.95},     # 5-15% defect rate
            "red": {"min": 0.0, "max": 0.85}         # >15% defect rate
        }
    },
    "risk": {
        "weight": 0.10,
        "thresholds": {
            "green": {"min": 0.0, "max": 15},        # Low risk score
            "amber": {"min": 15, "max": 25},         # Medium risk score
            "red": {"min": 25, "max": 100}           # High risk score
        }
    }
}

PROJECT_STATUS_MAPPING = {
    "planning": ["planning", "initiation", "chartered"],
    "active": ["active", "in_progress", "execution", "development"],
    "monitoring": ["monitoring", "testing", "review"],
    "completed": ["completed", "delivered", "closed"],
    "cancelled": ["cancelled", "terminated", "suspended"],
    "on_hold": ["on_hold", "paused", "blocked"]
}

PRIORITY_WEIGHTS = {
    "critical": 1.5,
    "high": 1.2,
    "medium": 1.0,
    "low": 0.8
}

INTERVENTION_THRESHOLDS = {
    "immediate": 30,     # Health score ≤30
    "urgent": 50,        # Health score ≤50
    "monitor": 70        # Health score ≤70
}


# ---------------------------------------------------------------------------
# Data Models
# ---------------------------------------------------------------------------

class ProjectMetrics:
    """Represents project health metrics and calculations."""
    
    def __init__(self, data: Dict[str, Any]):
        self.project_id: str = data.get("project_id", "")
        self.project_name: str = data.get("project_name", "")
        self.priority: str = data.get("priority", "medium").lower()
        self.status: str = data.get("status", "planning").lower()
        self.phase: str = data.get("phase", "planning")
        
        # Timeline metrics
        self.planned_start: str = data.get("planned_start", "")
        self.actual_start: Optional[str] = data.get("actual_start")
        self.planned_end: str = data.get("planned_end", "")
        self.forecasted_end: str = data.get("forecasted_end", "")
        self.completion_percentage: float = max(0, min(100, data.get("completion_percentage", 0))) / 100
        
        # Budget metrics
        self.planned_budget: float = data.get("planned_budget", 0)
        self.spent_to_date: float = data.get("spent_to_date", 0)
        self.forecasted_total_cost: float = data.get("forecasted_total_cost", 0)
        
        # Scope metrics
        self.planned_features: int = data.get("planned_features", 0)
        self.completed_features: int = data.get("completed_features", 0)
        self.descoped_features: int = data.get("descoped_features", 0)
        self.added_features: int = data.get("added_features", 0)
        
        # Quality metrics
        self.total_defects: int = data.get("total_defects", 0)
        self.resolved_defects: int = data.get("resolved_defects", 0)
        self.critical_defects: int = data.get("critical_defects", 0)
        self.test_coverage: float = max(0, min(1, data.get("test_coverage", 0)))
        
        # Risk metrics
        self.risk_score: float = data.get("risk_score", 0)
        self.open_risks: int = data.get("open_risks", 0)
        self.critical_risks: int = data.get("critical_risks", 0)
        
        # Team metrics
        self.team_size: int = data.get("team_size", 0)
        self.team_utilization: float = data.get("team_utilization", 0)
        self.team_satisfaction: Optional[float] = data.get("team_satisfaction")
        
        # Stakeholder metrics
        self.stakeholder_satisfaction: Optional[float] = data.get("stakeholder_satisfaction")
        self.last_status_update: str = data.get("last_status_update", "")
        
        # Calculate derived metrics
        self._calculate_health_metrics()
        self._normalize_status()
    
    def _calculate_health_metrics(self):
        """Calculate normalized health metrics for each dimension."""
        # Timeline health (0 = on time, 1 = severely delayed)
        self.timeline_health = self._calculate_timeline_variance()
        
        # Budget health (0 = on budget, 1 = severely over budget)
        self.budget_health = self._calculate_budget_variance()
        
        # Scope health (0 = no scope delivered, 1 = full scope delivered)
        self.scope_health = self._calculate_scope_completion()
        
        # Quality health (0 = poor quality, 1 = excellent quality)
        self.quality_health = self._calculate_quality_score()
        
        # Risk health (normalized risk score)
        self.risk_health = min(self.risk_score, 100)  # Cap at 100
    
    def _calculate_timeline_variance(self) -> float:
        """Calculate timeline variance as percentage of planned duration."""
        if not self.planned_start or not self.planned_end:
            return 0.0
        
        try:
            planned_start = datetime.strptime(self.planned_start, "%Y-%m-%d")
            planned_end = datetime.strptime(self.planned_end, "%Y-%m-%d")
            planned_duration = (planned_end - planned_start).days
            
            if planned_duration <= 0:
                return 0.0
            
            # Use forecasted end if available, otherwise current date for active projects
            if self.forecasted_end:
                forecast_date = datetime.strptime(self.forecasted_end, "%Y-%m-%d")
            elif self.status in ["completed", "cancelled"]:
                return 0.0  # Project is done
            else:
                forecast_date = datetime.now()
            
            actual_duration = (forecast_date - planned_start).days
            variance = max(0, actual_duration - planned_duration) / planned_duration
            
            return min(variance, 1.0)  # Cap at 100% delay
            
        except (ValueError, ZeroDivisionError):
            return 0.0
    
    def _calculate_budget_variance(self) -> float:
        """Calculate budget variance as percentage over original budget."""
        if self.planned_budget <= 0:
            return 0.0
        
        # Use forecasted total cost if available, otherwise spent to date
        actual_cost = self.forecasted_total_cost or self.spent_to_date
        variance = max(0, actual_cost - self.planned_budget) / self.planned_budget
        
        return min(variance, 1.0)  # Cap at 100% over budget
    
    def _calculate_scope_completion(self) -> float:
        """Calculate scope completion percentage."""
        if self.planned_features <= 0:
            return 1.0  # No planned features, consider complete
        
        # Account for scope changes
        effective_planned = self.planned_features + self.added_features - self.descoped_features
        if effective_planned <= 0:
            return 1.0
        
        return self.completed_features / effective_planned
    
    def _calculate_quality_score(self) -> float:
        """Calculate quality score based on defects and test coverage."""
        if self.total_defects == 0:
            defect_score = 1.0
        else:
            resolution_rate = self.resolved_defects / self.total_defects
            critical_penalty = self.critical_defects / max(self.total_defects, 1)
            defect_score = resolution_rate * (1 - critical_penalty * 0.5)
        
        # Combine defect score with test coverage
        quality_score = (defect_score * 0.7) + (self.test_coverage * 0.3)
        
        return max(0, min(1, quality_score))
    
    def _normalize_status(self):
        """Normalize project status to standard categories."""
        status_lower = self.status.lower()
        
        for category, statuses in PROJECT_STATUS_MAPPING.items():
            if status_lower in statuses:
                self.normalized_status = category
                return
        
        self.normalized_status = "active"  # Default
    
    @property
    def is_active(self) -> bool:
        return self.normalized_status in ["planning", "active", "monitoring"]
    
    @property
    def requires_intervention(self) -> bool:
        health_score = self.calculate_composite_health_score()
        return health_score <= INTERVENTION_THRESHOLDS["urgent"] and self.is_active


class PortfolioHealthResult:
    """Complete portfolio health analysis results."""
    
    def __init__(self):
        self.summary: Dict[str, Any] = {}
        self.project_scores: List[Dict[str, Any]] = []
        self.dimension_analysis: Dict[str, Any] = {}
        self.rag_status: Dict[str, Any] = {}
        self.intervention_list: List[Dict[str, Any]] = []
        self.portfolio_trends: Dict[str, Any] = {}
        self.recommendations: List[str] = []


# ---------------------------------------------------------------------------
# Health Calculation Functions
# ---------------------------------------------------------------------------

def calculate_dimension_score(value: float, dimension: str, is_reverse: bool = False) -> int:
    """Calculate dimension score (0-100) based on thresholds."""
    config = HEALTH_DIMENSIONS[dimension]
    thresholds = config["thresholds"]
    
    if not is_reverse:
        # Lower values are better (timeline, budget, risk)
        if value <= thresholds["green"]["max"]:
            return 90 + int((1 - value / thresholds["green"]["max"]) * 10)
        elif value <= thresholds["amber"]["max"]:
            range_size = thresholds["amber"]["max"] - thresholds["amber"]["min"]
            position = (value - thresholds["amber"]["min"]) / range_size
            return 60 + int((1 - position) * 30)
        else:
            # Red zone - score decreases with higher values
            excess = min(value - thresholds["red"]["min"], 1.0)
            return max(10, 60 - int(excess * 50))
    else:
        # Higher values are better (scope, quality)
        if value >= thresholds["green"]["min"]:
            range_size = thresholds["green"]["max"] - thresholds["green"]["min"]
            position = (value - thresholds["green"]["min"]) / range_size if range_size > 0 else 1
            return 90 + int(position * 10)
        elif value >= thresholds["amber"]["min"]:
            range_size = thresholds["amber"]["max"] - thresholds["amber"]["min"]
            position = (value - thresholds["amber"]["min"]) / range_size
            return 60 + int(position * 30)
        else:
            # Red zone
            if thresholds["red"]["max"] > 0:
                position = value / thresholds["red"]["max"]
                return max(10, int(position * 60))
            else:
                return 10


def calculate_project_health_score(project: ProjectMetrics) -> Dict[str, Any]:
    """Calculate comprehensive health score for a project."""
    # Calculate individual dimension scores
    timeline_score = calculate_dimension_score(project.timeline_health, "timeline")
    budget_score = calculate_dimension_score(project.budget_health, "budget")
    scope_score = calculate_dimension_score(project.scope_health, "scope", is_reverse=True)
    quality_score = calculate_dimension_score(project.quality_health, "quality", is_reverse=True)
    risk_score = calculate_dimension_score(project.risk_health, "risk")
    
    # Calculate weighted composite score
    dimensions = {
        "timeline": {"score": timeline_score, "weight": HEALTH_DIMENSIONS["timeline"]["weight"]},
        "budget": {"score": budget_score, "weight": HEALTH_DIMENSIONS["budget"]["weight"]},
        "scope": {"score": scope_score, "weight": HEALTH_DIMENSIONS["scope"]["weight"]},
        "quality": {"score": quality_score, "weight": HEALTH_DIMENSIONS["quality"]["weight"]},
        "risk": {"score": risk_score, "weight": HEALTH_DIMENSIONS["risk"]["weight"]}
    }
    
    composite_score = sum(
        dim_data["score"] * dim_data["weight"] 
        for dim_data in dimensions.values()
    )
    
    # Apply priority weighting
    priority_weight = PRIORITY_WEIGHTS.get(project.priority, 1.0)
    adjusted_score = composite_score * priority_weight
    
    # Determine RAG status
    if composite_score >= 80:
        rag_status = "green"
    elif composite_score >= 60:
        rag_status = "amber"
    else:
        rag_status = "red"
    
    # Determine intervention level
    if composite_score <= INTERVENTION_THRESHOLDS["immediate"]:
        intervention_level = "immediate"
    elif composite_score <= INTERVENTION_THRESHOLDS["urgent"]:
        intervention_level = "urgent"
    elif composite_score <= INTERVENTION_THRESHOLDS["monitor"]:
        intervention_level = "monitor"
    else:
        intervention_level = "none"
    
    return {
        "project_id": project.project_id,
        "project_name": project.project_name,
        "composite_score": composite_score,
        "adjusted_score": adjusted_score,
        "rag_status": rag_status,
        "intervention_level": intervention_level,
        "dimension_scores": dimensions,
        "priority": project.priority,
        "status": project.status,
        "completion_percentage": project.completion_percentage
    }


def analyze_portfolio_dimensions(project_scores: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Analyze portfolio performance across health dimensions."""
    dimension_analysis = {}
    
    for dimension in HEALTH_DIMENSIONS.keys():
        scores = [
            project["dimension_scores"][dimension]["score"] 
            for project in project_scores
        ]
        
        if scores:
            dimension_analysis[dimension] = {
                "average_score": statistics.mean(scores),
                "median_score": statistics.median(scores),
                "min_score": min(scores),
                "max_score": max(scores),
                "std_deviation": statistics.stdev(scores) if len(scores) > 1 else 0,
                "projects_below_60": len([s for s in scores if s < 60]),
                "projects_above_80": len([s for s in scores if s >= 80])
            }
    
    # Identify weakest and strongest dimensions
    avg_scores = {dim: data["average_score"] for dim, data in dimension_analysis.items()}
    weakest_dimension = min(avg_scores.keys(), key=lambda k: avg_scores[k])
    strongest_dimension = max(avg_scores.keys(), key=lambda k: avg_scores[k])
    
    return {
        "dimension_statistics": dimension_analysis,
        "weakest_dimension": weakest_dimension,
        "strongest_dimension": strongest_dimension,
        "dimension_rankings": sorted(avg_scores.items(), key=lambda x: x[1], reverse=True)
    }


def generate_rag_status_summary(project_scores: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Generate RAG status summary for portfolio."""
    rag_counts = {"green": 0, "amber": 0, "red": 0}
    
    # Count by RAG status
    for project in project_scores:
        rag_status = project["rag_status"]
        rag_counts[rag_status] += 1
    
    total_projects = len(project_scores)
    
    # Calculate percentages
    rag_percentages = {
        status: (count / max(total_projects, 1)) * 100 
        for status, count in rag_counts.items()
    }
    
    # Categorize projects by status
    green_projects = [p for p in project_scores if p["rag_status"] == "green"]
    amber_projects = [p for p in project_scores if p["rag_status"] == "amber"]
    red_projects = [p for p in project_scores if p["rag_status"] == "red"]
    
    # Calculate portfolio health grade
    if rag_percentages["red"] > 30:
        portfolio_grade = "critical"
    elif rag_percentages["red"] > 15 or rag_percentages["amber"] > 50:
        portfolio_grade = "concerning"
    elif rag_percentages["green"] > 60:
        portfolio_grade = "healthy"
    else:
        portfolio_grade = "moderate"
    
    return {
        "rag_counts": rag_counts,
        "rag_percentages": rag_percentages,
        "portfolio_grade": portfolio_grade,
        "green_projects": [{"id": p["project_id"], "name": p["project_name"], "score": p["composite_score"]} for p in green_projects],
        "amber_projects": [{"id": p["project_id"], "name": p["project_name"], "score": p["composite_score"]} for p in amber_projects],
        "red_projects": [{"id": p["project_id"], "name": p["project_name"], "score": p["composite_score"]} for p in red_projects]
    }


def identify_intervention_priorities(project_scores: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """Identify projects requiring intervention, prioritized by urgency and impact."""
    intervention_projects = [
        p for p in project_scores 
        if p["intervention_level"] in ["immediate", "urgent", "monitor"]
    ]
    
    # Sort by intervention level and then by adjusted score (priority-weighted)
    intervention_priority = {"immediate": 3, "urgent": 2, "monitor": 1}
    
    intervention_projects.sort(
        key=lambda p: (
            intervention_priority[p["intervention_level"]],
            -p["adjusted_score"]  # Lower scores need more urgent attention
        ),
        reverse=True
    )
    
    # Add recommended actions based on weakest dimensions
    for project in intervention_projects:
        project["recommended_actions"] = _generate_project_recommendations(project)
        project["risk_factors"] = _identify_risk_factors(project)
    
    return intervention_projects


def _generate_project_recommendations(project: Dict[str, Any]) -> List[str]:
    """Generate specific recommendations based on project's weak dimensions."""
    recommendations = []
    dimension_scores = project["dimension_scores"]
    
    # Timeline recommendations
    if dimension_scores["timeline"]["score"] < 60:
        recommendations.append("Conduct timeline recovery analysis and implement fast-tracking or crashing strategies")
    
    # Budget recommendations
    if dimension_scores["budget"]["score"] < 60:
        recommendations.append("Implement cost control measures and review budget forecasts")
    
    # Scope recommendations
    if dimension_scores["scope"]["score"] < 60:
        recommendations.append("Review scope management and consider feature prioritization or descoping")
    
    # Quality recommendations
    if dimension_scores["quality"]["score"] < 60:
        recommendations.append("Increase testing coverage and implement quality improvement processes")
    
    # Risk recommendations
    if dimension_scores["risk"]["score"] < 60:
        recommendations.append("Escalate critical risks and implement additional risk mitigation measures")
    
    # Overall health recommendations
    if project["composite_score"] < 40:
        recommendations.append("Consider project restructuring or emergency stakeholder review")
    
    return recommendations


def _identify_risk_factors(project: Dict[str, Any]) -> List[str]:
    """Identify specific risk factors for a project."""
    risk_factors = []
    
    if project["composite_score"] < 30:
        risk_factors.append("Critical project failure risk")
    
    if project["intervention_level"] == "immediate":
        risk_factors.append("Requires immediate management attention")
    
    dimension_scores = project["dimension_scores"]
    poor_dimensions = [
        dim for dim, data in dimension_scores.items() 
        if data["score"] < 50
    ]
    
    if len(poor_dimensions) > 2:
        risk_factors.append(f"Multiple failing dimensions: {', '.join(poor_dimensions)}")
    
    return risk_factors


def generate_portfolio_recommendations(analysis_results: Dict[str, Any]) -> List[str]:
    """Generate portfolio-level recommendations."""
    recommendations = []
    
    # RAG status recommendations
    rag_status = analysis_results.get("rag_status", {})
    red_percentage = rag_status.get("rag_percentages", {}).get("red", 0)
    amber_percentage = rag_status.get("rag_percentages", {}).get("amber", 0)
    
    if red_percentage > 30:
        recommendations.append("URGENT: 30%+ projects are in red status. Consider portfolio restructuring or resource reallocation.")
    elif red_percentage > 15:
        recommendations.append("HIGH: Significant number of projects in red status require immediate attention.")
    
    if amber_percentage > 50:
        recommendations.append("MEDIUM: Over half of portfolio projects need monitoring and support.")
    
    # Dimension-based recommendations
    dimension_analysis = analysis_results.get("dimension_analysis", {})
    weakest_dimension = dimension_analysis.get("weakest_dimension", "")
    
    if weakest_dimension:
        recommendations.append(f"Focus improvement efforts on {weakest_dimension} - weakest portfolio dimension.")
    
    # Intervention recommendations
    intervention_list = analysis_results.get("intervention_list", [])
    immediate_count = len([p for p in intervention_list if p["intervention_level"] == "immediate"])
    urgent_count = len([p for p in intervention_list if p["intervention_level"] == "urgent"])
    
    if immediate_count > 0:
        recommendations.append(f"CRITICAL: {immediate_count} projects require immediate intervention within 48 hours.")
    
    if urgent_count > 3:
        recommendations.append(f"Capacity alert: {urgent_count} projects need urgent attention - consider resource reallocation.")
    
    # Portfolio health recommendations
    portfolio_grade = rag_status.get("portfolio_grade", "")
    if portfolio_grade == "critical":
        recommendations.append("Portfolio health is critical. Recommend executive review and strategic realignment.")
    elif portfolio_grade == "concerning":
        recommendations.append("Portfolio health needs improvement. Implement enhanced monitoring and support.")
    
    return recommendations


# ---------------------------------------------------------------------------
# Main Analysis Function
# ---------------------------------------------------------------------------

def analyze_portfolio_health(data: Dict[str, Any]) -> PortfolioHealthResult:
    """Perform comprehensive portfolio health analysis."""
    result = PortfolioHealthResult()
    
    try:
        # Parse project data
        project_records = data.get("projects", [])
        projects = [ProjectMetrics(record) for record in project_records]
        
        if not projects:
            raise ValueError("No project data found")
        
        # Calculate health scores for each project
        project_scores = [calculate_project_health_score(project) for project in projects]
        result.project_scores = project_scores
        
        # Filter active projects for portfolio analysis
        active_scores = [score for i, score in enumerate(project_scores) if projects[i].is_active]
        
        # Portfolio summary
        if active_scores:
            composite_scores = [score["composite_score"] for score in active_scores]
            result.summary = {
                "total_projects": len(projects),
                "active_projects": len(active_scores),
                "portfolio_average_score": statistics.mean(composite_scores),
                "portfolio_median_score": statistics.median(composite_scores),
                "projects_needing_attention": len([s for s in active_scores if s["composite_score"] < 70]),
                "critical_projects": len([s for s in active_scores if s["composite_score"] < 40])
            }
        else:
            result.summary = {
                "total_projects": len(projects),
                "active_projects": 0,
                "portfolio_average_score": 0,
                "message": "No active projects found"
            }
        
        if active_scores:
            # Dimension analysis
            result.dimension_analysis = analyze_portfolio_dimensions(active_scores)
            
            # RAG status analysis
            result.rag_status = generate_rag_status_summary(active_scores)
            
            # Intervention priorities
            result.intervention_list = identify_intervention_priorities(active_scores)
            
            # Generate recommendations
            analysis_data = {
                "rag_status": result.rag_status,
                "dimension_analysis": result.dimension_analysis,
                "intervention_list": result.intervention_list
            }
            result.recommendations = generate_portfolio_recommendations(analysis_data)
        
    except Exception as e:
        result.summary = {"error": str(e)}
    
    return result


# ---------------------------------------------------------------------------
# Output Formatting
# ---------------------------------------------------------------------------

def format_text_output(result: PortfolioHealthResult) -> str:
    """Format analysis results as readable text report."""
    lines = []
    lines.append("="*60)
    lines.append("PROJECT HEALTH DASHBOARD")
    lines.append("="*60)
    lines.append("")
    
    if "error" in result.summary:
        lines.append(f"ERROR: {result.summary['error']}")
        return "\n".join(lines)
    
    # Executive Summary
    summary = result.summary
    lines.append("PORTFOLIO OVERVIEW")
    lines.append("-"*30)
    lines.append(f"Total Projects: {summary['total_projects']} ({summary.get('active_projects', 0)} active)")
    
    if "portfolio_average_score" in summary:
        lines.append(f"Portfolio Health Score: {summary['portfolio_average_score']:.1f}/100")
        lines.append(f"Projects Needing Attention: {summary.get('projects_needing_attention', 0)}")
        lines.append(f"Critical Projects: {summary.get('critical_projects', 0)}")
    
    if "message" in summary:
        lines.append(f"Status: {summary['message']}")
    
    lines.append("")
    
    # RAG Status Summary
    rag_status = result.rag_status
    if rag_status:
        lines.append("RAG STATUS SUMMARY")
        lines.append("-"*30)
        rag_counts = rag_status.get("rag_counts", {})
        rag_percentages = rag_status.get("rag_percentages", {})
        
        lines.append(f"🟢 Green: {rag_counts.get('green', 0)} ({rag_percentages.get('green', 0):.1f}%)")
        lines.append(f"🟡 Amber: {rag_counts.get('amber', 0)} ({rag_percentages.get('amber', 0):.1f}%)")
        lines.append(f"🔴 Red: {rag_counts.get('red', 0)} ({rag_percentages.get('red', 0):.1f}%)")
        lines.append(f"Portfolio Grade: {rag_status.get('portfolio_grade', 'N/A').title()}")
        lines.append("")
    
    # Dimension Analysis
    dimension_analysis = result.dimension_analysis
    if dimension_analysis:
        lines.append("HEALTH DIMENSION ANALYSIS")
        lines.append("-"*30)
        
        dimension_stats = dimension_analysis.get("dimension_statistics", {})
        for dimension, stats in dimension_stats.items():
            lines.append(f"{dimension.title()}: {stats['average_score']:.1f} avg "
                        f"({stats['projects_below_60']} below 60, {stats['projects_above_80']} above 80)")
        
        lines.append(f"Strongest: {dimension_analysis.get('strongest_dimension', '').title()}")
        lines.append(f"Weakest: {dimension_analysis.get('weakest_dimension', '').title()}")
        lines.append("")
    
    # Critical Projects Needing Intervention
    intervention_list = result.intervention_list
    if intervention_list:
        lines.append("PROJECTS REQUIRING INTERVENTION")
        lines.append("-"*30)
        
        immediate_projects = [p for p in intervention_list if p["intervention_level"] == "immediate"]
        urgent_projects = [p for p in intervention_list if p["intervention_level"] == "urgent"]
        
        if immediate_projects:
            lines.append("🚨 IMMEDIATE ACTION REQUIRED:")
            for project in immediate_projects[:5]:
                lines.append(f"  • {project['project_name']} (Score: {project['composite_score']:.0f})")
                if project.get("recommended_actions"):
                    lines.append(f"    → {project['recommended_actions'][0]}")
            lines.append("")
        
        if urgent_projects:
            lines.append("⚠️ URGENT ATTENTION NEEDED:")
            for project in urgent_projects[:5]:
                lines.append(f"  • {project['project_name']} (Score: {project['composite_score']:.0f})")
            lines.append("")
    
    # Top Performing Projects
    if result.project_scores:
        top_projects = sorted(result.project_scores, key=lambda p: p["composite_score"], reverse=True)[:5]
        lines.append("TOP PERFORMING PROJECTS")
        lines.append("-"*30)
        for project in top_projects:
            status_emoji = {"green": "🟢", "amber": "🟡", "red": "🔴"}.get(project["rag_status"], "⚫")
            lines.append(f"{status_emoji} {project['project_name']}: {project['composite_score']:.0f}/100")
        lines.append("")
    
    # Recommendations
    if result.recommendations:
        lines.append("PORTFOLIO RECOMMENDATIONS")
        lines.append("-"*30)
        for i, rec in enumerate(result.recommendations, 1):
            lines.append(f"{i}. {rec}")
    
    return "\n".join(lines)


def format_json_output(result: PortfolioHealthResult) -> Dict[str, Any]:
    """Format analysis results as JSON."""
    return {
        "summary": result.summary,
        "project_scores": result.project_scores,
        "dimension_analysis": result.dimension_analysis,
        "rag_status": result.rag_status,
        "intervention_list": result.intervention_list,
        "portfolio_trends": result.portfolio_trends,
        "recommendations": result.recommendations
    }


# ---------------------------------------------------------------------------
# ProjectMetrics Helper Method
# ---------------------------------------------------------------------------

def _calculate_composite_health_score(self) -> float:
    """Helper method to calculate composite health score."""
    health_calc = calculate_project_health_score(self)
    return health_calc["composite_score"]


# Add the method to the class
ProjectMetrics.calculate_composite_health_score = lambda self: calculate_project_health_score(self)["composite_score"]


# ---------------------------------------------------------------------------
# CLI Interface
# ---------------------------------------------------------------------------

def main() -> int:
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Analyze project portfolio health across multiple dimensions"
    )
    parser.add_argument(
        "data_file", 
        help="JSON file containing project portfolio data"
    )
    parser.add_argument(
        "--format", 
        choices=["text", "json"], 
        default="text",
        help="Output format (default: text)"
    )
    
    args = parser.parse_args()
    
    try:
        # Load and validate data
        with open(args.data_file, 'r') as f:
            data = json.load(f)
        
        # Perform analysis
        result = analyze_portfolio_health(data)
        
        # Output results
        if args.format == "json":
            output = format_json_output(result)
            print(json.dumps(output, indent=2))
        else:
            output = format_text_output(result)
            print(output)
        
        return 0
        
    except FileNotFoundError:
        print(f"Error: File '{args.data_file}' not found", file=sys.stderr)
        return 1
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in '{args.data_file}': {e}", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())