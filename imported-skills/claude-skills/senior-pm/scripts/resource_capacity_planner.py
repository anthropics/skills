#!/usr/bin/env python3
"""
Resource Capacity Planner

Models team capacity across projects, identifies over/under-allocation, simulates
"what-if" scenarios for adding/removing resources, calculates utilization rates,
and provides capacity optimization recommendations for project portfolios.

Usage:
    python resource_capacity_planner.py capacity_data.json
    python resource_capacity_planner.py capacity_data.json --format json
"""

import argparse
import json
import statistics
import sys
from datetime import datetime, timedelta
from typing import Any, Dict, List, Optional, Tuple, Union


# ---------------------------------------------------------------------------
# Capacity Planning Configuration
# ---------------------------------------------------------------------------

ROLE_TYPES = {
    "senior_engineer": {
        "hourly_rate": 150,
        "efficiency_factor": 1.2,
        "skill_multipliers": {
            "backend": 1.0,
            "frontend": 0.9,
            "mobile": 0.8,
            "devops": 1.1,
            "data": 0.9
        }
    },
    "mid_engineer": {
        "hourly_rate": 100,
        "efficiency_factor": 1.0,
        "skill_multipliers": {
            "backend": 1.0,
            "frontend": 1.0,
            "mobile": 0.9,
            "devops": 0.8,
            "data": 0.8
        }
    },
    "junior_engineer": {
        "hourly_rate": 70,
        "efficiency_factor": 0.7,
        "skill_multipliers": {
            "backend": 0.8,
            "frontend": 0.9,
            "mobile": 0.7,
            "devops": 0.6,
            "data": 0.7
        }
    },
    "product_manager": {
        "hourly_rate": 130,
        "efficiency_factor": 1.1,
        "skill_multipliers": {
            "planning": 1.0,
            "stakeholder_mgmt": 1.0,
            "analysis": 0.9
        }
    },
    "designer": {
        "hourly_rate": 90,
        "efficiency_factor": 1.0,
        "skill_multipliers": {
            "ui_design": 1.0,
            "ux_research": 1.0,
            "prototyping": 0.9
        }
    },
    "qa_engineer": {
        "hourly_rate": 80,
        "efficiency_factor": 0.9,
        "skill_multipliers": {
            "manual_testing": 1.0,
            "automation": 1.1,
            "performance": 0.9
        }
    }
}

UTILIZATION_THRESHOLDS = {
    "under_utilized": 0.60,   # Below 60%
    "optimal": 0.85,          # 60-85%
    "over_utilized": 0.95,    # 85-95%
    "critical": 1.0           # Above 95%
}

CAPACITY_FACTORS = {
    "meeting_overhead": 0.15,     # 15% for meetings
    "learning_development": 0.05,  # 5% for skill development
    "administrative": 0.10,       # 10% for admin tasks
    "context_switching": 0.05,    # 5% for project switching penalty
    "vacation_sick": 0.12         # 12% for time off
}

PROJECT_COMPLEXITY_FACTORS = {
    "simple": 1.0,
    "moderate": 1.2,
    "complex": 1.5,
    "very_complex": 2.0
}


# ---------------------------------------------------------------------------
# Data Models
# ---------------------------------------------------------------------------

class Resource:
    """Represents a team member with skills and capacity."""
    
    def __init__(self, data: Dict[str, Any]):
        self.id: str = data.get("id", "")
        self.name: str = data.get("name", "")
        self.role: str = data.get("role", "").lower()
        self.skills: List[str] = data.get("skills", [])
        self.skill_levels: Dict[str, float] = data.get("skill_levels", {})
        self.hourly_rate: float = data.get("hourly_rate", 0)
        self.max_hours_per_week: int = data.get("max_hours_per_week", 40)
        self.current_utilization: float = data.get("current_utilization", 0.0)
        self.availability_start: str = data.get("availability_start", "")
        self.availability_end: Optional[str] = data.get("availability_end")
        self.location: str = data.get("location", "")
        self.time_zone: str = data.get("time_zone", "")
        
        # Calculate derived metrics
        self._calculate_effective_capacity()
        self._determine_role_config()
    
    def _calculate_effective_capacity(self):
        """Calculate effective weekly capacity accounting for overhead."""
        base_capacity = self.max_hours_per_week
        
        # Apply overhead factors
        overhead_total = sum(CAPACITY_FACTORS.values())
        self.effective_hours_per_week = base_capacity * (1 - overhead_total)
        
        # Current available capacity
        self.available_hours = self.effective_hours_per_week * (1 - self.current_utilization)
    
    def _determine_role_config(self):
        """Get role configuration from predefined types."""
        self.role_config = ROLE_TYPES.get(self.role, {
            "hourly_rate": self.hourly_rate or 100,
            "efficiency_factor": 1.0,
            "skill_multipliers": {}
        })
        
        # Use provided rate if available, otherwise use role default
        if not self.hourly_rate:
            self.hourly_rate = self.role_config["hourly_rate"]
    
    def get_skill_effectiveness(self, skill: str) -> float:
        """Calculate effectiveness for a specific skill."""
        base_level = self.skill_levels.get(skill, 0.5)  # Default 50% if not specified
        multiplier = self.role_config.get("skill_multipliers", {}).get(skill, 1.0)
        efficiency = self.role_config.get("efficiency_factor", 1.0)
        
        return base_level * multiplier * efficiency
    
    def can_work_on_project(self, project_skills: List[str], min_effectiveness: float = 0.6) -> bool:
        """Check if resource can effectively work on project."""
        for skill in project_skills:
            if skill in self.skills and self.get_skill_effectiveness(skill) >= min_effectiveness:
                return True
        return False


class Project:
    """Represents a project with resource requirements."""
    
    def __init__(self, data: Dict[str, Any]):
        self.id: str = data.get("id", "")
        self.name: str = data.get("name", "")
        self.priority: str = data.get("priority", "medium").lower()
        self.complexity: str = data.get("complexity", "moderate").lower()
        self.estimated_hours: int = data.get("estimated_hours", 0)
        self.start_date: str = data.get("start_date", "")
        self.target_end_date: str = data.get("target_end_date", "")
        self.required_skills: List[str] = data.get("required_skills", [])
        self.skill_requirements: Dict[str, int] = data.get("skill_requirements", {})
        self.current_allocation: List[Dict[str, Any]] = data.get("current_allocation", [])
        self.status: str = data.get("status", "planned").lower()
        
        # Calculate derived metrics
        self._calculate_project_metrics()
    
    def _calculate_project_metrics(self):
        """Calculate project-specific metrics."""
        # Apply complexity factor
        complexity_multiplier = PROJECT_COMPLEXITY_FACTORS.get(self.complexity, 1.0)
        self.adjusted_hours = self.estimated_hours * complexity_multiplier
        
        # Calculate current allocation
        self.currently_allocated_hours = sum(
            alloc.get("hours_per_week", 0) for alloc in self.current_allocation
        )
        
        # Calculate timeline metrics
        if self.start_date and self.target_end_date:
            try:
                start = datetime.strptime(self.start_date, "%Y-%m-%d")
                end = datetime.strptime(self.target_end_date, "%Y-%m-%d")
                self.duration_weeks = (end - start).days / 7
                
                # Required weekly capacity
                if self.duration_weeks > 0:
                    self.required_hours_per_week = self.adjusted_hours / self.duration_weeks
                else:
                    self.required_hours_per_week = self.adjusted_hours
            except ValueError:
                self.duration_weeks = 0
                self.required_hours_per_week = 0
        else:
            self.duration_weeks = 0
            self.required_hours_per_week = 0
        
        # Capacity gap
        self.capacity_gap = self.required_hours_per_week - self.currently_allocated_hours


class CapacityAnalysisResult:
    """Complete capacity analysis results."""
    
    def __init__(self):
        self.summary: Dict[str, Any] = {}
        self.resource_analysis: Dict[str, Any] = {}
        self.project_analysis: Dict[str, Any] = {}
        self.allocation_optimization: Dict[str, Any] = {}
        self.scenario_analysis: Dict[str, Any] = {}
        self.recommendations: List[str] = []


# ---------------------------------------------------------------------------
# Capacity Analysis Functions
# ---------------------------------------------------------------------------

def analyze_resource_utilization(resources: List[Resource]) -> Dict[str, Any]:
    """Analyze current resource utilization and capacity."""
    utilization_stats = {
        "total_resources": len(resources),
        "total_capacity": sum(r.effective_hours_per_week for r in resources),
        "total_allocated": sum(r.effective_hours_per_week * r.current_utilization for r in resources),
        "total_available": sum(r.available_hours for r in resources)
    }
    
    # Calculate overall utilization
    utilization_stats["overall_utilization"] = (
        utilization_stats["total_allocated"] / max(utilization_stats["total_capacity"], 1)
    )
    
    # Categorize resources by utilization
    utilization_categories = {
        "under_utilized": [],
        "optimal": [],
        "over_utilized": [],
        "critical": []
    }
    
    for resource in resources:
        if resource.current_utilization <= UTILIZATION_THRESHOLDS["under_utilized"]:
            utilization_categories["under_utilized"].append(resource)
        elif resource.current_utilization <= UTILIZATION_THRESHOLDS["optimal"]:
            utilization_categories["optimal"].append(resource)
        elif resource.current_utilization <= UTILIZATION_THRESHOLDS["over_utilized"]:
            utilization_categories["over_utilized"].append(resource)
        else:
            utilization_categories["critical"].append(resource)
    
    # Role-based analysis
    role_analysis = {}
    for resource in resources:
        if resource.role not in role_analysis:
            role_analysis[resource.role] = {
                "count": 0,
                "total_capacity": 0,
                "average_utilization": 0,
                "available_hours": 0,
                "hourly_cost": 0
            }
        
        role_data = role_analysis[resource.role]
        role_data["count"] += 1
        role_data["total_capacity"] += resource.effective_hours_per_week
        role_data["available_hours"] += resource.available_hours
        role_data["hourly_cost"] += resource.hourly_rate
    
    # Calculate averages for roles
    for role in role_analysis:
        role_data = role_analysis[role]
        role_data["average_utilization"] = 1 - (role_data["available_hours"] / max(role_data["total_capacity"], 1))
        role_data["average_hourly_rate"] = role_data["hourly_cost"] / role_data["count"]
    
    return {
        "utilization_stats": utilization_stats,
        "utilization_categories": {
            k: [{"id": r.id, "name": r.name, "role": r.role, "utilization": r.current_utilization}
                for r in v]
            for k, v in utilization_categories.items()
        },
        "role_analysis": role_analysis,
        "capacity_alerts": _generate_capacity_alerts(utilization_categories)
    }


def analyze_project_capacity_requirements(projects: List[Project]) -> Dict[str, Any]:
    """Analyze project capacity requirements and gaps."""
    project_stats = {
        "total_projects": len(projects),
        "active_projects": len([p for p in projects if p.status in ["active", "in_progress"]]),
        "planned_projects": len([p for p in projects if p.status == "planned"]),
        "total_estimated_hours": sum(p.adjusted_hours for p in projects),
        "total_weekly_demand": sum(p.required_hours_per_week for p in projects if p.status != "completed")
    }
    
    # Project priority analysis
    priority_distribution = {}
    for priority in ["high", "medium", "low"]:
        priority_projects = [p for p in projects if p.priority == priority]
        priority_distribution[priority] = {
            "count": len(priority_projects),
            "total_hours": sum(p.adjusted_hours for p in priority_projects),
            "weekly_demand": sum(p.required_hours_per_week for p in priority_projects if p.status != "completed")
        }
    
    # Capacity gap analysis
    projects_with_gaps = [p for p in projects if p.capacity_gap > 0 and p.status != "completed"]
    total_capacity_gap = sum(p.capacity_gap for p in projects_with_gaps)
    
    # Skill demand analysis
    skill_demand = {}
    for project in projects:
        if project.status != "completed":
            for skill, hours in project.skill_requirements.items():
                if skill not in skill_demand:
                    skill_demand[skill] = 0
                skill_demand[skill] += hours
    
    # Sort skills by demand
    sorted_skill_demand = sorted(skill_demand.items(), key=lambda x: x[1], reverse=True)
    
    return {
        "project_stats": project_stats,
        "priority_distribution": priority_distribution,
        "capacity_gaps": {
            "projects_with_gaps": len(projects_with_gaps),
            "total_gap_hours_weekly": total_capacity_gap,
            "gap_projects": [
                {
                    "id": p.id,
                    "name": p.name,
                    "priority": p.priority,
                    "gap_hours": p.capacity_gap,
                    "required_skills": p.required_skills
                }
                for p in sorted(projects_with_gaps, key=lambda p: p.capacity_gap, reverse=True)[:10]
            ]
        },
        "skill_demand": dict(sorted_skill_demand[:10])  # Top 10 skills in demand
    }


def optimize_resource_allocation(resources: List[Resource], projects: List[Project]) -> Dict[str, Any]:
    """Optimize resource allocation across projects."""
    optimization_results = {
        "current_allocation_efficiency": 0.0,
        "optimization_opportunities": [],
        "suggested_reallocations": [],
        "skill_matching_scores": {}
    }
    
    # Calculate current allocation efficiency
    total_effectiveness = 0
    total_allocations = 0
    
    for project in projects:
        if project.status not in ["completed", "cancelled"] and project.current_allocation:
            project_effectiveness = 0
            
            for allocation in project.current_allocation:
                resource_id = allocation.get("resource_id", "")
                hours = allocation.get("hours_per_week", 0)
                
                # Find the resource
                resource = next((r for r in resources if r.id == resource_id), None)
                if resource:
                    # Calculate effectiveness for this allocation
                    avg_skill_effectiveness = 0
                    skill_count = 0
                    
                    for skill in project.required_skills:
                        if skill in resource.skills:
                            avg_skill_effectiveness += resource.get_skill_effectiveness(skill)
                            skill_count += 1
                    
                    if skill_count > 0:
                        avg_skill_effectiveness /= skill_count
                        project_effectiveness += avg_skill_effectiveness * hours
                        total_allocations += hours
            
            if total_allocations > 0:
                total_effectiveness += project_effectiveness / total_allocations
    
    current_efficiency = total_effectiveness / max(len(projects), 1)
    optimization_results["current_allocation_efficiency"] = current_efficiency
    
    # Find optimization opportunities
    under_utilized = [r for r in resources if r.current_utilization < UTILIZATION_THRESHOLDS["under_utilized"]]
    over_allocated_projects = [p for p in projects if p.capacity_gap < 0 and p.status != "completed"]
    
    # Generate reallocation suggestions
    for project in projects:
        if project.capacity_gap > 0 and project.status != "completed":
            # Find best-fit under-utilized resources
            suitable_resources = []
            
            for resource in under_utilized:
                if resource.can_work_on_project(project.required_skills):
                    skill_match_score = 0
                    for skill in project.required_skills:
                        if skill in resource.skills:
                            skill_match_score += resource.get_skill_effectiveness(skill)
                    
                    skill_match_score /= max(len(project.required_skills), 1)
                    
                    suitable_resources.append({
                        "resource": resource,
                        "skill_match_score": skill_match_score,
                        "available_hours": resource.available_hours
                    })
            
            # Sort by skill match and availability
            suitable_resources.sort(key=lambda x: (x["skill_match_score"], x["available_hours"]), reverse=True)
            
            if suitable_resources:
                optimization_results["suggested_reallocations"].append({
                    "project_id": project.id,
                    "project_name": project.name,
                    "gap_hours": project.capacity_gap,
                    "recommended_resources": suitable_resources[:3]  # Top 3 recommendations
                })
    
    return optimization_results


def simulate_capacity_scenarios(resources: List[Resource], projects: List[Project], scenarios: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Simulate what-if scenarios for capacity planning."""
    scenario_results = {}
    
    for scenario in scenarios:
        scenario_name = scenario.get("name", "Unnamed Scenario")
        scenario_type = scenario.get("type", "")
        scenario_params = scenario.get("parameters", {})
        
        # Create copies for simulation
        sim_resources = [Resource(r.__dict__.copy()) for r in resources]
        sim_projects = [Project(p.__dict__.copy()) for p in projects]
        
        # Apply scenario changes
        if scenario_type == "add_resource":
            # Add new resource
            new_resource_data = scenario_params.get("resource_data", {})
            new_resource = Resource(new_resource_data)
            sim_resources.append(new_resource)
            
        elif scenario_type == "remove_resource":
            # Remove resource
            resource_id = scenario_params.get("resource_id", "")
            sim_resources = [r for r in sim_resources if r.id != resource_id]
            
        elif scenario_type == "add_project":
            # Add new project
            new_project_data = scenario_params.get("project_data", {})
            new_project = Project(new_project_data)
            sim_projects.append(new_project)
            
        elif scenario_type == "adjust_utilization":
            # Adjust resource utilization
            resource_id = scenario_params.get("resource_id", "")
            new_utilization = scenario_params.get("new_utilization", 0)
            
            for resource in sim_resources:
                if resource.id == resource_id:
                    resource.current_utilization = new_utilization
                    resource._calculate_effective_capacity()
        
        # Analyze scenario results
        resource_analysis = analyze_resource_utilization(sim_resources)
        project_analysis = analyze_project_capacity_requirements(sim_projects)
        
        scenario_results[scenario_name] = {
            "scenario_type": scenario_type,
            "resource_utilization": resource_analysis["utilization_stats"]["overall_utilization"],
            "total_capacity": resource_analysis["utilization_stats"]["total_capacity"],
            "capacity_gaps": project_analysis["capacity_gaps"]["total_gap_hours_weekly"],
            "under_utilized_count": len(resource_analysis["utilization_categories"]["under_utilized"]),
            "over_utilized_count": len(resource_analysis["utilization_categories"]["over_utilized"]),
            "cost_impact": _calculate_cost_impact(sim_resources, resources)
        }
    
    return scenario_results


def _generate_capacity_alerts(utilization_categories: Dict[str, List[Resource]]) -> List[str]:
    """Generate capacity-related alerts and warnings."""
    alerts = []
    
    critical_resources = utilization_categories.get("critical", [])
    over_utilized = utilization_categories.get("over_utilized", [])
    under_utilized = utilization_categories.get("under_utilized", [])
    
    if critical_resources:
        alerts.append(f"CRITICAL: {len(critical_resources)} resources are severely over-allocated (>95%)")
    
    if over_utilized:
        alerts.append(f"WARNING: {len(over_utilized)} resources are over-allocated (85-95%)")
    
    if len(under_utilized) > len(critical_resources) + len(over_utilized):
        alerts.append(f"OPPORTUNITY: {len(under_utilized)} resources are under-utilized (<60%)")
    
    return alerts


def _calculate_cost_impact(sim_resources: List[Resource], baseline_resources: List[Resource]) -> float:
    """Calculate cost impact of scenario vs baseline."""
    sim_cost = sum(r.hourly_rate * r.effective_hours_per_week for r in sim_resources)
    baseline_cost = sum(r.hourly_rate * r.effective_hours_per_week for r in baseline_resources)
    
    return sim_cost - baseline_cost


def generate_capacity_recommendations(analysis_results: Dict[str, Any]) -> List[str]:
    """Generate actionable capacity management recommendations."""
    recommendations = []
    
    # Resource utilization recommendations
    resource_analysis = analysis_results.get("resource_analysis", {})
    utilization_categories = resource_analysis.get("utilization_categories", {})
    
    critical_count = len(utilization_categories.get("critical", []))
    over_utilized_count = len(utilization_categories.get("over_utilized", []))
    under_utilized_count = len(utilization_categories.get("under_utilized", []))
    
    if critical_count > 0:
        recommendations.append(f"URGENT: Redistribute workload for {critical_count} critically over-allocated resources to prevent burnout.")
    
    if over_utilized_count > 2:
        recommendations.append(f"Consider hiring or redistributing work - {over_utilized_count} team members are over-allocated.")
    
    if under_utilized_count > 0 and critical_count + over_utilized_count > 0:
        recommendations.append(f"Rebalance allocation - {under_utilized_count} under-utilized resources could help with over-allocated work.")
    
    # Project capacity recommendations
    project_analysis = analysis_results.get("project_analysis", {})
    capacity_gaps = project_analysis.get("capacity_gaps", {})
    
    total_gap = capacity_gaps.get("total_gap_hours_weekly", 0)
    if total_gap > 40:  # More than 1 FTE worth of gap
        recommendations.append(f"Capacity shortfall of {total_gap:.0f} hours/week detected. Consider hiring or timeline adjustments.")
    
    # Skill-based recommendations
    skill_demand = project_analysis.get("skill_demand", {})
    if skill_demand:
        top_skill = list(skill_demand.keys())[0]
        top_demand = skill_demand[top_skill]
        recommendations.append(f"High demand for {top_skill} skills ({top_demand} hours). Consider training or specialized hiring.")
    
    # Optimization recommendations
    optimization = analysis_results.get("allocation_optimization", {})
    efficiency = optimization.get("current_allocation_efficiency", 0)
    
    if efficiency < 0.7:
        recommendations.append("Low allocation efficiency detected. Review skill-to-project matching and consider reallocation.")
    
    return recommendations


# ---------------------------------------------------------------------------
# Main Analysis Function
# ---------------------------------------------------------------------------

def analyze_capacity(data: Dict[str, Any]) -> CapacityAnalysisResult:
    """Perform comprehensive capacity analysis."""
    result = CapacityAnalysisResult()
    
    try:
        # Parse resource and project data
        resource_records = data.get("resources", [])
        project_records = data.get("projects", [])
        
        resources = [Resource(record) for record in resource_records]
        projects = [Project(record) for record in project_records]
        
        if not resources:
            raise ValueError("No resource data found")
        
        # Basic summary
        result.summary = {
            "total_resources": len(resources),
            "total_projects": len(projects),
            "active_projects": len([p for p in projects if p.status in ["active", "in_progress"]]),
            "total_capacity_hours": sum(r.effective_hours_per_week for r in resources),
            "total_demand_hours": sum(p.required_hours_per_week for p in projects if p.status != "completed"),
            "overall_utilization": sum(r.current_utilization for r in resources) / max(len(resources), 1)
        }
        
        # Resource analysis
        result.resource_analysis = analyze_resource_utilization(resources)
        
        # Project analysis
        result.project_analysis = analyze_project_capacity_requirements(projects)
        
        # Allocation optimization
        result.allocation_optimization = optimize_resource_allocation(resources, projects)
        
        # Scenario analysis (if scenarios provided)
        scenarios = data.get("scenarios", [])
        if scenarios:
            result.scenario_analysis = simulate_capacity_scenarios(resources, projects, scenarios)
        
        # Generate recommendations
        analysis_data = {
            "resource_analysis": result.resource_analysis,
            "project_analysis": result.project_analysis,
            "allocation_optimization": result.allocation_optimization
        }
        result.recommendations = generate_capacity_recommendations(analysis_data)
        
    except Exception as e:
        result.summary = {"error": str(e)}
    
    return result


# ---------------------------------------------------------------------------
# Output Formatting
# ---------------------------------------------------------------------------

def format_text_output(result: CapacityAnalysisResult) -> str:
    """Format analysis results as readable text report."""
    lines = []
    lines.append("="*60)
    lines.append("RESOURCE CAPACITY PLANNING REPORT")
    lines.append("="*60)
    lines.append("")
    
    if "error" in result.summary:
        lines.append(f"ERROR: {result.summary['error']}")
        return "\n".join(lines)
    
    # Executive Summary
    summary = result.summary
    lines.append("CAPACITY OVERVIEW")
    lines.append("-"*30)
    lines.append(f"Total Resources: {summary['total_resources']}")
    lines.append(f"Total Projects: {summary['total_projects']} ({summary['active_projects']} active)")
    lines.append(f"Capacity vs Demand: {summary['total_capacity_hours']:.0f}h vs {summary['total_demand_hours']:.0f}h per week")
    lines.append(f"Overall Utilization: {summary['overall_utilization']:.1%}")
    lines.append("")
    
    # Resource Utilization
    resource_analysis = result.resource_analysis
    lines.append("RESOURCE UTILIZATION ANALYSIS")
    lines.append("-"*30)
    
    utilization_categories = resource_analysis.get("utilization_categories", {})
    for category, resources in utilization_categories.items():
        if resources:
            lines.append(f"{category.replace('_', ' ').title()}: {len(resources)} resources")
            for resource in resources[:3]:  # Show top 3
                lines.append(f"  - {resource['name']} ({resource['role']}): {resource['utilization']:.1%}")
            if len(resources) > 3:
                lines.append(f"  ... and {len(resources) - 3} more")
    lines.append("")
    
    # Capacity Alerts
    alerts = resource_analysis.get("capacity_alerts", [])
    if alerts:
        lines.append("CAPACITY ALERTS")
        lines.append("-"*30)
        for alert in alerts:
            lines.append(f"⚠️  {alert}")
        lines.append("")
    
    # Project Capacity Gaps
    project_analysis = result.project_analysis
    capacity_gaps = project_analysis.get("capacity_gaps", {})
    
    lines.append("PROJECT CAPACITY GAPS")
    lines.append("-"*30)
    lines.append(f"Projects with gaps: {capacity_gaps.get('projects_with_gaps', 0)}")
    lines.append(f"Total gap: {capacity_gaps.get('total_gap_hours_weekly', 0):.0f} hours/week")
    
    gap_projects = capacity_gaps.get("gap_projects", [])
    if gap_projects:
        lines.append("Top projects needing resources:")
        for project in gap_projects[:5]:
            lines.append(f"  - {project['name']} ({project['priority']}): {project['gap_hours']:.0f}h/week gap")
    lines.append("")
    
    # Skill Demand
    skill_demand = project_analysis.get("skill_demand", {})
    if skill_demand:
        lines.append("TOP SKILL DEMANDS")
        lines.append("-"*30)
        for skill, hours in list(skill_demand.items())[:5]:
            lines.append(f"{skill}: {hours} hours needed")
        lines.append("")
    
    # Optimization Suggestions
    optimization = result.allocation_optimization
    suggested_reallocations = optimization.get("suggested_reallocations", [])
    
    if suggested_reallocations:
        lines.append("RESOURCE REALLOCATION SUGGESTIONS")
        lines.append("-"*30)
        for suggestion in suggested_reallocations[:3]:
            lines.append(f"Project: {suggestion['project_name']}")
            lines.append(f"  Gap: {suggestion['gap_hours']:.0f} hours/week")
            recommended = suggestion.get("recommended_resources", [])
            if recommended:
                best_match = recommended[0]
                resource_info = best_match["resource"]
                lines.append(f"  Best fit: {resource_info.name} ({resource_info.role})")
                lines.append(f"  Skill match: {best_match['skill_match_score']:.1%}")
                lines.append(f"  Available: {best_match['available_hours']:.0f}h/week")
        lines.append("")
    
    # Scenario Analysis
    scenario_analysis = result.scenario_analysis
    if scenario_analysis:
        lines.append("SCENARIO ANALYSIS")
        lines.append("-"*30)
        for scenario_name, results in scenario_analysis.items():
            lines.append(f"{scenario_name}:")
            lines.append(f"  Utilization: {results['resource_utilization']:.1%}")
            lines.append(f"  Capacity gaps: {results['capacity_gaps']:.0f}h/week")
            lines.append(f"  Cost impact: ${results['cost_impact']:.0f}/week")
        lines.append("")
    
    # Recommendations
    if result.recommendations:
        lines.append("RECOMMENDATIONS")
        lines.append("-"*30)
        for i, rec in enumerate(result.recommendations, 1):
            lines.append(f"{i}. {rec}")
    
    return "\n".join(lines)


def format_json_output(result: CapacityAnalysisResult) -> Dict[str, Any]:
    """Format analysis results as JSON."""
    # Helper function to serialize Resource objects
    def serialize_resource(resource):
        if hasattr(resource, 'id'):
            return {
                "id": resource.id,
                "name": resource.name,
                "role": resource.role,
                "utilization": resource.current_utilization,
                "available_hours": resource.available_hours,
                "hourly_rate": resource.hourly_rate
            }
        return resource
    
    # Deep copy and clean up the result
    serialized_result = {
        "summary": result.summary,
        "resource_analysis": result.resource_analysis,
        "project_analysis": result.project_analysis,
        "allocation_optimization": result.allocation_optimization,
        "scenario_analysis": result.scenario_analysis,
        "recommendations": result.recommendations
    }
    
    # Handle Resource objects in optimization suggestions
    if "suggested_reallocations" in serialized_result["allocation_optimization"]:
        for suggestion in serialized_result["allocation_optimization"]["suggested_reallocations"]:
            if "recommended_resources" in suggestion:
                for rec in suggestion["recommended_resources"]:
                    if "resource" in rec:
                        rec["resource"] = serialize_resource(rec["resource"])
    
    return serialized_result


# ---------------------------------------------------------------------------
# CLI Interface
# ---------------------------------------------------------------------------

def main() -> int:
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Analyze resource capacity and allocation across project portfolio"
    )
    parser.add_argument(
        "data_file", 
        help="JSON file containing resource and project capacity data"
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
        result = analyze_capacity(data)
        
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