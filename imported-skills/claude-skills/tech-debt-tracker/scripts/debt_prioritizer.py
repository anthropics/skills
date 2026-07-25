#!/usr/bin/env python3
"""
Tech Debt Prioritizer

Takes a debt inventory (from scanner or manual JSON) and calculates interest rate,
effort estimates, and produces a prioritized backlog with recommended sprint allocation.
Uses cost-of-delay vs effort scoring and various prioritization frameworks.

Usage:
    python debt_prioritizer.py debt_inventory.json
    python debt_prioritizer.py debt_inventory.json --output prioritized_backlog.json
    python debt_prioritizer.py debt_inventory.json --team-size 6 --sprint-capacity 80
    python debt_prioritizer.py debt_inventory.json --framework wsjf --output results.json
"""

import json
import argparse
import sys
import math
from collections import defaultdict, Counter
from datetime import datetime, timedelta
from typing import Dict, List, Any, Optional, Tuple
from dataclasses import dataclass, asdict


@dataclass
class EffortEstimate:
    """Represents effort estimation for a debt item."""
    size_points: int
    hours_estimate: float
    risk_factor: float  # 1.0 = low risk, 1.5 = medium, 2.0+ = high
    skill_level_required: str  # junior, mid, senior, expert
    confidence: float  # 0.0-1.0


@dataclass
class BusinessImpact:
    """Represents business impact assessment for a debt item."""
    customer_impact: int  # 1-10 scale
    revenue_impact: int  # 1-10 scale  
    team_velocity_impact: int  # 1-10 scale
    quality_impact: int  # 1-10 scale
    security_impact: int  # 1-10 scale


@dataclass
class InterestRate:
    """Represents the interest rate calculation for technical debt."""
    daily_cost: float  # cost per day if left unfixed
    frequency_multiplier: float  # how often this code is touched
    team_impact_multiplier: float  # how many developers affected
    compound_rate: float  # how quickly this debt makes other debt worse


class DebtPrioritizer:
    """Main class for prioritizing technical debt items."""
    
    def __init__(self, team_size: int = 5, sprint_capacity_hours: int = 80):
        self.team_size = team_size
        self.sprint_capacity_hours = sprint_capacity_hours
        self.debt_items = []
        self.prioritized_items = []
        
        # Prioritization framework weights
        self.framework_weights = {
            "cost_of_delay": {
                "business_value": 0.3,
                "urgency": 0.3,
                "risk_reduction": 0.2,
                "team_productivity": 0.2
            },
            "wsjf": {
                "business_value": 0.25,
                "time_criticality": 0.25,
                "risk_reduction": 0.25,
                "effort": 0.25
            },
            "rice": {
                "reach": 0.25,
                "impact": 0.25,
                "confidence": 0.25,
                "effort": 0.25
            }
        }
    
    def load_debt_inventory(self, file_path: str) -> bool:
        """Load debt inventory from JSON file."""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                data = json.load(f)
            
            # Handle different input formats
            if isinstance(data, dict) and 'debt_items' in data:
                self.debt_items = data['debt_items']
            elif isinstance(data, list):
                self.debt_items = data
            else:
                raise ValueError("Invalid debt inventory format")
            
            print(f"Loaded {len(self.debt_items)} debt items from {file_path}")
            return True
            
        except Exception as e:
            print(f"Error loading debt inventory: {e}")
            return False
    
    def analyze_and_prioritize(self, framework: str = "cost_of_delay") -> Dict[str, Any]:
        """
        Analyze debt items and create prioritized backlog.
        
        Args:
            framework: Prioritization framework to use
            
        Returns:
            Dictionary containing prioritized backlog and analysis
        """
        print(f"Analyzing {len(self.debt_items)} debt items...")
        print(f"Using {framework} prioritization framework")
        print("=" * 50)
        
        # Step 1: Enrich debt items with estimates
        enriched_items = []
        for item in self.debt_items:
            enriched_item = self._enrich_debt_item(item)
            enriched_items.append(enriched_item)
        
        # Step 2: Calculate prioritization scores
        for item in enriched_items:
            if framework == "cost_of_delay":
                item["priority_score"] = self._calculate_cost_of_delay_score(item)
            elif framework == "wsjf":
                item["priority_score"] = self._calculate_wsjf_score(item)
            elif framework == "rice":
                item["priority_score"] = self._calculate_rice_score(item)
            else:
                raise ValueError(f"Unknown prioritization framework: {framework}")
        
        # Step 3: Sort by priority score
        self.prioritized_items = sorted(enriched_items, 
                                      key=lambda x: x["priority_score"], 
                                      reverse=True)
        
        # Step 4: Generate sprint allocation recommendations
        sprint_allocation = self._generate_sprint_allocation()
        
        # Step 5: Generate insights and recommendations
        insights = self._generate_insights()
        
        # Step 6: Create visualization data
        charts_data = self._generate_charts_data()
        
        return {
            "metadata": {
                "analysis_date": datetime.now().isoformat(),
                "framework_used": framework,
                "team_size": self.team_size,
                "sprint_capacity_hours": self.sprint_capacity_hours,
                "total_items_analyzed": len(self.debt_items)
            },
            "prioritized_backlog": self.prioritized_items,
            "sprint_allocation": sprint_allocation,
            "insights": insights,
            "charts_data": charts_data,
            "recommendations": self._generate_recommendations()
        }
    
    def _enrich_debt_item(self, item: Dict[str, Any]) -> Dict[str, Any]:
        """Enrich debt item with detailed estimates and impact analysis."""
        enriched = item.copy()
        
        # Generate effort estimate
        effort = self._estimate_effort(item)
        enriched["effort_estimate"] = asdict(effort)
        
        # Generate business impact assessment
        business_impact = self._assess_business_impact(item)
        enriched["business_impact"] = asdict(business_impact)
        
        # Calculate interest rate
        interest_rate = self._calculate_interest_rate(item, business_impact)
        enriched["interest_rate"] = asdict(interest_rate)
        
        # Calculate cost of delay
        enriched["cost_of_delay"] = self._calculate_cost_of_delay(interest_rate, effort)
        
        # Assign categories and tags
        enriched["category"] = self._categorize_debt_item(item)
        enriched["impact_tags"] = self._generate_impact_tags(item, business_impact)
        
        return enriched
    
    def _estimate_effort(self, item: Dict[str, Any]) -> EffortEstimate:
        """Estimate effort required to fix debt item."""
        debt_type = item.get("type", "unknown")
        severity = item.get("severity", "medium")
        
        # Base effort estimation by debt type
        base_efforts = {
            "todo_comment": (1, 2),
            "missing_docstring": (1, 4),
            "long_line": (0.5, 1),
            "large_function": (4, 16),
            "high_complexity": (8, 32),
            "duplicate_code": (6, 24),
            "large_file": (16, 64),
            "syntax_error": (2, 8),
            "security_risk": (4, 40),
            "architecture_debt": (40, 160),
            "test_debt": (8, 40),
            "dependency_debt": (4, 24)
        }
        
        min_hours, max_hours = base_efforts.get(debt_type, (4, 16))
        
        # Adjust by severity
        severity_multipliers = {
            "low": 0.5,
            "medium": 1.0,
            "high": 1.5,
            "critical": 2.0
        }
        
        multiplier = severity_multipliers.get(severity, 1.0)
        hours_estimate = (min_hours + max_hours) / 2 * multiplier
        
        # Convert to story points (assuming 6 hours per point)
        size_points = max(1, round(hours_estimate / 6))
        
        # Determine risk factor
        risk_factor = 1.0
        if debt_type in ["architecture_debt", "security_risk", "large_file"]:
            risk_factor = 1.8
        elif debt_type in ["high_complexity", "duplicate_code"]:
            risk_factor = 1.4
        elif debt_type in ["syntax_error", "dependency_debt"]:
            risk_factor = 1.2
        
        # Determine skill level required
        skill_requirements = {
            "architecture_debt": "expert",
            "security_risk": "senior",
            "high_complexity": "senior",
            "large_function": "mid",
            "duplicate_code": "mid",
            "dependency_debt": "mid",
            "test_debt": "mid",
            "todo_comment": "junior",
            "missing_docstring": "junior",
            "long_line": "junior"
        }
        
        skill_level = skill_requirements.get(debt_type, "mid")
        
        # Confidence based on debt type clarity
        confidence_levels = {
            "todo_comment": 0.9,
            "missing_docstring": 0.9,
            "long_line": 0.95,
            "syntax_error": 0.8,
            "large_function": 0.7,
            "duplicate_code": 0.6,
            "high_complexity": 0.5,
            "architecture_debt": 0.3,
            "security_risk": 0.4
        }
        
        confidence = confidence_levels.get(debt_type, 0.6)
        
        return EffortEstimate(
            size_points=size_points,
            hours_estimate=hours_estimate,
            risk_factor=risk_factor,
            skill_level_required=skill_level,
            confidence=confidence
        )
    
    def _assess_business_impact(self, item: Dict[str, Any]) -> BusinessImpact:
        """Assess business impact of debt item."""
        debt_type = item.get("type", "unknown")
        severity = item.get("severity", "medium")
        
        # Base impact scores by debt type (1-10 scale)
        impact_profiles = {
            "security_risk": (9, 8, 7, 9, 10),  # customer, revenue, velocity, quality, security
            "architecture_debt": (6, 7, 9, 8, 4),
            "large_function": (3, 4, 7, 6, 2),
            "high_complexity": (4, 5, 8, 7, 3),
            "duplicate_code": (3, 4, 6, 6, 2),
            "syntax_error": (7, 6, 8, 9, 3),
            "test_debt": (5, 5, 7, 8, 3),
            "dependency_debt": (6, 5, 6, 7, 7),
            "todo_comment": (1, 1, 2, 2, 1),
            "missing_docstring": (2, 2, 4, 3, 1)
        }
        
        base_impacts = impact_profiles.get(debt_type, (3, 3, 5, 5, 3))
        
        # Adjust by severity
        severity_adjustments = {
            "low": 0.6,
            "medium": 1.0,
            "high": 1.4,
            "critical": 1.8
        }
        
        adjustment = severity_adjustments.get(severity, 1.0)
        
        # Apply adjustment and cap at 10
        adjusted_impacts = [min(10, max(1, round(impact * adjustment))) 
                          for impact in base_impacts]
        
        return BusinessImpact(
            customer_impact=adjusted_impacts[0],
            revenue_impact=adjusted_impacts[1],
            team_velocity_impact=adjusted_impacts[2],
            quality_impact=adjusted_impacts[3],
            security_impact=adjusted_impacts[4]
        )
    
    def _calculate_interest_rate(self, item: Dict[str, Any], 
                               business_impact: BusinessImpact) -> InterestRate:
        """Calculate interest rate for technical debt."""
        
        # Base daily cost calculation
        velocity_impact = business_impact.team_velocity_impact
        quality_impact = business_impact.quality_impact
        
        # Daily cost in "developer hours lost"
        daily_cost = (velocity_impact * 0.5) + (quality_impact * 0.3)
        
        # Frequency multiplier based on code location and type
        file_path = item.get("file_path", "")
        debt_type = item.get("type", "unknown")
        
        # Estimate frequency based on file path patterns
        frequency_multiplier = 1.0
        if any(pattern in file_path.lower() for pattern in ["main", "core", "auth", "api"]):
            frequency_multiplier = 2.0
        elif any(pattern in file_path.lower() for pattern in ["util", "helper", "common"]):
            frequency_multiplier = 1.5
        elif any(pattern in file_path.lower() for pattern in ["test", "spec", "config"]):
            frequency_multiplier = 0.5
        
        # Team impact multiplier
        team_impact_multiplier = min(self.team_size, 8) / 5.0  # Normalize around team of 5
        
        # Compound rate - how this debt creates more debt
        compound_rates = {
            "architecture_debt": 0.1,  # Creates 10% more debt monthly
            "duplicate_code": 0.08,
            "high_complexity": 0.05,
            "large_function": 0.03,
            "test_debt": 0.04,
            "security_risk": 0.02,  # Doesn't compound much, but high initial impact
            "todo_comment": 0.01
        }
        
        compound_rate = compound_rates.get(debt_type, 0.02)
        
        return InterestRate(
            daily_cost=daily_cost,
            frequency_multiplier=frequency_multiplier,
            team_impact_multiplier=team_impact_multiplier,
            compound_rate=compound_rate
        )
    
    def _calculate_cost_of_delay(self, interest_rate: InterestRate, 
                               effort: EffortEstimate) -> float:
        """Calculate total cost of delay if debt is not fixed."""
        
        # Estimate delay in days (assuming debt gets fixed eventually)
        estimated_delay_days = effort.hours_estimate / (self.sprint_capacity_hours / 14)  # 2-week sprints
        
        # Calculate cumulative cost
        daily_cost = (interest_rate.daily_cost * 
                     interest_rate.frequency_multiplier * 
                     interest_rate.team_impact_multiplier)
        
        # Add compound interest effect
        compound_effect = (1 + interest_rate.compound_rate) ** (estimated_delay_days / 30)
        
        total_cost = daily_cost * estimated_delay_days * compound_effect
        
        return round(total_cost, 2)
    
    def _categorize_debt_item(self, item: Dict[str, Any]) -> str:
        """Categorize debt item into high-level categories."""
        debt_type = item.get("type", "unknown")
        
        categories = {
            "code_quality": ["large_function", "high_complexity", "duplicate_code", 
                           "long_line", "missing_docstring"],
            "architecture": ["architecture_debt", "large_file"],
            "security": ["security_risk", "hardcoded_secrets"],
            "testing": ["test_debt", "missing_tests"],
            "maintenance": ["todo_comment", "commented_code"],
            "dependencies": ["dependency_debt", "outdated_packages"],
            "infrastructure": ["deployment_debt", "monitoring_gaps"],
            "documentation": ["missing_docstring", "outdated_docs"]
        }
        
        for category, types in categories.items():
            if debt_type in types:
                return category
        
        return "other"
    
    def _generate_impact_tags(self, item: Dict[str, Any], 
                            business_impact: BusinessImpact) -> List[str]:
        """Generate impact tags for debt item."""
        tags = []
        
        if business_impact.security_impact >= 7:
            tags.append("security-critical")
        if business_impact.customer_impact >= 7:
            tags.append("customer-facing")
        if business_impact.revenue_impact >= 7:
            tags.append("revenue-impact")
        if business_impact.team_velocity_impact >= 7:
            tags.append("velocity-blocker")
        if business_impact.quality_impact >= 7:
            tags.append("quality-risk")
        
        # Add effort-based tags
        effort_hours = item.get("effort_estimate", {}).get("hours_estimate", 0)
        if effort_hours <= 4:
            tags.append("quick-win")
        elif effort_hours >= 40:
            tags.append("major-initiative")
        
        return tags
    
    def _calculate_cost_of_delay_score(self, item: Dict[str, Any]) -> float:
        """Calculate priority score using cost-of-delay framework."""
        business_impact = item["business_impact"]
        effort = item["effort_estimate"]
        
        # Business value (weighted average of impacts)
        business_value = (
            business_impact["customer_impact"] * 0.3 +
            business_impact["revenue_impact"] * 0.3 +
            business_impact["quality_impact"] * 0.2 +
            business_impact["team_velocity_impact"] * 0.2
        )
        
        # Urgency (how quickly value decreases)
        urgency = item["interest_rate"]["daily_cost"] * 10  # Scale to 1-10
        urgency = min(10, max(1, urgency))
        
        # Risk reduction
        risk_reduction = business_impact["security_impact"] * 0.6 + business_impact["quality_impact"] * 0.4
        
        # Team productivity impact
        team_productivity = business_impact["team_velocity_impact"]
        
        # Combine with weights
        weights = self.framework_weights["cost_of_delay"]
        numerator = (
            business_value * weights["business_value"] +
            urgency * weights["urgency"] +
            risk_reduction * weights["risk_reduction"] +
            team_productivity * weights["team_productivity"]
        )
        
        # Divide by effort (adjusted for risk)
        effort_adjusted = effort["hours_estimate"] * effort["risk_factor"]
        denominator = max(1, effort_adjusted / 8)  # Normalize to story points
        
        return round(numerator / denominator, 2)
    
    def _calculate_wsjf_score(self, item: Dict[str, Any]) -> float:
        """Calculate priority score using Weighted Shortest Job First (WSJF)."""
        business_impact = item["business_impact"]
        effort = item["effort_estimate"]
        
        # Business value
        business_value = (
            business_impact["customer_impact"] * 0.4 +
            business_impact["revenue_impact"] * 0.6
        )
        
        # Time criticality
        time_criticality = item["cost_of_delay"] / 10  # Normalize
        time_criticality = min(10, max(1, time_criticality))
        
        # Risk reduction
        risk_reduction = (
            business_impact["security_impact"] * 0.5 +
            business_impact["quality_impact"] * 0.5
        )
        
        # Job size (effort)
        job_size = effort["size_points"]
        
        # WSJF calculation
        numerator = business_value + time_criticality + risk_reduction
        denominator = max(1, job_size)
        
        return round(numerator / denominator, 2)
    
    def _calculate_rice_score(self, item: Dict[str, Any]) -> float:
        """Calculate priority score using RICE framework."""
        business_impact = item["business_impact"]
        effort = item["effort_estimate"]
        
        # Reach (how many developers/users affected)
        reach = min(10, self.team_size * business_impact["team_velocity_impact"] / 5)
        
        # Impact
        impact = (
            business_impact["customer_impact"] * 0.3 +
            business_impact["revenue_impact"] * 0.3 +
            business_impact["quality_impact"] * 0.4
        )
        
        # Confidence
        confidence = effort["confidence"] * 10
        
        # Effort
        effort_score = effort["size_points"]
        
        # RICE calculation
        rice_score = (reach * impact * confidence) / max(1, effort_score)
        
        return round(rice_score, 2)
    
    def _generate_sprint_allocation(self) -> Dict[str, Any]:
        """Generate sprint allocation recommendations."""
        # Calculate total effort needed
        total_effort_hours = sum(item["effort_estimate"]["hours_estimate"] 
                               for item in self.prioritized_items)
        
        # Assume 20% of sprint capacity goes to tech debt
        debt_capacity_per_sprint = self.sprint_capacity_hours * 0.2
        
        # Allocate items to sprints
        sprints = []
        current_sprint = {"sprint_number": 1, "items": [], "total_hours": 0, "capacity_used": 0}
        
        for item in self.prioritized_items:
            item_effort = item["effort_estimate"]["hours_estimate"]
            
            if current_sprint["total_hours"] + item_effort <= debt_capacity_per_sprint:
                current_sprint["items"].append(item)
                current_sprint["total_hours"] += item_effort
                current_sprint["capacity_used"] = current_sprint["total_hours"] / debt_capacity_per_sprint
            else:
                # Start new sprint
                sprints.append(current_sprint)
                current_sprint = {
                    "sprint_number": len(sprints) + 1,
                    "items": [item],
                    "total_hours": item_effort,
                    "capacity_used": item_effort / debt_capacity_per_sprint
                }
        
        # Add the last sprint
        if current_sprint["items"]:
            sprints.append(current_sprint)
        
        # Calculate summary statistics
        total_sprints_needed = len(sprints)
        high_priority_items = len([item for item in self.prioritized_items 
                                 if item.get("priority", "medium") in ["high", "critical"]])
        
        return {
            "total_debt_hours": round(total_effort_hours, 1),
            "debt_capacity_per_sprint": debt_capacity_per_sprint,
            "total_sprints_needed": total_sprints_needed,
            "high_priority_items": high_priority_items,
            "sprint_plan": sprints[:6],  # Show first 6 sprints
            "recommendations": [
                f"Allocate {debt_capacity_per_sprint} hours per sprint to tech debt",
                f"Focus on {high_priority_items} high-priority items first",
                f"Estimated {total_sprints_needed} sprints to clear current backlog"
            ]
        }
    
    def _generate_insights(self) -> Dict[str, Any]:
        """Generate insights from the prioritized debt analysis."""
        
        # Category distribution
        categories = Counter(item["category"] for item in self.prioritized_items)
        
        # Effort distribution
        total_effort = sum(item["effort_estimate"]["hours_estimate"] 
                          for item in self.prioritized_items)
        effort_by_category = defaultdict(float)
        for item in self.prioritized_items:
            effort_by_category[item["category"]] += item["effort_estimate"]["hours_estimate"]
        
        # Priority distribution
        priorities = Counter()
        for item in self.prioritized_items:
            score = item["priority_score"]
            if score >= 8:
                priorities["critical"] += 1
            elif score >= 5:
                priorities["high"] += 1
            elif score >= 2:
                priorities["medium"] += 1
            else:
                priorities["low"] += 1
        
        # Risk analysis
        high_risk_items = [item for item in self.prioritized_items 
                          if item["effort_estimate"]["risk_factor"] >= 1.5]
        
        # Quick wins identification
        quick_wins = [item for item in self.prioritized_items 
                     if (item["effort_estimate"]["hours_estimate"] <= 8 and 
                         item["priority_score"] >= 3)]
        
        # Cost analysis
        total_cost_of_delay = sum(item["cost_of_delay"] for item in self.prioritized_items)
        avg_interest_rate = sum(item["interest_rate"]["daily_cost"] 
                              for item in self.prioritized_items) / len(self.prioritized_items)
        
        return {
            "category_distribution": dict(categories),
            "total_effort_hours": round(total_effort, 1),
            "effort_by_category": {k: round(v, 1) for k, v in effort_by_category.items()},
            "priority_distribution": dict(priorities),
            "high_risk_items_count": len(high_risk_items),
            "quick_wins_count": len(quick_wins),
            "total_cost_of_delay": round(total_cost_of_delay, 1),
            "average_daily_interest_rate": round(avg_interest_rate, 2),
            "top_categories_by_effort": sorted(effort_by_category.items(), 
                                             key=lambda x: x[1], reverse=True)[:3]
        }
    
    def _generate_charts_data(self) -> Dict[str, Any]:
        """Generate data for charts and visualizations."""
        
        # Priority vs Effort scatter plot data
        scatter_data = []
        for item in self.prioritized_items:
            scatter_data.append({
                "x": item["effort_estimate"]["hours_estimate"],
                "y": item["priority_score"],
                "label": item.get("description", "")[:50],
                "category": item["category"],
                "size": item["cost_of_delay"]
            })
        
        # Category effort distribution (pie chart)
        effort_by_category = defaultdict(float)
        for item in self.prioritized_items:
            effort_by_category[item["category"]] += item["effort_estimate"]["hours_estimate"]
        
        pie_data = [{"category": k, "effort": round(v, 1)} 
                   for k, v in effort_by_category.items()]
        
        # Priority timeline (bar chart)
        timeline_data = []
        cumulative_effort = 0
        for i, item in enumerate(self.prioritized_items[:20]):  # Top 20 items
            cumulative_effort += item["effort_estimate"]["hours_estimate"]
            timeline_data.append({
                "item_rank": i + 1,
                "description": item.get("description", "")[:30],
                "effort": item["effort_estimate"]["hours_estimate"],
                "cumulative_effort": round(cumulative_effort, 1),
                "priority_score": item["priority_score"]
            })
        
        # Interest rate trend (line chart data structure)
        interest_trend_data = []
        for i, item in enumerate(self.prioritized_items):
            interest_trend_data.append({
                "item_index": i,
                "daily_cost": item["interest_rate"]["daily_cost"],
                "category": item["category"]
            })
        
        return {
            "priority_effort_scatter": scatter_data,
            "category_effort_distribution": pie_data,
            "priority_timeline": timeline_data,
            "interest_rate_trend": interest_trend_data[:50]  # Limit for performance
        }
    
    def _generate_recommendations(self) -> List[str]:
        """Generate actionable recommendations based on analysis."""
        recommendations = []
        
        insights = self._generate_insights()
        
        # Quick wins recommendation
        if insights["quick_wins_count"] > 0:
            recommendations.append(
                f"Start with {insights['quick_wins_count']} quick wins to build momentum "
                "and demonstrate immediate value from tech debt reduction efforts."
            )
        
        # High-risk items
        if insights["high_risk_items_count"] > 5:
            recommendations.append(
                f"Plan careful execution for {insights['high_risk_items_count']} high-risk items. "
                "Consider pair programming, extra testing, and incremental approaches."
            )
        
        # Category focus
        top_category = insights["top_categories_by_effort"][0][0]
        recommendations.append(
            f"Focus initial efforts on '{top_category}' category debt, which represents "
            f"the largest effort investment ({insights['top_categories_by_effort'][0][1]:.1f} hours)."
        )
        
        # Cost of delay urgency
        if insights["average_daily_interest_rate"] > 5:
            recommendations.append(
                f"High average daily interest rate ({insights['average_daily_interest_rate']:.1f}) "
                "suggests urgent action needed. Consider increasing tech debt budget allocation."
            )
        
        # Sprint planning
        sprints_needed = len(self.prioritized_items) / 10  # Rough estimate
        if sprints_needed > 12:
            recommendations.append(
                "Large debt backlog detected. Consider dedicating entire sprints to debt reduction "
                "rather than trying to fit debt work around features."
            )
        
        # Team capacity
        total_effort = insights["total_effort_hours"]
        weeks_needed = total_effort / (self.sprint_capacity_hours * 0.2)
        if weeks_needed > 26:  # Half a year
            recommendations.append(
                f"With current capacity allocation, debt backlog will take {weeks_needed:.0f} weeks. "
                "Consider increasing tech debt budget or focusing on highest-impact items only."
            )
        
        return recommendations


def format_prioritized_report(analysis_result: Dict[str, Any]) -> str:
    """Format the prioritization analysis in human-readable format."""
    output = []
    
    # Header
    output.append("=" * 60)
    output.append("TECHNICAL DEBT PRIORITIZATION REPORT")
    output.append("=" * 60)
    metadata = analysis_result["metadata"]
    output.append(f"Analysis Date: {metadata['analysis_date']}")
    output.append(f"Framework: {metadata['framework_used'].upper()}")
    output.append(f"Team Size: {metadata['team_size']}")
    output.append(f"Sprint Capacity: {metadata['sprint_capacity_hours']} hours")
    output.append("")
    
    # Executive Summary
    insights = analysis_result["insights"]
    output.append("EXECUTIVE SUMMARY")
    output.append("-" * 30)
    output.append(f"Total Debt Items: {metadata['total_items_analyzed']}")
    output.append(f"Total Effort Required: {insights['total_effort_hours']} hours")
    output.append(f"Total Cost of Delay: ${insights['total_cost_of_delay']:,.0f}")
    output.append(f"Quick Wins Available: {insights['quick_wins_count']}")
    output.append(f"High-Risk Items: {insights['high_risk_items_count']}")
    output.append("")
    
    # Sprint Plan
    sprint_plan = analysis_result["sprint_allocation"]
    output.append("SPRINT ALLOCATION PLAN")
    output.append("-" * 30)
    output.append(f"Sprints Needed: {sprint_plan['total_sprints_needed']}")
    output.append(f"Hours per Sprint: {sprint_plan['debt_capacity_per_sprint']}")
    output.append("")
    
    for sprint in sprint_plan["sprint_plan"][:3]:  # Show first 3 sprints
        output.append(f"Sprint {sprint['sprint_number']} ({sprint['capacity_used']:.0%} capacity):")
        for item in sprint["items"][:3]:  # Top 3 items per sprint
            output.append(f"  • {item['description'][:50]}...")
            output.append(f"    Effort: {item['effort_estimate']['hours_estimate']:.1f}h, "
                        f"Priority: {item['priority_score']}")
        output.append("")
    
    # Top Priority Items
    output.append("TOP 10 PRIORITY ITEMS")
    output.append("-" * 30)
    for i, item in enumerate(analysis_result["prioritized_backlog"][:10], 1):
        output.append(f"{i}. [{item['priority_score']:.1f}] {item['description']}")
        output.append(f"   Category: {item['category']}, "
                    f"Effort: {item['effort_estimate']['hours_estimate']:.1f}h, "
                    f"Cost of Delay: ${item['cost_of_delay']:.0f}")
        if item["impact_tags"]:
            output.append(f"   Tags: {', '.join(item['impact_tags'])}")
        output.append("")
    
    # Recommendations
    output.append("RECOMMENDATIONS")
    output.append("-" * 30)
    for i, rec in enumerate(analysis_result["recommendations"], 1):
        output.append(f"{i}. {rec}")
        output.append("")
    
    return "\n".join(output)


def main():
    """Main entry point for the debt prioritizer."""
    parser = argparse.ArgumentParser(description="Prioritize technical debt backlog")
    parser.add_argument("inventory_file", help="Path to debt inventory JSON file")
    parser.add_argument("--output", help="Output file path")
    parser.add_argument("--format", choices=["json", "text", "both"], 
                       default="both", help="Output format")
    parser.add_argument("--framework", choices=["cost_of_delay", "wsjf", "rice"],
                       default="cost_of_delay", help="Prioritization framework")
    parser.add_argument("--team-size", type=int, default=5, help="Team size")
    parser.add_argument("--sprint-capacity", type=int, default=80, 
                       help="Sprint capacity in hours")
    
    args = parser.parse_args()
    
    # Initialize prioritizer
    prioritizer = DebtPrioritizer(args.team_size, args.sprint_capacity)
    
    # Load inventory
    if not prioritizer.load_debt_inventory(args.inventory_file):
        sys.exit(1)
    
    # Analyze and prioritize
    try:
        analysis_result = prioritizer.analyze_and_prioritize(args.framework)
    except Exception as e:
        print(f"Analysis failed: {e}")
        sys.exit(1)
    
    # Output results
    if args.format in ["json", "both"]:
        json_output = json.dumps(analysis_result, indent=2, default=str)
        if args.output:
            output_path = args.output if args.output.endswith('.json') else f"{args.output}.json"
            with open(output_path, 'w') as f:
                f.write(json_output)
            print(f"JSON report written to: {output_path}")
        else:
            print("JSON REPORT:")
            print("=" * 50)
            print(json_output)
    
    if args.format in ["text", "both"]:
        text_output = format_prioritized_report(analysis_result)
        if args.output:
            output_path = args.output if args.output.endswith('.txt') else f"{args.output}.txt"
            with open(output_path, 'w') as f:
                f.write(text_output)
            print(f"Text report written to: {output_path}")
        else:
            print("\nTEXT REPORT:")
            print("=" * 50)
            print(text_output)


if __name__ == "__main__":
    main()