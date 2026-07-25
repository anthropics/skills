#!/usr/bin/env python3
"""
Risk Matrix Analyzer

Builds probability/impact matrices, calculates risk scores, suggests mitigation 
strategies based on risk category, and tracks risk trends over time. Provides 
comprehensive risk assessment and prioritization for project portfolios.

Usage:
    python risk_matrix_analyzer.py risk_data.json
    python risk_matrix_analyzer.py risk_data.json --format json
"""

import argparse
import json
import statistics
import sys
from datetime import datetime, timedelta
from typing import Any, Dict, List, Optional, Tuple, Union


# ---------------------------------------------------------------------------
# Risk Assessment Configuration
# ---------------------------------------------------------------------------

RISK_CATEGORIES = {
    "technical": {
        "weight": 1.2,
        "description": "Technology, architecture, integration risks",
        "mitigation_strategies": [
            "Proof of concept development",
            "Technical spike implementation",
            "Expert consultation",
            "Alternative technology evaluation",
            "Incremental development approach"
        ]
    },
    "resource": {
        "weight": 1.1,
        "description": "Team capacity, skills, availability risks",
        "mitigation_strategies": [
            "Resource planning and buffer allocation",
            "Skill development and training",
            "Cross-training and knowledge sharing",
            "Contractor or consultant engagement",
            "Timeline adjustment for capacity"
        ]
    },
    "schedule": {
        "weight": 1.0,
        "description": "Timeline, deadline, dependency risks",
        "mitigation_strategies": [
            "Critical path analysis and optimization",
            "Buffer time allocation",
            "Dependency management and coordination",
            "Scope prioritization and phasing",
            "Parallel work streams where possible"
        ]
    },
    "business": {
        "weight": 1.3,
        "description": "Market, customer, competitive risks",
        "mitigation_strategies": [
            "Market research and validation",
            "Customer feedback integration",
            "Competitive analysis monitoring",
            "Stakeholder engagement strategy",
            "Business case validation checkpoints"
        ]
    },
    "financial": {
        "weight": 1.4,
        "description": "Budget, ROI, cost overrun risks",
        "mitigation_strategies": [
            "Detailed cost estimation and tracking",
            "Budget reserve allocation",
            "Regular financial checkpoint reviews",
            "Cost-benefit analysis updates",
            "Alternative funding source identification"
        ]
    },
    "regulatory": {
        "weight": 1.5,
        "description": "Compliance, legal, governance risks",
        "mitigation_strategies": [
            "Legal review and approval processes",
            "Compliance audit preparation",
            "Regulatory body engagement",
            "Documentation and audit trail maintenance",
            "External legal counsel consultation"
        ]
    },
    "external": {
        "weight": 1.0,
        "description": "Vendor, partner, environmental risks",
        "mitigation_strategies": [
            "Vendor assessment and backup options",
            "Contract negotiation and SLA definition",
            "Environmental monitoring and adaptation",
            "Partner relationship management",
            "External dependency tracking"
        ]
    }
}

PROBABILITY_LEVELS = {
    1: {"label": "Very Low", "range": "0-10%", "description": "Highly unlikely to occur"},
    2: {"label": "Low", "range": "11-30%", "description": "Unlikely but possible"},
    3: {"label": "Medium", "range": "31-60%", "description": "Moderate likelihood"},
    4: {"label": "High", "range": "61-85%", "description": "Likely to occur"},
    5: {"label": "Very High", "range": "86-100%", "description": "Almost certain to occur"}
}

IMPACT_LEVELS = {
    1: {"label": "Very Low", "description": "Minimal impact on project success"},
    2: {"label": "Low", "description": "Minor delays or cost increases"},
    3: {"label": "Medium", "description": "Significant impact on timeline/budget"},
    4: {"label": "High", "description": "Major project disruption"},
    5: {"label": "Very High", "description": "Project failure or critical compromise"}
}

RISK_TOLERANCE_THRESHOLDS = {
    "low": 8,      # Risk score <= 8: Accept
    "medium": 15,  # Risk score 9-15: Monitor
    "high": 20,    # Risk score 16-20: Mitigate
    "critical": 25 # Risk score >20: Urgent action
}

MITIGATION_STRATEGIES = {
    "accept": "Monitor risk without active mitigation",
    "avoid": "Eliminate risk through scope or approach changes",
    "mitigate": "Reduce probability or impact through proactive measures",
    "transfer": "Share or transfer risk to third parties",
    "contingency": "Prepare response plan for risk occurrence"
}


# ---------------------------------------------------------------------------
# Data Models
# ---------------------------------------------------------------------------

class Risk:
    """Represents a single project risk with assessment and mitigation data."""
    
    def __init__(self, data: Dict[str, Any]):
        self.id: str = data.get("id", "")
        self.title: str = data.get("title", "")
        self.description: str = data.get("description", "")
        self.category: str = data.get("category", "technical").lower()
        self.probability: int = max(1, min(5, data.get("probability", 3)))
        self.impact: int = max(1, min(5, data.get("impact", 3)))
        self.owner: str = data.get("owner", "")
        self.status: str = data.get("status", "open").lower()
        self.identified_date: str = data.get("identified_date", "")
        self.target_resolution: Optional[str] = data.get("target_resolution")
        self.mitigation_strategy: str = data.get("mitigation_strategy", "").lower()
        self.mitigation_actions: List[str] = data.get("mitigation_actions", [])
        self.cost_impact: Optional[float] = data.get("cost_impact")
        self.schedule_impact: Optional[int] = data.get("schedule_impact_days")
        
        # Calculate derived metrics
        self._calculate_risk_score()
        self._determine_risk_level()
        self._suggest_mitigation_approach()
    
    def _calculate_risk_score(self):
        """Calculate weighted risk score based on category, probability, and impact."""
        base_score = self.probability * self.impact
        category_weight = RISK_CATEGORIES.get(self.category, {}).get("weight", 1.0)
        self.risk_score = base_score * category_weight
    
    def _determine_risk_level(self):
        """Determine risk level based on score thresholds."""
        if self.risk_score <= RISK_TOLERANCE_THRESHOLDS["low"]:
            self.risk_level = "low"
        elif self.risk_score <= RISK_TOLERANCE_THRESHOLDS["medium"]:
            self.risk_level = "medium"
        elif self.risk_score <= RISK_TOLERANCE_THRESHOLDS["high"]:
            self.risk_level = "high"
        else:
            self.risk_level = "critical"
    
    def _suggest_mitigation_approach(self):
        """Suggest mitigation approach based on risk characteristics."""
        if self.risk_level == "low":
            self.suggested_approach = "accept"
        elif self.probability >= 4 and self.impact <= 2:
            self.suggested_approach = "mitigate"  # Likely but low impact
        elif self.probability <= 2 and self.impact >= 4:
            self.suggested_approach = "contingency"  # Unlikely but high impact
        elif self.impact >= 4:
            self.suggested_approach = "avoid"  # High impact risks
        else:
            self.suggested_approach = "mitigate"
    
    @property
    def is_active(self) -> bool:
        return self.status.lower() in ["open", "identified", "monitoring", "mitigating"]
    
    @property
    def is_overdue(self) -> bool:
        if not self.target_resolution:
            return False
        
        try:
            target_date = datetime.strptime(self.target_resolution, "%Y-%m-%d")
            return datetime.now() > target_date and self.is_active
        except ValueError:
            return False


class RiskAnalysisResult:
    """Complete risk analysis results."""
    
    def __init__(self):
        self.summary: Dict[str, Any] = {}
        self.risk_matrix: Dict[str, Any] = {}
        self.category_analysis: Dict[str, Any] = {}
        self.mitigation_analysis: Dict[str, Any] = {}
        self.trend_analysis: Dict[str, Any] = {}
        self.recommendations: List[str] = []


# ---------------------------------------------------------------------------
# Risk Analysis Functions
# ---------------------------------------------------------------------------

def build_risk_matrix(risks: List[Risk]) -> Dict[str, Any]:
    """Build probability/impact risk matrix with risk distribution."""
    matrix = {}
    risk_distribution = {}
    
    # Initialize matrix
    for prob in range(1, 6):
        matrix[prob] = {}
        for impact in range(1, 6):
            matrix[prob][impact] = []
    
    # Populate matrix with risks
    for risk in risks:
        if risk.is_active:
            matrix[risk.probability][risk.impact].append({
                "id": risk.id,
                "title": risk.title,
                "risk_score": risk.risk_score,
                "category": risk.category
            })
    
    # Calculate distribution statistics
    total_risks = len([r for r in risks if r.is_active])
    risk_distribution = {
        "critical": len([r for r in risks if r.is_active and r.risk_level == "critical"]),
        "high": len([r for r in risks if r.is_active and r.risk_level == "high"]),
        "medium": len([r for r in risks if r.is_active and r.risk_level == "medium"]),
        "low": len([r for r in risks if r.is_active and r.risk_level == "low"])
    }
    
    # Calculate risk exposure
    total_score = sum(r.risk_score for r in risks if r.is_active)
    average_score = total_score / max(total_risks, 1)
    
    return {
        "matrix": matrix,
        "distribution": risk_distribution,
        "total_risks": total_risks,
        "total_risk_score": total_score,
        "average_risk_score": average_score,
        "risk_exposure_level": _classify_risk_exposure(average_score)
    }


def analyze_risk_categories(risks: List[Risk]) -> Dict[str, Any]:
    """Analyze risks by category with detailed statistics."""
    category_stats = {}
    active_risks = [r for r in risks if r.is_active]
    
    for category, config in RISK_CATEGORIES.items():
        category_risks = [r for r in active_risks if r.category == category]
        
        if category_risks:
            risk_scores = [r.risk_score for r in category_risks]
            category_stats[category] = {
                "count": len(category_risks),
                "total_score": sum(risk_scores),
                "average_score": statistics.mean(risk_scores),
                "max_score": max(risk_scores),
                "risk_level_distribution": _get_risk_level_distribution(category_risks),
                "top_risks": sorted(category_risks, key=lambda r: r.risk_score, reverse=True)[:3],
                "mitigation_coverage": _calculate_mitigation_coverage(category_risks),
                "suggested_strategies": config["mitigation_strategies"][:3]
            }
        else:
            category_stats[category] = {
                "count": 0,
                "total_score": 0,
                "average_score": 0,
                "risk_level_distribution": {},
                "mitigation_coverage": 0
            }
    
    # Identify highest risk categories
    sorted_categories = sorted(
        [(cat, stats) for cat, stats in category_stats.items() if stats["count"] > 0],
        key=lambda x: x[1]["total_score"],
        reverse=True
    )
    
    return {
        "category_statistics": category_stats,
        "highest_risk_categories": [cat for cat, _ in sorted_categories[:3]],
        "category_concentration": len([c for c in category_stats if category_stats[c]["count"] > 0])
    }


def analyze_mitigation_effectiveness(risks: List[Risk]) -> Dict[str, Any]:
    """Analyze mitigation strategy effectiveness and coverage."""
    active_risks = [r for r in risks if r.is_active]
    
    # Mitigation strategy distribution
    strategy_distribution = {}
    for strategy in MITIGATION_STRATEGIES.keys():
        strategy_risks = [r for r in active_risks if r.mitigation_strategy == strategy]
        if strategy_risks:
            strategy_distribution[strategy] = {
                "count": len(strategy_risks),
                "average_risk_score": statistics.mean([r.risk_score for r in strategy_risks]),
                "risk_levels": _get_risk_level_distribution(strategy_risks)
            }
    
    # Mitigation coverage analysis
    risks_with_mitigation = [r for r in active_risks if r.mitigation_actions]
    mitigation_coverage = len(risks_with_mitigation) / max(len(active_risks), 1)
    
    # Action item analysis
    total_actions = sum(len(r.mitigation_actions) for r in active_risks)
    average_actions_per_risk = total_actions / max(len(active_risks), 1)
    
    # Overdue mitigation analysis
    overdue_risks = [r for r in active_risks if r.is_overdue]
    overdue_rate = len(overdue_risks) / max(len(active_risks), 1)
    
    return {
        "strategy_distribution": strategy_distribution,
        "mitigation_coverage": mitigation_coverage,
        "average_actions_per_risk": average_actions_per_risk,
        "overdue_mitigation_count": len(overdue_risks),
        "overdue_rate": overdue_rate,
        "top_overdue_risks": sorted(overdue_risks, key=lambda r: r.risk_score, reverse=True)[:5]
    }


def analyze_risk_trends(current_risks: List[Risk], historical_data: Optional[List[Dict]] = None) -> Dict[str, Any]:
    """Analyze risk trends over time if historical data is available."""
    if not historical_data:
        return {
            "trend_analysis_available": False,
            "message": "Historical data required for trend analysis"
        }
    
    # Simple trend analysis based on current vs. historical risk levels
    current_total_score = sum(r.risk_score for r in current_risks if r.is_active)
    current_risk_count = len([r for r in current_risks if r.is_active])
    
    # This is a simplified implementation - in practice, you'd track risks over time
    trend_data = {
        "trend_analysis_available": True,
        "current_total_risk_score": current_total_score,
        "current_active_risks": current_risk_count,
        "risk_velocity": {
            "new_risks_rate": "Calculate from historical data",
            "resolution_rate": "Calculate from historical data",
            "escalation_rate": "Calculate from historical data"
        }
    }
    
    return trend_data


def generate_risk_recommendations(risks: List[Risk], analysis_results: Dict[str, Any]) -> List[str]:
    """Generate actionable risk management recommendations."""
    recommendations = []
    
    # Critical risk recommendations
    critical_risks = [r for r in risks if r.is_active and r.risk_level == "critical"]
    if critical_risks:
        recommendations.append(f"URGENT: Address {len(critical_risks)} critical risks immediately. These require executive attention and dedicated resources.")
        
        for risk in critical_risks[:3]:  # Top 3 critical risks
            recommendations.append(f"Critical Risk - {risk.title}: Implement {risk.suggested_approach} strategy within 48 hours.")
    
    # High-concentration category recommendations
    category_analysis = analysis_results.get("category_analysis", {})
    highest_categories = category_analysis.get("highest_risk_categories", [])
    
    if highest_categories:
        top_category = highest_categories[0]
        recommendations.append(f"Focus mitigation efforts on {top_category} risks - highest concentration of risk exposure.")
    
    # Mitigation coverage recommendations
    mitigation_analysis = analysis_results.get("mitigation_analysis", {})
    coverage = mitigation_analysis.get("mitigation_coverage", 0)
    
    if coverage < 0.7:
        recommendations.append("Improve mitigation coverage - less than 70% of risks have defined mitigation actions.")
    
    overdue_rate = mitigation_analysis.get("overdue_rate", 0)
    if overdue_rate > 0.2:
        recommendations.append("Address overdue mitigation actions - more than 20% of risks are past their target resolution date.")
    
    # Risk matrix recommendations
    matrix_analysis = analysis_results.get("risk_matrix", {})
    avg_score = matrix_analysis.get("average_risk_score", 0)
    
    if avg_score > 15:
        recommendations.append("Portfolio risk exposure is high. Consider scope reduction or additional risk mitigation investments.")
    elif avg_score < 8:
        recommendations.append("Risk exposure is well-managed. Consider taking on additional strategic initiatives.")
    
    return recommendations


# ---------------------------------------------------------------------------
# Utility Functions
# ---------------------------------------------------------------------------

def _classify_risk_exposure(average_score: float) -> str:
    """Classify overall portfolio risk exposure level."""
    if average_score > 18:
        return "very_high"
    elif average_score > 15:
        return "high"
    elif average_score > 12:
        return "medium"
    elif average_score > 8:
        return "low"
    else:
        return "very_low"


def _get_risk_level_distribution(risks: List[Risk]) -> Dict[str, int]:
    """Get distribution of risk levels for a set of risks."""
    distribution = {"critical": 0, "high": 0, "medium": 0, "low": 0}
    for risk in risks:
        distribution[risk.risk_level] += 1
    return distribution


def _calculate_mitigation_coverage(risks: List[Risk]) -> float:
    """Calculate percentage of risks with defined mitigation actions."""
    if not risks:
        return 0.0
    
    risks_with_mitigation = sum(1 for r in risks if r.mitigation_actions)
    return risks_with_mitigation / len(risks)


# ---------------------------------------------------------------------------
# Main Analysis Function
# ---------------------------------------------------------------------------

def analyze_risks(data: Dict[str, Any]) -> RiskAnalysisResult:
    """Perform comprehensive risk analysis."""
    result = RiskAnalysisResult()
    
    try:
        # Parse risk data
        risk_records = data.get("risks", [])
        risks = [Risk(record) for record in risk_records]
        
        if not risks:
            raise ValueError("No risk data found")
        
        # Basic summary
        active_risks = [r for r in risks if r.is_active]
        result.summary = {
            "total_risks": len(risks),
            "active_risks": len(active_risks),
            "closed_risks": len(risks) - len(active_risks),
            "critical_risks": len([r for r in active_risks if r.risk_level == "critical"]),
            "high_risks": len([r for r in active_risks if r.risk_level == "high"]),
            "total_risk_exposure": sum(r.risk_score for r in active_risks),
            "average_risk_score": sum(r.risk_score for r in active_risks) / max(len(active_risks), 1),
            "overdue_risks": len([r for r in active_risks if r.is_overdue])
        }
        
        # Risk matrix analysis
        result.risk_matrix = build_risk_matrix(risks)
        
        # Category analysis
        result.category_analysis = analyze_risk_categories(risks)
        
        # Mitigation analysis
        result.mitigation_analysis = analyze_mitigation_effectiveness(risks)
        
        # Trend analysis (simplified without historical data)
        result.trend_analysis = analyze_risk_trends(risks, data.get("historical_data"))
        
        # Generate recommendations
        analysis_data = {
            "category_analysis": result.category_analysis,
            "mitigation_analysis": result.mitigation_analysis,
            "risk_matrix": result.risk_matrix
        }
        result.recommendations = generate_risk_recommendations(risks, analysis_data)
        
    except Exception as e:
        result.summary = {"error": str(e)}
    
    return result


# ---------------------------------------------------------------------------
# Output Formatting
# ---------------------------------------------------------------------------

def format_text_output(result: RiskAnalysisResult) -> str:
    """Format analysis results as readable text report."""
    lines = []
    lines.append("="*60)
    lines.append("RISK MATRIX ANALYSIS REPORT")
    lines.append("="*60)
    lines.append("")
    
    if "error" in result.summary:
        lines.append(f"ERROR: {result.summary['error']}")
        return "\n".join(lines)
    
    # Executive Summary
    summary = result.summary
    lines.append("EXECUTIVE SUMMARY")
    lines.append("-"*30)
    lines.append(f"Total Risks: {summary['total_risks']} ({summary['active_risks']} active)")
    lines.append(f"Risk Exposure: {summary['total_risk_exposure']:.1f} points (avg: {summary['average_risk_score']:.1f})")
    lines.append(f"Critical/High Risks: {summary['critical_risks']}/{summary['high_risks']}")
    lines.append(f"Overdue Mitigations: {summary['overdue_risks']}")
    lines.append("")
    
    # Risk Distribution
    matrix = result.risk_matrix
    lines.append("RISK LEVEL DISTRIBUTION")
    lines.append("-"*30)
    distribution = matrix.get("distribution", {})
    for level in ["critical", "high", "medium", "low"]:
        count = distribution.get(level, 0)
        percentage = (count / max(summary["active_risks"], 1)) * 100
        lines.append(f"{level.title()}: {count} ({percentage:.1f}%)")
    lines.append("")
    
    # Risk Matrix Visualization
    lines.append("RISK MATRIX (Probability vs Impact)")
    lines.append("-"*50)
    lines.append("     1    2    3    4    5   (Impact)")
    
    matrix_data = matrix.get("matrix", {})
    for prob in range(5, 0, -1):
        line = f"{prob} "
        for impact in range(1, 6):
            risk_count = len(matrix_data.get(prob, {}).get(impact, []))
            line += f" [{risk_count:2}]"
        lines.append(line)
    lines.append("(P)")
    lines.append("")
    
    # Category Analysis
    category_analysis = result.category_analysis
    lines.append("RISK BY CATEGORY")
    lines.append("-"*30)
    
    category_stats = category_analysis.get("category_statistics", {})
    for category, stats in category_stats.items():
        if stats["count"] > 0:
            lines.append(f"{category.title()}: {stats['count']} risks, "
                        f"avg score: {stats['average_score']:.1f}, "
                        f"total exposure: {stats['total_score']:.1f}")
    lines.append("")
    
    # Mitigation Analysis
    mitigation = result.mitigation_analysis
    lines.append("MITIGATION EFFECTIVENESS")
    lines.append("-"*30)
    lines.append(f"Mitigation Coverage: {mitigation.get('mitigation_coverage', 0):.1%}")
    lines.append(f"Average Actions per Risk: {mitigation.get('average_actions_per_risk', 0):.1f}")
    lines.append(f"Overdue Mitigations: {mitigation.get('overdue_mitigation_count', 0)} "
                f"({mitigation.get('overdue_rate', 0):.1%})")
    lines.append("")
    
    # Top Risks
    lines.append("TOP RISKS REQUIRING ATTENTION")
    lines.append("-"*30)
    
    # Find top risks across all categories
    all_risks = []
    for category_stats in category_stats.values():
        if "top_risks" in category_stats:
            all_risks.extend(category_stats["top_risks"])
    
    top_risks = sorted(all_risks, key=lambda r: r.risk_score, reverse=True)[:5]
    for i, risk in enumerate(top_risks, 1):
        lines.append(f"{i}. {risk.title} (Score: {risk.risk_score:.1f}, Level: {risk.risk_level.title()})")
        lines.append(f"   Category: {risk.category.title()}, Strategy: {risk.suggested_approach.title()}")
    lines.append("")
    
    # Recommendations
    if result.recommendations:
        lines.append("RECOMMENDATIONS")
        lines.append("-"*30)
        for i, rec in enumerate(result.recommendations, 1):
            lines.append(f"{i}. {rec}")
    
    return "\n".join(lines)


def format_json_output(result: RiskAnalysisResult) -> Dict[str, Any]:
    """Format analysis results as JSON."""
    # Convert Risk objects to dictionaries for JSON serialization
    def serialize_risks(obj):
        if isinstance(obj, list):
            return [serialize_risks(item) for item in obj]
        elif hasattr(obj, 'id') and hasattr(obj, 'title'):  # This is a Risk object
            return {
                "id": obj.id,
                "title": obj.title,
                "risk_score": obj.risk_score,
                "risk_level": obj.risk_level,
                "category": obj.category,
                "probability": obj.probability,
                "impact": obj.impact,
                "status": obj.status
            }
        elif isinstance(obj, dict):
            return {key: serialize_risks(value) for key, value in obj.items()}
        else:
            return obj
    
    # Deep copy and serialize all risk objects recursively
    return serialize_risks({
        "summary": result.summary,
        "risk_matrix": result.risk_matrix,
        "category_analysis": result.category_analysis,
        "mitigation_analysis": result.mitigation_analysis,
        "trend_analysis": result.trend_analysis,
        "recommendations": result.recommendations
    })


# ---------------------------------------------------------------------------
# CLI Interface
# ---------------------------------------------------------------------------

def main() -> int:
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Analyze project risks with probability/impact matrix and mitigation recommendations"
    )
    parser.add_argument(
        "data_file", 
        help="JSON file containing risk register data"
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
        result = analyze_risks(data)
        
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