#!/usr/bin/env python3
"""
Sprint Velocity Analyzer

Analyzes sprint velocity data to calculate rolling averages, detect trends, forecast
capacity, and identify anomalies. Supports multiple statistical measures and 
probabilistic forecasting for scrum teams.

Usage:
    python velocity_analyzer.py sprint_data.json
    python velocity_analyzer.py sprint_data.json --format json
"""

import argparse
import json
import math
import statistics
import sys
from datetime import datetime, timedelta
from typing import Any, Dict, List, Optional, Tuple, Union


# ---------------------------------------------------------------------------
# Constants and Configuration
# ---------------------------------------------------------------------------

VELOCITY_THRESHOLDS: Dict[str, Dict[str, float]] = {
    "trend_detection": {
        "strong_improvement": 0.15,    # 15% improvement
        "improvement": 0.08,           # 8% improvement
        "stable": 0.05,                # ±5% stable range
        "decline": -0.08,              # 8% decline
        "strong_decline": -0.15,       # 15% decline
    },
    "volatility": {
        "low": 0.15,                   # CV below 15%
        "moderate": 0.25,              # CV 15-25%
        "high": 0.40,                  # CV 25-40%
        "very_high": 0.40,             # CV above 40%
    },
    "anomaly_detection": {
        "outlier_threshold": 2.0,      # Standard deviations from mean
        "extreme_outlier": 3.0,        # Extreme outlier threshold
    }
}

FORECASTING_CONFIG: Dict[str, Any] = {
    "confidence_levels": [0.50, 0.70, 0.85, 0.95],
    "monte_carlo_iterations": 10000,
    "min_sprints_for_forecast": 3,
    "max_sprints_lookback": 8,
}


# ---------------------------------------------------------------------------
# Data Structures and Types
# ---------------------------------------------------------------------------

class SprintData:
    """Represents a single sprint's velocity and metadata."""
    
    def __init__(self, data: Dict[str, Any]):
        self.sprint_number: int = data.get("sprint_number", 0)
        self.sprint_name: str = data.get("sprint_name", "")
        self.start_date: str = data.get("start_date", "")
        self.end_date: str = data.get("end_date", "")
        self.planned_points: int = data.get("planned_points", 0)
        self.completed_points: int = data.get("completed_points", 0)
        self.added_points: int = data.get("added_points", 0)
        self.removed_points: int = data.get("removed_points", 0)
        self.carry_over_points: int = data.get("carry_over_points", 0)
        self.team_capacity: float = data.get("team_capacity", 0.0)
        self.working_days: int = data.get("working_days", 10)
        
        # Calculate derived metrics
        self.velocity: int = self.completed_points
        self.commitment_ratio: float = (
            self.completed_points / max(self.planned_points, 1)
        )
        self.scope_change_ratio: float = (
            (self.added_points + self.removed_points) / max(self.planned_points, 1)
        )


class VelocityAnalysis:
    """Complete velocity analysis results."""
    
    def __init__(self):
        self.summary: Dict[str, Any] = {}
        self.trend_analysis: Dict[str, Any] = {}
        self.forecasting: Dict[str, Any] = {}
        self.anomalies: List[Dict[str, Any]] = []
        self.recommendations: List[str] = []


# ---------------------------------------------------------------------------
# Core Analysis Functions
# ---------------------------------------------------------------------------

def calculate_rolling_averages(sprints: List[SprintData], 
                             window_sizes: List[int] = [3, 5, 8]) -> Dict[int, List[float]]:
    """Calculate rolling averages for different window sizes."""
    velocities = [sprint.velocity for sprint in sprints]
    rolling_averages = {}
    
    for window_size in window_sizes:
        averages = []
        for i in range(len(velocities)):
            start_idx = max(0, i - window_size + 1)
            window = velocities[start_idx:i + 1]
            if len(window) >= min(3, window_size):  # Minimum data points
                averages.append(sum(window) / len(window))
            else:
                averages.append(None)
        rolling_averages[window_size] = averages
    
    return rolling_averages


def detect_trend(sprints: List[SprintData], lookback_sprints: int = 6) -> Dict[str, Any]:
    """Detect velocity trends using linear regression and statistical analysis."""
    if len(sprints) < 3:
        return {"trend": "insufficient_data", "confidence": 0.0}
    
    # Use recent sprints for trend analysis
    recent_sprints = sprints[-lookback_sprints:] if len(sprints) > lookback_sprints else sprints
    velocities = [sprint.velocity for sprint in recent_sprints]
    
    # Calculate linear trend
    n = len(velocities)
    x_values = list(range(n))
    x_mean = sum(x_values) / n
    y_mean = sum(velocities) / n
    
    # Linear regression slope
    numerator = sum((x - x_mean) * (y - y_mean) for x, y in zip(x_values, velocities))
    denominator = sum((x - x_mean) ** 2 for x in x_values)
    
    if denominator == 0:
        slope = 0
    else:
        slope = numerator / denominator
    
    # Calculate correlation coefficient for trend strength
    if n > 2:
        try:
            correlation = statistics.correlation(x_values, velocities)
        except statistics.StatisticsError:
            correlation = 0.0
    else:
        correlation = 0.0
    
    # Determine trend direction and strength
    avg_velocity = statistics.mean(velocities)
    relative_slope = slope / max(avg_velocity, 1)  # Normalize by average velocity
    
    thresholds = VELOCITY_THRESHOLDS["trend_detection"]
    
    if relative_slope > thresholds["strong_improvement"]:
        trend = "strong_improvement"
    elif relative_slope > thresholds["improvement"]:
        trend = "improvement"
    elif relative_slope > -thresholds["stable"]:
        trend = "stable"
    elif relative_slope > thresholds["decline"]:
        trend = "decline"
    else:
        trend = "strong_decline"
    
    return {
        "trend": trend,
        "slope": slope,
        "relative_slope": relative_slope,
        "correlation": abs(correlation),
        "confidence": abs(correlation),
        "recent_sprints_analyzed": len(recent_sprints),
        "average_velocity": avg_velocity,
    }


def calculate_volatility(sprints: List[SprintData]) -> Dict[str, Any]:
    """Calculate velocity volatility and stability metrics."""
    if len(sprints) < 2:
        return {"volatility": "insufficient_data"}
    
    velocities = [sprint.velocity for sprint in sprints]
    mean_velocity = statistics.mean(velocities)
    
    if mean_velocity == 0:
        return {"volatility": "no_velocity"}
    
    # Coefficient of Variation (CV)
    std_dev = statistics.stdev(velocities) if len(velocities) > 1 else 0
    cv = std_dev / mean_velocity
    
    # Classify volatility
    thresholds = VELOCITY_THRESHOLDS["volatility"]
    
    if cv <= thresholds["low"]:
        volatility_level = "low"
    elif cv <= thresholds["moderate"]:
        volatility_level = "moderate"
    elif cv <= thresholds["high"]:
        volatility_level = "high"
    else:
        volatility_level = "very_high"
    
    # Calculate additional stability metrics
    velocity_range = max(velocities) - min(velocities)
    range_ratio = velocity_range / mean_velocity if mean_velocity > 0 else 0
    
    return {
        "volatility": volatility_level,
        "coefficient_of_variation": cv,
        "standard_deviation": std_dev,
        "mean_velocity": mean_velocity,
        "velocity_range": velocity_range,
        "range_ratio": range_ratio,
        "min_velocity": min(velocities),
        "max_velocity": max(velocities),
    }


def detect_anomalies(sprints: List[SprintData]) -> List[Dict[str, Any]]:
    """Detect velocity anomalies using statistical methods."""
    if len(sprints) < 3:
        return []
    
    velocities = [sprint.velocity for sprint in sprints]
    mean_velocity = statistics.mean(velocities)
    std_dev = statistics.stdev(velocities) if len(velocities) > 1 else 0
    
    anomalies = []
    threshold = VELOCITY_THRESHOLDS["anomaly_detection"]["outlier_threshold"]
    extreme_threshold = VELOCITY_THRESHOLDS["anomaly_detection"]["extreme_outlier"]
    
    for i, sprint in enumerate(sprints):
        if std_dev == 0:
            continue
            
        z_score = abs(sprint.velocity - mean_velocity) / std_dev
        
        if z_score >= extreme_threshold:
            anomaly_type = "extreme_outlier"
        elif z_score >= threshold:
            anomaly_type = "outlier"
        else:
            continue
        
        anomalies.append({
            "sprint_number": sprint.sprint_number,
            "sprint_name": sprint.sprint_name,
            "velocity": sprint.velocity,
            "expected_range": (mean_velocity - 2 * std_dev, mean_velocity + 2 * std_dev),
            "z_score": z_score,
            "anomaly_type": anomaly_type,
            "deviation_percentage": ((sprint.velocity - mean_velocity) / mean_velocity) * 100,
        })
    
    return anomalies


def monte_carlo_forecast(sprints: List[SprintData], sprints_ahead: int = 6) -> Dict[str, Any]:
    """Generate probabilistic velocity forecasts using Monte Carlo simulation."""
    if len(sprints) < FORECASTING_CONFIG["min_sprints_for_forecast"]:
        return {"error": "insufficient_historical_data"}
    
    # Use recent sprints for forecasting
    lookback = min(len(sprints), FORECASTING_CONFIG["max_sprints_lookback"])
    recent_sprints = sprints[-lookback:]
    velocities = [sprint.velocity for sprint in recent_sprints]
    
    if not velocities:
        return {"error": "no_velocity_data"}
    
    mean_velocity = statistics.mean(velocities)
    std_dev = statistics.stdev(velocities) if len(velocities) > 1 else 0
    
    # Monte Carlo simulation
    iterations = FORECASTING_CONFIG["monte_carlo_iterations"]
    confidence_levels = FORECASTING_CONFIG["confidence_levels"]
    
    simulated_totals = []
    
    for _ in range(iterations):
        total_points = 0
        for _ in range(sprints_ahead):
            # Sample from normal distribution
            if std_dev > 0:
                simulated_velocity = max(0, random_normal(mean_velocity, std_dev))
            else:
                simulated_velocity = mean_velocity
            total_points += simulated_velocity
        simulated_totals.append(total_points)
    
    # Calculate percentiles for confidence intervals
    simulated_totals.sort()
    forecasts = {}
    
    for confidence in confidence_levels:
        percentile_index = int(confidence * iterations)
        percentile_index = min(percentile_index, iterations - 1)
        forecasts[f"{int(confidence * 100)}%"] = simulated_totals[percentile_index]
    
    return {
        "sprints_ahead": sprints_ahead,
        "historical_sprints_used": lookback,
        "mean_velocity": mean_velocity,
        "velocity_std_dev": std_dev,
        "forecasted_totals": forecasts,
        "average_per_sprint": mean_velocity,
        "expected_total": mean_velocity * sprints_ahead,
    }


def random_normal(mean: float, std_dev: float) -> float:
    """Generate a random number from a normal distribution using Box-Muller transform."""
    import random
    import math
    
    # Box-Muller transformation
    u1 = random.random()
    u2 = random.random()
    
    z0 = math.sqrt(-2 * math.log(u1)) * math.cos(2 * math.pi * u2)
    return mean + z0 * std_dev


def generate_recommendations(analysis: VelocityAnalysis) -> List[str]:
    """Generate actionable recommendations based on velocity analysis."""
    recommendations = []
    
    # Trend-based recommendations
    trend = analysis.trend_analysis.get("trend", "")
    if trend == "strong_decline":
        recommendations.append("URGENT: Address strong declining velocity trend. Review impediments, team capacity, and story complexity.")
    elif trend == "decline":
        recommendations.append("Monitor declining velocity. Consider impediment removal and capacity planning review.")
    elif trend == "strong_improvement":
        recommendations.append("Excellent improvement trend! Document successful practices to maintain momentum.")
    
    # Volatility-based recommendations
    volatility = analysis.summary.get("volatility", {}).get("volatility", "")
    if volatility == "very_high":
        recommendations.append("HIGH PRIORITY: Reduce velocity volatility. Review story sizing, definition of done, and sprint planning process.")
    elif volatility == "high":
        recommendations.append("Work on consistency. Review estimation practices and sprint commitment process.")
    elif volatility == "low":
        recommendations.append("Good velocity stability. Continue current practices.")
    
    # Anomaly-based recommendations
    if len(analysis.anomalies) > 0:
        extreme_anomalies = [a for a in analysis.anomalies if a["anomaly_type"] == "extreme_outlier"]
        if extreme_anomalies:
            recommendations.append(f"Investigate {len(extreme_anomalies)} extreme velocity anomalies for root causes.")
    
    # Commitment ratio recommendations
    commitment_ratios = analysis.summary.get("commitment_analysis", {})
    avg_commitment = commitment_ratios.get("average_commitment_ratio", 1.0)
    if avg_commitment < 0.8:
        recommendations.append("Low sprint commitment achievement. Review capacity planning and story complexity estimation.")
    elif avg_commitment > 1.2:
        recommendations.append("Consistently over-committing. Consider more realistic sprint planning.")
    
    return recommendations


# ---------------------------------------------------------------------------
# Main Analysis Function
# ---------------------------------------------------------------------------

def analyze_velocity(data: Dict[str, Any]) -> VelocityAnalysis:
    """Perform comprehensive velocity analysis."""
    analysis = VelocityAnalysis()
    
    try:
        # Parse sprint data
        sprint_records = data.get("sprints", [])
        sprints = [SprintData(record) for record in sprint_records]
        
        if not sprints:
            raise ValueError("No sprint data found")
        
        # Sort by sprint number
        sprints.sort(key=lambda s: s.sprint_number)
        
        # Basic summary statistics
        velocities = [sprint.velocity for sprint in sprints]
        commitment_ratios = [sprint.commitment_ratio for sprint in sprints]
        scope_change_ratios = [sprint.scope_change_ratio for sprint in sprints]
        
        analysis.summary = {
            "total_sprints": len(sprints),
            "velocity_stats": {
                "mean": statistics.mean(velocities),
                "median": statistics.median(velocities),
                "min": min(velocities),
                "max": max(velocities),
                "total_points": sum(velocities),
            },
            "commitment_analysis": {
                "average_commitment_ratio": statistics.mean(commitment_ratios),
                "commitment_consistency": statistics.stdev(commitment_ratios) if len(commitment_ratios) > 1 else 0,
                "sprints_under_committed": sum(1 for r in commitment_ratios if r < 1.0),
                "sprints_over_committed": sum(1 for r in commitment_ratios if r > 1.0),
            },
            "scope_change_analysis": {
                "average_scope_change": statistics.mean(scope_change_ratios),
                "scope_change_volatility": statistics.stdev(scope_change_ratios) if len(scope_change_ratios) > 1 else 0,
            },
            "rolling_averages": calculate_rolling_averages(sprints),
            "volatility": calculate_volatility(sprints),
        }
        
        # Trend analysis
        analysis.trend_analysis = detect_trend(sprints)
        
        # Forecasting
        analysis.forecasting = monte_carlo_forecast(sprints, sprints_ahead=6)
        
        # Anomaly detection
        analysis.anomalies = detect_anomalies(sprints)
        
        # Generate recommendations
        analysis.recommendations = generate_recommendations(analysis)
        
    except Exception as e:
        analysis.summary = {"error": str(e)}
    
    return analysis


# ---------------------------------------------------------------------------
# Output Formatting
# ---------------------------------------------------------------------------

def format_text_output(analysis: VelocityAnalysis) -> str:
    """Format analysis results as readable text report."""
    lines = []
    lines.append("="*60)
    lines.append("SPRINT VELOCITY ANALYSIS REPORT")
    lines.append("="*60)
    lines.append("")
    
    if "error" in analysis.summary:
        lines.append(f"ERROR: {analysis.summary['error']}")
        return "\n".join(lines)
    
    # Summary section
    summary = analysis.summary
    lines.append("VELOCITY SUMMARY")
    lines.append("-"*30)
    lines.append(f"Total Sprints Analyzed: {summary['total_sprints']}")
    
    velocity_stats = summary.get("velocity_stats", {})
    lines.append(f"Average Velocity: {velocity_stats.get('mean', 0):.1f} points")
    lines.append(f"Median Velocity: {velocity_stats.get('median', 0):.1f} points")
    lines.append(f"Velocity Range: {velocity_stats.get('min', 0)} - {velocity_stats.get('max', 0)} points")
    lines.append(f"Total Points Completed: {velocity_stats.get('total_points', 0)}")
    lines.append("")
    
    # Volatility analysis
    volatility = summary.get("volatility", {})
    lines.append("VELOCITY STABILITY")
    lines.append("-"*30)
    lines.append(f"Volatility Level: {volatility.get('volatility', 'Unknown').replace('_', ' ').title()}")
    lines.append(f"Coefficient of Variation: {volatility.get('coefficient_of_variation', 0):.2%}")
    lines.append(f"Standard Deviation: {volatility.get('standard_deviation', 0):.1f} points")
    lines.append("")
    
    # Trend analysis
    trend_analysis = analysis.trend_analysis
    lines.append("TREND ANALYSIS")
    lines.append("-"*30)
    lines.append(f"Trend Direction: {trend_analysis.get('trend', 'Unknown').replace('_', ' ').title()}")
    lines.append(f"Trend Confidence: {trend_analysis.get('confidence', 0):.1%}")
    lines.append(f"Velocity Change Rate: {trend_analysis.get('relative_slope', 0):.1%} per sprint")
    lines.append("")
    
    # Forecasting
    forecasting = analysis.forecasting
    lines.append("CAPACITY FORECAST (Next 6 Sprints)")
    lines.append("-"*30)
    if "error" not in forecasting:
        lines.append(f"Expected Total: {forecasting.get('expected_total', 0):.0f} points")
        lines.append(f"Average Per Sprint: {forecasting.get('average_per_sprint', 0):.1f} points")
        
        forecasted_totals = forecasting.get("forecasted_totals", {})
        lines.append("Confidence Intervals:")
        for confidence, total in forecasted_totals.items():
            lines.append(f"  {confidence}: {total:.0f} points")
    else:
        lines.append(f"Forecast unavailable: {forecasting.get('error', 'Unknown error')}")
    lines.append("")
    
    # Anomalies
    if analysis.anomalies:
        lines.append("VELOCITY ANOMALIES")
        lines.append("-"*30)
        for anomaly in analysis.anomalies:
            lines.append(f"Sprint {anomaly['sprint_number']} ({anomaly['sprint_name']})")
            lines.append(f"  Velocity: {anomaly['velocity']} points")
            lines.append(f"  Deviation: {anomaly['deviation_percentage']:.1f}%")
            lines.append(f"  Type: {anomaly['anomaly_type'].replace('_', ' ').title()}")
        lines.append("")
    
    # Recommendations
    if analysis.recommendations:
        lines.append("RECOMMENDATIONS")
        lines.append("-"*30)
        for i, rec in enumerate(analysis.recommendations, 1):
            lines.append(f"{i}. {rec}")
    
    return "\n".join(lines)


def format_json_output(analysis: VelocityAnalysis) -> Dict[str, Any]:
    """Format analysis results as JSON."""
    return {
        "summary": analysis.summary,
        "trend_analysis": analysis.trend_analysis,
        "forecasting": analysis.forecasting,
        "anomalies": analysis.anomalies,
        "recommendations": analysis.recommendations,
    }


# ---------------------------------------------------------------------------
# CLI Interface
# ---------------------------------------------------------------------------

def main() -> int:
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Analyze sprint velocity data with trend detection and forecasting"
    )
    parser.add_argument(
        "data_file", 
        help="JSON file containing sprint data"
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
        analysis = analyze_velocity(data)
        
        # Output results
        if args.format == "json":
            output = format_json_output(analysis)
            print(json.dumps(output, indent=2))
        else:
            output = format_text_output(analysis)
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