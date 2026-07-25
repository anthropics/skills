#!/usr/bin/env python3
"""
Sprint Health Scorer

Scores sprint health across multiple dimensions including commitment reliability,
scope creep, blocker resolution time, ceremony attendance, and story completion
distribution. Produces composite health scores with actionable recommendations.

Usage:
    python sprint_health_scorer.py sprint_data.json
    python sprint_health_scorer.py sprint_data.json --format json
"""

import argparse
import json
import statistics
import sys
from datetime import datetime, timedelta
from typing import Any, Dict, List, Optional, Tuple


# ---------------------------------------------------------------------------
# Scoring Configuration
# ---------------------------------------------------------------------------

HEALTH_DIMENSIONS = {
    "commitment_reliability": {
        "weight": 0.25,
        "excellent_threshold": 0.95,  # 95%+ commitment achievement
        "good_threshold": 0.85,       # 85%+ commitment achievement
        "poor_threshold": 0.70,       # Below 70% is poor
    },
    "scope_stability": {
        "weight": 0.20,
        "excellent_threshold": 0.05,  # ≤5% scope change
        "good_threshold": 0.15,       # ≤15% scope change
        "poor_threshold": 0.30,       # >30% scope change is poor
    },
    "blocker_resolution": {
        "weight": 0.15,
        "excellent_threshold": 1.0,   # ≤1 day average resolution
        "good_threshold": 3.0,        # ≤3 days average resolution
        "poor_threshold": 7.0,        # >7 days is poor
    },
    "ceremony_engagement": {
        "weight": 0.15,
        "excellent_threshold": 0.95,  # 95%+ attendance
        "good_threshold": 0.85,       # 85%+ attendance
        "poor_threshold": 0.70,       # Below 70% is poor
    },
    "story_completion_distribution": {
        "weight": 0.15,
        "excellent_threshold": 0.80,  # 80%+ stories fully completed
        "good_threshold": 0.65,       # 65%+ stories completed
        "poor_threshold": 0.50,       # Below 50% is poor
    },
    "velocity_predictability": {
        "weight": 0.10,
        "excellent_threshold": 0.10,  # ≤10% CV
        "good_threshold": 0.20,       # ≤20% CV
        "poor_threshold": 0.35,       # >35% CV is poor
    }
}

OVERALL_HEALTH_THRESHOLDS = {
    "excellent": 85,
    "good": 70,
    "fair": 55,
    "poor": 40,
}

STORY_STATUS_MAPPING = {
    "completed": ["done", "completed", "closed", "resolved"],
    "in_progress": ["in progress", "in_progress", "development", "testing"],
    "blocked": ["blocked", "impediment", "waiting"],
    "not_started": ["todo", "to do", "backlog", "new", "open"],
}


# ---------------------------------------------------------------------------
# Data Models
# ---------------------------------------------------------------------------

class Story:
    """Represents a user story within a sprint."""
    
    def __init__(self, data: Dict[str, Any]):
        self.id: str = data.get("id", "")
        self.title: str = data.get("title", "")
        self.points: int = data.get("points", 0)
        self.status: str = data.get("status", "").lower()
        self.assigned_to: str = data.get("assigned_to", "")
        self.created_date: str = data.get("created_date", "")
        self.completed_date: Optional[str] = data.get("completed_date")
        self.blocked_days: int = data.get("blocked_days", 0)
        self.priority: str = data.get("priority", "medium")
        
        # Normalize status
        self.normalized_status = self._normalize_status(self.status)
    
    def _normalize_status(self, status: str) -> str:
        """Normalize status to standard categories."""
        status_lower = status.lower().strip()
        
        for category, statuses in STORY_STATUS_MAPPING.items():
            if status_lower in statuses:
                return category
        
        return "unknown"
    
    @property
    def is_completed(self) -> bool:
        return self.normalized_status == "completed"
    
    @property
    def is_blocked(self) -> bool:
        return self.normalized_status == "blocked" or self.blocked_days > 0


class SprintHealthData:
    """Comprehensive sprint health data model."""
    
    def __init__(self, data: Dict[str, Any]):
        self.sprint_number: int = data.get("sprint_number", 0)
        self.sprint_name: str = data.get("sprint_name", "")
        self.start_date: str = data.get("start_date", "")
        self.end_date: str = data.get("end_date", "")
        self.team_size: int = data.get("team_size", 0)
        self.working_days: int = data.get("working_days", 10)
        
        # Commitment and delivery
        self.planned_points: int = data.get("planned_points", 0)
        self.completed_points: int = data.get("completed_points", 0)
        self.added_points: int = data.get("added_points", 0)
        self.removed_points: int = data.get("removed_points", 0)
        
        # Stories
        story_data = data.get("stories", [])
        self.stories: List[Story] = [Story(story) for story in story_data]
        
        # Blockers
        self.blockers: List[Dict[str, Any]] = data.get("blockers", [])
        
        # Ceremonies
        self.ceremonies: Dict[str, Any] = data.get("ceremonies", {})
        
        # Calculate derived metrics
        self._calculate_derived_metrics()
    
    def _calculate_derived_metrics(self):
        """Calculate derived health metrics."""
        # Commitment reliability
        self.commitment_ratio = (
            self.completed_points / max(self.planned_points, 1)
        )
        
        # Scope change
        total_scope_change = self.added_points + self.removed_points
        self.scope_change_ratio = total_scope_change / max(self.planned_points, 1)
        
        # Story completion distribution
        total_stories = len(self.stories)
        if total_stories > 0:
            completed_stories = sum(1 for story in self.stories if story.is_completed)
            self.story_completion_ratio = completed_stories / total_stories
        else:
            self.story_completion_ratio = 0.0
        
        # Blocked stories analysis
        blocked_stories = [story for story in self.stories if story.is_blocked]
        self.blocked_stories_count = len(blocked_stories)
        self.blocked_points = sum(story.points for story in blocked_stories)


class HealthScoreResult:
    """Complete health scoring results."""
    
    def __init__(self):
        self.dimension_scores: Dict[str, Dict[str, Any]] = {}
        self.overall_score: float = 0.0
        self.health_grade: str = ""
        self.trend_analysis: Dict[str, Any] = {}
        self.recommendations: List[str] = []
        self.detailed_metrics: Dict[str, Any] = {}


# ---------------------------------------------------------------------------
# Scoring Functions
# ---------------------------------------------------------------------------

def score_commitment_reliability(sprints: List[SprintHealthData]) -> Dict[str, Any]:
    """Score commitment reliability across sprints."""
    if not sprints:
        return {"score": 0, "grade": "insufficient_data"}
    
    commitment_ratios = [sprint.commitment_ratio for sprint in sprints]
    avg_commitment = statistics.mean(commitment_ratios)
    consistency = 1.0 - (statistics.stdev(commitment_ratios) if len(commitment_ratios) > 1 else 0)
    
    # Score based on average achievement and consistency
    config = HEALTH_DIMENSIONS["commitment_reliability"]
    base_score = _calculate_dimension_score(avg_commitment, config)
    
    # Penalty for inconsistency
    consistency_bonus = min(10, consistency * 10)
    final_score = min(100, base_score + consistency_bonus)
    
    return {
        "score": final_score,
        "grade": _score_to_grade(final_score),
        "average_commitment": avg_commitment,
        "consistency": consistency,
        "commitment_ratios": commitment_ratios,
        "details": f"Average commitment: {avg_commitment:.1%}, Consistency: {consistency:.1%}"
    }


def score_scope_stability(sprints: List[SprintHealthData]) -> Dict[str, Any]:
    """Score scope stability (low scope change is better)."""
    if not sprints:
        return {"score": 0, "grade": "insufficient_data"}
    
    scope_change_ratios = [sprint.scope_change_ratio for sprint in sprints]
    avg_scope_change = statistics.mean(scope_change_ratios)
    
    # For scope change, lower is better, so invert the scoring
    config = HEALTH_DIMENSIONS["scope_stability"]
    
    if avg_scope_change <= config["excellent_threshold"]:
        score = 90 + (config["excellent_threshold"] - avg_scope_change) * 200
    elif avg_scope_change <= config["good_threshold"]:
        score = 70 + (config["good_threshold"] - avg_scope_change) * 200
    elif avg_scope_change <= config["poor_threshold"]:
        score = 40 + (config["poor_threshold"] - avg_scope_change) * 200
    else:
        score = max(0, 40 - (avg_scope_change - config["poor_threshold"]) * 100)
    
    score = min(100, max(0, score))
    
    return {
        "score": score,
        "grade": _score_to_grade(score),
        "average_scope_change": avg_scope_change,
        "scope_change_ratios": scope_change_ratios,
        "details": f"Average scope change: {avg_scope_change:.1%}"
    }


def score_blocker_resolution(sprints: List[SprintHealthData]) -> Dict[str, Any]:
    """Score blocker resolution efficiency."""
    if not sprints:
        return {"score": 0, "grade": "insufficient_data"}
    
    all_blockers = []
    for sprint in sprints:
        all_blockers.extend(sprint.blockers)
    
    if not all_blockers:
        return {
            "score": 100,
            "grade": "excellent",
            "average_resolution_time": 0,
            "details": "No blockers reported"
        }
    
    # Calculate average resolution time
    resolution_times = []
    for blocker in all_blockers:
        resolution_time = blocker.get("resolution_days", 0)
        if resolution_time > 0:
            resolution_times.append(resolution_time)
    
    if not resolution_times:
        return {"score": 50, "grade": "fair", "details": "No resolution time data"}
    
    avg_resolution_time = statistics.mean(resolution_times)
    
    # Score based on resolution time (lower is better)
    config = HEALTH_DIMENSIONS["blocker_resolution"]
    
    if avg_resolution_time <= config["excellent_threshold"]:
        score = 95
    elif avg_resolution_time <= config["good_threshold"]:
        score = 80 - (avg_resolution_time - config["excellent_threshold"]) * 10
    elif avg_resolution_time <= config["poor_threshold"]:
        score = 60 - (avg_resolution_time - config["good_threshold"]) * 5
    else:
        score = max(20, 40 - (avg_resolution_time - config["poor_threshold"]) * 3)
    
    return {
        "score": score,
        "grade": _score_to_grade(score),
        "average_resolution_time": avg_resolution_time,
        "total_blockers": len(all_blockers),
        "resolved_blockers": len(resolution_times),
        "details": f"Average resolution: {avg_resolution_time:.1f} days from {len(all_blockers)} blockers"
    }


def score_ceremony_engagement(sprints: List[SprintHealthData]) -> Dict[str, Any]:
    """Score team engagement in scrum ceremonies."""
    if not sprints:
        return {"score": 0, "grade": "insufficient_data"}
    
    ceremony_scores = []
    ceremony_details = {}
    
    for sprint in sprints:
        ceremonies = sprint.ceremonies
        sprint_ceremony_scores = []
        
        for ceremony_name, ceremony_data in ceremonies.items():
            if isinstance(ceremony_data, dict):
                attendance_rate = ceremony_data.get("attendance_rate", 0)
                engagement_score = ceremony_data.get("engagement_score", 0)
                
                # Weight attendance more heavily than engagement
                ceremony_score = (attendance_rate * 0.7) + (engagement_score * 0.3)
                sprint_ceremony_scores.append(ceremony_score)
                
                if ceremony_name not in ceremony_details:
                    ceremony_details[ceremony_name] = []
                ceremony_details[ceremony_name].append({
                    "sprint": sprint.sprint_number,
                    "attendance": attendance_rate,
                    "engagement": engagement_score,
                    "score": ceremony_score
                })
        
        if sprint_ceremony_scores:
            ceremony_scores.append(statistics.mean(sprint_ceremony_scores))
    
    if not ceremony_scores:
        return {"score": 50, "grade": "fair", "details": "No ceremony data available"}
    
    avg_ceremony_score = statistics.mean(ceremony_scores)
    
    config = HEALTH_DIMENSIONS["ceremony_engagement"]
    score = _calculate_dimension_score(avg_ceremony_score, config)
    
    return {
        "score": score,
        "grade": _score_to_grade(score),
        "average_ceremony_score": avg_ceremony_score,
        "ceremony_details": ceremony_details,
        "details": f"Average ceremony engagement: {avg_ceremony_score:.1%}"
    }


def score_story_completion_distribution(sprints: List[SprintHealthData]) -> Dict[str, Any]:
    """Score how well stories are completed vs. partially done."""
    if not sprints:
        return {"score": 0, "grade": "insufficient_data"}
    
    completion_ratios = []
    story_analysis = {
        "total_stories": 0,
        "completed_stories": 0,
        "blocked_stories": 0,
        "partial_completion": 0
    }
    
    for sprint in sprints:
        if sprint.stories:
            sprint_completion = sprint.story_completion_ratio
            completion_ratios.append(sprint_completion)
            
            story_analysis["total_stories"] += len(sprint.stories)
            story_analysis["completed_stories"] += sum(1 for s in sprint.stories if s.is_completed)
            story_analysis["blocked_stories"] += sum(1 for s in sprint.stories if s.is_blocked)
    
    if not completion_ratios:
        return {"score": 50, "grade": "fair", "details": "No story data available"}
    
    avg_completion_ratio = statistics.mean(completion_ratios)
    
    config = HEALTH_DIMENSIONS["story_completion_distribution"]
    score = _calculate_dimension_score(avg_completion_ratio, config)
    
    # Penalty for high number of blocked stories
    if story_analysis["total_stories"] > 0:
        blocked_ratio = story_analysis["blocked_stories"] / story_analysis["total_stories"]
        if blocked_ratio > 0.20:  # More than 20% blocked
            score = max(0, score - (blocked_ratio - 0.20) * 100)
    
    return {
        "score": score,
        "grade": _score_to_grade(score),
        "average_completion_ratio": avg_completion_ratio,
        "story_analysis": story_analysis,
        "details": f"Average story completion: {avg_completion_ratio:.1%}"
    }


def score_velocity_predictability(sprints: List[SprintHealthData]) -> Dict[str, Any]:
    """Score velocity predictability based on coefficient of variation."""
    if len(sprints) < 2:
        return {"score": 50, "grade": "fair", "details": "Insufficient sprints for predictability analysis"}
    
    velocities = [sprint.completed_points for sprint in sprints]
    mean_velocity = statistics.mean(velocities)
    
    if mean_velocity == 0:
        return {"score": 0, "grade": "poor", "details": "No velocity recorded"}
    
    velocity_cv = statistics.stdev(velocities) / mean_velocity
    
    # Lower CV is better for predictability
    config = HEALTH_DIMENSIONS["velocity_predictability"]
    
    if velocity_cv <= config["excellent_threshold"]:
        score = 95
    elif velocity_cv <= config["good_threshold"]:
        score = 80 - (velocity_cv - config["excellent_threshold"]) * 150
    elif velocity_cv <= config["poor_threshold"]:
        score = 60 - (velocity_cv - config["good_threshold"]) * 100
    else:
        score = max(20, 40 - (velocity_cv - config["poor_threshold"]) * 50)
    
    return {
        "score": score,
        "grade": _score_to_grade(score),
        "coefficient_of_variation": velocity_cv,
        "mean_velocity": mean_velocity,
        "velocity_std_dev": statistics.stdev(velocities),
        "details": f"Velocity CV: {velocity_cv:.1%} (lower is more predictable)"
    }


def _calculate_dimension_score(value: float, config: Dict[str, Any]) -> float:
    """Calculate dimension score based on thresholds."""
    if value >= config["excellent_threshold"]:
        return 95
    elif value >= config["good_threshold"]:
        # Linear interpolation between good and excellent
        range_size = config["excellent_threshold"] - config["good_threshold"]
        position = (value - config["good_threshold"]) / range_size
        return 80 + (position * 15)
    elif value >= config["poor_threshold"]:
        # Linear interpolation between poor and good
        range_size = config["good_threshold"] - config["poor_threshold"]
        position = (value - config["poor_threshold"]) / range_size
        return 50 + (position * 30)
    else:
        # Below poor threshold
        return max(20, 50 - (config["poor_threshold"] - value) * 100)


def _score_to_grade(score: float) -> str:
    """Convert numerical score to letter grade."""
    if score >= OVERALL_HEALTH_THRESHOLDS["excellent"]:
        return "excellent"
    elif score >= OVERALL_HEALTH_THRESHOLDS["good"]:
        return "good"
    elif score >= OVERALL_HEALTH_THRESHOLDS["fair"]:
        return "fair"
    else:
        return "poor"


# ---------------------------------------------------------------------------
# Main Analysis Function
# ---------------------------------------------------------------------------

def analyze_sprint_health(data: Dict[str, Any]) -> HealthScoreResult:
    """Perform comprehensive sprint health analysis."""
    result = HealthScoreResult()
    
    try:
        # Parse sprint data
        sprint_records = data.get("sprints", [])
        sprints = [SprintHealthData(record) for record in sprint_records]
        
        if not sprints:
            raise ValueError("No sprint data found")
        
        # Sort by sprint number
        sprints.sort(key=lambda s: s.sprint_number)
        
        # Calculate dimension scores
        dimensions = {
            "commitment_reliability": score_commitment_reliability,
            "scope_stability": score_scope_stability,
            "blocker_resolution": score_blocker_resolution,
            "ceremony_engagement": score_ceremony_engagement,
            "story_completion_distribution": score_story_completion_distribution,
            "velocity_predictability": score_velocity_predictability,
        }
        
        weighted_scores = []
        
        for dimension_name, scoring_func in dimensions.items():
            dimension_result = scoring_func(sprints)
            result.dimension_scores[dimension_name] = dimension_result
            
            # Calculate weighted contribution
            weight = HEALTH_DIMENSIONS[dimension_name]["weight"]
            weighted_score = dimension_result["score"] * weight
            weighted_scores.append(weighted_score)
        
        # Calculate overall score
        result.overall_score = sum(weighted_scores)
        result.health_grade = _score_to_grade(result.overall_score)
        
        # Generate detailed metrics
        result.detailed_metrics = _generate_detailed_metrics(sprints)
        
        # Generate recommendations
        result.recommendations = _generate_health_recommendations(result)
        
    except Exception as e:
        result.dimension_scores = {"error": str(e)}
        result.overall_score = 0
    
    return result


def _generate_detailed_metrics(sprints: List[SprintHealthData]) -> Dict[str, Any]:
    """Generate detailed metrics for analysis."""
    metrics = {
        "sprint_count": len(sprints),
        "date_range": {
            "start": sprints[0].start_date if sprints else "",
            "end": sprints[-1].end_date if sprints else "",
        },
        "team_metrics": {},
        "story_metrics": {},
        "blocker_metrics": {},
    }
    
    if not sprints:
        return metrics
    
    # Team metrics
    team_sizes = [sprint.team_size for sprint in sprints if sprint.team_size > 0]
    if team_sizes:
        metrics["team_metrics"] = {
            "average_team_size": statistics.mean(team_sizes),
            "team_size_stability": statistics.stdev(team_sizes) if len(team_sizes) > 1 else 0,
        }
    
    # Story metrics
    all_stories = []
    for sprint in sprints:
        all_stories.extend(sprint.stories)
    
    if all_stories:
        story_points = [story.points for story in all_stories if story.points > 0]
        metrics["story_metrics"] = {
            "total_stories": len(all_stories),
            "average_story_points": statistics.mean(story_points) if story_points else 0,
            "completed_stories": sum(1 for story in all_stories if story.is_completed),
            "blocked_stories": sum(1 for story in all_stories if story.is_blocked),
        }
    
    # Blocker metrics
    all_blockers = []
    for sprint in sprints:
        all_blockers.extend(sprint.blockers)
    
    if all_blockers:
        resolution_times = [b.get("resolution_days", 0) for b in all_blockers if b.get("resolution_days", 0) > 0]
        metrics["blocker_metrics"] = {
            "total_blockers": len(all_blockers),
            "resolved_blockers": len(resolution_times),
            "average_resolution_days": statistics.mean(resolution_times) if resolution_times else 0,
        }
    
    return metrics


def _generate_health_recommendations(result: HealthScoreResult) -> List[str]:
    """Generate actionable recommendations based on health scores."""
    recommendations = []
    
    # Overall health recommendations
    if result.overall_score < OVERALL_HEALTH_THRESHOLDS["poor"]:
        recommendations.append("CRITICAL: Sprint health is poor across multiple dimensions. Immediate intervention required.")
    elif result.overall_score < OVERALL_HEALTH_THRESHOLDS["fair"]:
        recommendations.append("Sprint health needs improvement. Focus on top 2-3 problem areas.")
    elif result.overall_score >= OVERALL_HEALTH_THRESHOLDS["excellent"]:
        recommendations.append("Excellent sprint health! Maintain current practices and share learnings with other teams.")
    
    # Dimension-specific recommendations
    for dimension, scores in result.dimension_scores.items():
        if isinstance(scores, dict) and "score" in scores:
            score = scores["score"]
            grade = scores["grade"]
            
            if score < 50:  # Poor performance
                if dimension == "commitment_reliability":
                    recommendations.append("Improve sprint planning accuracy and realistic capacity estimation.")
                elif dimension == "scope_stability":
                    recommendations.append("Reduce mid-sprint scope changes. Strengthen backlog refinement process.")
                elif dimension == "blocker_resolution":
                    recommendations.append("Implement faster blocker escalation and resolution processes.")
                elif dimension == "ceremony_engagement":
                    recommendations.append("Improve ceremony facilitation and team engagement strategies.")
                elif dimension == "story_completion_distribution":
                    recommendations.append("Focus on completing stories fully rather than starting many partially.")
                elif dimension == "velocity_predictability":
                    recommendations.append("Work on consistent estimation and delivery patterns.")
            
            elif score >= 85:  # Excellent performance
                dimension_name = dimension.replace("_", " ").title()
                recommendations.append(f"Excellent {dimension_name}! Document and share best practices.")
    
    return recommendations


# ---------------------------------------------------------------------------
# Output Formatting
# ---------------------------------------------------------------------------

def format_text_output(result: HealthScoreResult) -> str:
    """Format results as readable text report."""
    lines = []
    lines.append("="*60)
    lines.append("SPRINT HEALTH ANALYSIS REPORT")
    lines.append("="*60)
    lines.append("")
    
    if "error" in result.dimension_scores:
        lines.append(f"ERROR: {result.dimension_scores['error']}")
        return "\n".join(lines)
    
    # Overall health summary
    lines.append("OVERALL HEALTH SUMMARY")
    lines.append("-"*30)
    lines.append(f"Health Score: {result.overall_score:.1f}/100")
    lines.append(f"Health Grade: {result.health_grade.title()}")
    lines.append("")
    
    # Dimension scores
    lines.append("DIMENSION SCORES")
    lines.append("-"*30)
    
    for dimension, scores in result.dimension_scores.items():
        if isinstance(scores, dict) and "score" in scores:
            dimension_name = dimension.replace("_", " ").title()
            weight = HEALTH_DIMENSIONS[dimension]["weight"]
            lines.append(f"{dimension_name} (Weight: {weight:.0%})")
            lines.append(f"  Score: {scores['score']:.1f}/100 ({scores['grade'].title()})")
            lines.append(f"  Details: {scores['details']}")
            lines.append("")
    
    # Detailed metrics
    metrics = result.detailed_metrics
    if metrics:
        lines.append("DETAILED METRICS")
        lines.append("-"*30)
        lines.append(f"Sprints Analyzed: {metrics.get('sprint_count', 0)}")
        
        if "team_metrics" in metrics and metrics["team_metrics"]:
            team = metrics["team_metrics"]
            lines.append(f"Average Team Size: {team.get('average_team_size', 0):.1f}")
        
        if "story_metrics" in metrics and metrics["story_metrics"]:
            stories = metrics["story_metrics"]
            lines.append(f"Total Stories: {stories.get('total_stories', 0)}")
            lines.append(f"Completed Stories: {stories.get('completed_stories', 0)}")
            lines.append(f"Blocked Stories: {stories.get('blocked_stories', 0)}")
        
        if "blocker_metrics" in metrics and metrics["blocker_metrics"]:
            blockers = metrics["blocker_metrics"]
            lines.append(f"Total Blockers: {blockers.get('total_blockers', 0)}")
            lines.append(f"Average Resolution Time: {blockers.get('average_resolution_days', 0):.1f} days")
        
        lines.append("")
    
    # Recommendations
    if result.recommendations:
        lines.append("RECOMMENDATIONS")
        lines.append("-"*30)
        for i, rec in enumerate(result.recommendations, 1):
            lines.append(f"{i}. {rec}")
    
    return "\n".join(lines)


def format_json_output(result: HealthScoreResult) -> Dict[str, Any]:
    """Format results as JSON."""
    return {
        "overall_score": result.overall_score,
        "health_grade": result.health_grade,
        "dimension_scores": result.dimension_scores,
        "detailed_metrics": result.detailed_metrics,
        "recommendations": result.recommendations,
    }


# ---------------------------------------------------------------------------
# CLI Interface
# ---------------------------------------------------------------------------

def main() -> int:
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Analyze sprint health across multiple dimensions"
    )
    parser.add_argument(
        "data_file", 
        help="JSON file containing sprint health data"
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
        result = analyze_sprint_health(data)
        
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