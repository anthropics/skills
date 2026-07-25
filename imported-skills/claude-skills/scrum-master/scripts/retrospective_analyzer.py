#!/usr/bin/env python3
"""
Retrospective Analyzer

Processes retrospective data to track action item completion rates, identify
recurring themes, measure improvement trends, and generate insights for
continuous team improvement.

Usage:
    python retrospective_analyzer.py retro_data.json
    python retrospective_analyzer.py retro_data.json --format json
"""

import argparse
import json
import re
import statistics
import sys
from collections import Counter, defaultdict
from datetime import datetime, timedelta
from typing import Any, Dict, List, Optional, Set, Tuple


# ---------------------------------------------------------------------------
# Configuration and Constants
# ---------------------------------------------------------------------------

SENTIMENT_KEYWORDS = {
    "positive": [
        "good", "great", "excellent", "awesome", "fantastic", "wonderful",
        "improved", "better", "success", "achievement", "celebration",
        "working well", "effective", "efficient", "smooth", "pleased",
        "happy", "satisfied", "proud", "accomplished", "breakthrough"
    ],
    "negative": [
        "bad", "terrible", "awful", "horrible", "frustrating", "annoying",
        "problem", "issue", "blocker", "impediment", "concern", "worry",
        "difficult", "challenging", "struggling", "failing", "broken",
        "slow", "delayed", "confused", "unclear", "chaos", "stressed"
    ],
    "neutral": [
        "okay", "average", "normal", "standard", "typical", "usual",
        "process", "procedure", "meeting", "discussion", "review",
        "update", "status", "information", "data", "report"
    ]
}

THEME_CATEGORIES = {
    "communication": [
        "communication", "meeting", "standup", "discussion", "feedback",
        "information", "clarity", "understanding", "alignment", "sync",
        "reporting", "updates", "transparency", "visibility"
    ],
    "process": [
        "process", "procedure", "workflow", "methodology", "framework",
        "scrum", "agile", "ceremony", "planning", "retrospective",
        "review", "estimation", "refinement", "definition of done"
    ],
    "technical": [
        "technical", "code", "development", "bug", "testing", "deployment",
        "architecture", "infrastructure", "tools", "technology",
        "performance", "quality", "automation", "ci/cd", "devops"
    ],
    "team_dynamics": [
        "team", "collaboration", "cooperation", "support", "morale",
        "motivation", "engagement", "culture", "relationship", "trust",
        "conflict", "personality", "workload", "capacity", "burnout"
    ],
    "external": [
        "customer", "stakeholder", "management", "product owner", "business",
        "requirement", "priority", "deadline", "budget", "resource",
        "dependency", "vendor", "third party", "integration"
    ]
}

ACTION_PRIORITY_KEYWORDS = {
    "high": ["urgent", "critical", "asap", "immediately", "blocker", "must"],
    "medium": ["important", "should", "needed", "required", "significant"],
    "low": ["nice to have", "consider", "explore", "investigate", "eventually"]
}

COMPLETION_STATUS_MAPPING = {
    "completed": ["done", "completed", "finished", "resolved", "closed", "achieved"],
    "in_progress": ["in progress", "ongoing", "working on", "started", "partial"],
    "blocked": ["blocked", "stuck", "waiting", "dependent", "impediment"],
    "cancelled": ["cancelled", "dropped", "abandoned", "not needed", "deprioritized"],
    "not_started": ["not started", "pending", "todo", "planned", "upcoming"]
}


# ---------------------------------------------------------------------------
# Data Models
# ---------------------------------------------------------------------------

class ActionItem:
    """Represents a single action item from a retrospective."""
    
    def __init__(self, data: Dict[str, Any]):
        self.id: str = data.get("id", "")
        self.description: str = data.get("description", "")
        self.owner: str = data.get("owner", "")
        self.priority: str = data.get("priority", "medium").lower()
        self.due_date: Optional[str] = data.get("due_date")
        self.status: str = data.get("status", "not_started").lower()
        self.created_sprint: int = data.get("created_sprint", 0)
        self.completed_sprint: Optional[int] = data.get("completed_sprint")
        self.category: str = data.get("category", "")
        self.effort_estimate: str = data.get("effort_estimate", "medium")
        
        # Normalize status
        self.normalized_status = self._normalize_status(self.status)
        
        # Infer priority from description if not explicitly set
        if self.priority == "medium":
            self.inferred_priority = self._infer_priority(self.description)
        else:
            self.inferred_priority = self.priority
    
    def _normalize_status(self, status: str) -> str:
        """Normalize status to standard categories."""
        status_lower = status.lower().strip()
        
        for category, statuses in COMPLETION_STATUS_MAPPING.items():
            if any(s in status_lower for s in statuses):
                return category
        
        return "not_started"
    
    def _infer_priority(self, description: str) -> str:
        """Infer priority from description text."""
        description_lower = description.lower()
        
        for priority, keywords in ACTION_PRIORITY_KEYWORDS.items():
            if any(keyword in description_lower for keyword in keywords):
                return priority
        
        return "medium"
    
    @property
    def is_completed(self) -> bool:
        return self.normalized_status == "completed"
    
    @property
    def is_overdue(self) -> bool:
        if not self.due_date:
            return False
        
        try:
            due_date = datetime.strptime(self.due_date, "%Y-%m-%d")
            return datetime.now() > due_date and not self.is_completed
        except ValueError:
            return False


class RetrospectiveData:
    """Represents data from a single retrospective session."""
    
    def __init__(self, data: Dict[str, Any]):
        self.sprint_number: int = data.get("sprint_number", 0)
        self.date: str = data.get("date", "")
        self.facilitator: str = data.get("facilitator", "")
        self.attendees: List[str] = data.get("attendees", [])
        self.duration_minutes: int = data.get("duration_minutes", 0)
        
        # Retrospective categories
        self.went_well: List[str] = data.get("went_well", [])
        self.to_improve: List[str] = data.get("to_improve", [])
        self.action_items_data: List[Dict[str, Any]] = data.get("action_items", [])
        
        # Create action items
        self.action_items: List[ActionItem] = [
            ActionItem({**item, "created_sprint": self.sprint_number})
            for item in self.action_items_data
        ]
        
        # Calculate metrics
        self._calculate_metrics()
    
    def _calculate_metrics(self):
        """Calculate retrospective session metrics."""
        self.total_items = len(self.went_well) + len(self.to_improve)
        self.action_items_count = len(self.action_items)
        self.attendance_rate = len(self.attendees) / max(1, 5)  # Assume team of 5
        
        # Sentiment analysis
        self.sentiment_scores = self._analyze_sentiment()
        
        # Theme analysis
        self.themes = self._extract_themes()
    
    def _analyze_sentiment(self) -> Dict[str, float]:
        """Analyze sentiment of retrospective items."""
        all_text = " ".join(self.went_well + self.to_improve).lower()
        
        sentiment_scores = {}
        for sentiment, keywords in SENTIMENT_KEYWORDS.items():
            count = sum(1 for keyword in keywords if keyword in all_text)
            sentiment_scores[sentiment] = count
        
        # Normalize to percentages
        total_sentiment = sum(sentiment_scores.values())
        if total_sentiment > 0:
            for sentiment in sentiment_scores:
                sentiment_scores[sentiment] = sentiment_scores[sentiment] / total_sentiment
        
        return sentiment_scores
    
    def _extract_themes(self) -> Dict[str, int]:
        """Extract themes from retrospective items."""
        all_text = " ".join(self.went_well + self.to_improve).lower()
        
        theme_counts = {}
        for theme, keywords in THEME_CATEGORIES.items():
            count = sum(1 for keyword in keywords if keyword in all_text)
            if count > 0:
                theme_counts[theme] = count
        
        return theme_counts


class RetroAnalysisResult:
    """Complete retrospective analysis results."""
    
    def __init__(self):
        self.summary: Dict[str, Any] = {}
        self.action_item_analysis: Dict[str, Any] = {}
        self.theme_analysis: Dict[str, Any] = {}
        self.improvement_trends: Dict[str, Any] = {}
        self.recommendations: List[str] = []


# ---------------------------------------------------------------------------
# Analysis Functions
# ---------------------------------------------------------------------------

def analyze_action_item_completion(retros: List[RetrospectiveData]) -> Dict[str, Any]:
    """Analyze action item completion rates and patterns."""
    all_action_items = []
    for retro in retros:
        all_action_items.extend(retro.action_items)
    
    if not all_action_items:
        return {
            "total_action_items": 0,
            "completion_rate": 0.0,
            "average_completion_time": 0.0
        }
    
    # Overall completion statistics
    completed_items = [item for item in all_action_items if item.is_completed]
    completion_rate = len(completed_items) / len(all_action_items)
    
    # Completion time analysis
    completion_times = []
    for item in completed_items:
        if item.completed_sprint and item.created_sprint:
            completion_time = item.completed_sprint - item.created_sprint
            if completion_time >= 0:
                completion_times.append(completion_time)
    
    avg_completion_time = statistics.mean(completion_times) if completion_times else 0.0
    
    # Status distribution
    status_counts = Counter(item.normalized_status for item in all_action_items)
    
    # Priority analysis
    priority_completion = {}
    for priority in ["high", "medium", "low"]:
        priority_items = [item for item in all_action_items if item.inferred_priority == priority]
        if priority_items:
            priority_completed = sum(1 for item in priority_items if item.is_completed)
            priority_completion[priority] = {
                "total": len(priority_items),
                "completed": priority_completed,
                "completion_rate": priority_completed / len(priority_items)
            }
    
    # Owner analysis
    owner_performance = defaultdict(lambda: {"total": 0, "completed": 0})
    for item in all_action_items:
        if item.owner:
            owner_performance[item.owner]["total"] += 1
            if item.is_completed:
                owner_performance[item.owner]["completed"] += 1
    
    for owner in owner_performance:
        owner_data = owner_performance[owner]
        owner_data["completion_rate"] = owner_data["completed"] / owner_data["total"]
    
    # Overdue items
    overdue_items = [item for item in all_action_items if item.is_overdue]
    
    return {
        "total_action_items": len(all_action_items),
        "completion_rate": completion_rate,
        "completed_items": len(completed_items),
        "average_completion_time": avg_completion_time,
        "status_distribution": dict(status_counts),
        "priority_analysis": priority_completion,
        "owner_performance": dict(owner_performance),
        "overdue_items": len(overdue_items),
        "overdue_rate": len(overdue_items) / len(all_action_items) if all_action_items else 0.0
    }


def analyze_recurring_themes(retros: List[RetrospectiveData]) -> Dict[str, Any]:
    """Identify recurring themes across retrospectives."""
    theme_evolution = defaultdict(list)
    sentiment_evolution = defaultdict(list)
    
    # Track themes over time
    for retro in retros:
        sprint = retro.sprint_number
        
        # Theme tracking
        for theme, count in retro.themes.items():
            theme_evolution[theme].append((sprint, count))
        
        # Sentiment tracking
        for sentiment, score in retro.sentiment_scores.items():
            sentiment_evolution[sentiment].append((sprint, score))
    
    # Identify recurring themes (appear in >50% of retros)
    recurring_threshold = len(retros) * 0.5
    recurring_themes = {}
    
    for theme, occurrences in theme_evolution.items():
        if len(occurrences) >= recurring_threshold:
            sprints, counts = zip(*occurrences)
            recurring_themes[theme] = {
                "frequency": len(occurrences) / len(retros),
                "average_mentions": statistics.mean(counts),
                "trend": _calculate_trend(list(counts)),
                "first_appearance": min(sprints),
                "last_appearance": max(sprints),
                "total_mentions": sum(counts)
            }
    
    # Sentiment trend analysis
    sentiment_trends = {}
    for sentiment, scores_by_sprint in sentiment_evolution.items():
        if len(scores_by_sprint) >= 3:  # Need at least 3 data points
            _, scores = zip(*scores_by_sprint)
            sentiment_trends[sentiment] = {
                "average_score": statistics.mean(scores),
                "trend": _calculate_trend(list(scores)),
                "volatility": statistics.stdev(scores) if len(scores) > 1 else 0.0
            }
    
    # Identify persistent issues (negative themes that recur)
    persistent_issues = []
    for theme, data in recurring_themes.items():
        if theme in ["technical", "process", "external"] and data["frequency"] > 0.6:
            if data["trend"]["direction"] in ["stable", "increasing"]:
                persistent_issues.append({
                    "theme": theme,
                    "frequency": data["frequency"],
                    "severity": data["average_mentions"],
                    "trend": data["trend"]["direction"]
                })
    
    return {
        "recurring_themes": recurring_themes,
        "sentiment_trends": sentiment_trends,
        "persistent_issues": persistent_issues,
        "total_themes_identified": len(theme_evolution),
        "themes_per_retro": sum(len(r.themes) for r in retros) / len(retros) if retros else 0
    }


def analyze_improvement_trends(retros: List[RetrospectiveData]) -> Dict[str, Any]:
    """Analyze improvement trends across retrospectives."""
    if len(retros) < 3:
        return {"error": "Need at least 3 retrospectives for trend analysis"}
    
    # Sort retrospectives by sprint number
    sorted_retros = sorted(retros, key=lambda r: r.sprint_number)
    
    # Track various metrics over time
    metrics_over_time = {
        "action_items_per_retro": [len(r.action_items) for r in sorted_retros],
        "attendance_rate": [r.attendance_rate for r in sorted_retros],
        "duration": [r.duration_minutes for r in sorted_retros],
        "positive_sentiment": [r.sentiment_scores.get("positive", 0) for r in sorted_retros],
        "negative_sentiment": [r.sentiment_scores.get("negative", 0) for r in sorted_retros],
        "total_items_discussed": [r.total_items for r in sorted_retros]
    }
    
    # Calculate trends for each metric
    trend_analysis = {}
    for metric_name, values in metrics_over_time.items():
        if len(values) >= 3:
            trend_analysis[metric_name] = {
                "values": values,
                "trend": _calculate_trend(values),
                "average": statistics.mean(values),
                "latest": values[-1],
                "change_from_first": ((values[-1] - values[0]) / values[0]) if values[0] != 0 else 0
            }
    
    # Action item completion trend
    completion_rates_by_sprint = []
    for i, retro in enumerate(sorted_retros):
        if i > 0:  # Skip first retro as it has no previous action items to complete
            prev_retro = sorted_retros[i-1]
            if prev_retro.action_items:
                completed_count = sum(1 for item in prev_retro.action_items 
                                    if item.is_completed and item.completed_sprint == retro.sprint_number)
                completion_rate = completed_count / len(prev_retro.action_items)
                completion_rates_by_sprint.append(completion_rate)
    
    if completion_rates_by_sprint:
        trend_analysis["action_item_completion"] = {
            "values": completion_rates_by_sprint,
            "trend": _calculate_trend(completion_rates_by_sprint),
            "average": statistics.mean(completion_rates_by_sprint),
            "latest": completion_rates_by_sprint[-1] if completion_rates_by_sprint else 0
        }
    
    # Team maturity indicators
    maturity_score = _calculate_team_maturity(sorted_retros)
    
    return {
        "trend_analysis": trend_analysis,
        "team_maturity_score": maturity_score,
        "retrospective_quality_trend": _assess_retrospective_quality_trend(sorted_retros),
        "improvement_velocity": _calculate_improvement_velocity(sorted_retros)
    }


def _calculate_trend(values: List[float]) -> Dict[str, Any]:
    """Calculate trend direction and strength for a series of values."""
    if len(values) < 2:
        return {"direction": "insufficient_data", "strength": 0.0}
    
    # Simple linear regression
    n = len(values)
    x_values = list(range(n))
    x_mean = sum(x_values) / n
    y_mean = sum(values) / n
    
    numerator = sum((x - x_mean) * (y - y_mean) for x, y in zip(x_values, values))
    denominator = sum((x - x_mean) ** 2 for x in x_values)
    
    if denominator == 0:
        slope = 0
    else:
        slope = numerator / denominator
    
    # Calculate correlation coefficient for trend strength
    try:
        correlation = statistics.correlation(x_values, values) if n > 2 else 0.0
    except statistics.StatisticsError:
        correlation = 0.0
    
    # Determine trend direction
    if abs(slope) < 0.01:  # Practically no change
        direction = "stable"
    elif slope > 0:
        direction = "increasing"
    else:
        direction = "decreasing"
    
    return {
        "direction": direction,
        "slope": slope,
        "strength": abs(correlation),
        "correlation": correlation
    }


def _calculate_team_maturity(retros: List[RetrospectiveData]) -> Dict[str, Any]:
    """Calculate team maturity based on retrospective patterns."""
    if len(retros) < 3:
        return {"score": 50, "level": "developing"}
    
    maturity_indicators = {
        "action_item_focus": 0,      # Fewer but higher quality action items
        "sentiment_balance": 0,      # Balanced positive/negative sentiment
        "theme_consistency": 0,      # Consistent themes without chaos
        "participation": 0,          # High attendance rates
        "follow_through": 0          # Good action item completion
    }
    
    # Action item focus (quality over quantity)
    avg_action_items = sum(len(r.action_items) for r in retros) / len(retros)
    if 2 <= avg_action_items <= 5:  # Sweet spot
        maturity_indicators["action_item_focus"] = 100
    elif avg_action_items < 2 or avg_action_items > 8:
        maturity_indicators["action_item_focus"] = 30
    else:
        maturity_indicators["action_item_focus"] = 70
    
    # Sentiment balance
    avg_positive = sum(r.sentiment_scores.get("positive", 0) for r in retros) / len(retros)
    avg_negative = sum(r.sentiment_scores.get("negative", 0) for r in retros) / len(retros)
    
    if 0.3 <= avg_positive <= 0.6 and 0.2 <= avg_negative <= 0.4:
        maturity_indicators["sentiment_balance"] = 100
    else:
        maturity_indicators["sentiment_balance"] = 50
    
    # Participation
    avg_attendance = sum(r.attendance_rate for r in retros) / len(retros)
    maturity_indicators["participation"] = min(100, avg_attendance * 100)
    
    # Theme consistency (not too chaotic, not too narrow)
    avg_themes = sum(len(r.themes) for r in retros) / len(retros)
    if 2 <= avg_themes <= 4:
        maturity_indicators["theme_consistency"] = 100
    else:
        maturity_indicators["theme_consistency"] = 70
    
    # Follow-through (estimated from action item patterns)
    # This is simplified - in reality would track actual completion
    recent_retros = retros[-3:] if len(retros) >= 3 else retros
    avg_recent_actions = sum(len(r.action_items) for r in recent_retros) / len(recent_retros)
    
    if avg_recent_actions <= 3:  # Fewer action items might indicate better follow-through
        maturity_indicators["follow_through"] = 80
    else:
        maturity_indicators["follow_through"] = 60
    
    # Calculate overall maturity score
    overall_score = sum(maturity_indicators.values()) / len(maturity_indicators)
    
    if overall_score >= 85:
        level = "high_performing"
    elif overall_score >= 70:
        level = "performing"
    elif overall_score >= 55:
        level = "developing"
    else:
        level = "forming"
    
    return {
        "score": overall_score,
        "level": level,
        "indicators": maturity_indicators
    }


def _assess_retrospective_quality_trend(retros: List[RetrospectiveData]) -> Dict[str, Any]:
    """Assess the quality trend of retrospectives over time."""
    quality_scores = []
    
    for retro in retros:
        score = 0
        
        # Duration appropriateness (60-90 minutes is ideal)
        if 60 <= retro.duration_minutes <= 90:
            score += 25
        elif 45 <= retro.duration_minutes <= 120:
            score += 15
        else:
            score += 5
        
        # Participation
        score += min(25, retro.attendance_rate * 25)
        
        # Balance of content
        went_well_count = len(retro.went_well)
        to_improve_count = len(retro.to_improve)
        total_items = went_well_count + to_improve_count
        
        if total_items > 0:
            balance = min(went_well_count, to_improve_count) / total_items
            score += balance * 25
        
        # Action items quality (not too many, not too few)
        action_count = len(retro.action_items)
        if 2 <= action_count <= 5:
            score += 25
        elif 1 <= action_count <= 7:
            score += 15
        else:
            score += 5
        
        quality_scores.append(score)
    
    if len(quality_scores) >= 2:
        trend = _calculate_trend(quality_scores)
    else:
        trend = {"direction": "insufficient_data", "strength": 0.0}
    
    return {
        "quality_scores": quality_scores,
        "average_quality": statistics.mean(quality_scores),
        "trend": trend,
        "latest_quality": quality_scores[-1] if quality_scores else 0
    }


def _calculate_improvement_velocity(retros: List[RetrospectiveData]) -> Dict[str, Any]:
    """Calculate how quickly the team improves based on retrospective patterns."""
    if len(retros) < 4:
        return {"velocity": "insufficient_data"}
    
    # Look at theme evolution - are persistent issues being resolved?
    theme_counts = defaultdict(list)
    for retro in retros:
        for theme, count in retro.themes.items():
            theme_counts[theme].append(count)
    
    resolved_themes = 0
    persistent_themes = 0
    
    for theme, counts in theme_counts.items():
        if len(counts) >= 3:
            recent_avg = statistics.mean(counts[-2:])
            early_avg = statistics.mean(counts[:2])
            
            if recent_avg < early_avg * 0.7:  # 30% reduction
                resolved_themes += 1
            elif recent_avg > early_avg * 0.9:  # Still persistent
                persistent_themes += 1
    
    total_themes = resolved_themes + persistent_themes
    if total_themes > 0:
        resolution_rate = resolved_themes / total_themes
    else:
        resolution_rate = 0.5  # Neutral if no data
    
    # Action item completion trends
    if len(retros) >= 4:
        recent_action_density = sum(len(r.action_items) for r in retros[-2:]) / 2
        early_action_density = sum(len(r.action_items) for r in retros[:2]) / 2
        
        action_efficiency = 1.0
        if early_action_density > 0:
            action_efficiency = min(1.0, early_action_density / max(recent_action_density, 1))
    else:
        action_efficiency = 0.5
    
    # Overall velocity score
    velocity_score = (resolution_rate * 0.6) + (action_efficiency * 0.4)
    
    if velocity_score >= 0.8:
        velocity = "high"
    elif velocity_score >= 0.6:
        velocity = "moderate"
    elif velocity_score >= 0.4:
        velocity = "low"
    else:
        velocity = "stagnant"
    
    return {
        "velocity": velocity,
        "velocity_score": velocity_score,
        "theme_resolution_rate": resolution_rate,
        "action_efficiency": action_efficiency,
        "resolved_themes": resolved_themes,
        "persistent_themes": persistent_themes
    }


def generate_recommendations(result: RetroAnalysisResult) -> List[str]:
    """Generate actionable recommendations based on retrospective analysis."""
    recommendations = []
    
    # Action item recommendations
    action_analysis = result.action_item_analysis
    completion_rate = action_analysis.get("completion_rate", 0)
    
    if completion_rate < 0.5:
        recommendations.append("CRITICAL: Low action item completion rate (<50%). Reduce action items per retro and focus on realistic, achievable goals.")
    elif completion_rate < 0.7:
        recommendations.append("Improve action item follow-through. Consider assigning owners and due dates more systematically.")
    elif completion_rate > 0.9:
        recommendations.append("Excellent action item completion! Consider taking on more ambitious improvement initiatives.")
    
    overdue_rate = action_analysis.get("overdue_rate", 0)
    if overdue_rate > 0.3:
        recommendations.append("High overdue rate suggests unrealistic timelines. Review estimation and prioritization process.")
    
    # Theme recommendations
    theme_analysis = result.theme_analysis
    persistent_issues = theme_analysis.get("persistent_issues", [])
    if len(persistent_issues) >= 2:
        recommendations.append(f"Address {len(persistent_issues)} persistent issues that keep recurring across retrospectives.")
        for issue in persistent_issues[:2]:  # Top 2 issues
            recommendations.append(f"Focus on resolving recurring {issue['theme']} issues (appears in {issue['frequency']:.0%} of retros).")
    
    # Trend-based recommendations
    improvement_trends = result.improvement_trends
    if "team_maturity_score" in improvement_trends:
        maturity = improvement_trends["team_maturity_score"]
        level = maturity.get("level", "forming")
        
        if level == "forming":
            recommendations.append("Team is in forming stage. Focus on establishing basic retrospective disciplines and psychological safety.")
        elif level == "developing":
            recommendations.append("Team is developing. Work on action item follow-through and deeper root cause analysis.")
        elif level == "performing":
            recommendations.append("Good team maturity. Consider advanced techniques like continuous improvement tracking.")
        elif level == "high_performing":
            recommendations.append("Excellent retrospective maturity! Share practices with other teams and focus on innovation.")
    
    # Quality recommendations
    if "retrospective_quality_trend" in improvement_trends:
        quality_trend = improvement_trends["retrospective_quality_trend"]
        avg_quality = quality_trend.get("average_quality", 50)
        
        if avg_quality < 60:
            recommendations.append("Retrospective quality is below average. Review facilitation techniques and engagement strategies.")
        
        trend_direction = quality_trend.get("trend", {}).get("direction", "stable")
        if trend_direction == "decreasing":
            recommendations.append("Retrospective quality is declining. Consider changing facilitation approach or addressing team engagement issues.")
    
    return recommendations


# ---------------------------------------------------------------------------
# Main Analysis Function
# ---------------------------------------------------------------------------

def analyze_retrospectives(data: Dict[str, Any]) -> RetroAnalysisResult:
    """Perform comprehensive retrospective analysis."""
    result = RetroAnalysisResult()
    
    try:
        # Parse retrospective data
        retro_records = data.get("retrospectives", [])
        retros = [RetrospectiveData(record) for record in retro_records]
        
        if not retros:
            raise ValueError("No retrospective data found")
        
        # Sort by sprint number
        retros.sort(key=lambda r: r.sprint_number)
        
        # Basic summary
        result.summary = {
            "total_retrospectives": len(retros),
            "date_range": {
                "first": retros[0].date if retros else "",
                "last": retros[-1].date if retros else "",
                "span_sprints": retros[-1].sprint_number - retros[0].sprint_number + 1 if retros else 0
            },
            "average_duration": statistics.mean([r.duration_minutes for r in retros if r.duration_minutes > 0]),
            "average_attendance": statistics.mean([r.attendance_rate for r in retros]),
        }
        
        # Action item analysis
        result.action_item_analysis = analyze_action_item_completion(retros)
        
        # Theme analysis
        result.theme_analysis = analyze_recurring_themes(retros)
        
        # Improvement trends
        result.improvement_trends = analyze_improvement_trends(retros)
        
        # Generate recommendations
        result.recommendations = generate_recommendations(result)
        
    except Exception as e:
        result.summary = {"error": str(e)}
    
    return result


# ---------------------------------------------------------------------------
# Output Formatting
# ---------------------------------------------------------------------------

def format_text_output(result: RetroAnalysisResult) -> str:
    """Format analysis results as readable text report."""
    lines = []
    lines.append("="*60)
    lines.append("RETROSPECTIVE ANALYSIS REPORT")
    lines.append("="*60)
    lines.append("")
    
    if "error" in result.summary:
        lines.append(f"ERROR: {result.summary['error']}")
        return "\n".join(lines)
    
    # Summary section
    summary = result.summary
    lines.append("RETROSPECTIVE SUMMARY")
    lines.append("-"*30)
    lines.append(f"Total Retrospectives: {summary['total_retrospectives']}")
    lines.append(f"Sprint Range: {summary['date_range']['span_sprints']} sprints")
    lines.append(f"Average Duration: {summary.get('average_duration', 0):.0f} minutes")
    lines.append(f"Average Attendance: {summary.get('average_attendance', 0):.1%}")
    lines.append("")
    
    # Action item analysis
    action_analysis = result.action_item_analysis
    lines.append("ACTION ITEM ANALYSIS")
    lines.append("-"*30)
    lines.append(f"Total Action Items: {action_analysis.get('total_action_items', 0)}")
    lines.append(f"Completion Rate: {action_analysis.get('completion_rate', 0):.1%}")
    lines.append(f"Average Completion Time: {action_analysis.get('average_completion_time', 0):.1f} sprints")
    lines.append(f"Overdue Items: {action_analysis.get('overdue_items', 0)} ({action_analysis.get('overdue_rate', 0):.1%})")
    
    priority_analysis = action_analysis.get('priority_analysis', {})
    if priority_analysis:
        lines.append("Priority-based completion rates:")
        for priority, data in priority_analysis.items():
            lines.append(f"  {priority.title()}: {data['completion_rate']:.1%} ({data['completed']}/{data['total']})")
    lines.append("")
    
    # Theme analysis
    theme_analysis = result.theme_analysis
    lines.append("THEME ANALYSIS")
    lines.append("-"*30)
    recurring_themes = theme_analysis.get("recurring_themes", {})
    if recurring_themes:
        lines.append("Top recurring themes:")
        sorted_themes = sorted(recurring_themes.items(), key=lambda x: x[1]['frequency'], reverse=True)
        for theme, data in sorted_themes[:5]:
            lines.append(f"  {theme.replace('_', ' ').title()}: {data['frequency']:.1%} frequency, {data['trend']['direction']} trend")
    
    persistent_issues = theme_analysis.get("persistent_issues", [])
    if persistent_issues:
        lines.append("Persistent issues requiring attention:")
        for issue in persistent_issues:
            lines.append(f"  {issue['theme'].replace('_', ' ').title()}: {issue['frequency']:.1%} frequency")
    lines.append("")
    
    # Improvement trends
    improvement_trends = result.improvement_trends
    if "team_maturity_score" in improvement_trends:
        maturity = improvement_trends["team_maturity_score"]
        lines.append("TEAM MATURITY")
        lines.append("-"*30)
        lines.append(f"Maturity Level: {maturity['level'].replace('_', ' ').title()}")
        lines.append(f"Maturity Score: {maturity['score']:.0f}/100")
        lines.append("")
    
    if "improvement_velocity" in improvement_trends:
        velocity = improvement_trends["improvement_velocity"]
        lines.append("IMPROVEMENT VELOCITY")
        lines.append("-"*30)
        lines.append(f"Velocity: {velocity['velocity'].title()}")
        lines.append(f"Theme Resolution Rate: {velocity.get('theme_resolution_rate', 0):.1%}")
        lines.append("")
    
    # Recommendations
    if result.recommendations:
        lines.append("RECOMMENDATIONS")
        lines.append("-"*30)
        for i, rec in enumerate(result.recommendations, 1):
            lines.append(f"{i}. {rec}")
    
    return "\n".join(lines)


def format_json_output(result: RetroAnalysisResult) -> Dict[str, Any]:
    """Format analysis results as JSON."""
    return {
        "summary": result.summary,
        "action_item_analysis": result.action_item_analysis,
        "theme_analysis": result.theme_analysis,
        "improvement_trends": result.improvement_trends,
        "recommendations": result.recommendations,
    }


# ---------------------------------------------------------------------------
# CLI Interface
# ---------------------------------------------------------------------------

def main() -> int:
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Analyze retrospective data for continuous improvement insights"
    )
    parser.add_argument(
        "data_file", 
        help="JSON file containing retrospective data"
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
        result = analyze_retrospectives(data)
        
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