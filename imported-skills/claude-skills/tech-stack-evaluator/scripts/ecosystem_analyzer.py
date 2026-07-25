"""
Ecosystem Health Analyzer.

Analyzes technology ecosystem health including community size, maintenance status,
GitHub metrics, npm downloads, and long-term viability assessment.
"""

from typing import Dict, List, Any, Optional
from datetime import datetime, timedelta


class EcosystemAnalyzer:
    """Analyze technology ecosystem health and viability."""

    def __init__(self, ecosystem_data: Dict[str, Any]):
        """
        Initialize analyzer with ecosystem data.

        Args:
            ecosystem_data: Dictionary containing GitHub, npm, and community metrics
        """
        self.technology = ecosystem_data.get('technology', 'Unknown')
        self.github_data = ecosystem_data.get('github', {})
        self.npm_data = ecosystem_data.get('npm', {})
        self.community_data = ecosystem_data.get('community', {})
        self.corporate_backing = ecosystem_data.get('corporate_backing', {})

    def calculate_health_score(self) -> Dict[str, float]:
        """
        Calculate overall ecosystem health score (0-100).

        Returns:
            Dictionary of health score components
        """
        scores = {
            'github_health': self._score_github_health(),
            'npm_health': self._score_npm_health(),
            'community_health': self._score_community_health(),
            'corporate_backing': self._score_corporate_backing(),
            'maintenance_health': self._score_maintenance_health()
        }

        # Calculate weighted average
        weights = {
            'github_health': 0.25,
            'npm_health': 0.20,
            'community_health': 0.20,
            'corporate_backing': 0.15,
            'maintenance_health': 0.20
        }

        overall = sum(scores[k] * weights[k] for k in scores.keys())
        scores['overall_health'] = overall

        return scores

    def _score_github_health(self) -> float:
        """
        Score GitHub repository health.

        Returns:
            GitHub health score (0-100)
        """
        score = 0.0

        # Stars (0-30 points)
        stars = self.github_data.get('stars', 0)
        if stars >= 50000:
            score += 30
        elif stars >= 20000:
            score += 25
        elif stars >= 10000:
            score += 20
        elif stars >= 5000:
            score += 15
        elif stars >= 1000:
            score += 10
        else:
            score += max(0, stars / 100)  # 1 point per 100 stars

        # Forks (0-20 points)
        forks = self.github_data.get('forks', 0)
        if forks >= 10000:
            score += 20
        elif forks >= 5000:
            score += 15
        elif forks >= 2000:
            score += 12
        elif forks >= 1000:
            score += 10
        else:
            score += max(0, forks / 100)

        # Contributors (0-20 points)
        contributors = self.github_data.get('contributors', 0)
        if contributors >= 500:
            score += 20
        elif contributors >= 200:
            score += 15
        elif contributors >= 100:
            score += 12
        elif contributors >= 50:
            score += 10
        else:
            score += max(0, contributors / 5)

        # Commit frequency (0-30 points)
        commits_last_month = self.github_data.get('commits_last_month', 0)
        if commits_last_month >= 100:
            score += 30
        elif commits_last_month >= 50:
            score += 25
        elif commits_last_month >= 25:
            score += 20
        elif commits_last_month >= 10:
            score += 15
        else:
            score += max(0, commits_last_month * 1.5)

        return min(100.0, score)

    def _score_npm_health(self) -> float:
        """
        Score npm package health (if applicable).

        Returns:
            npm health score (0-100)
        """
        if not self.npm_data:
            return 50.0  # Neutral score if not applicable

        score = 0.0

        # Weekly downloads (0-40 points)
        weekly_downloads = self.npm_data.get('weekly_downloads', 0)
        if weekly_downloads >= 1000000:
            score += 40
        elif weekly_downloads >= 500000:
            score += 35
        elif weekly_downloads >= 100000:
            score += 30
        elif weekly_downloads >= 50000:
            score += 25
        elif weekly_downloads >= 10000:
            score += 20
        else:
            score += max(0, weekly_downloads / 500)

        # Version stability (0-20 points)
        version = self.npm_data.get('version', '0.0.1')
        major_version = int(version.split('.')[0]) if version else 0

        if major_version >= 5:
            score += 20
        elif major_version >= 3:
            score += 15
        elif major_version >= 1:
            score += 10
        else:
            score += 5

        # Dependencies count (0-20 points, fewer is better)
        dependencies = self.npm_data.get('dependencies_count', 50)
        if dependencies <= 10:
            score += 20
        elif dependencies <= 25:
            score += 15
        elif dependencies <= 50:
            score += 10
        else:
            score += max(0, 20 - (dependencies - 50) / 10)

        # Last publish date (0-20 points)
        days_since_publish = self.npm_data.get('days_since_last_publish', 365)
        if days_since_publish <= 30:
            score += 20
        elif days_since_publish <= 90:
            score += 15
        elif days_since_publish <= 180:
            score += 10
        elif days_since_publish <= 365:
            score += 5
        else:
            score += 0

        return min(100.0, score)

    def _score_community_health(self) -> float:
        """
        Score community health and engagement.

        Returns:
            Community health score (0-100)
        """
        score = 0.0

        # Stack Overflow questions (0-25 points)
        so_questions = self.community_data.get('stackoverflow_questions', 0)
        if so_questions >= 50000:
            score += 25
        elif so_questions >= 20000:
            score += 20
        elif so_questions >= 10000:
            score += 15
        elif so_questions >= 5000:
            score += 10
        else:
            score += max(0, so_questions / 500)

        # Job postings (0-25 points)
        job_postings = self.community_data.get('job_postings', 0)
        if job_postings >= 5000:
            score += 25
        elif job_postings >= 2000:
            score += 20
        elif job_postings >= 1000:
            score += 15
        elif job_postings >= 500:
            score += 10
        else:
            score += max(0, job_postings / 50)

        # Tutorials and resources (0-25 points)
        tutorials = self.community_data.get('tutorials_count', 0)
        if tutorials >= 1000:
            score += 25
        elif tutorials >= 500:
            score += 20
        elif tutorials >= 200:
            score += 15
        elif tutorials >= 100:
            score += 10
        else:
            score += max(0, tutorials / 10)

        # Active forums/Discord (0-25 points)
        forum_members = self.community_data.get('forum_members', 0)
        if forum_members >= 50000:
            score += 25
        elif forum_members >= 20000:
            score += 20
        elif forum_members >= 10000:
            score += 15
        elif forum_members >= 5000:
            score += 10
        else:
            score += max(0, forum_members / 500)

        return min(100.0, score)

    def _score_corporate_backing(self) -> float:
        """
        Score corporate backing strength.

        Returns:
            Corporate backing score (0-100)
        """
        backing_type = self.corporate_backing.get('type', 'none')

        scores = {
            'major_tech_company': 100,  # Google, Microsoft, Meta, etc.
            'established_company': 80,   # Dedicated company (Vercel, HashiCorp)
            'startup_backed': 60,        # Funded startup
            'community_led': 40,         # Strong community, no corporate backing
            'none': 20                   # Individual maintainers
        }

        base_score = scores.get(backing_type, 40)

        # Adjust for funding
        funding = self.corporate_backing.get('funding_millions', 0)
        if funding >= 100:
            base_score = min(100, base_score + 20)
        elif funding >= 50:
            base_score = min(100, base_score + 10)
        elif funding >= 10:
            base_score = min(100, base_score + 5)

        return base_score

    def _score_maintenance_health(self) -> float:
        """
        Score maintenance activity and responsiveness.

        Returns:
            Maintenance health score (0-100)
        """
        score = 0.0

        # Issue response time (0-30 points)
        avg_response_hours = self.github_data.get('avg_issue_response_hours', 168)  # 7 days default
        if avg_response_hours <= 24:
            score += 30
        elif avg_response_hours <= 48:
            score += 25
        elif avg_response_hours <= 168:  # 1 week
            score += 20
        elif avg_response_hours <= 336:  # 2 weeks
            score += 10
        else:
            score += 5

        # Issue resolution rate (0-30 points)
        resolution_rate = self.github_data.get('issue_resolution_rate', 0.5)
        score += resolution_rate * 30

        # Release frequency (0-20 points)
        releases_per_year = self.github_data.get('releases_per_year', 4)
        if releases_per_year >= 12:
            score += 20
        elif releases_per_year >= 6:
            score += 15
        elif releases_per_year >= 4:
            score += 10
        elif releases_per_year >= 2:
            score += 5
        else:
            score += 0

        # Active maintainers (0-20 points)
        active_maintainers = self.github_data.get('active_maintainers', 1)
        if active_maintainers >= 10:
            score += 20
        elif active_maintainers >= 5:
            score += 15
        elif active_maintainers >= 3:
            score += 10
        elif active_maintainers >= 1:
            score += 5
        else:
            score += 0

        return min(100.0, score)

    def assess_viability(self) -> Dict[str, Any]:
        """
        Assess long-term viability of technology.

        Returns:
            Viability assessment with risk factors
        """
        health = self.calculate_health_score()
        overall_health = health['overall_health']

        # Determine viability level
        if overall_health >= 80:
            viability = "Excellent - Strong long-term viability"
            risk_level = "Low"
        elif overall_health >= 65:
            viability = "Good - Solid viability with minor concerns"
            risk_level = "Low-Medium"
        elif overall_health >= 50:
            viability = "Moderate - Viable but with notable risks"
            risk_level = "Medium"
        elif overall_health >= 35:
            viability = "Concerning - Significant viability risks"
            risk_level = "Medium-High"
        else:
            viability = "Poor - High risk of abandonment"
            risk_level = "High"

        # Identify specific risks
        risks = self._identify_viability_risks(health)

        # Identify strengths
        strengths = self._identify_viability_strengths(health)

        return {
            'overall_viability': viability,
            'risk_level': risk_level,
            'health_score': overall_health,
            'risks': risks,
            'strengths': strengths,
            'recommendation': self._generate_viability_recommendation(overall_health, risks)
        }

    def _identify_viability_risks(self, health: Dict[str, float]) -> List[str]:
        """
        Identify viability risks from health scores.

        Args:
            health: Health score components

        Returns:
            List of identified risks
        """
        risks = []

        if health['maintenance_health'] < 50:
            risks.append("Low maintenance activity - slow issue resolution")

        if health['github_health'] < 50:
            risks.append("Limited GitHub activity - smaller community")

        if health['corporate_backing'] < 40:
            risks.append("Weak corporate backing - sustainability concerns")

        if health['npm_health'] < 50 and self.npm_data:
            risks.append("Low npm adoption - limited ecosystem")

        if health['community_health'] < 50:
            risks.append("Small community - limited resources and support")

        return risks if risks else ["No significant risks identified"]

    def _identify_viability_strengths(self, health: Dict[str, float]) -> List[str]:
        """
        Identify viability strengths from health scores.

        Args:
            health: Health score components

        Returns:
            List of identified strengths
        """
        strengths = []

        if health['maintenance_health'] >= 70:
            strengths.append("Active maintenance with responsive issue resolution")

        if health['github_health'] >= 70:
            strengths.append("Strong GitHub presence with active community")

        if health['corporate_backing'] >= 70:
            strengths.append("Strong corporate backing ensures sustainability")

        if health['npm_health'] >= 70 and self.npm_data:
            strengths.append("High npm adoption with stable releases")

        if health['community_health'] >= 70:
            strengths.append("Large, active community with extensive resources")

        return strengths if strengths else ["Baseline viability maintained"]

    def _generate_viability_recommendation(self, health_score: float, risks: List[str]) -> str:
        """
        Generate viability recommendation.

        Args:
            health_score: Overall health score
            risks: List of identified risks

        Returns:
            Recommendation string
        """
        if health_score >= 80:
            return "Recommended for long-term adoption - strong ecosystem support"
        elif health_score >= 65:
            return "Suitable for adoption - monitor identified risks"
        elif health_score >= 50:
            return "Proceed with caution - have contingency plans"
        else:
            return "Not recommended - consider alternatives with stronger ecosystems"

    def generate_ecosystem_report(self) -> Dict[str, Any]:
        """
        Generate comprehensive ecosystem report.

        Returns:
            Complete ecosystem analysis
        """
        health = self.calculate_health_score()
        viability = self.assess_viability()

        return {
            'technology': self.technology,
            'health_scores': health,
            'viability_assessment': viability,
            'github_metrics': self._format_github_metrics(),
            'npm_metrics': self._format_npm_metrics() if self.npm_data else None,
            'community_metrics': self._format_community_metrics()
        }

    def _format_github_metrics(self) -> Dict[str, Any]:
        """Format GitHub metrics for reporting."""
        return {
            'stars': f"{self.github_data.get('stars', 0):,}",
            'forks': f"{self.github_data.get('forks', 0):,}",
            'contributors': f"{self.github_data.get('contributors', 0):,}",
            'commits_last_month': self.github_data.get('commits_last_month', 0),
            'open_issues': self.github_data.get('open_issues', 0),
            'issue_resolution_rate': f"{self.github_data.get('issue_resolution_rate', 0) * 100:.1f}%"
        }

    def _format_npm_metrics(self) -> Dict[str, Any]:
        """Format npm metrics for reporting."""
        return {
            'weekly_downloads': f"{self.npm_data.get('weekly_downloads', 0):,}",
            'version': self.npm_data.get('version', 'N/A'),
            'dependencies': self.npm_data.get('dependencies_count', 0),
            'days_since_publish': self.npm_data.get('days_since_last_publish', 0)
        }

    def _format_community_metrics(self) -> Dict[str, Any]:
        """Format community metrics for reporting."""
        return {
            'stackoverflow_questions': f"{self.community_data.get('stackoverflow_questions', 0):,}",
            'job_postings': f"{self.community_data.get('job_postings', 0):,}",
            'tutorials': self.community_data.get('tutorials_count', 0),
            'forum_members': f"{self.community_data.get('forum_members', 0):,}"
        }
