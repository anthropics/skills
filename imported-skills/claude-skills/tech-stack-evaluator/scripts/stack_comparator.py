"""
Technology Stack Comparator - Main comparison engine with weighted scoring.

Provides comprehensive technology comparison with customizable weighted criteria,
feature matrices, and intelligent recommendation generation.
"""

from typing import Dict, List, Any, Optional, Tuple
import json


class StackComparator:
    """Main comparison engine for technology stack evaluation."""

    # Feature categories for evaluation
    FEATURE_CATEGORIES = [
        "performance",
        "scalability",
        "developer_experience",
        "ecosystem",
        "learning_curve",
        "documentation",
        "community_support",
        "enterprise_readiness"
    ]

    # Default weights if not provided
    DEFAULT_WEIGHTS = {
        "performance": 15,
        "scalability": 15,
        "developer_experience": 20,
        "ecosystem": 15,
        "learning_curve": 10,
        "documentation": 10,
        "community_support": 10,
        "enterprise_readiness": 5
    }

    def __init__(self, comparison_data: Dict[str, Any]):
        """
        Initialize comparator with comparison data.

        Args:
            comparison_data: Dictionary containing technologies to compare and criteria
        """
        self.technologies = comparison_data.get('technologies', [])
        self.use_case = comparison_data.get('use_case', 'general')
        self.priorities = comparison_data.get('priorities', {})
        self.weights = self._normalize_weights(comparison_data.get('weights', {}))
        self.scores = {}

    def _normalize_weights(self, custom_weights: Dict[str, float]) -> Dict[str, float]:
        """
        Normalize weights to sum to 100.

        Args:
            custom_weights: User-provided weights

        Returns:
            Normalized weights dictionary
        """
        # Start with defaults
        weights = self.DEFAULT_WEIGHTS.copy()

        # Override with custom weights
        weights.update(custom_weights)

        # Normalize to 100
        total = sum(weights.values())
        if total == 0:
            return self.DEFAULT_WEIGHTS

        return {k: (v / total) * 100 for k, v in weights.items()}

    def score_technology(self, tech_name: str, tech_data: Dict[str, Any]) -> Dict[str, float]:
        """
        Score a single technology across all criteria.

        Args:
            tech_name: Name of technology
            tech_data: Technology feature and metric data

        Returns:
            Dictionary of category scores (0-100 scale)
        """
        scores = {}

        for category in self.FEATURE_CATEGORIES:
            # Get raw score from tech data (0-100 scale)
            raw_score = tech_data.get(category, {}).get('score', 50.0)

            # Apply use-case specific adjustments
            adjusted_score = self._adjust_for_use_case(category, raw_score, tech_name)

            scores[category] = min(100.0, max(0.0, adjusted_score))

        return scores

    def _adjust_for_use_case(self, category: str, score: float, tech_name: str) -> float:
        """
        Apply use-case specific adjustments to scores.

        Args:
            category: Feature category
            score: Raw score
            tech_name: Technology name

        Returns:
            Adjusted score
        """
        # Use case specific bonuses/penalties
        adjustments = {
            'real-time': {
                'performance': 1.1,  # 10% bonus for real-time use cases
                'scalability': 1.1
            },
            'enterprise': {
                'enterprise_readiness': 1.2,  # 20% bonus
                'documentation': 1.1
            },
            'startup': {
                'developer_experience': 1.15,
                'learning_curve': 1.1
            }
        }

        # Determine use case type
        use_case_lower = self.use_case.lower()
        use_case_type = None

        for uc_key in adjustments.keys():
            if uc_key in use_case_lower:
                use_case_type = uc_key
                break

        # Apply adjustment if applicable
        if use_case_type and category in adjustments[use_case_type]:
            multiplier = adjustments[use_case_type][category]
            return score * multiplier

        return score

    def calculate_weighted_score(self, category_scores: Dict[str, float]) -> float:
        """
        Calculate weighted total score.

        Args:
            category_scores: Dictionary of category scores

        Returns:
            Weighted total score (0-100 scale)
        """
        total = 0.0

        for category, score in category_scores.items():
            weight = self.weights.get(category, 0.0) / 100.0  # Convert to decimal
            total += score * weight

        return total

    def compare_technologies(self, tech_data_list: List[Dict[str, Any]]) -> Dict[str, Any]:
        """
        Compare multiple technologies and generate recommendation.

        Args:
            tech_data_list: List of technology data dictionaries

        Returns:
            Comparison results with scores and recommendation
        """
        results = {
            'technologies': {},
            'recommendation': None,
            'confidence': 0.0,
            'decision_factors': [],
            'comparison_matrix': []
        }

        # Score each technology
        tech_scores = {}
        for tech_data in tech_data_list:
            tech_name = tech_data.get('name', 'Unknown')
            category_scores = self.score_technology(tech_name, tech_data)
            weighted_score = self.calculate_weighted_score(category_scores)

            tech_scores[tech_name] = {
                'category_scores': category_scores,
                'weighted_total': weighted_score,
                'strengths': self._identify_strengths(category_scores),
                'weaknesses': self._identify_weaknesses(category_scores)
            }

        results['technologies'] = tech_scores

        # Generate recommendation
        results['recommendation'], results['confidence'] = self._generate_recommendation(tech_scores)
        results['decision_factors'] = self._extract_decision_factors(tech_scores)
        results['comparison_matrix'] = self._build_comparison_matrix(tech_scores)

        return results

    def _identify_strengths(self, category_scores: Dict[str, float], threshold: float = 75.0) -> List[str]:
        """
        Identify strength categories (scores above threshold).

        Args:
            category_scores: Category scores dictionary
            threshold: Score threshold for strength identification

        Returns:
            List of strength categories
        """
        return [
            category for category, score in category_scores.items()
            if score >= threshold
        ]

    def _identify_weaknesses(self, category_scores: Dict[str, float], threshold: float = 50.0) -> List[str]:
        """
        Identify weakness categories (scores below threshold).

        Args:
            category_scores: Category scores dictionary
            threshold: Score threshold for weakness identification

        Returns:
            List of weakness categories
        """
        return [
            category for category, score in category_scores.items()
            if score < threshold
        ]

    def _generate_recommendation(self, tech_scores: Dict[str, Dict[str, Any]]) -> Tuple[str, float]:
        """
        Generate recommendation and confidence level.

        Args:
            tech_scores: Technology scores dictionary

        Returns:
            Tuple of (recommended_technology, confidence_score)
        """
        if not tech_scores:
            return "Insufficient data", 0.0

        # Sort by weighted total score
        sorted_techs = sorted(
            tech_scores.items(),
            key=lambda x: x[1]['weighted_total'],
            reverse=True
        )

        top_tech = sorted_techs[0][0]
        top_score = sorted_techs[0][1]['weighted_total']

        # Calculate confidence based on score gap
        if len(sorted_techs) > 1:
            second_score = sorted_techs[1][1]['weighted_total']
            score_gap = top_score - second_score

            # Confidence increases with score gap
            # 0-5 gap: low confidence
            # 5-15 gap: medium confidence
            # 15+ gap: high confidence
            if score_gap < 5:
                confidence = 40.0 + (score_gap * 2)  # 40-50%
            elif score_gap < 15:
                confidence = 50.0 + (score_gap - 5) * 2  # 50-70%
            else:
                confidence = 70.0 + min(score_gap - 15, 30)  # 70-100%
        else:
            confidence = 100.0  # Only one option

        return top_tech, min(100.0, confidence)

    def _extract_decision_factors(self, tech_scores: Dict[str, Dict[str, Any]]) -> List[Dict[str, Any]]:
        """
        Extract key decision factors from comparison.

        Args:
            tech_scores: Technology scores dictionary

        Returns:
            List of decision factors with importance weights
        """
        factors = []

        # Get top weighted categories
        sorted_weights = sorted(
            self.weights.items(),
            key=lambda x: x[1],
            reverse=True
        )[:3]  # Top 3 factors

        for category, weight in sorted_weights:
            # Get scores for this category across all techs
            category_scores = {
                tech: scores['category_scores'].get(category, 0.0)
                for tech, scores in tech_scores.items()
            }

            # Find best performer
            best_tech = max(category_scores.items(), key=lambda x: x[1])

            factors.append({
                'category': category,
                'importance': f"{weight:.1f}%",
                'best_performer': best_tech[0],
                'score': best_tech[1]
            })

        return factors

    def _build_comparison_matrix(self, tech_scores: Dict[str, Dict[str, Any]]) -> List[Dict[str, Any]]:
        """
        Build comparison matrix for display.

        Args:
            tech_scores: Technology scores dictionary

        Returns:
            List of comparison matrix rows
        """
        matrix = []

        for category in self.FEATURE_CATEGORIES:
            row = {
                'category': category,
                'weight': f"{self.weights.get(category, 0):.1f}%",
                'scores': {}
            }

            for tech_name, scores in tech_scores.items():
                category_score = scores['category_scores'].get(category, 0.0)
                row['scores'][tech_name] = f"{category_score:.1f}"

            matrix.append(row)

        # Add weighted totals row
        totals_row = {
            'category': 'WEIGHTED TOTAL',
            'weight': '100%',
            'scores': {}
        }

        for tech_name, scores in tech_scores.items():
            totals_row['scores'][tech_name] = f"{scores['weighted_total']:.1f}"

        matrix.append(totals_row)

        return matrix

    def generate_pros_cons(self, tech_name: str, tech_scores: Dict[str, Any]) -> Dict[str, List[str]]:
        """
        Generate pros and cons for a technology.

        Args:
            tech_name: Technology name
            tech_scores: Technology scores dictionary

        Returns:
            Dictionary with 'pros' and 'cons' lists
        """
        category_scores = tech_scores['category_scores']
        strengths = tech_scores['strengths']
        weaknesses = tech_scores['weaknesses']

        pros = []
        cons = []

        # Generate pros from strengths
        for strength in strengths[:3]:  # Top 3
            score = category_scores[strength]
            pros.append(f"Excellent {strength.replace('_', ' ')} (score: {score:.1f}/100)")

        # Generate cons from weaknesses
        for weakness in weaknesses[:3]:  # Top 3
            score = category_scores[weakness]
            cons.append(f"Weaker {weakness.replace('_', ' ')} (score: {score:.1f}/100)")

        # Add generic pros/cons if not enough specific ones
        if len(pros) == 0:
            pros.append(f"Balanced performance across all categories")

        if len(cons) == 0:
            cons.append(f"No significant weaknesses identified")

        return {'pros': pros, 'cons': cons}
