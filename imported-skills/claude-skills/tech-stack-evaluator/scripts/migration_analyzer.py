"""
Migration Path Analyzer.

Analyzes migration complexity, risks, timelines, and strategies for moving
from legacy technology stacks to modern alternatives.
"""

from typing import Dict, List, Any, Optional, Tuple


class MigrationAnalyzer:
    """Analyze migration paths and complexity for technology stack changes."""

    # Migration complexity factors
    COMPLEXITY_FACTORS = [
        'code_volume',
        'architecture_changes',
        'data_migration',
        'api_compatibility',
        'dependency_changes',
        'testing_requirements'
    ]

    def __init__(self, migration_data: Dict[str, Any]):
        """
        Initialize migration analyzer with migration parameters.

        Args:
            migration_data: Dictionary containing source/target technologies and constraints
        """
        self.source_tech = migration_data.get('source_technology', 'Unknown')
        self.target_tech = migration_data.get('target_technology', 'Unknown')
        self.codebase_stats = migration_data.get('codebase_stats', {})
        self.constraints = migration_data.get('constraints', {})
        self.team_info = migration_data.get('team', {})

    def calculate_complexity_score(self) -> Dict[str, Any]:
        """
        Calculate overall migration complexity (1-10 scale).

        Returns:
            Dictionary with complexity scores by factor
        """
        scores = {
            'code_volume': self._score_code_volume(),
            'architecture_changes': self._score_architecture_changes(),
            'data_migration': self._score_data_migration(),
            'api_compatibility': self._score_api_compatibility(),
            'dependency_changes': self._score_dependency_changes(),
            'testing_requirements': self._score_testing_requirements()
        }

        # Calculate weighted average
        weights = {
            'code_volume': 0.20,
            'architecture_changes': 0.25,
            'data_migration': 0.20,
            'api_compatibility': 0.15,
            'dependency_changes': 0.10,
            'testing_requirements': 0.10
        }

        overall = sum(scores[k] * weights[k] for k in scores.keys())
        scores['overall_complexity'] = overall

        return scores

    def _score_code_volume(self) -> float:
        """
        Score complexity based on codebase size.

        Returns:
            Code volume complexity score (1-10)
        """
        lines_of_code = self.codebase_stats.get('lines_of_code', 10000)
        num_files = self.codebase_stats.get('num_files', 100)
        num_components = self.codebase_stats.get('num_components', 50)

        # Score based on lines of code (primary factor)
        if lines_of_code < 5000:
            base_score = 2
        elif lines_of_code < 20000:
            base_score = 4
        elif lines_of_code < 50000:
            base_score = 6
        elif lines_of_code < 100000:
            base_score = 8
        else:
            base_score = 10

        # Adjust for component count
        if num_components > 200:
            base_score = min(10, base_score + 1)
        elif num_components > 500:
            base_score = min(10, base_score + 2)

        return float(base_score)

    def _score_architecture_changes(self) -> float:
        """
        Score complexity based on architectural changes.

        Returns:
            Architecture complexity score (1-10)
        """
        arch_change_level = self.codebase_stats.get('architecture_change_level', 'moderate')

        scores = {
            'minimal': 2,      # Same patterns, just different framework
            'moderate': 5,     # Some pattern changes, similar concepts
            'significant': 7,  # Different patterns, major refactoring
            'complete': 10     # Complete rewrite, different paradigm
        }

        return float(scores.get(arch_change_level, 5))

    def _score_data_migration(self) -> float:
        """
        Score complexity based on data migration requirements.

        Returns:
            Data migration complexity score (1-10)
        """
        has_database = self.codebase_stats.get('has_database', True)
        if not has_database:
            return 1.0

        database_size_gb = self.codebase_stats.get('database_size_gb', 10)
        schema_changes = self.codebase_stats.get('schema_changes_required', 'minimal')
        data_transformation = self.codebase_stats.get('data_transformation_required', False)

        # Base score from database size
        if database_size_gb < 1:
            score = 2
        elif database_size_gb < 10:
            score = 3
        elif database_size_gb < 100:
            score = 5
        elif database_size_gb < 1000:
            score = 7
        else:
            score = 9

        # Adjust for schema changes
        schema_adjustments = {
            'none': 0,
            'minimal': 1,
            'moderate': 2,
            'significant': 3
        }
        score += schema_adjustments.get(schema_changes, 1)

        # Adjust for data transformation
        if data_transformation:
            score += 2

        return min(10.0, float(score))

    def _score_api_compatibility(self) -> float:
        """
        Score complexity based on API compatibility.

        Returns:
            API compatibility complexity score (1-10)
        """
        breaking_api_changes = self.codebase_stats.get('breaking_api_changes', 'some')

        scores = {
            'none': 1,         # Fully compatible
            'minimal': 3,      # Few breaking changes
            'some': 5,         # Moderate breaking changes
            'many': 7,         # Significant breaking changes
            'complete': 10     # Complete API rewrite
        }

        return float(scores.get(breaking_api_changes, 5))

    def _score_dependency_changes(self) -> float:
        """
        Score complexity based on dependency changes.

        Returns:
            Dependency complexity score (1-10)
        """
        num_dependencies = self.codebase_stats.get('num_dependencies', 20)
        dependencies_to_replace = self.codebase_stats.get('dependencies_to_replace', 5)

        # Score based on replacement percentage
        if num_dependencies == 0:
            return 1.0

        replacement_pct = (dependencies_to_replace / num_dependencies) * 100

        if replacement_pct < 10:
            return 2.0
        elif replacement_pct < 25:
            return 4.0
        elif replacement_pct < 50:
            return 6.0
        elif replacement_pct < 75:
            return 8.0
        else:
            return 10.0

    def _score_testing_requirements(self) -> float:
        """
        Score complexity based on testing requirements.

        Returns:
            Testing complexity score (1-10)
        """
        test_coverage = self.codebase_stats.get('current_test_coverage', 0.5)  # 0-1 scale
        num_tests = self.codebase_stats.get('num_tests', 100)

        # If good test coverage, easier migration (can verify)
        if test_coverage >= 0.8:
            base_score = 3
        elif test_coverage >= 0.6:
            base_score = 5
        elif test_coverage >= 0.4:
            base_score = 7
        else:
            base_score = 9  # Poor coverage = hard to verify migration

        # Large test suites need updates
        if num_tests > 500:
            base_score = min(10, base_score + 1)

        return float(base_score)

    def estimate_effort(self) -> Dict[str, Any]:
        """
        Estimate migration effort in person-hours and timeline.

        Returns:
            Dictionary with effort estimates
        """
        complexity = self.calculate_complexity_score()
        overall_complexity = complexity['overall_complexity']

        # Base hours estimation
        lines_of_code = self.codebase_stats.get('lines_of_code', 10000)
        base_hours = lines_of_code / 50  # 50 lines per hour baseline

        # Complexity multiplier
        complexity_multiplier = 1 + (overall_complexity / 10)
        estimated_hours = base_hours * complexity_multiplier

        # Break down by phase
        phases = self._calculate_phase_breakdown(estimated_hours)

        # Calculate timeline
        team_size = self.team_info.get('team_size', 3)
        hours_per_week_per_dev = self.team_info.get('hours_per_week', 30)  # Account for other work

        total_dev_weeks = estimated_hours / (team_size * hours_per_week_per_dev)
        total_calendar_weeks = total_dev_weeks * 1.2  # Buffer for blockers

        return {
            'total_hours': estimated_hours,
            'total_person_months': estimated_hours / 160,  # 160 hours per person-month
            'phases': phases,
            'estimated_timeline': {
                'dev_weeks': total_dev_weeks,
                'calendar_weeks': total_calendar_weeks,
                'calendar_months': total_calendar_weeks / 4.33
            },
            'team_assumptions': {
                'team_size': team_size,
                'hours_per_week_per_dev': hours_per_week_per_dev
            }
        }

    def _calculate_phase_breakdown(self, total_hours: float) -> Dict[str, Dict[str, float]]:
        """
        Calculate effort breakdown by migration phase.

        Args:
            total_hours: Total estimated hours

        Returns:
            Hours breakdown by phase
        """
        # Standard phase percentages
        phase_percentages = {
            'planning_and_prototyping': 0.15,
            'core_migration': 0.45,
            'testing_and_validation': 0.25,
            'deployment_and_monitoring': 0.10,
            'buffer_and_contingency': 0.05
        }

        phases = {}
        for phase, percentage in phase_percentages.items():
            hours = total_hours * percentage
            phases[phase] = {
                'hours': hours,
                'person_weeks': hours / 40,
                'percentage': f"{percentage * 100:.0f}%"
            }

        return phases

    def assess_risks(self) -> Dict[str, List[Dict[str, str]]]:
        """
        Identify and assess migration risks.

        Returns:
            Categorized risks with mitigation strategies
        """
        complexity = self.calculate_complexity_score()

        risks = {
            'technical_risks': self._identify_technical_risks(complexity),
            'business_risks': self._identify_business_risks(),
            'team_risks': self._identify_team_risks()
        }

        return risks

    def _identify_technical_risks(self, complexity: Dict[str, float]) -> List[Dict[str, str]]:
        """
        Identify technical risks.

        Args:
            complexity: Complexity scores

        Returns:
            List of technical risks with mitigations
        """
        risks = []

        # API compatibility risks
        if complexity['api_compatibility'] >= 7:
            risks.append({
                'risk': 'Breaking API changes may cause integration failures',
                'severity': 'High',
                'mitigation': 'Create compatibility layer; implement feature flags for gradual rollout'
            })

        # Data migration risks
        if complexity['data_migration'] >= 7:
            risks.append({
                'risk': 'Data migration could cause data loss or corruption',
                'severity': 'Critical',
                'mitigation': 'Implement robust backup strategy; run parallel systems during migration; extensive validation'
            })

        # Architecture risks
        if complexity['architecture_changes'] >= 8:
            risks.append({
                'risk': 'Major architectural changes increase risk of performance regression',
                'severity': 'High',
                'mitigation': 'Extensive performance testing; staged rollout; monitoring and alerting'
            })

        # Testing risks
        if complexity['testing_requirements'] >= 7:
            risks.append({
                'risk': 'Inadequate test coverage may miss critical bugs',
                'severity': 'Medium',
                'mitigation': 'Improve test coverage before migration; automated regression testing; user acceptance testing'
            })

        if not risks:
            risks.append({
                'risk': 'Standard technical risks (bugs, edge cases)',
                'severity': 'Low',
                'mitigation': 'Standard QA processes and staged rollout'
            })

        return risks

    def _identify_business_risks(self) -> List[Dict[str, str]]:
        """
        Identify business risks.

        Returns:
            List of business risks with mitigations
        """
        risks = []

        # Downtime risk
        downtime_tolerance = self.constraints.get('downtime_tolerance', 'low')
        if downtime_tolerance == 'none':
            risks.append({
                'risk': 'Zero-downtime migration increases complexity and risk',
                'severity': 'High',
                'mitigation': 'Blue-green deployment; feature flags; gradual traffic migration'
            })

        # Feature parity risk
        risks.append({
            'risk': 'New implementation may lack feature parity',
            'severity': 'Medium',
            'mitigation': 'Comprehensive feature audit; prioritized feature list; clear communication'
        })

        # Timeline risk
        risks.append({
            'risk': 'Migration may take longer than estimated',
            'severity': 'Medium',
            'mitigation': 'Build in 20% buffer; regular progress reviews; scope management'
        })

        return risks

    def _identify_team_risks(self) -> List[Dict[str, str]]:
        """
        Identify team-related risks.

        Returns:
            List of team risks with mitigations
        """
        risks = []

        # Learning curve
        team_experience = self.team_info.get('target_tech_experience', 'low')
        if team_experience in ['low', 'none']:
            risks.append({
                'risk': 'Team lacks experience with target technology',
                'severity': 'High',
                'mitigation': 'Training program; hire experienced developers; external consulting'
            })

        # Team size
        team_size = self.team_info.get('team_size', 3)
        if team_size < 3:
            risks.append({
                'risk': 'Small team size may extend timeline',
                'severity': 'Medium',
                'mitigation': 'Consider augmenting team; reduce scope; extend timeline'
            })

        # Knowledge retention
        risks.append({
            'risk': 'Loss of institutional knowledge during migration',
            'severity': 'Medium',
            'mitigation': 'Comprehensive documentation; knowledge sharing sessions; pair programming'
        })

        return risks

    def generate_migration_plan(self) -> Dict[str, Any]:
        """
        Generate comprehensive migration plan.

        Returns:
            Complete migration plan with timeline and recommendations
        """
        complexity = self.calculate_complexity_score()
        effort = self.estimate_effort()
        risks = self.assess_risks()

        # Generate phased approach
        approach = self._recommend_migration_approach(complexity['overall_complexity'])

        # Generate recommendation
        recommendation = self._generate_migration_recommendation(complexity, effort, risks)

        return {
            'source_technology': self.source_tech,
            'target_technology': self.target_tech,
            'complexity_analysis': complexity,
            'effort_estimation': effort,
            'risk_assessment': risks,
            'recommended_approach': approach,
            'overall_recommendation': recommendation,
            'success_criteria': self._define_success_criteria()
        }

    def _recommend_migration_approach(self, complexity_score: float) -> Dict[str, Any]:
        """
        Recommend migration approach based on complexity.

        Args:
            complexity_score: Overall complexity score

        Returns:
            Recommended approach details
        """
        if complexity_score <= 3:
            approach = 'direct_migration'
            description = 'Direct migration - low complexity allows straightforward migration'
            timeline_multiplier = 1.0
        elif complexity_score <= 6:
            approach = 'phased_migration'
            description = 'Phased migration - migrate components incrementally to manage risk'
            timeline_multiplier = 1.3
        else:
            approach = 'strangler_pattern'
            description = 'Strangler pattern - gradually replace old system while running in parallel'
            timeline_multiplier = 1.5

        return {
            'approach': approach,
            'description': description,
            'timeline_multiplier': timeline_multiplier,
            'phases': self._generate_approach_phases(approach)
        }

    def _generate_approach_phases(self, approach: str) -> List[str]:
        """
        Generate phase descriptions for migration approach.

        Args:
            approach: Migration approach type

        Returns:
            List of phase descriptions
        """
        phases = {
            'direct_migration': [
                'Phase 1: Set up target environment and migrate configuration',
                'Phase 2: Migrate codebase and dependencies',
                'Phase 3: Migrate data with validation',
                'Phase 4: Comprehensive testing',
                'Phase 5: Cutover and monitoring'
            ],
            'phased_migration': [
                'Phase 1: Identify and prioritize components for migration',
                'Phase 2: Migrate non-critical components first',
                'Phase 3: Migrate core components with parallel running',
                'Phase 4: Migrate critical components with rollback plan',
                'Phase 5: Decommission old system'
            ],
            'strangler_pattern': [
                'Phase 1: Set up routing layer between old and new systems',
                'Phase 2: Implement new features in target technology only',
                'Phase 3: Gradually migrate existing features (lowest risk first)',
                'Phase 4: Migrate high-risk components last with extensive testing',
                'Phase 5: Complete migration and remove routing layer'
            ]
        }

        return phases.get(approach, phases['phased_migration'])

    def _generate_migration_recommendation(
        self,
        complexity: Dict[str, float],
        effort: Dict[str, Any],
        risks: Dict[str, List[Dict[str, str]]]
    ) -> str:
        """
        Generate overall migration recommendation.

        Args:
            complexity: Complexity analysis
            effort: Effort estimation
            risks: Risk assessment

        Returns:
            Recommendation string
        """
        overall_complexity = complexity['overall_complexity']
        timeline_months = effort['estimated_timeline']['calendar_months']

        # Count high/critical severity risks
        high_risk_count = sum(
            1 for risk_list in risks.values()
            for risk in risk_list
            if risk['severity'] in ['High', 'Critical']
        )

        if overall_complexity <= 4 and high_risk_count <= 2:
            return f"Recommended - Low complexity migration achievable in {timeline_months:.1f} months with manageable risks"
        elif overall_complexity <= 7 and high_risk_count <= 4:
            return f"Proceed with caution - Moderate complexity migration requiring {timeline_months:.1f} months and careful risk management"
        else:
            return f"High risk - Complex migration requiring {timeline_months:.1f} months. Consider: incremental approach, additional resources, or alternative solutions"

    def _define_success_criteria(self) -> List[str]:
        """
        Define success criteria for migration.

        Returns:
            List of success criteria
        """
        return [
            'Feature parity with current system',
            'Performance equal or better than current system',
            'Zero data loss or corruption',
            'All tests passing (unit, integration, E2E)',
            'Successful production deployment with <1% error rate',
            'Team trained and comfortable with new technology',
            'Documentation complete and up-to-date'
        ]
