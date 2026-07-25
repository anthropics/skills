"""
Report Generator - Context-aware report generation with progressive disclosure.

Generates reports adapted for Claude Desktop (rich markdown) or CLI (terminal-friendly),
with executive summaries and detailed breakdowns on demand.
"""

from typing import Dict, List, Any, Optional
import os
import platform


class ReportGenerator:
    """Generate context-aware technology evaluation reports."""

    def __init__(self, report_data: Dict[str, Any], output_context: Optional[str] = None):
        """
        Initialize report generator.

        Args:
            report_data: Complete evaluation data
            output_context: 'desktop', 'cli', or None for auto-detect
        """
        self.report_data = report_data
        self.output_context = output_context or self._detect_context()

    def _detect_context(self) -> str:
        """
        Detect output context (Desktop vs CLI).

        Returns:
            Context type: 'desktop' or 'cli'
        """
        # Check for Claude Desktop environment variables or indicators
        # This is a simplified detection - actual implementation would check for
        # Claude Desktop-specific environment variables

        if os.getenv('CLAUDE_DESKTOP'):
            return 'desktop'

        # Check if running in terminal
        if os.isatty(1):  # stdout is a terminal
            return 'cli'

        # Default to desktop for rich formatting
        return 'desktop'

    def generate_executive_summary(self, max_tokens: int = 300) -> str:
        """
        Generate executive summary (200-300 tokens).

        Args:
            max_tokens: Maximum tokens for summary

        Returns:
            Executive summary markdown
        """
        summary_parts = []

        # Title
        technologies = self.report_data.get('technologies', [])
        tech_names = ', '.join(technologies[:3])  # First 3
        summary_parts.append(f"# Technology Evaluation: {tech_names}\n")

        # Recommendation
        recommendation = self.report_data.get('recommendation', {})
        rec_text = recommendation.get('text', 'No recommendation available')
        confidence = recommendation.get('confidence', 0)

        summary_parts.append(f"## Recommendation\n")
        summary_parts.append(f"**{rec_text}**\n")
        summary_parts.append(f"*Confidence: {confidence:.0f}%*\n")

        # Top 3 Pros
        pros = recommendation.get('pros', [])[:3]
        if pros:
            summary_parts.append(f"\n### Top Strengths\n")
            for pro in pros:
                summary_parts.append(f"- {pro}\n")

        # Top 3 Cons
        cons = recommendation.get('cons', [])[:3]
        if cons:
            summary_parts.append(f"\n### Key Concerns\n")
            for con in cons:
                summary_parts.append(f"- {con}\n")

        # Key Decision Factors
        decision_factors = self.report_data.get('decision_factors', [])[:3]
        if decision_factors:
            summary_parts.append(f"\n### Decision Factors\n")
            for factor in decision_factors:
                category = factor.get('category', 'Unknown')
                best = factor.get('best_performer', 'Unknown')
                summary_parts.append(f"- **{category.replace('_', ' ').title()}**: {best}\n")

        summary_parts.append(f"\n---\n")
        summary_parts.append(f"*For detailed analysis, request full report sections*\n")

        return ''.join(summary_parts)

    def generate_full_report(self, sections: Optional[List[str]] = None) -> str:
        """
        Generate complete report with selected sections.

        Args:
            sections: List of sections to include, or None for all

        Returns:
            Complete report markdown
        """
        if sections is None:
            sections = self._get_available_sections()

        report_parts = []

        # Title and metadata
        report_parts.append(self._generate_title())

        # Generate each requested section
        for section in sections:
            section_content = self._generate_section(section)
            if section_content:
                report_parts.append(section_content)

        return '\n\n'.join(report_parts)

    def _get_available_sections(self) -> List[str]:
        """
        Get list of available report sections.

        Returns:
            List of section names
        """
        sections = ['executive_summary']

        if 'comparison_matrix' in self.report_data:
            sections.append('comparison_matrix')

        if 'tco_analysis' in self.report_data:
            sections.append('tco_analysis')

        if 'ecosystem_health' in self.report_data:
            sections.append('ecosystem_health')

        if 'security_assessment' in self.report_data:
            sections.append('security_assessment')

        if 'migration_analysis' in self.report_data:
            sections.append('migration_analysis')

        if 'performance_benchmarks' in self.report_data:
            sections.append('performance_benchmarks')

        return sections

    def _generate_title(self) -> str:
        """Generate report title section."""
        technologies = self.report_data.get('technologies', [])
        tech_names = ' vs '.join(technologies)
        use_case = self.report_data.get('use_case', 'General Purpose')

        if self.output_context == 'desktop':
            return f"""# Technology Stack Evaluation Report

**Technologies**: {tech_names}
**Use Case**: {use_case}
**Generated**: {self._get_timestamp()}

---
"""
        else:  # CLI
            return f"""================================================================================
TECHNOLOGY STACK EVALUATION REPORT
================================================================================

Technologies: {tech_names}
Use Case: {use_case}
Generated: {self._get_timestamp()}

================================================================================
"""

    def _generate_section(self, section_name: str) -> Optional[str]:
        """
        Generate specific report section.

        Args:
            section_name: Name of section to generate

        Returns:
            Section markdown or None
        """
        generators = {
            'executive_summary': self._section_executive_summary,
            'comparison_matrix': self._section_comparison_matrix,
            'tco_analysis': self._section_tco_analysis,
            'ecosystem_health': self._section_ecosystem_health,
            'security_assessment': self._section_security_assessment,
            'migration_analysis': self._section_migration_analysis,
            'performance_benchmarks': self._section_performance_benchmarks
        }

        generator = generators.get(section_name)
        if generator:
            return generator()

        return None

    def _section_executive_summary(self) -> str:
        """Generate executive summary section."""
        return self.generate_executive_summary()

    def _section_comparison_matrix(self) -> str:
        """Generate comparison matrix section."""
        matrix_data = self.report_data.get('comparison_matrix', [])
        if not matrix_data:
            return ""

        if self.output_context == 'desktop':
            return self._render_matrix_desktop(matrix_data)
        else:
            return self._render_matrix_cli(matrix_data)

    def _render_matrix_desktop(self, matrix_data: List[Dict[str, Any]]) -> str:
        """Render comparison matrix for desktop (rich markdown table)."""
        parts = ["## Comparison Matrix\n"]

        if not matrix_data:
            return ""

        # Get technology names from first row
        tech_names = list(matrix_data[0].get('scores', {}).keys())

        # Build table header
        header = "| Category | Weight |"
        for tech in tech_names:
            header += f" {tech} |"
        parts.append(header)

        # Separator
        separator = "|----------|--------|"
        separator += "--------|" * len(tech_names)
        parts.append(separator)

        # Rows
        for row in matrix_data:
            category = row.get('category', '').replace('_', ' ').title()
            weight = row.get('weight', '')
            scores = row.get('scores', {})

            row_str = f"| {category} | {weight} |"
            for tech in tech_names:
                score = scores.get(tech, '0.0')
                row_str += f" {score} |"

            parts.append(row_str)

        return '\n'.join(parts)

    def _render_matrix_cli(self, matrix_data: List[Dict[str, Any]]) -> str:
        """Render comparison matrix for CLI (ASCII table)."""
        parts = ["COMPARISON MATRIX", "=" * 80, ""]

        if not matrix_data:
            return ""

        # Get technology names
        tech_names = list(matrix_data[0].get('scores', {}).keys())

        # Calculate column widths
        category_width = 25
        weight_width = 8
        score_width = 10

        # Header
        header = f"{'Category':<{category_width}} {'Weight':<{weight_width}}"
        for tech in tech_names:
            header += f" {tech[:score_width-1]:<{score_width}}"
        parts.append(header)
        parts.append("-" * 80)

        # Rows
        for row in matrix_data:
            category = row.get('category', '').replace('_', ' ').title()[:category_width-1]
            weight = row.get('weight', '')
            scores = row.get('scores', {})

            row_str = f"{category:<{category_width}} {weight:<{weight_width}}"
            for tech in tech_names:
                score = scores.get(tech, '0.0')
                row_str += f" {score:<{score_width}}"

            parts.append(row_str)

        return '\n'.join(parts)

    def _section_tco_analysis(self) -> str:
        """Generate TCO analysis section."""
        tco_data = self.report_data.get('tco_analysis', {})
        if not tco_data:
            return ""

        parts = ["## Total Cost of Ownership Analysis\n"]

        # Summary
        total_tco = tco_data.get('total_tco', 0)
        timeline = tco_data.get('timeline_years', 5)
        avg_yearly = tco_data.get('average_yearly_cost', 0)

        parts.append(f"**{timeline}-Year Total**: ${total_tco:,.2f}")
        parts.append(f"**Average Yearly**: ${avg_yearly:,.2f}\n")

        # Cost breakdown
        initial = tco_data.get('initial_costs', {})
        parts.append(f"### Initial Costs: ${initial.get('total_initial', 0):,.2f}")

        # Operational costs
        operational = tco_data.get('operational_costs', {})
        if operational:
            parts.append(f"\n### Operational Costs (Yearly)")
            yearly_totals = operational.get('total_yearly', [])
            for year, cost in enumerate(yearly_totals, 1):
                parts.append(f"- Year {year}: ${cost:,.2f}")

        return '\n'.join(parts)

    def _section_ecosystem_health(self) -> str:
        """Generate ecosystem health section."""
        ecosystem_data = self.report_data.get('ecosystem_health', {})
        if not ecosystem_data:
            return ""

        parts = ["## Ecosystem Health Analysis\n"]

        # Overall score
        overall_score = ecosystem_data.get('overall_health', 0)
        parts.append(f"**Overall Health Score**: {overall_score:.1f}/100\n")

        # Component scores
        scores = ecosystem_data.get('health_scores', {})
        parts.append("### Health Metrics")
        for metric, score in scores.items():
            if metric != 'overall_health':
                metric_name = metric.replace('_', ' ').title()
                parts.append(f"- {metric_name}: {score:.1f}/100")

        # Viability assessment
        viability = ecosystem_data.get('viability_assessment', {})
        if viability:
            parts.append(f"\n### Viability: {viability.get('overall_viability', 'Unknown')}")
            parts.append(f"**Risk Level**: {viability.get('risk_level', 'Unknown')}")

        return '\n'.join(parts)

    def _section_security_assessment(self) -> str:
        """Generate security assessment section."""
        security_data = self.report_data.get('security_assessment', {})
        if not security_data:
            return ""

        parts = ["## Security & Compliance Assessment\n"]

        # Security score
        security_score = security_data.get('security_score', {})
        overall = security_score.get('overall_security_score', 0)
        grade = security_score.get('security_grade', 'N/A')

        parts.append(f"**Security Score**: {overall:.1f}/100 (Grade: {grade})\n")

        # Compliance
        compliance = security_data.get('compliance_assessment', {})
        if compliance:
            parts.append("### Compliance Readiness")
            for standard, assessment in compliance.items():
                level = assessment.get('readiness_level', 'Unknown')
                pct = assessment.get('readiness_percentage', 0)
                parts.append(f"- **{standard}**: {level} ({pct:.0f}%)")

        return '\n'.join(parts)

    def _section_migration_analysis(self) -> str:
        """Generate migration analysis section."""
        migration_data = self.report_data.get('migration_analysis', {})
        if not migration_data:
            return ""

        parts = ["## Migration Path Analysis\n"]

        # Complexity
        complexity = migration_data.get('complexity_analysis', {})
        overall_complexity = complexity.get('overall_complexity', 0)
        parts.append(f"**Migration Complexity**: {overall_complexity:.1f}/10\n")

        # Effort estimation
        effort = migration_data.get('effort_estimation', {})
        if effort:
            total_hours = effort.get('total_hours', 0)
            person_months = effort.get('total_person_months', 0)
            timeline = effort.get('estimated_timeline', {})
            calendar_months = timeline.get('calendar_months', 0)

            parts.append(f"### Effort Estimate")
            parts.append(f"- Total Effort: {person_months:.1f} person-months ({total_hours:.0f} hours)")
            parts.append(f"- Timeline: {calendar_months:.1f} calendar months")

        # Recommended approach
        approach = migration_data.get('recommended_approach', {})
        if approach:
            parts.append(f"\n### Recommended Approach: {approach.get('approach', 'Unknown').replace('_', ' ').title()}")
            parts.append(f"{approach.get('description', '')}")

        return '\n'.join(parts)

    def _section_performance_benchmarks(self) -> str:
        """Generate performance benchmarks section."""
        benchmark_data = self.report_data.get('performance_benchmarks', {})
        if not benchmark_data:
            return ""

        parts = ["## Performance Benchmarks\n"]

        # Throughput
        throughput = benchmark_data.get('throughput', {})
        if throughput:
            parts.append("### Throughput")
            for tech, rps in throughput.items():
                parts.append(f"- {tech}: {rps:,} requests/sec")

        # Latency
        latency = benchmark_data.get('latency', {})
        if latency:
            parts.append("\n### Latency (P95)")
            for tech, ms in latency.items():
                parts.append(f"- {tech}: {ms}ms")

        return '\n'.join(parts)

    def _get_timestamp(self) -> str:
        """Get current timestamp."""
        from datetime import datetime
        return datetime.now().strftime("%Y-%m-%d %H:%M")

    def export_to_file(self, filename: str, sections: Optional[List[str]] = None) -> str:
        """
        Export report to file.

        Args:
            filename: Output filename
            sections: Sections to include

        Returns:
            Path to exported file
        """
        report = self.generate_full_report(sections)

        with open(filename, 'w', encoding='utf-8') as f:
            f.write(report)

        return filename
