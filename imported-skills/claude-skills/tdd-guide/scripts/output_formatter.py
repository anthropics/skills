"""
Output formatting module.

Provides context-aware output formatting for different environments (Desktop, CLI, API).
Implements progressive disclosure and token-efficient reporting.
"""

from typing import Dict, List, Any, Optional


class OutputFormatter:
    """Format output based on environment and preferences."""

    def __init__(self, environment: str = "cli", verbose: bool = False):
        """
        Initialize output formatter.

        Args:
            environment: Target environment (desktop, cli, api)
            verbose: Whether to include detailed output
        """
        self.environment = environment
        self.verbose = verbose

    def format_coverage_summary(
        self,
        summary: Dict[str, Any],
        detailed: bool = False
    ) -> str:
        """
        Format coverage summary.

        Args:
            summary: Coverage summary data
            detailed: Whether to include detailed breakdown

        Returns:
            Formatted coverage summary
        """
        if self.environment == "desktop":
            return self._format_coverage_markdown(summary, detailed)
        elif self.environment == "api":
            return self._format_coverage_json(summary)
        else:
            return self._format_coverage_terminal(summary, detailed)

    def _format_coverage_markdown(self, summary: Dict[str, Any], detailed: bool) -> str:
        """Format coverage as rich markdown (for Claude Desktop)."""
        lines = ["## Test Coverage Summary\n"]

        # Overall metrics
        lines.append("### Overall Metrics")
        lines.append(f"- **Line Coverage**: {summary.get('line_coverage', 0):.1f}%")
        lines.append(f"- **Branch Coverage**: {summary.get('branch_coverage', 0):.1f}%")
        lines.append(f"- **Function Coverage**: {summary.get('function_coverage', 0):.1f}%\n")

        # Visual indicator
        line_cov = summary.get('line_coverage', 0)
        lines.append(self._coverage_badge(line_cov))
        lines.append("")

        # Detailed breakdown if requested
        if detailed:
            lines.append("### Detailed Breakdown")
            lines.append(f"- Total Lines: {summary.get('total_lines', 0)}")
            lines.append(f"- Covered Lines: {summary.get('covered_lines', 0)}")
            lines.append(f"- Total Branches: {summary.get('total_branches', 0)}")
            lines.append(f"- Covered Branches: {summary.get('covered_branches', 0)}")
            lines.append(f"- Total Functions: {summary.get('total_functions', 0)}")
            lines.append(f"- Covered Functions: {summary.get('covered_functions', 0)}\n")

        return "\n".join(lines)

    def _format_coverage_terminal(self, summary: Dict[str, Any], detailed: bool) -> str:
        """Format coverage for terminal (Claude Code CLI)."""
        lines = ["Coverage Summary:"]
        lines.append(f"  Line:     {summary.get('line_coverage', 0):.1f}%")
        lines.append(f"  Branch:   {summary.get('branch_coverage', 0):.1f}%")
        lines.append(f"  Function: {summary.get('function_coverage', 0):.1f}%")

        if detailed:
            lines.append(f"\nDetails:")
            lines.append(f"  Lines: {summary.get('covered_lines', 0)}/{summary.get('total_lines', 0)}")
            lines.append(f"  Branches: {summary.get('covered_branches', 0)}/{summary.get('total_branches', 0)}")

        return "\n".join(lines)

    def _format_coverage_json(self, summary: Dict[str, Any]) -> str:
        """Format coverage as JSON (for API/CI integration)."""
        import json
        return json.dumps(summary, indent=2)

    def _coverage_badge(self, coverage: float) -> str:
        """Generate coverage badge markdown."""
        if coverage >= 80:
            color = "green"
            emoji = "✅"
        elif coverage >= 60:
            color = "yellow"
            emoji = "⚠️"
        else:
            color = "red"
            emoji = "❌"

        return f"{emoji} **{coverage:.1f}%** coverage ({color})"

    def format_recommendations(
        self,
        recommendations: List[Dict[str, Any]],
        max_items: Optional[int] = None
    ) -> str:
        """
        Format recommendations with progressive disclosure.

        Args:
            recommendations: List of recommendation dictionaries
            max_items: Maximum number of items to show (None for all)

        Returns:
            Formatted recommendations
        """
        if not recommendations:
            return "No recommendations at this time."

        # Group by priority
        p0 = [r for r in recommendations if r.get('priority') == 'P0']
        p1 = [r for r in recommendations if r.get('priority') == 'P1']
        p2 = [r for r in recommendations if r.get('priority') == 'P2']

        if self.environment == "desktop":
            return self._format_recommendations_markdown(p0, p1, p2, max_items)
        elif self.environment == "api":
            return self._format_recommendations_json(recommendations)
        else:
            return self._format_recommendations_terminal(p0, p1, p2, max_items)

    def _format_recommendations_markdown(
        self,
        p0: List[Dict],
        p1: List[Dict],
        p2: List[Dict],
        max_items: Optional[int]
    ) -> str:
        """Format recommendations as rich markdown."""
        lines = ["## Recommendations\n"]

        if p0:
            lines.append("### 🔴 Critical (P0)")
            for i, rec in enumerate(p0[:max_items] if max_items else p0):
                lines.append(f"{i+1}. **{rec.get('message', 'No message')}**")
                lines.append(f"   - Action: {rec.get('action', 'No action specified')}")
                if 'file' in rec:
                    lines.append(f"   - File: `{rec['file']}`")
                lines.append("")

        if p1 and (not max_items or len(p0) < max_items):
            remaining = max_items - len(p0) if max_items else None
            lines.append("### 🟡 Important (P1)")
            for i, rec in enumerate(p1[:remaining] if remaining else p1):
                lines.append(f"{i+1}. {rec.get('message', 'No message')}")
                lines.append(f"   - Action: {rec.get('action', 'No action specified')}")
                lines.append("")

        if p2 and self.verbose:
            lines.append("### 🔵 Nice to Have (P2)")
            for i, rec in enumerate(p2):
                lines.append(f"{i+1}. {rec.get('message', 'No message')}")
                lines.append("")

        return "\n".join(lines)

    def _format_recommendations_terminal(
        self,
        p0: List[Dict],
        p1: List[Dict],
        p2: List[Dict],
        max_items: Optional[int]
    ) -> str:
        """Format recommendations for terminal."""
        lines = ["Recommendations:"]

        if p0:
            lines.append("\nCritical (P0):")
            for i, rec in enumerate(p0[:max_items] if max_items else p0):
                lines.append(f"  {i+1}. {rec.get('message', 'No message')}")
                lines.append(f"     Action: {rec.get('action', 'No action')}")

        if p1 and (not max_items or len(p0) < max_items):
            remaining = max_items - len(p0) if max_items else None
            lines.append("\nImportant (P1):")
            for i, rec in enumerate(p1[:remaining] if remaining else p1):
                lines.append(f"  {i+1}. {rec.get('message', 'No message')}")

        return "\n".join(lines)

    def _format_recommendations_json(self, recommendations: List[Dict[str, Any]]) -> str:
        """Format recommendations as JSON."""
        import json
        return json.dumps(recommendations, indent=2)

    def format_test_results(
        self,
        results: Dict[str, Any],
        show_details: bool = False
    ) -> str:
        """
        Format test execution results.

        Args:
            results: Test results data
            show_details: Whether to show detailed results

        Returns:
            Formatted test results
        """
        if self.environment == "desktop":
            return self._format_results_markdown(results, show_details)
        elif self.environment == "api":
            return self._format_results_json(results)
        else:
            return self._format_results_terminal(results, show_details)

    def _format_results_markdown(self, results: Dict[str, Any], show_details: bool) -> str:
        """Format test results as markdown."""
        lines = ["## Test Results\n"]

        total = results.get('total_tests', 0)
        passed = results.get('passed', 0)
        failed = results.get('failed', 0)
        skipped = results.get('skipped', 0)

        # Summary
        lines.append(f"- **Total Tests**: {total}")
        lines.append(f"- **Passed**: ✅ {passed}")
        if failed > 0:
            lines.append(f"- **Failed**: ❌ {failed}")
        if skipped > 0:
            lines.append(f"- **Skipped**: ⏭️ {skipped}")

        # Pass rate
        pass_rate = (passed / total * 100) if total > 0 else 0
        lines.append(f"- **Pass Rate**: {pass_rate:.1f}%\n")

        # Failed tests details
        if show_details and failed > 0:
            lines.append("### Failed Tests")
            for test in results.get('failed_tests', []):
                lines.append(f"- `{test.get('name', 'Unknown')}`")
                if 'error' in test:
                    lines.append(f"  ```\n  {test['error']}\n  ```")

        return "\n".join(lines)

    def _format_results_terminal(self, results: Dict[str, Any], show_details: bool) -> str:
        """Format test results for terminal."""
        total = results.get('total_tests', 0)
        passed = results.get('passed', 0)
        failed = results.get('failed', 0)

        lines = [f"Test Results: {passed}/{total} passed"]

        if failed > 0:
            lines.append(f"  Failed: {failed}")

        if show_details and failed > 0:
            lines.append("\nFailed tests:")
            for test in results.get('failed_tests', [])[:5]:
                lines.append(f"  - {test.get('name', 'Unknown')}")

        return "\n".join(lines)

    def _format_results_json(self, results: Dict[str, Any]) -> str:
        """Format test results as JSON."""
        import json
        return json.dumps(results, indent=2)

    def create_summary_report(
        self,
        coverage: Dict[str, Any],
        metrics: Dict[str, Any],
        recommendations: List[Dict[str, Any]]
    ) -> str:
        """
        Create comprehensive summary report (token-efficient).

        Args:
            coverage: Coverage data
            metrics: Quality metrics
            recommendations: Recommendations list

        Returns:
            Summary report (<200 tokens)
        """
        lines = []

        # Coverage (1-2 lines)
        line_cov = coverage.get('line_coverage', 0)
        branch_cov = coverage.get('branch_coverage', 0)
        lines.append(f"Coverage: {line_cov:.0f}% lines, {branch_cov:.0f}% branches")

        # Quality (1-2 lines)
        if 'test_quality' in metrics:
            quality_score = metrics['test_quality'].get('quality_score', 0)
            lines.append(f"Test Quality: {quality_score:.0f}/100")

        # Top recommendations (2-3 lines)
        p0_count = sum(1 for r in recommendations if r.get('priority') == 'P0')
        if p0_count > 0:
            lines.append(f"Critical issues: {p0_count}")
            top_rec = next((r for r in recommendations if r.get('priority') == 'P0'), None)
            if top_rec:
                lines.append(f"  - {top_rec.get('message', '')}")

        return "\n".join(lines)

    def should_show_detailed(self, data_size: int) -> bool:
        """
        Determine if detailed output should be shown based on data size.

        Args:
            data_size: Size of data to display

        Returns:
            Whether to show detailed output
        """
        if self.verbose:
            return True

        # Progressive disclosure thresholds
        if self.environment == "desktop":
            return data_size < 100  # Show more in Desktop
        else:
            return data_size < 20  # Show less in CLI

    def truncate_output(self, text: str, max_lines: int = 50) -> str:
        """
        Truncate output to maximum lines.

        Args:
            text: Text to truncate
            max_lines: Maximum number of lines

        Returns:
            Truncated text with indicator
        """
        lines = text.split('\n')

        if len(lines) <= max_lines:
            return text

        truncated = '\n'.join(lines[:max_lines])
        remaining = len(lines) - max_lines

        return f"{truncated}\n\n... ({remaining} more lines, use --verbose for full output)"
