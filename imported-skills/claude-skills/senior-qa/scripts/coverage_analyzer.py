#!/usr/bin/env python3
"""
Coverage Analyzer

Parses Jest/Istanbul coverage reports and identifies gaps, uncovered branches,
and provides actionable recommendations for improving test coverage.

Usage:
    python coverage_analyzer.py coverage/coverage-final.json --threshold 80
    python coverage_analyzer.py coverage/ --format html --output report.html
    python coverage_analyzer.py coverage/ --critical-paths
"""

import os
import sys
import json
import argparse
import re
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, field, asdict
from datetime import datetime
from collections import defaultdict


@dataclass
class FileCoverage:
    """Coverage data for a single file"""
    path: str
    statements: Tuple[int, int]  # (covered, total)
    branches: Tuple[int, int]
    functions: Tuple[int, int]
    lines: Tuple[int, int]
    uncovered_lines: List[int] = field(default_factory=list)
    uncovered_branches: List[str] = field(default_factory=list)

    @property
    def statement_pct(self) -> float:
        return (self.statements[0] / self.statements[1] * 100) if self.statements[1] > 0 else 100

    @property
    def branch_pct(self) -> float:
        return (self.branches[0] / self.branches[1] * 100) if self.branches[1] > 0 else 100

    @property
    def function_pct(self) -> float:
        return (self.functions[0] / self.functions[1] * 100) if self.functions[1] > 0 else 100

    @property
    def line_pct(self) -> float:
        return (self.lines[0] / self.lines[1] * 100) if self.lines[1] > 0 else 100


@dataclass
class CoverageGap:
    """An identified coverage gap"""
    file: str
    gap_type: str  # 'statements', 'branches', 'functions', 'lines'
    lines: List[int]
    severity: str  # 'critical', 'high', 'medium', 'low'
    description: str
    recommendation: str


@dataclass
class CoverageSummary:
    """Overall coverage summary"""
    statements: Tuple[int, int]
    branches: Tuple[int, int]
    functions: Tuple[int, int]
    lines: Tuple[int, int]
    files_analyzed: int
    files_below_threshold: int = 0


class CoverageParser:
    """Parses various coverage report formats"""

    def __init__(self, verbose: bool = False):
        self.verbose = verbose

    def parse(self, path: Path) -> Tuple[Dict[str, FileCoverage], CoverageSummary]:
        """Parse coverage data from file or directory"""
        if path.is_file():
            if path.suffix == '.json':
                return self._parse_istanbul_json(path)
            elif path.suffix == '.info' or 'lcov' in path.name:
                return self._parse_lcov(path)
        elif path.is_dir():
            # Look for common coverage files
            for filename in ['coverage-final.json', 'coverage-summary.json', 'lcov.info']:
                candidate = path / filename
                if candidate.exists():
                    return self.parse(candidate)

            # Check for coverage-final.json in coverage directory
            coverage_json = path / 'coverage-final.json'
            if coverage_json.exists():
                return self._parse_istanbul_json(coverage_json)

        raise ValueError(f"Could not find or parse coverage data at: {path}")

    def _parse_istanbul_json(self, path: Path) -> Tuple[Dict[str, FileCoverage], CoverageSummary]:
        """Parse Istanbul/Jest JSON coverage format"""
        with open(path, 'r') as f:
            data = json.load(f)

        files = {}
        total_statements = [0, 0]
        total_branches = [0, 0]
        total_functions = [0, 0]
        total_lines = [0, 0]

        for file_path, file_data in data.items():
            # Skip node_modules
            if 'node_modules' in file_path:
                continue

            # Parse statement coverage
            s_map = file_data.get('statementMap', {})
            s_hits = file_data.get('s', {})
            covered_statements = sum(1 for h in s_hits.values() if h > 0)
            total_statements[0] += covered_statements
            total_statements[1] += len(s_map)

            # Parse branch coverage
            b_map = file_data.get('branchMap', {})
            b_hits = file_data.get('b', {})
            covered_branches = sum(
                sum(1 for h in hits if h > 0)
                for hits in b_hits.values()
            )
            total_branch_count = sum(len(b['locations']) for b in b_map.values())
            total_branches[0] += covered_branches
            total_branches[1] += total_branch_count

            # Parse function coverage
            fn_map = file_data.get('fnMap', {})
            fn_hits = file_data.get('f', {})
            covered_functions = sum(1 for h in fn_hits.values() if h > 0)
            total_functions[0] += covered_functions
            total_functions[1] += len(fn_map)

            # Determine uncovered lines
            uncovered_lines = []
            for stmt_id, hits in s_hits.items():
                if hits == 0 and stmt_id in s_map:
                    stmt = s_map[stmt_id]
                    start_line = stmt.get('start', {}).get('line', 0)
                    if start_line not in uncovered_lines:
                        uncovered_lines.append(start_line)

            # Count lines
            line_coverage = self._calculate_line_coverage(s_map, s_hits)
            total_lines[0] += line_coverage[0]
            total_lines[1] += line_coverage[1]

            # Identify uncovered branches
            uncovered_branches = []
            for branch_id, hits in b_hits.items():
                for idx, hit in enumerate(hits):
                    if hit == 0:
                        uncovered_branches.append(f"{branch_id}:{idx}")

            files[file_path] = FileCoverage(
                path=file_path,
                statements=(covered_statements, len(s_map)),
                branches=(covered_branches, total_branch_count),
                functions=(covered_functions, len(fn_map)),
                lines=line_coverage,
                uncovered_lines=sorted(uncovered_lines)[:50],  # Limit
                uncovered_branches=uncovered_branches[:20]
            )

        summary = CoverageSummary(
            statements=tuple(total_statements),
            branches=tuple(total_branches),
            functions=tuple(total_functions),
            lines=tuple(total_lines),
            files_analyzed=len(files)
        )

        return files, summary

    def _calculate_line_coverage(self, s_map: Dict, s_hits: Dict) -> Tuple[int, int]:
        """Calculate line coverage from statement data"""
        lines = set()
        covered_lines = set()

        for stmt_id, stmt in s_map.items():
            start_line = stmt.get('start', {}).get('line', 0)
            end_line = stmt.get('end', {}).get('line', start_line)
            for line in range(start_line, end_line + 1):
                lines.add(line)
                if s_hits.get(stmt_id, 0) > 0:
                    covered_lines.add(line)

        return (len(covered_lines), len(lines))

    def _parse_lcov(self, path: Path) -> Tuple[Dict[str, FileCoverage], CoverageSummary]:
        """Parse LCOV format coverage data"""
        with open(path, 'r') as f:
            content = f.read()

        files = {}
        current_file = None
        current_data = {}

        total = {
            'statements': [0, 0],
            'branches': [0, 0],
            'functions': [0, 0],
            'lines': [0, 0]
        }

        for line in content.split('\n'):
            line = line.strip()

            if line.startswith('SF:'):
                current_file = line[3:]
                current_data = {
                    'lines_hit': 0, 'lines_total': 0,
                    'functions_hit': 0, 'functions_total': 0,
                    'branches_hit': 0, 'branches_total': 0,
                    'uncovered_lines': []
                }
            elif line.startswith('DA:'):
                parts = line[3:].split(',')
                if len(parts) >= 2:
                    line_num = int(parts[0])
                    hits = int(parts[1])
                    current_data['lines_total'] += 1
                    if hits > 0:
                        current_data['lines_hit'] += 1
                    else:
                        current_data['uncovered_lines'].append(line_num)
            elif line.startswith('FN:'):
                current_data['functions_total'] += 1
            elif line.startswith('FNDA:'):
                parts = line[5:].split(',')
                if len(parts) >= 1 and int(parts[0]) > 0:
                    current_data['functions_hit'] += 1
            elif line.startswith('BRDA:'):
                parts = line[5:].split(',')
                current_data['branches_total'] += 1
                if len(parts) >= 4 and parts[3] != '-' and int(parts[3]) > 0:
                    current_data['branches_hit'] += 1
            elif line == 'end_of_record' and current_file:
                # Skip node_modules
                if 'node_modules' not in current_file:
                    files[current_file] = FileCoverage(
                        path=current_file,
                        statements=(current_data['lines_hit'], current_data['lines_total']),
                        branches=(current_data['branches_hit'], current_data['branches_total']),
                        functions=(current_data['functions_hit'], current_data['functions_total']),
                        lines=(current_data['lines_hit'], current_data['lines_total']),
                        uncovered_lines=current_data['uncovered_lines'][:50]
                    )

                    for key in total:
                        if key == 'statements' or key == 'lines':
                            total[key][0] += current_data['lines_hit']
                            total[key][1] += current_data['lines_total']
                        elif key == 'branches':
                            total[key][0] += current_data['branches_hit']
                            total[key][1] += current_data['branches_total']
                        elif key == 'functions':
                            total[key][0] += current_data['functions_hit']
                            total[key][1] += current_data['functions_total']

                current_file = None

        summary = CoverageSummary(
            statements=tuple(total['statements']),
            branches=tuple(total['branches']),
            functions=tuple(total['functions']),
            lines=tuple(total['lines']),
            files_analyzed=len(files)
        )

        return files, summary


class CoverageAnalyzer:
    """Analyzes coverage data and generates recommendations"""

    CRITICAL_PATTERNS = [
        r'auth', r'payment', r'security', r'login', r'register',
        r'checkout', r'order', r'transaction', r'billing'
    ]

    SERVICE_PATTERNS = [
        r'service', r'api', r'handler', r'controller', r'middleware'
    ]

    def __init__(
        self,
        threshold: int = 80,
        critical_paths: bool = False,
        verbose: bool = False
    ):
        self.threshold = threshold
        self.critical_paths = critical_paths
        self.verbose = verbose

    def analyze(
        self,
        files: Dict[str, FileCoverage],
        summary: CoverageSummary
    ) -> Tuple[List[CoverageGap], Dict[str, Any]]:
        """Analyze coverage and return gaps and recommendations"""
        gaps = []
        recommendations = {
            'critical': [],
            'high': [],
            'medium': [],
            'low': []
        }

        # Analyze each file
        for file_path, coverage in files.items():
            file_gaps = self._analyze_file(file_path, coverage)
            gaps.extend(file_gaps)

        # Sort gaps by severity
        severity_order = {'critical': 0, 'high': 1, 'medium': 2, 'low': 3}
        gaps.sort(key=lambda g: (severity_order[g.severity], -len(g.lines)))

        # Generate recommendations
        for gap in gaps:
            recommendations[gap.severity].append({
                'file': gap.file,
                'type': gap.gap_type,
                'lines': gap.lines[:10],  # Limit
                'description': gap.description,
                'recommendation': gap.recommendation
            })

        # Add summary stats
        stats = {
            'overall_statement_pct': (summary.statements[0] / summary.statements[1] * 100) if summary.statements[1] > 0 else 100,
            'overall_branch_pct': (summary.branches[0] / summary.branches[1] * 100) if summary.branches[1] > 0 else 100,
            'overall_function_pct': (summary.functions[0] / summary.functions[1] * 100) if summary.functions[1] > 0 else 100,
            'overall_line_pct': (summary.lines[0] / summary.lines[1] * 100) if summary.lines[1] > 0 else 100,
            'files_analyzed': summary.files_analyzed,
            'files_below_threshold': sum(
                1 for f in files.values()
                if f.line_pct < self.threshold
            ),
            'total_gaps': len(gaps),
            'critical_gaps': len(recommendations['critical']),
            'threshold': self.threshold,
            'meets_threshold': (summary.lines[0] / summary.lines[1] * 100) >= self.threshold if summary.lines[1] > 0 else True
        }

        return gaps, {
            'recommendations': recommendations,
            'stats': stats
        }

    def _analyze_file(self, file_path: str, coverage: FileCoverage) -> List[CoverageGap]:
        """Analyze a single file for coverage gaps"""
        gaps = []

        # Determine if file is critical
        is_critical = any(
            re.search(pattern, file_path.lower())
            for pattern in self.CRITICAL_PATTERNS
        )

        is_service = any(
            re.search(pattern, file_path.lower())
            for pattern in self.SERVICE_PATTERNS
        )

        # Determine severity based on file type and coverage level
        if is_critical:
            base_severity = 'critical'
            target_threshold = 95
        elif is_service:
            base_severity = 'high'
            target_threshold = 85
        else:
            base_severity = 'medium'
            target_threshold = self.threshold

        # Check line coverage
        if coverage.line_pct < target_threshold:
            severity = base_severity if coverage.line_pct < 50 else self._lower_severity(base_severity)

            gaps.append(CoverageGap(
                file=file_path,
                gap_type='lines',
                lines=coverage.uncovered_lines[:20],
                severity=severity,
                description=f"Line coverage at {coverage.line_pct:.1f}% (target: {target_threshold}%)",
                recommendation=self._get_line_recommendation(coverage)
            ))

        # Check branch coverage
        if coverage.branch_pct < target_threshold - 5:  # Allow 5% less for branches
            severity = base_severity if coverage.branch_pct < 40 else self._lower_severity(base_severity)

            gaps.append(CoverageGap(
                file=file_path,
                gap_type='branches',
                lines=[],
                severity=severity,
                description=f"Branch coverage at {coverage.branch_pct:.1f}%",
                recommendation=f"Add tests for conditional logic. {len(coverage.uncovered_branches)} uncovered branches."
            ))

        # Check function coverage
        if coverage.function_pct < target_threshold:
            severity = self._lower_severity(base_severity)

            gaps.append(CoverageGap(
                file=file_path,
                gap_type='functions',
                lines=[],
                severity=severity,
                description=f"Function coverage at {coverage.function_pct:.1f}%",
                recommendation="Add tests for uncovered functions/methods."
            ))

        return gaps

    def _lower_severity(self, severity: str) -> str:
        """Lower severity by one level"""
        mapping = {
            'critical': 'high',
            'high': 'medium',
            'medium': 'low',
            'low': 'low'
        }
        return mapping[severity]

    def _get_line_recommendation(self, coverage: FileCoverage) -> str:
        """Generate recommendation for line coverage gaps"""
        if coverage.line_pct < 30:
            return "This file has very low coverage. Consider adding basic render/unit tests first."
        elif coverage.line_pct < 60:
            return "Add tests covering the main functionality and happy paths."
        else:
            return "Focus on edge cases and error handling paths."


class ReportGenerator:
    """Generates coverage reports in various formats"""

    def __init__(self, verbose: bool = False):
        self.verbose = verbose

    def generate_text_report(
        self,
        files: Dict[str, FileCoverage],
        summary: CoverageSummary,
        analysis: Dict[str, Any],
        threshold: int
    ) -> str:
        """Generate a text report"""
        lines = []

        # Header
        lines.append("=" * 60)
        lines.append("COVERAGE ANALYSIS REPORT")
        lines.append(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        lines.append("=" * 60)
        lines.append("")

        # Overall summary
        stats = analysis['stats']
        lines.append("OVERALL COVERAGE:")
        lines.append(f"  Statements: {stats['overall_statement_pct']:.1f}%")
        lines.append(f"  Branches:   {stats['overall_branch_pct']:.1f}%")
        lines.append(f"  Functions:  {stats['overall_function_pct']:.1f}%")
        lines.append(f"  Lines:      {stats['overall_line_pct']:.1f}%")
        lines.append("")

        # Threshold check
        threshold_status = "PASS" if stats['meets_threshold'] else "FAIL"
        lines.append(f"Threshold ({threshold}%): {threshold_status}")
        lines.append(f"Files analyzed: {stats['files_analyzed']}")
        lines.append(f"Files below threshold: {stats['files_below_threshold']}")
        lines.append("")

        # Critical gaps
        recs = analysis['recommendations']
        if recs['critical']:
            lines.append("-" * 60)
            lines.append("CRITICAL GAPS (requires immediate attention):")
            for rec in recs['critical'][:5]:
                lines.append(f"  - {rec['file']}")
                lines.append(f"    {rec['description']}")
                if rec['lines']:
                    lines.append(f"    Uncovered lines: {', '.join(map(str, rec['lines'][:5]))}")
            lines.append("")

        # High priority gaps
        if recs['high']:
            lines.append("-" * 60)
            lines.append("HIGH PRIORITY GAPS:")
            for rec in recs['high'][:5]:
                lines.append(f"  - {rec['file']}")
                lines.append(f"    {rec['description']}")
            lines.append("")

        # Files below threshold
        below_threshold = [
            (path, cov) for path, cov in files.items()
            if cov.line_pct < threshold
        ]
        below_threshold.sort(key=lambda x: x[1].line_pct)

        if below_threshold:
            lines.append("-" * 60)
            lines.append(f"FILES BELOW {threshold}% THRESHOLD:")
            for path, cov in below_threshold[:10]:
                short_path = path.split('/')[-1] if '/' in path else path
                lines.append(f"  {cov.line_pct:5.1f}%  {short_path}")
            if len(below_threshold) > 10:
                lines.append(f"  ... and {len(below_threshold) - 10} more files")
            lines.append("")

        # Recommendations
        lines.append("-" * 60)
        lines.append("RECOMMENDATIONS:")
        all_recs = (
            recs['critical'][:2] + recs['high'][:2] + recs['medium'][:2]
        )
        for i, rec in enumerate(all_recs[:5], 1):
            lines.append(f"  {i}. {rec['recommendation']}")
            lines.append(f"     File: {rec['file']}")
        lines.append("")

        lines.append("=" * 60)
        return '\n'.join(lines)

    def generate_html_report(
        self,
        files: Dict[str, FileCoverage],
        summary: CoverageSummary,
        analysis: Dict[str, Any],
        threshold: int
    ) -> str:
        """Generate an HTML report"""
        stats = analysis['stats']
        recs = analysis['recommendations']

        html = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Coverage Analysis Report</title>
    <style>
        body {{ font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif; margin: 40px; }}
        h1 {{ color: #333; }}
        .summary {{ display: grid; grid-template-columns: repeat(4, 1fr); gap: 20px; margin: 20px 0; }}
        .stat {{ background: #f5f5f5; padding: 20px; border-radius: 8px; text-align: center; }}
        .stat-value {{ font-size: 2em; font-weight: bold; }}
        .pass {{ color: #22c55e; }}
        .fail {{ color: #ef4444; }}
        .warn {{ color: #f59e0b; }}
        table {{ width: 100%; border-collapse: collapse; margin: 20px 0; }}
        th, td {{ padding: 12px; text-align: left; border-bottom: 1px solid #ddd; }}
        th {{ background: #f5f5f5; }}
        .gap-critical {{ background: #fef2f2; }}
        .gap-high {{ background: #fffbeb; }}
        .progress {{ background: #e5e7eb; border-radius: 4px; height: 8px; }}
        .progress-bar {{ height: 100%; border-radius: 4px; }}
    </style>
</head>
<body>
    <h1>Coverage Analysis Report</h1>
    <p>Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}</p>

    <div class="summary">
        <div class="stat">
            <div class="stat-value {'pass' if stats['overall_statement_pct'] >= threshold else 'fail'}">{stats['overall_statement_pct']:.1f}%</div>
            <div>Statements</div>
        </div>
        <div class="stat">
            <div class="stat-value {'pass' if stats['overall_branch_pct'] >= threshold - 5 else 'fail'}">{stats['overall_branch_pct']:.1f}%</div>
            <div>Branches</div>
        </div>
        <div class="stat">
            <div class="stat-value {'pass' if stats['overall_function_pct'] >= threshold else 'fail'}">{stats['overall_function_pct']:.1f}%</div>
            <div>Functions</div>
        </div>
        <div class="stat">
            <div class="stat-value {'pass' if stats['overall_line_pct'] >= threshold else 'fail'}">{stats['overall_line_pct']:.1f}%</div>
            <div>Lines</div>
        </div>
    </div>

    <h2>Threshold Status: <span class="{'pass' if stats['meets_threshold'] else 'fail'}">{'PASS' if stats['meets_threshold'] else 'FAIL'}</span></h2>
    <p>Target: {threshold}% | Files Analyzed: {stats['files_analyzed']} | Below Threshold: {stats['files_below_threshold']}</p>

    <h2>Coverage Gaps</h2>
    <table>
        <thead>
            <tr>
                <th>Severity</th>
                <th>File</th>
                <th>Issue</th>
                <th>Recommendation</th>
            </tr>
        </thead>
        <tbody>
"""

        # Add gaps to table
        all_gaps = (
            [(g, 'critical') for g in recs['critical']] +
            [(g, 'high') for g in recs['high']] +
            [(g, 'medium') for g in recs['medium'][:5]]
        )

        for gap, severity in all_gaps[:15]:
            row_class = f"gap-{severity}" if severity in ['critical', 'high'] else ""
            html += f"""            <tr class="{row_class}">
                <td>{severity.upper()}</td>
                <td>{gap['file'].split('/')[-1]}</td>
                <td>{gap['description']}</td>
                <td>{gap['recommendation']}</td>
            </tr>
"""

        html += """        </tbody>
    </table>

    <h2>File Coverage Details</h2>
    <table>
        <thead>
            <tr>
                <th>File</th>
                <th>Statements</th>
                <th>Branches</th>
                <th>Functions</th>
                <th>Lines</th>
            </tr>
        </thead>
        <tbody>
"""

        # Sort files by line coverage
        sorted_files = sorted(files.items(), key=lambda x: x[1].line_pct)

        for path, cov in sorted_files[:20]:
            short_path = path.split('/')[-1] if '/' in path else path
            html += f"""            <tr>
                <td>{short_path}</td>
                <td>{cov.statement_pct:.1f}%</td>
                <td>{cov.branch_pct:.1f}%</td>
                <td>{cov.function_pct:.1f}%</td>
                <td>{cov.line_pct:.1f}%</td>
            </tr>
"""

        html += """        </tbody>
    </table>
</body>
</html>
"""
        return html


class CoverageAnalyzerTool:
    """Main tool class"""

    def __init__(
        self,
        coverage_path: str,
        threshold: int = 80,
        critical_paths: bool = False,
        strict: bool = False,
        output_format: str = 'text',
        output_path: Optional[str] = None,
        verbose: bool = False
    ):
        self.coverage_path = Path(coverage_path)
        self.threshold = threshold
        self.critical_paths = critical_paths
        self.strict = strict
        self.output_format = output_format
        self.output_path = output_path
        self.verbose = verbose

    def run(self) -> Dict[str, Any]:
        """Run the coverage analysis"""
        print(f"Analyzing coverage from: {self.coverage_path}")

        # Parse coverage data
        parser = CoverageParser(self.verbose)
        files, summary = parser.parse(self.coverage_path)

        print(f"Found coverage data for {len(files)} files")

        # Analyze coverage
        analyzer = CoverageAnalyzer(
            threshold=self.threshold,
            critical_paths=self.critical_paths,
            verbose=self.verbose
        )
        gaps, analysis = analyzer.analyze(files, summary)

        # Generate report
        reporter = ReportGenerator(self.verbose)

        if self.output_format == 'html':
            report = reporter.generate_html_report(files, summary, analysis, self.threshold)
        else:
            report = reporter.generate_text_report(files, summary, analysis, self.threshold)

        # Output report
        if self.output_path:
            with open(self.output_path, 'w') as f:
                f.write(report)
            print(f"Report written to: {self.output_path}")
        else:
            print(report)

        # Return results
        results = {
            'status': 'pass' if analysis['stats']['meets_threshold'] else 'fail',
            'threshold': self.threshold,
            'coverage': {
                'statements': analysis['stats']['overall_statement_pct'],
                'branches': analysis['stats']['overall_branch_pct'],
                'functions': analysis['stats']['overall_function_pct'],
                'lines': analysis['stats']['overall_line_pct']
            },
            'files_analyzed': summary.files_analyzed,
            'files_below_threshold': analysis['stats']['files_below_threshold'],
            'total_gaps': analysis['stats']['total_gaps'],
            'critical_gaps': analysis['stats']['critical_gaps']
        }

        # Exit with error if strict mode and below threshold
        if self.strict and not analysis['stats']['meets_threshold']:
            print(f"\nFailed: Coverage {analysis['stats']['overall_line_pct']:.1f}% below threshold {self.threshold}%")
            sys.exit(1)

        return results


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description="Analyze Jest/Istanbul coverage reports and identify gaps",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Basic analysis
  python coverage_analyzer.py coverage/coverage-final.json

  # With threshold enforcement
  python coverage_analyzer.py coverage/ --threshold 80 --strict

  # Generate HTML report
  python coverage_analyzer.py coverage/ --format html --output report.html

  # Focus on critical paths
  python coverage_analyzer.py coverage/ --critical-paths
        """
    )
    parser.add_argument(
        'coverage',
        help='Path to coverage file or directory'
    )
    parser.add_argument(
        '--threshold', '-t',
        type=int,
        default=80,
        help='Coverage threshold percentage (default: 80)'
    )
    parser.add_argument(
        '--strict',
        action='store_true',
        help='Exit with error if coverage is below threshold'
    )
    parser.add_argument(
        '--critical-paths',
        action='store_true',
        help='Focus analysis on critical business paths'
    )
    parser.add_argument(
        '--format', '-f',
        choices=['text', 'html', 'json'],
        default='text',
        help='Output format (default: text)'
    )
    parser.add_argument(
        '--output', '-o',
        help='Output file path'
    )
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Enable verbose output'
    )
    parser.add_argument(
        '--json',
        action='store_true',
        help='Output results as JSON (summary only)'
    )

    args = parser.parse_args()

    try:
        tool = CoverageAnalyzerTool(
            coverage_path=args.coverage,
            threshold=args.threshold,
            critical_paths=args.critical_paths,
            strict=args.strict,
            output_format=args.format,
            output_path=args.output,
            verbose=args.verbose
        )

        results = tool.run()

        if args.json:
            print(json.dumps(results, indent=2))

    except Exception as e:
        print(f"Error: {e}")
        if args.verbose:
            import traceback
            traceback.print_exc()
        sys.exit(1)


if __name__ == '__main__':
    main()
