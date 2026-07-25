"""
Coverage analysis module.

Parse and analyze test coverage reports in multiple formats (LCOV, JSON, XML).
Identify gaps, calculate metrics, and provide actionable recommendations.
"""

from typing import Dict, List, Any, Optional, Tuple
import json
import xml.etree.ElementTree as ET


class CoverageFormat:
    """Supported coverage report formats."""
    LCOV = "lcov"
    JSON = "json"
    XML = "xml"
    COBERTURA = "cobertura"


class CoverageAnalyzer:
    """Analyze test coverage reports and identify gaps."""

    def __init__(self):
        """Initialize coverage analyzer."""
        self.coverage_data = {}
        self.gaps = []
        self.summary = {}

    def parse_coverage_report(
        self,
        report_content: str,
        format_type: str
    ) -> Dict[str, Any]:
        """
        Parse coverage report in various formats.

        Args:
            report_content: Raw coverage report content
            format_type: Format (lcov, json, xml, cobertura)

        Returns:
            Parsed coverage data
        """
        if format_type == CoverageFormat.LCOV:
            return self._parse_lcov(report_content)
        elif format_type == CoverageFormat.JSON:
            return self._parse_json(report_content)
        elif format_type in [CoverageFormat.XML, CoverageFormat.COBERTURA]:
            return self._parse_xml(report_content)
        else:
            raise ValueError(f"Unsupported format: {format_type}")

    def _parse_lcov(self, content: str) -> Dict[str, Any]:
        """Parse LCOV format coverage report."""
        files = {}
        current_file = None
        file_data = {}

        for line in content.split('\n'):
            line = line.strip()

            if line.startswith('SF:'):
                # Source file
                current_file = line[3:]
                file_data = {
                    'lines': {},
                    'functions': {},
                    'branches': {}
                }

            elif line.startswith('DA:'):
                # Line coverage data (line_number,hit_count)
                parts = line[3:].split(',')
                line_num = int(parts[0])
                hit_count = int(parts[1])
                file_data['lines'][line_num] = hit_count

            elif line.startswith('FNDA:'):
                # Function coverage (hit_count,function_name)
                parts = line[5:].split(',', 1)
                hit_count = int(parts[0])
                func_name = parts[1] if len(parts) > 1 else 'unknown'
                file_data['functions'][func_name] = hit_count

            elif line.startswith('BRDA:'):
                # Branch coverage (line,block,branch,hit_count)
                parts = line[5:].split(',')
                branch_id = f"{parts[0]}:{parts[1]}:{parts[2]}"
                hit_count = 0 if parts[3] == '-' else int(parts[3])
                file_data['branches'][branch_id] = hit_count

            elif line == 'end_of_record':
                if current_file:
                    files[current_file] = file_data
                current_file = None
                file_data = {}

        self.coverage_data = files
        return files

    def _parse_json(self, content: str) -> Dict[str, Any]:
        """Parse JSON format coverage report (Istanbul/nyc)."""
        try:
            data = json.loads(content)
            files = {}

            for file_path, file_data in data.items():
                lines = {}
                functions = {}
                branches = {}

                # Line coverage
                if 's' in file_data:  # Statement map
                    statement_map = file_data['s']
                    for stmt_id, hit_count in statement_map.items():
                        # Map statement to line number
                        if 'statementMap' in file_data:
                            stmt_info = file_data['statementMap'].get(stmt_id, {})
                            line_num = stmt_info.get('start', {}).get('line')
                            if line_num:
                                lines[line_num] = hit_count

                # Function coverage
                if 'f' in file_data:
                    func_map = file_data['f']
                    func_names = file_data.get('fnMap', {})
                    for func_id, hit_count in func_map.items():
                        func_info = func_names.get(func_id, {})
                        func_name = func_info.get('name', f'func_{func_id}')
                        functions[func_name] = hit_count

                # Branch coverage
                if 'b' in file_data:
                    branch_map = file_data['b']
                    for branch_id, locations in branch_map.items():
                        for idx, hit_count in enumerate(locations):
                            branch_key = f"{branch_id}:{idx}"
                            branches[branch_key] = hit_count

                files[file_path] = {
                    'lines': lines,
                    'functions': functions,
                    'branches': branches
                }

            self.coverage_data = files
            return files

        except json.JSONDecodeError as e:
            raise ValueError(f"Invalid JSON coverage report: {e}")

    def _parse_xml(self, content: str) -> Dict[str, Any]:
        """Parse XML/Cobertura format coverage report."""
        try:
            root = ET.fromstring(content)
            files = {}

            # Handle Cobertura format
            for package in root.findall('.//package'):
                for cls in package.findall('classes/class'):
                    filename = cls.get('filename', cls.get('name', 'unknown'))

                    lines = {}
                    branches = {}

                    for line in cls.findall('lines/line'):
                        line_num = int(line.get('number', 0))
                        hit_count = int(line.get('hits', 0))
                        lines[line_num] = hit_count

                        # Branch info
                        branch = line.get('branch', 'false')
                        if branch == 'true':
                            condition_coverage = line.get('condition-coverage', '0% (0/0)')
                            # Parse "(covered/total)"
                            if '(' in condition_coverage:
                                branch_info = condition_coverage.split('(')[1].split(')')[0]
                                covered, total = map(int, branch_info.split('/'))
                                branches[f"{line_num}:branch"] = covered

                    files[filename] = {
                        'lines': lines,
                        'functions': {},
                        'branches': branches
                    }

            self.coverage_data = files
            return files

        except ET.ParseError as e:
            raise ValueError(f"Invalid XML coverage report: {e}")

    def calculate_summary(self) -> Dict[str, Any]:
        """
        Calculate overall coverage summary.

        Returns:
            Summary with line, branch, and function coverage percentages
        """
        total_lines = 0
        covered_lines = 0
        total_branches = 0
        covered_branches = 0
        total_functions = 0
        covered_functions = 0

        for file_path, file_data in self.coverage_data.items():
            # Lines
            for line_num, hit_count in file_data.get('lines', {}).items():
                total_lines += 1
                if hit_count > 0:
                    covered_lines += 1

            # Branches
            for branch_id, hit_count in file_data.get('branches', {}).items():
                total_branches += 1
                if hit_count > 0:
                    covered_branches += 1

            # Functions
            for func_name, hit_count in file_data.get('functions', {}).items():
                total_functions += 1
                if hit_count > 0:
                    covered_functions += 1

        summary = {
            'line_coverage': self._safe_percentage(covered_lines, total_lines),
            'branch_coverage': self._safe_percentage(covered_branches, total_branches),
            'function_coverage': self._safe_percentage(covered_functions, total_functions),
            'total_lines': total_lines,
            'covered_lines': covered_lines,
            'total_branches': total_branches,
            'covered_branches': covered_branches,
            'total_functions': total_functions,
            'covered_functions': covered_functions
        }

        self.summary = summary
        return summary

    def _safe_percentage(self, covered: int, total: int) -> float:
        """Safely calculate percentage."""
        if total == 0:
            return 0.0
        return round((covered / total) * 100, 2)

    def identify_gaps(self, threshold: float = 80.0) -> List[Dict[str, Any]]:
        """
        Identify coverage gaps below threshold.

        Args:
            threshold: Minimum acceptable coverage percentage

        Returns:
            List of files with coverage gaps
        """
        gaps = []

        for file_path, file_data in self.coverage_data.items():
            file_gaps = self._analyze_file_gaps(file_path, file_data, threshold)
            if file_gaps:
                gaps.append(file_gaps)

        self.gaps = gaps
        return gaps

    def _analyze_file_gaps(
        self,
        file_path: str,
        file_data: Dict[str, Any],
        threshold: float
    ) -> Optional[Dict[str, Any]]:
        """Analyze coverage gaps for a single file."""
        lines = file_data.get('lines', {})
        branches = file_data.get('branches', {})
        functions = file_data.get('functions', {})

        # Calculate file coverage
        total_lines = len(lines)
        covered_lines = sum(1 for hit in lines.values() if hit > 0)
        line_coverage = self._safe_percentage(covered_lines, total_lines)

        total_branches = len(branches)
        covered_branches = sum(1 for hit in branches.values() if hit > 0)
        branch_coverage = self._safe_percentage(covered_branches, total_branches)

        # Find uncovered lines
        uncovered_lines = [line_num for line_num, hit in lines.items() if hit == 0]
        uncovered_branches = [branch_id for branch_id, hit in branches.items() if hit == 0]

        # Only report if below threshold
        if line_coverage < threshold or branch_coverage < threshold:
            return {
                'file': file_path,
                'line_coverage': line_coverage,
                'branch_coverage': branch_coverage,
                'uncovered_lines': sorted(uncovered_lines),
                'uncovered_branches': uncovered_branches,
                'priority': self._calculate_priority(line_coverage, branch_coverage, threshold)
            }

        return None

    def _calculate_priority(
        self,
        line_coverage: float,
        branch_coverage: float,
        threshold: float
    ) -> str:
        """Calculate priority based on coverage gap severity."""
        gap = threshold - min(line_coverage, branch_coverage)

        if gap >= 40:
            return 'P0'  # Critical - less than 40% coverage
        elif gap >= 20:
            return 'P1'  # Important - 60-80% coverage
        else:
            return 'P2'  # Nice to have - 80%+ coverage

    def get_file_coverage(self, file_path: str) -> Dict[str, Any]:
        """
        Get detailed coverage information for a specific file.

        Args:
            file_path: Path to file

        Returns:
            Detailed coverage data for file
        """
        if file_path not in self.coverage_data:
            return {}

        file_data = self.coverage_data[file_path]
        lines = file_data.get('lines', {})
        branches = file_data.get('branches', {})
        functions = file_data.get('functions', {})

        total_lines = len(lines)
        covered_lines = sum(1 for hit in lines.values() if hit > 0)

        total_branches = len(branches)
        covered_branches = sum(1 for hit in branches.values() if hit > 0)

        total_functions = len(functions)
        covered_functions = sum(1 for hit in functions.values() if hit > 0)

        return {
            'file': file_path,
            'line_coverage': self._safe_percentage(covered_lines, total_lines),
            'branch_coverage': self._safe_percentage(covered_branches, total_branches),
            'function_coverage': self._safe_percentage(covered_functions, total_functions),
            'lines': lines,
            'branches': branches,
            'functions': functions
        }

    def generate_recommendations(self) -> List[Dict[str, Any]]:
        """
        Generate prioritized recommendations for improving coverage.

        Returns:
            List of recommendations with priority and actions
        """
        recommendations = []

        # Check overall coverage
        summary = self.summary or self.calculate_summary()

        if summary['line_coverage'] < 80:
            recommendations.append({
                'priority': 'P0',
                'type': 'overall_coverage',
                'message': f"Overall line coverage ({summary['line_coverage']}%) is below 80% threshold",
                'action': 'Focus on adding tests for critical paths and business logic',
                'impact': 'high'
            })

        if summary['branch_coverage'] < 70:
            recommendations.append({
                'priority': 'P0',
                'type': 'branch_coverage',
                'message': f"Branch coverage ({summary['branch_coverage']}%) is below 70% threshold",
                'action': 'Add tests for conditional logic and error handling paths',
                'impact': 'high'
            })

        # File-specific recommendations
        for gap in self.gaps:
            if gap['priority'] == 'P0':
                recommendations.append({
                    'priority': 'P0',
                    'type': 'file_coverage',
                    'file': gap['file'],
                    'message': f"Critical coverage gap in {gap['file']}",
                    'action': f"Add tests for lines: {gap['uncovered_lines'][:10]}",
                    'impact': 'high'
                })

        # Sort by priority
        priority_order = {'P0': 0, 'P1': 1, 'P2': 2}
        recommendations.sort(key=lambda x: priority_order.get(x['priority'], 3))

        return recommendations

    def detect_format(self, content: str) -> str:
        """
        Automatically detect coverage report format.

        Args:
            content: Raw coverage report content

        Returns:
            Detected format (lcov, json, xml)
        """
        content_stripped = content.strip()

        # Check for LCOV format
        if content_stripped.startswith('TN:') or 'SF:' in content_stripped[:100]:
            return CoverageFormat.LCOV

        # Check for JSON format
        if content_stripped.startswith('{') or content_stripped.startswith('['):
            try:
                json.loads(content_stripped)
                return CoverageFormat.JSON
            except:
                pass

        # Check for XML format
        if content_stripped.startswith('<?xml') or content_stripped.startswith('<coverage'):
            return CoverageFormat.XML

        raise ValueError("Unable to detect coverage report format")
