#!/usr/bin/env python3
"""
Project Architect

Analyzes project structure and detects:
- Architectural patterns (MVC, layered, hexagonal, microservices)
- Code organization issues (god classes, mixed concerns)
- Layer violations
- Missing architectural components

Provides architecture assessment and improvement recommendations.
"""

import os
import sys
import json
import argparse
import re
from pathlib import Path
from typing import Dict, List, Set, Tuple, Optional
from collections import defaultdict


class PatternDetector:
    """Detects architectural patterns in a project."""

    # Pattern signatures
    PATTERNS = {
        'layered': {
            'indicators': ['controller', 'service', 'repository', 'dao', 'model', 'entity'],
            'structure': ['controllers', 'services', 'repositories', 'models'],
            'weight': 0,
        },
        'mvc': {
            'indicators': ['model', 'view', 'controller'],
            'structure': ['models', 'views', 'controllers'],
            'weight': 0,
        },
        'hexagonal': {
            'indicators': ['port', 'adapter', 'domain', 'infrastructure', 'application'],
            'structure': ['ports', 'adapters', 'domain', 'infrastructure'],
            'weight': 0,
        },
        'clean': {
            'indicators': ['entity', 'usecase', 'interface', 'framework', 'adapter'],
            'structure': ['entities', 'usecases', 'interfaces', 'frameworks'],
            'weight': 0,
        },
        'microservices': {
            'indicators': ['service', 'api', 'gateway', 'docker', 'kubernetes'],
            'structure': ['services', 'api-gateway', 'docker-compose'],
            'weight': 0,
        },
        'modular_monolith': {
            'indicators': ['module', 'feature', 'bounded'],
            'structure': ['modules', 'features'],
            'weight': 0,
        },
        'feature_based': {
            'indicators': ['feature', 'component', 'page'],
            'structure': ['features', 'components', 'pages'],
            'weight': 0,
        },
    }

    # Layer definitions for violation detection
    LAYER_HIERARCHY = {
        'presentation': ['controller', 'handler', 'view', 'page', 'component', 'ui', 'route'],
        'application': ['service', 'usecase', 'application', 'facade'],
        'domain': ['domain', 'entity', 'model', 'aggregate', 'valueobject'],
        'infrastructure': ['repository', 'dao', 'adapter', 'gateway', 'client', 'config'],
    }

    LAYER_ORDER = ['presentation', 'application', 'domain', 'infrastructure']

    def __init__(self, project_path: Path):
        self.project_path = project_path
        self.directories: Set[str] = set()
        self.files: Dict[str, List[str]] = defaultdict(list)  # dir -> files
        self.detected_pattern: Optional[str] = None
        self.confidence: float = 0
        self.layer_assignments: Dict[str, str] = {}  # dir -> layer

    def scan(self) -> Dict:
        """Scan project and detect patterns."""
        self._scan_structure()
        self._detect_pattern()
        self._assign_layers()

        return {
            'detected_pattern': self.detected_pattern,
            'confidence': self.confidence,
            'directories': list(self.directories),
            'layer_assignments': self.layer_assignments,
            'pattern_scores': {p: d['weight'] for p, d in self.PATTERNS.items()},
        }

    def _scan_structure(self):
        """Scan directory structure."""
        ignore_dirs = {'.git', 'node_modules', '__pycache__', '.venv', 'venv',
                       'dist', 'build', '.next', 'coverage', '.pytest_cache'}

        for item in self.project_path.iterdir():
            if item.is_dir() and item.name not in ignore_dirs and not item.name.startswith('.'):
                self.directories.add(item.name.lower())

                # Scan files in directory
                try:
                    for f in item.rglob('*'):
                        if f.is_file():
                            self.files[item.name.lower()].append(f.name.lower())
                except PermissionError:
                    pass

    def _detect_pattern(self):
        """Detect the primary architectural pattern."""
        for pattern, config in self.PATTERNS.items():
            score = 0

            # Check directory structure
            for struct in config['structure']:
                if struct.lower() in self.directories:
                    score += 2

            # Check indicator presence in directory names
            for indicator in config['indicators']:
                for dir_name in self.directories:
                    if indicator in dir_name:
                        score += 1

            # Check file patterns
            all_files = [f for files in self.files.values() for f in files]
            for indicator in config['indicators']:
                matching_files = sum(1 for f in all_files if indicator in f)
                score += min(matching_files // 5, 3)  # Cap contribution

            config['weight'] = score

        # Find best match
        best_pattern = max(self.PATTERNS.items(), key=lambda x: x[1]['weight'])
        if best_pattern[1]['weight'] > 3:
            self.detected_pattern = best_pattern[0]
            max_possible = len(best_pattern[1]['structure']) * 2 + len(best_pattern[1]['indicators']) * 2
            self.confidence = min(100, int((best_pattern[1]['weight'] / max(max_possible, 1)) * 100))
        else:
            self.detected_pattern = 'unstructured'
            self.confidence = 0

    def _assign_layers(self):
        """Assign directories to architectural layers."""
        for dir_name in self.directories:
            for layer, indicators in self.LAYER_HIERARCHY.items():
                for indicator in indicators:
                    if indicator in dir_name:
                        self.layer_assignments[dir_name] = layer
                        break
                if dir_name in self.layer_assignments:
                    break

            if dir_name not in self.layer_assignments:
                self.layer_assignments[dir_name] = 'unknown'


class CodeAnalyzer:
    """Analyzes code for architectural issues."""

    # Thresholds
    MAX_FILE_LINES = 500
    MAX_CLASS_LINES = 300
    MAX_FUNCTION_LINES = 50
    MAX_IMPORTS_PER_FILE = 30

    def __init__(self, project_path: Path, verbose: bool = False):
        self.project_path = project_path
        self.verbose = verbose
        self.issues: List[Dict] = []
        self.metrics: Dict = {}

    def analyze(self) -> Dict:
        """Run code analysis."""
        self._analyze_file_sizes()
        self._analyze_imports()
        self._detect_god_classes()
        self._check_naming_conventions()

        return {
            'issues': self.issues,
            'metrics': self.metrics,
        }

    def _analyze_file_sizes(self):
        """Check for oversized files."""
        extensions = ['.py', '.js', '.ts', '.jsx', '.tsx', '.go', '.rs', '.java']
        large_files = []
        total_lines = 0
        file_count = 0

        ignore_dirs = {'.git', 'node_modules', '__pycache__', '.venv', 'venv',
                       'dist', 'build', '.next', 'coverage'}

        for ext in extensions:
            for file_path in self.project_path.rglob(f'*{ext}'):
                if any(ignored in file_path.parts for ignored in ignore_dirs):
                    continue

                try:
                    content = file_path.read_text(encoding='utf-8', errors='ignore')
                    lines = len(content.split('\n'))
                    total_lines += lines
                    file_count += 1

                    if lines > self.MAX_FILE_LINES:
                        large_files.append({
                            'path': str(file_path.relative_to(self.project_path)),
                            'lines': lines,
                        })
                        self.issues.append({
                            'type': 'large_file',
                            'severity': 'warning',
                            'file': str(file_path.relative_to(self.project_path)),
                            'message': f"File has {lines} lines (threshold: {self.MAX_FILE_LINES})",
                            'suggestion': "Consider splitting into smaller, focused modules",
                        })
                except Exception:
                    pass

        self.metrics['total_lines'] = total_lines
        self.metrics['file_count'] = file_count
        self.metrics['avg_file_lines'] = total_lines // file_count if file_count > 0 else 0
        self.metrics['large_files'] = large_files

    def _analyze_imports(self):
        """Analyze import patterns."""
        extensions = ['.py', '.js', '.ts', '.jsx', '.tsx']
        high_import_files = []

        ignore_dirs = {'.git', 'node_modules', '__pycache__', '.venv', 'venv',
                       'dist', 'build', '.next', 'coverage'}

        for ext in extensions:
            for file_path in self.project_path.rglob(f'*{ext}'):
                if any(ignored in file_path.parts for ignored in ignore_dirs):
                    continue

                try:
                    content = file_path.read_text(encoding='utf-8', errors='ignore')

                    # Count imports
                    py_imports = len(re.findall(r'^(?:from|import)\s+', content, re.MULTILINE))
                    js_imports = len(re.findall(r'^import\s+', content, re.MULTILINE))
                    imports = py_imports + js_imports

                    if imports > self.MAX_IMPORTS_PER_FILE:
                        high_import_files.append({
                            'path': str(file_path.relative_to(self.project_path)),
                            'imports': imports,
                        })
                        self.issues.append({
                            'type': 'high_imports',
                            'severity': 'info',
                            'file': str(file_path.relative_to(self.project_path)),
                            'message': f"File has {imports} imports (threshold: {self.MAX_IMPORTS_PER_FILE})",
                            'suggestion': "Consider if all imports are necessary or if the file has too many responsibilities",
                        })
                except Exception:
                    pass

        self.metrics['high_import_files'] = high_import_files

    def _detect_god_classes(self):
        """Detect potential god classes (oversized classes)."""
        extensions = ['.py', '.js', '.ts', '.java']
        god_classes = []

        ignore_dirs = {'.git', 'node_modules', '__pycache__', '.venv', 'venv',
                       'dist', 'build', '.next', 'coverage'}

        for ext in extensions:
            for file_path in self.project_path.rglob(f'*{ext}'):
                if any(ignored in file_path.parts for ignored in ignore_dirs):
                    continue

                try:
                    content = file_path.read_text(encoding='utf-8', errors='ignore')
                    lines = content.split('\n')

                    # Simple class detection
                    class_pattern = r'^\s*(?:export\s+)?(?:abstract\s+)?class\s+(\w+)'
                    in_class = False
                    class_name = None
                    class_start = 0
                    brace_count = 0

                    for i, line in enumerate(lines):
                        match = re.match(class_pattern, line)
                        if match:
                            if in_class and class_name:
                                # End previous class
                                class_lines = i - class_start
                                if class_lines > self.MAX_CLASS_LINES:
                                    god_classes.append({
                                        'file': str(file_path.relative_to(self.project_path)),
                                        'class': class_name,
                                        'lines': class_lines,
                                    })
                            class_name = match.group(1)
                            class_start = i
                            in_class = True

                    # Check last class
                    if in_class and class_name:
                        class_lines = len(lines) - class_start
                        if class_lines > self.MAX_CLASS_LINES:
                            god_classes.append({
                                'file': str(file_path.relative_to(self.project_path)),
                                'class': class_name,
                                'lines': class_lines,
                            })
                            self.issues.append({
                                'type': 'god_class',
                                'severity': 'warning',
                                'file': str(file_path.relative_to(self.project_path)),
                                'message': f"Class '{class_name}' has ~{class_lines} lines (threshold: {self.MAX_CLASS_LINES})",
                                'suggestion': "Consider applying Single Responsibility Principle and splitting into smaller classes",
                            })

                except Exception:
                    pass

        self.metrics['god_classes'] = god_classes

    def _check_naming_conventions(self):
        """Check for naming convention issues."""
        ignore_dirs = {'.git', 'node_modules', '__pycache__', '.venv', 'venv',
                       'dist', 'build', '.next', 'coverage'}

        naming_issues = []

        # Check directory naming
        for dir_path in self.project_path.rglob('*'):
            if not dir_path.is_dir():
                continue
            if any(ignored in dir_path.parts for ignored in ignore_dirs):
                continue

            dir_name = dir_path.name
            # Check for mixed case in directories (should be kebab-case or snake_case)
            if re.search(r'[A-Z]', dir_name) and '-' not in dir_name and '_' not in dir_name:
                rel_path = str(dir_path.relative_to(self.project_path))
                if len(rel_path.split('/')) <= 3:  # Only check top-level dirs
                    naming_issues.append({
                        'type': 'directory',
                        'path': rel_path,
                        'issue': 'PascalCase directory name',
                    })

        if naming_issues:
            self.issues.append({
                'type': 'naming_convention',
                'severity': 'info',
                'message': f"Found {len(naming_issues)} naming convention inconsistencies",
                'details': naming_issues[:5],  # Show first 5
            })

        self.metrics['naming_issues'] = naming_issues


class LayerViolationDetector:
    """Detects architectural layer violations."""

    LAYER_ORDER = ['presentation', 'application', 'domain', 'infrastructure']

    # Valid dependency directions (key can depend on values)
    VALID_DEPENDENCIES = {
        'presentation': ['application', 'domain'],
        'application': ['domain', 'infrastructure'],
        'domain': [],  # Domain should not depend on other layers
        'infrastructure': ['domain'],
    }

    def __init__(self, project_path: Path, layer_assignments: Dict[str, str]):
        self.project_path = project_path
        self.layer_assignments = layer_assignments
        self.violations: List[Dict] = []

    def detect(self) -> List[Dict]:
        """Detect layer violations."""
        self._analyze_imports()
        return self.violations

    def _analyze_imports(self):
        """Analyze imports for layer violations."""
        extensions = ['.py', '.js', '.ts', '.jsx', '.tsx']
        ignore_dirs = {'.git', 'node_modules', '__pycache__', '.venv', 'venv',
                       'dist', 'build', '.next', 'coverage'}

        for ext in extensions:
            for file_path in self.project_path.rglob(f'*{ext}'):
                if any(ignored in file_path.parts for ignored in ignore_dirs):
                    continue

                try:
                    rel_path = file_path.relative_to(self.project_path)
                    if len(rel_path.parts) < 2:
                        continue

                    source_dir = rel_path.parts[0].lower()
                    source_layer = self.layer_assignments.get(source_dir)

                    if not source_layer or source_layer == 'unknown':
                        continue

                    # Extract imports
                    content = file_path.read_text(encoding='utf-8', errors='ignore')
                    imports = self._extract_imports(content)

                    # Check each import for layer violations
                    for imp in imports:
                        target_dir = self._get_import_directory(imp)
                        if not target_dir:
                            continue

                        target_layer = self.layer_assignments.get(target_dir.lower())
                        if not target_layer or target_layer == 'unknown':
                            continue

                        if self._is_violation(source_layer, target_layer):
                            self.violations.append({
                                'type': 'layer_violation',
                                'severity': 'warning',
                                'file': str(rel_path),
                                'source_layer': source_layer,
                                'target_layer': target_layer,
                                'import': imp,
                                'message': f"{source_layer} layer should not depend on {target_layer} layer",
                            })

                except Exception:
                    pass

    def _extract_imports(self, content: str) -> List[str]:
        """Extract import statements."""
        imports = []

        # Python imports
        imports.extend(re.findall(r'^(?:from|import)\s+([\w.]+)', content, re.MULTILINE))

        # JS/TS imports
        imports.extend(re.findall(r'(?:import|require)\s*\(?[\'"]([^\'"\s]+)[\'"]', content))

        return imports

    def _get_import_directory(self, imp: str) -> Optional[str]:
        """Get the directory from an import path."""
        # Handle relative imports
        if imp.startswith('.'):
            return None  # Skip relative imports

        parts = imp.replace('@/', '').replace('~/', '').split('/')
        if parts:
            return parts[0].split('.')[0]
        return None

    def _is_violation(self, source_layer: str, target_layer: str) -> bool:
        """Check if the dependency is a violation."""
        if source_layer == target_layer:
            return False

        valid_deps = self.VALID_DEPENDENCIES.get(source_layer, [])
        return target_layer not in valid_deps and target_layer != source_layer


class ProjectArchitect:
    """Main class that orchestrates architecture analysis."""

    def __init__(self, project_path: Path, verbose: bool = False):
        self.project_path = project_path
        self.verbose = verbose

    def analyze(self) -> Dict:
        """Run full architecture analysis."""
        if self.verbose:
            print(f"Analyzing project: {self.project_path}")

        # Pattern detection
        pattern_detector = PatternDetector(self.project_path)
        pattern_result = pattern_detector.scan()

        if self.verbose:
            print(f"Detected pattern: {pattern_result['detected_pattern']} "
                  f"(confidence: {pattern_result['confidence']}%)")

        # Code analysis
        code_analyzer = CodeAnalyzer(self.project_path, self.verbose)
        code_result = code_analyzer.analyze()

        if self.verbose:
            print(f"Found {len(code_result['issues'])} code issues")

        # Layer violation detection
        violation_detector = LayerViolationDetector(
            self.project_path,
            pattern_result['layer_assignments']
        )
        violations = violation_detector.detect()

        if self.verbose:
            print(f"Found {len(violations)} layer violations")

        # Generate recommendations
        recommendations = self._generate_recommendations(
            pattern_result, code_result, violations
        )

        return {
            'project_path': str(self.project_path),
            'architecture': {
                'detected_pattern': pattern_result['detected_pattern'],
                'confidence': pattern_result['confidence'],
                'layer_assignments': pattern_result['layer_assignments'],
                'pattern_scores': pattern_result['pattern_scores'],
            },
            'structure': {
                'directories': pattern_result['directories'],
            },
            'code_quality': {
                'metrics': code_result['metrics'],
                'issues': code_result['issues'],
            },
            'layer_violations': violations,
            'recommendations': recommendations,
            'summary': {
                'pattern': pattern_result['detected_pattern'],
                'confidence': pattern_result['confidence'],
                'total_issues': len(code_result['issues']) + len(violations),
                'code_issues': len(code_result['issues']),
                'layer_violations': len(violations),
            },
        }

    def _generate_recommendations(self, pattern_result: Dict, code_result: Dict,
                                   violations: List[Dict]) -> List[str]:
        """Generate actionable recommendations."""
        recommendations = []

        # Pattern recommendations
        pattern = pattern_result['detected_pattern']
        confidence = pattern_result['confidence']

        if pattern == 'unstructured' or confidence < 30:
            recommendations.append(
                "Consider adopting a clear architectural pattern (Layered, Clean, or Hexagonal) "
                "to improve code organization and maintainability"
            )

        # Layer violation recommendations
        if violations:
            recommendations.append(
                f"Fix {len(violations)} layer violation(s) to maintain proper separation of concerns. "
                "Dependencies should flow from presentation → application → domain ← infrastructure"
            )

        # God class recommendations
        god_classes = code_result['metrics'].get('god_classes', [])
        if god_classes:
            recommendations.append(
                f"Split {len(god_classes)} large class(es) into smaller, focused classes "
                "following the Single Responsibility Principle"
            )

        # Large file recommendations
        large_files = code_result['metrics'].get('large_files', [])
        if large_files:
            recommendations.append(
                f"Consider refactoring {len(large_files)} large file(s) into smaller modules"
            )

        # Missing layer recommendations
        assigned_layers = set(pattern_result['layer_assignments'].values())
        if pattern in ['layered', 'clean', 'hexagonal']:
            expected_layers = {'presentation', 'application', 'domain', 'infrastructure'}
            missing = expected_layers - assigned_layers - {'unknown'}
            if missing:
                recommendations.append(
                    f"Consider adding missing architectural layer(s): {', '.join(missing)}"
                )

        return recommendations


def print_human_report(report: Dict):
    """Print human-readable report."""
    print("\n" + "=" * 60)
    print("ARCHITECTURE ASSESSMENT")
    print("=" * 60)
    print(f"\nProject: {report['project_path']}")

    arch = report['architecture']
    print(f"\n--- Architecture Pattern ---")
    print(f"Detected: {arch['detected_pattern'].replace('_', ' ').title()}")
    print(f"Confidence: {arch['confidence']}%")

    if arch['layer_assignments']:
        print(f"\nLayer Assignments:")
        for dir_name, layer in sorted(arch['layer_assignments'].items()):
            if layer != 'unknown':
                status = "OK"
            else:
                status = "?"
            print(f"  {status} {dir_name:20} -> {layer}")

    summary = report['summary']
    print(f"\n--- Summary ---")
    print(f"Total issues: {summary['total_issues']}")
    print(f"  Code issues: {summary['code_issues']}")
    print(f"  Layer violations: {summary['layer_violations']}")

    if report['code_quality']['issues']:
        print(f"\n--- Code Issues ---")
        for issue in report['code_quality']['issues'][:10]:
            severity = issue['severity'].upper()
            print(f"  [{severity}] {issue.get('file', 'N/A')}")
            print(f"          {issue['message']}")
            if 'suggestion' in issue:
                print(f"          Suggestion: {issue['suggestion']}")

    if report['layer_violations']:
        print(f"\n--- Layer Violations ---")
        for v in report['layer_violations'][:5]:
            print(f"  {v['file']}")
            print(f"      {v['message']}")

    if report['recommendations']:
        print(f"\n--- Recommendations ---")
        for i, rec in enumerate(report['recommendations'], 1):
            print(f"  {i}. {rec}")

    metrics = report['code_quality']['metrics']
    print(f"\n--- Metrics ---")
    print(f"  Total lines: {metrics.get('total_lines', 'N/A')}")
    print(f"  File count: {metrics.get('file_count', 'N/A')}")
    print(f"  Avg lines/file: {metrics.get('avg_file_lines', 'N/A')}")

    print("\n" + "=" * 60)


def main():
    parser = argparse.ArgumentParser(
        description='Analyze project architecture and detect patterns and issues',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
Examples:
  %(prog)s ./my-project
  %(prog)s ./my-project --verbose
  %(prog)s ./my-project --output json
  %(prog)s ./my-project --check layers

Detects:
  - Architectural patterns (Layered, MVC, Hexagonal, Clean, Microservices)
  - Code organization issues (large files, god classes)
  - Layer violations (incorrect dependencies between layers)
  - Missing architectural components
        '''
    )

    parser.add_argument(
        'project_path',
        help='Path to the project directory'
    )
    parser.add_argument(
        '--output', '-o',
        choices=['human', 'json'],
        default='human',
        help='Output format (default: human)'
    )
    parser.add_argument(
        '--check',
        choices=['all', 'pattern', 'layers', 'code'],
        default='all',
        help='What to check (default: all)'
    )
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Enable verbose output'
    )
    parser.add_argument(
        '--save', '-s',
        help='Save report to file'
    )

    args = parser.parse_args()

    project_path = Path(args.project_path).resolve()
    if not project_path.exists():
        print(f"Error: Project path does not exist: {project_path}", file=sys.stderr)
        sys.exit(1)

    if not project_path.is_dir():
        print(f"Error: Project path is not a directory: {project_path}", file=sys.stderr)
        sys.exit(1)

    # Run analysis
    architect = ProjectArchitect(project_path, verbose=args.verbose)
    report = architect.analyze()

    # Handle specific checks
    if args.check == 'pattern':
        arch = report['architecture']
        print(f"Pattern: {arch['detected_pattern']} (confidence: {arch['confidence']}%)")
        sys.exit(0)
    elif args.check == 'layers':
        violations = report['layer_violations']
        if violations:
            print(f"Found {len(violations)} layer violation(s):")
            for v in violations:
                print(f"  {v['file']}: {v['message']}")
            sys.exit(1)
        else:
            print("No layer violations found.")
            sys.exit(0)
    elif args.check == 'code':
        issues = report['code_quality']['issues']
        if issues:
            print(f"Found {len(issues)} code issue(s):")
            for issue in issues[:10]:
                print(f"  [{issue['severity'].upper()}] {issue['message']}")
            sys.exit(1 if any(i['severity'] == 'warning' for i in issues) else 0)
        else:
            print("No code issues found.")
            sys.exit(0)

    # Output report
    if args.output == 'json':
        output = json.dumps(report, indent=2)
        if args.save:
            Path(args.save).write_text(output)
            print(f"Report saved to {args.save}")
        else:
            print(output)
    else:
        print_human_report(report)
        if args.save:
            Path(args.save).write_text(json.dumps(report, indent=2))
            print(f"\nJSON report saved to {args.save}")


if __name__ == '__main__':
    main()
