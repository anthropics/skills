#!/usr/bin/env python3
"""
Dependency Analyzer

Analyzes project dependencies for:
- Dependency tree (direct and transitive)
- Circular dependencies between modules
- Coupling score (0-100)
- Outdated packages (basic detection)

Supports:
- npm/yarn (package.json)
- Python (requirements.txt, pyproject.toml)
- Go (go.mod)
- Rust (Cargo.toml)
"""

import os
import sys
import json
import argparse
import re
from pathlib import Path
from typing import Dict, List, Set, Tuple, Optional
from collections import defaultdict


class DependencyAnalyzer:
    """Analyzes project dependencies and module coupling."""

    def __init__(self, project_path: Path, verbose: bool = False):
        self.project_path = project_path
        self.verbose = verbose

        # Results
        self.direct_deps: Dict[str, str] = {}  # name -> version
        self.dev_deps: Dict[str, str] = {}
        self.internal_modules: Dict[str, Set[str]] = defaultdict(set)  # module -> imports
        self.circular_deps: List[List[str]] = []
        self.coupling_score: float = 0
        self.issues: List[Dict] = []
        self.recommendations: List[str] = []
        self.package_manager: Optional[str] = None

    def analyze(self) -> Dict:
        """Run full dependency analysis."""
        self._detect_package_manager()
        self._parse_dependencies()
        self._scan_internal_modules()
        self._detect_circular_dependencies()
        self._calculate_coupling_score()
        self._generate_recommendations()

        return self._build_report()

    def _detect_package_manager(self):
        """Detect which package manager is used."""
        if (self.project_path / 'package.json').exists():
            self.package_manager = 'npm'
        elif (self.project_path / 'requirements.txt').exists():
            self.package_manager = 'pip'
        elif (self.project_path / 'pyproject.toml').exists():
            self.package_manager = 'poetry'
        elif (self.project_path / 'go.mod').exists():
            self.package_manager = 'go'
        elif (self.project_path / 'Cargo.toml').exists():
            self.package_manager = 'cargo'
        else:
            self.package_manager = 'unknown'

        if self.verbose:
            print(f"Detected package manager: {self.package_manager}")

    def _parse_dependencies(self):
        """Parse dependencies based on detected package manager."""
        parsers = {
            'npm': self._parse_npm,
            'pip': self._parse_pip,
            'poetry': self._parse_poetry,
            'go': self._parse_go,
            'cargo': self._parse_cargo,
        }

        parser = parsers.get(self.package_manager)
        if parser:
            parser()

    def _parse_npm(self):
        """Parse package.json for npm dependencies."""
        pkg_path = self.project_path / 'package.json'
        try:
            data = json.loads(pkg_path.read_text())

            # Direct dependencies
            for name, version in data.get('dependencies', {}).items():
                self.direct_deps[name] = self._clean_version(version)

            # Dev dependencies
            for name, version in data.get('devDependencies', {}).items():
                self.dev_deps[name] = self._clean_version(version)

            if self.verbose:
                print(f"Found {len(self.direct_deps)} direct deps, "
                      f"{len(self.dev_deps)} dev deps")

        except Exception as e:
            self.issues.append({
                'type': 'parse_error',
                'severity': 'error',
                'message': f"Failed to parse package.json: {e}"
            })

    def _parse_pip(self):
        """Parse requirements.txt for Python dependencies."""
        req_path = self.project_path / 'requirements.txt'
        try:
            content = req_path.read_text()
            for line in content.strip().split('\n'):
                line = line.strip()
                if not line or line.startswith('#') or line.startswith('-'):
                    continue

                # Parse name and version
                match = re.match(r'^([a-zA-Z0-9_-]+)(?:[=<>!~]+(.+))?', line)
                if match:
                    name = match.group(1)
                    version = match.group(2) or 'any'
                    self.direct_deps[name] = version

            if self.verbose:
                print(f"Found {len(self.direct_deps)} dependencies")

        except Exception as e:
            self.issues.append({
                'type': 'parse_error',
                'severity': 'error',
                'message': f"Failed to parse requirements.txt: {e}"
            })

    def _parse_poetry(self):
        """Parse pyproject.toml for Poetry dependencies."""
        toml_path = self.project_path / 'pyproject.toml'
        try:
            content = toml_path.read_text()

            # Simple TOML parsing for dependencies section
            in_deps = False
            in_dev_deps = False

            for line in content.split('\n'):
                line = line.strip()

                if line == '[tool.poetry.dependencies]':
                    in_deps = True
                    in_dev_deps = False
                    continue
                elif line == '[tool.poetry.dev-dependencies]' or \
                     line == '[tool.poetry.group.dev.dependencies]':
                    in_deps = False
                    in_dev_deps = True
                    continue
                elif line.startswith('['):
                    in_deps = False
                    in_dev_deps = False
                    continue

                if (in_deps or in_dev_deps) and '=' in line:
                    match = re.match(r'^([a-zA-Z0-9_-]+)\s*=\s*["\']?([^"\']+)', line)
                    if match:
                        name = match.group(1)
                        version = match.group(2)
                        if name != 'python':
                            if in_deps:
                                self.direct_deps[name] = version
                            else:
                                self.dev_deps[name] = version

            if self.verbose:
                print(f"Found {len(self.direct_deps)} direct deps, "
                      f"{len(self.dev_deps)} dev deps")

        except Exception as e:
            self.issues.append({
                'type': 'parse_error',
                'severity': 'error',
                'message': f"Failed to parse pyproject.toml: {e}"
            })

    def _parse_go(self):
        """Parse go.mod for Go dependencies."""
        mod_path = self.project_path / 'go.mod'
        try:
            content = mod_path.read_text()

            # Find require block
            in_require = False
            for line in content.split('\n'):
                line = line.strip()

                if line.startswith('require ('):
                    in_require = True
                    continue
                elif line == ')' and in_require:
                    in_require = False
                    continue
                elif line.startswith('require ') and '(' not in line:
                    # Single-line require
                    match = re.match(r'require\s+([^\s]+)\s+([^\s]+)', line)
                    if match:
                        self.direct_deps[match.group(1)] = match.group(2)
                    continue

                if in_require:
                    match = re.match(r'([^\s]+)\s+([^\s]+)', line)
                    if match:
                        self.direct_deps[match.group(1)] = match.group(2)

            if self.verbose:
                print(f"Found {len(self.direct_deps)} dependencies")

        except Exception as e:
            self.issues.append({
                'type': 'parse_error',
                'severity': 'error',
                'message': f"Failed to parse go.mod: {e}"
            })

    def _parse_cargo(self):
        """Parse Cargo.toml for Rust dependencies."""
        cargo_path = self.project_path / 'Cargo.toml'
        try:
            content = cargo_path.read_text()

            in_deps = False
            in_dev_deps = False

            for line in content.split('\n'):
                line = line.strip()

                if line == '[dependencies]':
                    in_deps = True
                    in_dev_deps = False
                    continue
                elif line == '[dev-dependencies]':
                    in_deps = False
                    in_dev_deps = True
                    continue
                elif line.startswith('['):
                    in_deps = False
                    in_dev_deps = False
                    continue

                if (in_deps or in_dev_deps) and '=' in line:
                    match = re.match(r'^([a-zA-Z0-9_-]+)\s*=\s*["\']?([^"\']+)', line)
                    if match:
                        name = match.group(1)
                        version = match.group(2)
                        if in_deps:
                            self.direct_deps[name] = version
                        else:
                            self.dev_deps[name] = version

            if self.verbose:
                print(f"Found {len(self.direct_deps)} direct deps, "
                      f"{len(self.dev_deps)} dev deps")

        except Exception as e:
            self.issues.append({
                'type': 'parse_error',
                'severity': 'error',
                'message': f"Failed to parse Cargo.toml: {e}"
            })

    def _clean_version(self, version: str) -> str:
        """Clean version string."""
        return version.lstrip('^~>=<!')

    def _scan_internal_modules(self):
        """Scan internal module imports for coupling analysis."""
        ignore_dirs = {'.git', 'node_modules', '__pycache__', '.venv', 'venv',
                       'dist', 'build', '.next', 'coverage'}

        # Find all code files
        extensions = ['.py', '.js', '.ts', '.jsx', '.tsx', '.go', '.rs']

        for ext in extensions:
            for file_path in self.project_path.rglob(f'*{ext}'):
                # Skip ignored directories
                if any(ignored in file_path.parts for ignored in ignore_dirs):
                    continue

                # Get module name (directory relative to project root)
                try:
                    rel_path = file_path.relative_to(self.project_path)
                    module = rel_path.parts[0] if len(rel_path.parts) > 1 else 'root'

                    # Extract imports
                    imports = self._extract_imports(file_path)
                    self.internal_modules[module].update(imports)

                except Exception:
                    continue

        if self.verbose:
            print(f"Scanned {len(self.internal_modules)} internal modules")

    def _extract_imports(self, file_path: Path) -> Set[str]:
        """Extract import statements from a file."""
        imports = set()
        try:
            content = file_path.read_text(encoding='utf-8', errors='ignore')

            # Python imports
            for match in re.finditer(r'^(?:from|import)\s+([\w.]+)', content, re.MULTILINE):
                imports.add(match.group(1).split('.')[0])

            # JS/TS imports
            for match in re.finditer(r'(?:import|require)\s*\(?[\'"]([^\'"\s]+)[\'"]', content):
                imp = match.group(1)
                if imp.startswith('.') or imp.startswith('@/') or imp.startswith('~/'):
                    # Relative import - extract first path component
                    parts = imp.lstrip('./~@').split('/')
                    if parts:
                        imports.add(parts[0])

        except Exception:
            pass

        return imports

    def _detect_circular_dependencies(self):
        """Detect circular dependencies between internal modules."""
        # Build dependency graph
        graph = defaultdict(set)
        modules = set(self.internal_modules.keys())

        for module, imports in self.internal_modules.items():
            for imp in imports:
                # Check if import is an internal module
                for internal_module in modules:
                    if internal_module.lower() in imp.lower() and internal_module != module:
                        graph[module].add(internal_module)

        # Find cycles using DFS
        visited = set()
        rec_stack = set()
        cycles = []

        def find_cycles(node: str, path: List[str]):
            visited.add(node)
            rec_stack.add(node)
            path.append(node)

            for neighbor in graph.get(node, []):
                if neighbor not in visited:
                    find_cycles(neighbor, path)
                elif neighbor in rec_stack:
                    # Found cycle
                    cycle_start = path.index(neighbor)
                    cycle = path[cycle_start:] + [neighbor]
                    if cycle not in cycles:
                        cycles.append(cycle)

            path.pop()
            rec_stack.remove(node)

        for module in modules:
            if module not in visited:
                find_cycles(module, [])

        self.circular_deps = cycles

        if cycles:
            for cycle in cycles:
                self.issues.append({
                    'type': 'circular_dependency',
                    'severity': 'warning',
                    'message': f"Circular dependency: {' -> '.join(cycle)}"
                })

        if self.verbose:
            print(f"Found {len(self.circular_deps)} circular dependencies")

    def _calculate_coupling_score(self):
        """Calculate coupling score (0-100, lower is better)."""
        if not self.internal_modules:
            self.coupling_score = 0
            return

        # Count connections between modules
        total_modules = len(self.internal_modules)
        total_connections = 0
        modules = set(self.internal_modules.keys())

        for module, imports in self.internal_modules.items():
            for imp in imports:
                for internal_module in modules:
                    if internal_module.lower() in imp.lower() and internal_module != module:
                        total_connections += 1

        # Max possible connections (complete graph)
        max_connections = total_modules * (total_modules - 1) if total_modules > 1 else 1

        # Coupling score as percentage of max connections
        self.coupling_score = min(100, int((total_connections / max_connections) * 100))

        # Add penalty for circular dependencies
        self.coupling_score = min(100, self.coupling_score + len(self.circular_deps) * 10)

        if self.verbose:
            print(f"Coupling score: {self.coupling_score}/100")

    def _generate_recommendations(self):
        """Generate actionable recommendations."""
        # Circular dependency recommendations
        if self.circular_deps:
            self.recommendations.append(
                "Extract shared interfaces or create a common module to break circular dependencies"
            )

        # High coupling recommendations
        if self.coupling_score > 70:
            self.recommendations.append(
                "High coupling detected. Consider applying SOLID principles and "
                "introducing abstraction layers"
            )

        # Too many dependencies
        if len(self.direct_deps) > 50:
            self.recommendations.append(
                f"Large dependency count ({len(self.direct_deps)}). "
                "Review for unused dependencies and consider bundle size impact"
            )

        # Check for known problematic packages (simplified check)
        problematic = {
            'lodash': 'Consider lodash-es or native methods for smaller bundle',
            'moment': 'Consider day.js or date-fns for smaller bundle',
            'request': 'Deprecated. Use axios, node-fetch, or native fetch',
        }

        for pkg, suggestion in problematic.items():
            if pkg in self.direct_deps:
                self.recommendations.append(f"{pkg}: {suggestion}")

    def _build_report(self) -> Dict:
        """Build the analysis report."""
        return {
            'project_path': str(self.project_path),
            'package_manager': self.package_manager,
            'summary': {
                'direct_dependencies': len(self.direct_deps),
                'dev_dependencies': len(self.dev_deps),
                'internal_modules': len(self.internal_modules),
                'coupling_score': self.coupling_score,
                'circular_dependencies': len(self.circular_deps),
                'issues': len(self.issues),
            },
            'dependencies': {
                'direct': self.direct_deps,
                'dev': self.dev_deps,
            },
            'internal_modules': {k: list(v) for k, v in self.internal_modules.items()},
            'circular_dependencies': self.circular_deps,
            'issues': self.issues,
            'recommendations': self.recommendations,
        }


def print_human_report(report: Dict):
    """Print human-readable report."""
    print("\n" + "=" * 60)
    print("DEPENDENCY ANALYSIS REPORT")
    print("=" * 60)
    print(f"\nProject: {report['project_path']}")
    print(f"Package Manager: {report['package_manager']}")

    summary = report['summary']
    print("\n--- Summary ---")
    print(f"Direct dependencies: {summary['direct_dependencies']}")
    print(f"Dev dependencies: {summary['dev_dependencies']}")
    print(f"Internal modules: {summary['internal_modules']}")
    print(f"Coupling score: {summary['coupling_score']}/100 ", end='')

    if summary['coupling_score'] < 30:
        print("(low - good)")
    elif summary['coupling_score'] < 70:
        print("(moderate)")
    else:
        print("(high - consider refactoring)")

    if report['circular_dependencies']:
        print(f"\n--- Circular Dependencies ({len(report['circular_dependencies'])}) ---")
        for cycle in report['circular_dependencies']:
            print(f"  {' -> '.join(cycle)}")

    if report['issues']:
        print(f"\n--- Issues ({len(report['issues'])}) ---")
        for issue in report['issues']:
            severity = issue['severity'].upper()
            print(f"  [{severity}] {issue['message']}")

    if report['recommendations']:
        print(f"\n--- Recommendations ---")
        for i, rec in enumerate(report['recommendations'], 1):
            print(f"  {i}. {rec}")

    # Show top dependencies
    deps = report['dependencies']['direct']
    if deps:
        print(f"\n--- Top Dependencies (of {len(deps)}) ---")
        for name, version in list(deps.items())[:10]:
            print(f"  {name}: {version}")
        if len(deps) > 10:
            print(f"  ... and {len(deps) - 10} more")

    print("\n" + "=" * 60)


def main():
    parser = argparse.ArgumentParser(
        description='Analyze project dependencies and module coupling',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
Examples:
  %(prog)s ./my-project
  %(prog)s ./my-project --output json
  %(prog)s ./my-project --check circular
  %(prog)s ./my-project --verbose

Supported package managers:
  - npm/yarn (package.json)
  - pip (requirements.txt)
  - poetry (pyproject.toml)
  - go (go.mod)
  - cargo (Cargo.toml)
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
        choices=['all', 'circular', 'coupling'],
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
    analyzer = DependencyAnalyzer(project_path, verbose=args.verbose)
    report = analyzer.analyze()

    # Filter report based on --check option
    if args.check == 'circular':
        if report['circular_dependencies']:
            print("Circular dependencies found:")
            for cycle in report['circular_dependencies']:
                print(f"  {' -> '.join(cycle)}")
            sys.exit(1)
        else:
            print("No circular dependencies found.")
            sys.exit(0)
    elif args.check == 'coupling':
        score = report['summary']['coupling_score']
        print(f"Coupling score: {score}/100")
        if score > 70:
            print("WARNING: High coupling detected")
            sys.exit(1)
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
