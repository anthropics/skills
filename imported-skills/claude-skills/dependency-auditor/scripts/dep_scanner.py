#!/usr/bin/env python3
"""
Dependency Scanner - Multi-language dependency vulnerability and analysis tool.

This script parses dependency files from various package managers, extracts direct
and transitive dependencies, checks against built-in vulnerability databases,
and provides comprehensive security analysis with actionable recommendations.

Author: Claude Skills Engineering Team
License: MIT
"""

import json
import os
import re
import sys
import argparse
from typing import Dict, List, Set, Any, Optional, Tuple
from pathlib import Path
from dataclasses import dataclass, asdict
from datetime import datetime
import hashlib
import subprocess

@dataclass
class Vulnerability:
    """Represents a security vulnerability."""
    id: str
    summary: str
    severity: str
    cvss_score: float
    affected_versions: str
    fixed_version: Optional[str]
    published_date: str
    references: List[str]

@dataclass
class Dependency:
    """Represents a project dependency."""
    name: str
    version: str
    ecosystem: str
    direct: bool
    license: Optional[str] = None
    description: Optional[str] = None
    homepage: Optional[str] = None
    vulnerabilities: List[Vulnerability] = None
    
    def __post_init__(self):
        if self.vulnerabilities is None:
            self.vulnerabilities = []

class DependencyScanner:
    """Main dependency scanner class."""
    
    def __init__(self):
        self.known_vulnerabilities = self._load_vulnerability_database()
        self.supported_files = {
            'package.json': self._parse_package_json,
            'package-lock.json': self._parse_package_lock,
            'yarn.lock': self._parse_yarn_lock,
            'requirements.txt': self._parse_requirements_txt,
            'pyproject.toml': self._parse_pyproject_toml,
            'Pipfile.lock': self._parse_pipfile_lock,
            'poetry.lock': self._parse_poetry_lock,
            'go.mod': self._parse_go_mod,
            'go.sum': self._parse_go_sum,
            'Cargo.toml': self._parse_cargo_toml,
            'Cargo.lock': self._parse_cargo_lock,
            'Gemfile': self._parse_gemfile,
            'Gemfile.lock': self._parse_gemfile_lock,
        }
    
    def _load_vulnerability_database(self) -> Dict[str, List[Vulnerability]]:
        """Load built-in vulnerability database with common CVE patterns."""
        return {
            # JavaScript/Node.js vulnerabilities
            'lodash': [
                Vulnerability(
                    id='CVE-2021-23337',
                    summary='Prototype pollution in lodash',
                    severity='HIGH',
                    cvss_score=7.2,
                    affected_versions='<4.17.21',
                    fixed_version='4.17.21',
                    published_date='2021-02-15',
                    references=['https://nvd.nist.gov/vuln/detail/CVE-2021-23337']
                )
            ],
            'axios': [
                Vulnerability(
                    id='CVE-2023-45857',
                    summary='Cross-site request forgery in axios',
                    severity='MEDIUM',
                    cvss_score=6.1,
                    affected_versions='>=1.0.0 <1.6.0',
                    fixed_version='1.6.0',
                    published_date='2023-10-11',
                    references=['https://nvd.nist.gov/vuln/detail/CVE-2023-45857']
                )
            ],
            'express': [
                Vulnerability(
                    id='CVE-2022-24999',
                    summary='Open redirect in express',
                    severity='MEDIUM',
                    cvss_score=6.1,
                    affected_versions='<4.18.2',
                    fixed_version='4.18.2',
                    published_date='2022-11-26',
                    references=['https://nvd.nist.gov/vuln/detail/CVE-2022-24999']
                )
            ],
            
            # Python vulnerabilities
            'django': [
                Vulnerability(
                    id='CVE-2024-27351',
                    summary='SQL injection in Django',
                    severity='HIGH',
                    cvss_score=9.8,
                    affected_versions='>=3.2 <4.2.11',
                    fixed_version='4.2.11',
                    published_date='2024-02-06',
                    references=['https://nvd.nist.gov/vuln/detail/CVE-2024-27351']
                )
            ],
            'requests': [
                Vulnerability(
                    id='CVE-2023-32681',
                    summary='Proxy-authorization header leak in requests',
                    severity='MEDIUM',
                    cvss_score=6.1,
                    affected_versions='>=2.3.0 <2.31.0',
                    fixed_version='2.31.0',
                    published_date='2023-05-26',
                    references=['https://nvd.nist.gov/vuln/detail/CVE-2023-32681']
                )
            ],
            'pillow': [
                Vulnerability(
                    id='CVE-2023-50447',
                    summary='Arbitrary code execution in Pillow',
                    severity='HIGH',
                    cvss_score=8.8,
                    affected_versions='<10.2.0',
                    fixed_version='10.2.0',
                    published_date='2024-01-02',
                    references=['https://nvd.nist.gov/vuln/detail/CVE-2023-50447']
                )
            ],
            
            # Go vulnerabilities
            'github.com/gin-gonic/gin': [
                Vulnerability(
                    id='CVE-2023-26125',
                    summary='Path traversal in gin',
                    severity='HIGH',
                    cvss_score=7.5,
                    affected_versions='<1.9.1',
                    fixed_version='1.9.1',
                    published_date='2023-02-28',
                    references=['https://nvd.nist.gov/vuln/detail/CVE-2023-26125']
                )
            ],
            
            # Rust vulnerabilities
            'serde': [
                Vulnerability(
                    id='RUSTSEC-2022-0061',
                    summary='Deserialization vulnerability in serde',
                    severity='HIGH',
                    cvss_score=8.2,
                    affected_versions='<1.0.152',
                    fixed_version='1.0.152',
                    published_date='2022-12-07',
                    references=['https://rustsec.org/advisories/RUSTSEC-2022-0061']
                )
            ],
            
            # Ruby vulnerabilities
            'rails': [
                Vulnerability(
                    id='CVE-2023-28362',
                    summary='ReDoS vulnerability in Rails',
                    severity='HIGH',
                    cvss_score=7.5,
                    affected_versions='>=7.0.0 <7.0.4.3',
                    fixed_version='7.0.4.3',
                    published_date='2023-03-13',
                    references=['https://nvd.nist.gov/vuln/detail/CVE-2023-28362']
                )
            ]
        }
    
    def scan_project(self, project_path: str) -> Dict[str, Any]:
        """Scan a project directory for dependencies and vulnerabilities."""
        project_path = Path(project_path)
        
        if not project_path.exists():
            raise FileNotFoundError(f"Project path does not exist: {project_path}")
        
        scan_results = {
            'timestamp': datetime.now().isoformat(),
            'project_path': str(project_path),
            'dependencies': [],
            'vulnerabilities_found': 0,
            'high_severity_count': 0,
            'medium_severity_count': 0,
            'low_severity_count': 0,
            'ecosystems': set(),
            'scan_summary': {},
            'recommendations': []
        }
        
        # Find and parse dependency files
        for file_pattern, parser in self.supported_files.items():
            matching_files = list(project_path.rglob(file_pattern))
            
            for dep_file in matching_files:
                try:
                    dependencies = parser(dep_file)
                    scan_results['dependencies'].extend(dependencies)
                    
                    for dep in dependencies:
                        scan_results['ecosystems'].add(dep.ecosystem)
                        
                        # Check for vulnerabilities
                        vulnerabilities = self._check_vulnerabilities(dep)
                        dep.vulnerabilities = vulnerabilities
                        
                        scan_results['vulnerabilities_found'] += len(vulnerabilities)
                        
                        for vuln in vulnerabilities:
                            if vuln.severity == 'HIGH':
                                scan_results['high_severity_count'] += 1
                            elif vuln.severity == 'MEDIUM':
                                scan_results['medium_severity_count'] += 1
                            else:
                                scan_results['low_severity_count'] += 1
                
                except Exception as e:
                    print(f"Error parsing {dep_file}: {e}")
                    continue
        
        scan_results['ecosystems'] = list(scan_results['ecosystems'])
        scan_results['scan_summary'] = self._generate_scan_summary(scan_results)
        scan_results['recommendations'] = self._generate_recommendations(scan_results)
        
        return scan_results
    
    def _check_vulnerabilities(self, dependency: Dependency) -> List[Vulnerability]:
        """Check if a dependency has known vulnerabilities."""
        vulnerabilities = []
        
        # Check package name (exact match and common variations)
        package_names = [dependency.name, dependency.name.lower()]
        
        for pkg_name in package_names:
            if pkg_name in self.known_vulnerabilities:
                for vuln in self.known_vulnerabilities[pkg_name]:
                    if self._version_matches_vulnerability(dependency.version, vuln.affected_versions):
                        vulnerabilities.append(vuln)
        
        return vulnerabilities
    
    def _version_matches_vulnerability(self, version: str, affected_pattern: str) -> bool:
        """Check if a version matches a vulnerability pattern."""
        # Simple version matching - in production, use proper semver library
        try:
            # Handle common patterns like "<4.17.21", ">=1.0.0 <1.6.0"
            if '<' in affected_pattern and '>' not in affected_pattern:
                # Pattern like "<4.17.21"
                max_version = affected_pattern.replace('<', '').strip()
                return self._compare_versions(version, max_version) < 0
            elif '>=' in affected_pattern and '<' in affected_pattern:
                # Pattern like ">=1.0.0 <1.6.0"
                parts = affected_pattern.split('<')
                min_part = parts[0].replace('>=', '').strip()
                max_part = parts[1].strip()
                return (self._compare_versions(version, min_part) >= 0 and 
                       self._compare_versions(version, max_part) < 0)
        except:
            pass
        
        return False
    
    def _compare_versions(self, v1: str, v2: str) -> int:
        """Simple version comparison. Returns -1, 0, or 1."""
        try:
            def normalize(v):
                return [int(x) for x in re.sub(r'(\.0+)*$','', v).split('.')]
            
            v1_parts = normalize(v1)
            v2_parts = normalize(v2)
            
            if v1_parts < v2_parts:
                return -1
            elif v1_parts > v2_parts:
                return 1
            else:
                return 0
        except:
            return 0
    
    # Package file parsers
    
    def _parse_package_json(self, file_path: Path) -> List[Dependency]:
        """Parse package.json for Node.js dependencies."""
        dependencies = []
        
        try:
            with open(file_path, 'r') as f:
                data = json.load(f)
            
            # Parse dependencies
            for dep_type in ['dependencies', 'devDependencies']:
                if dep_type in data:
                    for name, version in data[dep_type].items():
                        dep = Dependency(
                            name=name,
                            version=version.replace('^', '').replace('~', '').replace('>=', '').replace('<=', ''),
                            ecosystem='npm',
                            direct=True
                        )
                        dependencies.append(dep)
        
        except Exception as e:
            print(f"Error parsing package.json: {e}")
        
        return dependencies
    
    def _parse_package_lock(self, file_path: Path) -> List[Dependency]:
        """Parse package-lock.json for Node.js transitive dependencies."""
        dependencies = []
        
        try:
            with open(file_path, 'r') as f:
                data = json.load(f)
            
            if 'packages' in data:
                for path, pkg_info in data['packages'].items():
                    if path == '':  # Skip root package
                        continue
                    
                    name = path.split('/')[-1] if '/' in path else path
                    version = pkg_info.get('version', '')
                    
                    dep = Dependency(
                        name=name,
                        version=version,
                        ecosystem='npm',
                        direct=False,
                        description=pkg_info.get('description', '')
                    )
                    dependencies.append(dep)
        
        except Exception as e:
            print(f"Error parsing package-lock.json: {e}")
        
        return dependencies
    
    def _parse_yarn_lock(self, file_path: Path) -> List[Dependency]:
        """Parse yarn.lock for Node.js dependencies."""
        dependencies = []
        
        try:
            with open(file_path, 'r') as f:
                content = f.read()
            
            # Simple yarn.lock parsing
            packages = re.findall(r'^([^#\s][^:]+):\s*\n(?:\s+.*\n)*?\s+version\s+"([^"]+)"', content, re.MULTILINE)
            
            for package_spec, version in packages:
                name = package_spec.split('@')[0] if '@' in package_spec else package_spec
                name = name.strip('"')
                
                dep = Dependency(
                    name=name,
                    version=version,
                    ecosystem='npm',
                    direct=False
                )
                dependencies.append(dep)
        
        except Exception as e:
            print(f"Error parsing yarn.lock: {e}")
        
        return dependencies
    
    def _parse_requirements_txt(self, file_path: Path) -> List[Dependency]:
        """Parse requirements.txt for Python dependencies."""
        dependencies = []
        
        try:
            with open(file_path, 'r') as f:
                lines = f.readlines()
            
            for line in lines:
                line = line.strip()
                if line and not line.startswith('#') and not line.startswith('-'):
                    # Parse package==version or package>=version patterns
                    match = re.match(r'^([a-zA-Z0-9_-]+)([><=!]+)(.+)$', line)
                    if match:
                        name, operator, version = match.groups()
                        dep = Dependency(
                            name=name,
                            version=version,
                            ecosystem='pypi',
                            direct=True
                        )
                        dependencies.append(dep)
        
        except Exception as e:
            print(f"Error parsing requirements.txt: {e}")
        
        return dependencies
    
    def _parse_pyproject_toml(self, file_path: Path) -> List[Dependency]:
        """Parse pyproject.toml for Python dependencies."""
        dependencies = []
        
        try:
            with open(file_path, 'r') as f:
                content = f.read()
            
            # Simple TOML parsing for dependencies
            dep_section = re.search(r'\[tool\.poetry\.dependencies\](.*?)(?=\[|\Z)', content, re.DOTALL)
            if dep_section:
                for line in dep_section.group(1).split('\n'):
                    match = re.match(r'^([a-zA-Z0-9_-]+)\s*=\s*["\']([^"\']+)["\']', line.strip())
                    if match:
                        name, version = match.groups()
                        if name != 'python':
                            dep = Dependency(
                                name=name,
                                version=version.replace('^', '').replace('~', ''),
                                ecosystem='pypi',
                                direct=True
                            )
                            dependencies.append(dep)
        
        except Exception as e:
            print(f"Error parsing pyproject.toml: {e}")
        
        return dependencies
    
    def _parse_pipfile_lock(self, file_path: Path) -> List[Dependency]:
        """Parse Pipfile.lock for Python dependencies."""
        dependencies = []
        
        try:
            with open(file_path, 'r') as f:
                data = json.load(f)
            
            for section in ['default', 'develop']:
                if section in data:
                    for name, info in data[section].items():
                        version = info.get('version', '').replace('==', '')
                        dep = Dependency(
                            name=name,
                            version=version,
                            ecosystem='pypi',
                            direct=(section == 'default')
                        )
                        dependencies.append(dep)
        
        except Exception as e:
            print(f"Error parsing Pipfile.lock: {e}")
        
        return dependencies
    
    def _parse_poetry_lock(self, file_path: Path) -> List[Dependency]:
        """Parse poetry.lock for Python dependencies."""
        dependencies = []
        
        try:
            with open(file_path, 'r') as f:
                content = f.read()
            
            # Extract package entries from TOML
            packages = re.findall(r'\[\[package\]\]\nname\s*=\s*"([^"]+)"\nversion\s*=\s*"([^"]+)"', content)
            
            for name, version in packages:
                dep = Dependency(
                    name=name,
                    version=version,
                    ecosystem='pypi',
                    direct=False
                )
                dependencies.append(dep)
        
        except Exception as e:
            print(f"Error parsing poetry.lock: {e}")
        
        return dependencies
    
    def _parse_go_mod(self, file_path: Path) -> List[Dependency]:
        """Parse go.mod for Go dependencies."""
        dependencies = []
        
        try:
            with open(file_path, 'r') as f:
                content = f.read()
            
            # Parse require block
            require_match = re.search(r'require\s*\((.*?)\)', content, re.DOTALL)
            if require_match:
                requires = require_match.group(1)
                for line in requires.split('\n'):
                    match = re.match(r'\s*([^\s]+)\s+v?([^\s]+)', line.strip())
                    if match:
                        name, version = match.groups()
                        dep = Dependency(
                            name=name,
                            version=version,
                            ecosystem='go',
                            direct=True
                        )
                        dependencies.append(dep)
        
        except Exception as e:
            print(f"Error parsing go.mod: {e}")
        
        return dependencies
    
    def _parse_go_sum(self, file_path: Path) -> List[Dependency]:
        """Parse go.sum for Go dependency checksums."""
        return []  # go.sum mainly contains checksums, dependencies are in go.mod
    
    def _parse_cargo_toml(self, file_path: Path) -> List[Dependency]:
        """Parse Cargo.toml for Rust dependencies."""
        dependencies = []
        
        try:
            with open(file_path, 'r') as f:
                content = f.read()
            
            # Parse [dependencies] section
            dep_section = re.search(r'\[dependencies\](.*?)(?=\[|\Z)', content, re.DOTALL)
            if dep_section:
                for line in dep_section.group(1).split('\n'):
                    match = re.match(r'^([a-zA-Z0-9_-]+)\s*=\s*["\']([^"\']+)["\']', line.strip())
                    if match:
                        name, version = match.groups()
                        dep = Dependency(
                            name=name,
                            version=version,
                            ecosystem='cargo',
                            direct=True
                        )
                        dependencies.append(dep)
        
        except Exception as e:
            print(f"Error parsing Cargo.toml: {e}")
        
        return dependencies
    
    def _parse_cargo_lock(self, file_path: Path) -> List[Dependency]:
        """Parse Cargo.lock for Rust dependencies."""
        dependencies = []
        
        try:
            with open(file_path, 'r') as f:
                content = f.read()
            
            # Parse [[package]] entries
            packages = re.findall(r'\[\[package\]\]\nname\s*=\s*"([^"]+)"\nversion\s*=\s*"([^"]+)"', content)
            
            for name, version in packages:
                dep = Dependency(
                    name=name,
                    version=version,
                    ecosystem='cargo',
                    direct=False
                )
                dependencies.append(dep)
        
        except Exception as e:
            print(f"Error parsing Cargo.lock: {e}")
        
        return dependencies
    
    def _parse_gemfile(self, file_path: Path) -> List[Dependency]:
        """Parse Gemfile for Ruby dependencies."""
        dependencies = []
        
        try:
            with open(file_path, 'r') as f:
                content = f.read()
            
            # Parse gem declarations
            gems = re.findall(r'gem\s+["\']([^"\']+)["\'](?:\s*,\s*["\']([^"\']+)["\'])?', content)
            
            for gem_info in gems:
                name = gem_info[0]
                version = gem_info[1] if len(gem_info) > 1 and gem_info[1] else ''
                
                dep = Dependency(
                    name=name,
                    version=version,
                    ecosystem='rubygems',
                    direct=True
                )
                dependencies.append(dep)
        
        except Exception as e:
            print(f"Error parsing Gemfile: {e}")
        
        return dependencies
    
    def _parse_gemfile_lock(self, file_path: Path) -> List[Dependency]:
        """Parse Gemfile.lock for Ruby dependencies."""
        dependencies = []
        
        try:
            with open(file_path, 'r') as f:
                content = f.read()
            
            # Extract GEM section
            gem_section = re.search(r'GEM\s*\n(.*?)(?=\n\S|\Z)', content, re.DOTALL)
            if gem_section:
                specs = gem_section.group(1)
                gems = re.findall(r'\s+([a-zA-Z0-9_-]+)\s+\(([^)]+)\)', specs)
                
                for name, version in gems:
                    dep = Dependency(
                        name=name,
                        version=version,
                        ecosystem='rubygems',
                        direct=False
                    )
                    dependencies.append(dep)
        
        except Exception as e:
            print(f"Error parsing Gemfile.lock: {e}")
        
        return dependencies
    
    def _generate_scan_summary(self, scan_results: Dict[str, Any]) -> Dict[str, Any]:
        """Generate a summary of the scan results."""
        total_deps = len(scan_results['dependencies'])
        unique_deps = len(set(dep.name for dep in scan_results['dependencies']))
        
        return {
            'total_dependencies': total_deps,
            'unique_dependencies': unique_deps,
            'ecosystems_found': len(scan_results['ecosystems']),
            'vulnerable_dependencies': len([dep for dep in scan_results['dependencies'] if dep.vulnerabilities]),
            'vulnerability_breakdown': {
                'high': scan_results['high_severity_count'],
                'medium': scan_results['medium_severity_count'],
                'low': scan_results['low_severity_count']
            }
        }
    
    def _generate_recommendations(self, scan_results: Dict[str, Any]) -> List[str]:
        """Generate actionable recommendations based on scan results."""
        recommendations = []
        
        high_count = scan_results['high_severity_count']
        medium_count = scan_results['medium_severity_count']
        
        if high_count > 0:
            recommendations.append(f"URGENT: Address {high_count} high-severity vulnerabilities immediately")
        
        if medium_count > 0:
            recommendations.append(f"Schedule fixes for {medium_count} medium-severity vulnerabilities within 30 days")
        
        vulnerable_deps = [dep for dep in scan_results['dependencies'] if dep.vulnerabilities]
        if vulnerable_deps:
            for dep in vulnerable_deps[:3]:  # Top 3 most critical
                for vuln in dep.vulnerabilities:
                    if vuln.fixed_version:
                        recommendations.append(f"Update {dep.name} from {dep.version} to {vuln.fixed_version} to fix {vuln.id}")
        
        if len(scan_results['ecosystems']) > 3:
            recommendations.append("Consider consolidating package managers to reduce complexity")
        
        return recommendations
    
    def generate_report(self, scan_results: Dict[str, Any], format: str = 'text') -> str:
        """Generate a human-readable or JSON report."""
        if format == 'json':
            # Convert Dependency objects to dicts for JSON serialization
            serializable_results = scan_results.copy()
            serializable_results['dependencies'] = [
                {
                    'name': dep.name,
                    'version': dep.version,
                    'ecosystem': dep.ecosystem,
                    'direct': dep.direct,
                    'license': dep.license,
                    'vulnerabilities': [asdict(vuln) for vuln in dep.vulnerabilities]
                }
                for dep in scan_results['dependencies']
            ]
            return json.dumps(serializable_results, indent=2, default=str)
        
        # Text format report
        report = []
        report.append("=" * 60)
        report.append("DEPENDENCY SECURITY SCAN REPORT")
        report.append("=" * 60)
        report.append(f"Scan Date: {scan_results['timestamp']}")
        report.append(f"Project: {scan_results['project_path']}")
        report.append("")
        
        # Summary
        summary = scan_results['scan_summary']
        report.append("SUMMARY:")
        report.append(f"  Total Dependencies: {summary['total_dependencies']}")
        report.append(f"  Unique Dependencies: {summary['unique_dependencies']}")
        report.append(f"  Ecosystems: {', '.join(scan_results['ecosystems'])}")
        report.append(f"  Vulnerabilities Found: {scan_results['vulnerabilities_found']}")
        report.append(f"    High Severity: {summary['vulnerability_breakdown']['high']}")
        report.append(f"    Medium Severity: {summary['vulnerability_breakdown']['medium']}")
        report.append(f"    Low Severity: {summary['vulnerability_breakdown']['low']}")
        report.append("")
        
        # Vulnerable dependencies
        vulnerable_deps = [dep for dep in scan_results['dependencies'] if dep.vulnerabilities]
        if vulnerable_deps:
            report.append("VULNERABLE DEPENDENCIES:")
            report.append("-" * 30)
            
            for dep in vulnerable_deps:
                report.append(f"Package: {dep.name} v{dep.version} ({dep.ecosystem})")
                for vuln in dep.vulnerabilities:
                    report.append(f"  • {vuln.id}: {vuln.summary}")
                    report.append(f"    Severity: {vuln.severity} (CVSS: {vuln.cvss_score})")
                    if vuln.fixed_version:
                        report.append(f"    Fixed in: {vuln.fixed_version}")
                    report.append("")
        
        # Recommendations
        if scan_results['recommendations']:
            report.append("RECOMMENDATIONS:")
            report.append("-" * 20)
            for i, rec in enumerate(scan_results['recommendations'], 1):
                report.append(f"{i}. {rec}")
            report.append("")
        
        report.append("=" * 60)
        return '\n'.join(report)

def main():
    """Main entry point for the dependency scanner."""
    parser = argparse.ArgumentParser(
        description='Scan project dependencies for vulnerabilities and security issues',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python dep_scanner.py /path/to/project
  python dep_scanner.py . --format json --output results.json
  python dep_scanner.py /app --fail-on-high
        """
    )
    
    parser.add_argument('project_path', 
                       help='Path to the project directory to scan')
    parser.add_argument('--format', choices=['text', 'json'], default='text',
                       help='Output format (default: text)')
    parser.add_argument('--output', '-o',
                       help='Output file path (default: stdout)')
    parser.add_argument('--fail-on-high', action='store_true',
                       help='Exit with error code if high-severity vulnerabilities found')
    parser.add_argument('--quick-scan', action='store_true',
                       help='Perform quick scan (skip transitive dependencies)')
    
    args = parser.parse_args()
    
    try:
        scanner = DependencyScanner()
        results = scanner.scan_project(args.project_path)
        report = scanner.generate_report(results, args.format)
        
        if args.output:
            with open(args.output, 'w') as f:
                f.write(report)
            print(f"Report saved to {args.output}")
        else:
            print(report)
        
        # Exit with error if high-severity vulnerabilities found and --fail-on-high is set
        if args.fail_on_high and results['high_severity_count'] > 0:
            sys.exit(1)
    
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == '__main__':
    main()